import Mathlib

namespace OAI

section
open scoped BigOperators
open Finset
open scoped Classical
namespace SharpLogRamsey.SupportMixtures
noncomputable section
variable {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

 def kernel (S : Finset A) (a : A) : ℝ :=
  if a∈S then 1/(S.card:ℝ) else 0

omit [Fintype A] in
lemma kernel_nonneg (S : Finset A) (a : A) : 0≤kernel S a := by
  unfold kernel
  split_ifs <;> positivity

lemma kernel_total (S : Finset A) (hS : S.Nonempty) : ∑ a, kernel S a=1 := by
  classical
  simp only [kernel,←sum_filter]
  have hf : univ.filter (fun a => a∈S)=S := by ext; simp
  rw [hf,sum_const,nsmul_eq_mul]
  have hn : (S.card:ℝ)≠0 := by exact_mod_cast card_ne_zero.mpr hS
  field_simp

 def mixture (w : I→ℝ) (S : I→Finset A) (a : A) : ℝ :=
  ∑ i, w i*kernel (S i) a

 def pairing (f : A→ℝ) (g : B→ℝ) (R : A→B→ℝ) : ℝ :=
  ∑ a, ∑ b, f a*g b*R a b

lemma pairing_mono (f f' : A→ℝ) (g g' : B→ℝ) (R : A→B→ℝ)
    (hf : ∀ a, 0≤f a) (hg : ∀ b, 0≤g b) (hR : ∀ a b, 0≤R a b)
    (hff : ∀ a,f a≤f' a) (hgg : ∀ b,g b≤g' b) :
    pairing f g R≤pairing f' g' R := by
  apply sum_le_sum
  intro a _
  apply sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_right _ (hR a b)
  exact mul_le_mul (hff a) (hgg b) (hg b) ((hf a).trans (hff a))

lemma pairing_scale (f : A→ℝ) (g : B→ℝ) (R : A→B→ℝ) (c d : ℝ) :
    pairing (fun a => c*f a) (fun b => d*g b) R=c*d*pairing f g R := by
  simp only [pairing,mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ring

lemma independent_pairing (w : I→ℝ) (v : J→ℝ)
    (S : I→Finset A) (T : J→Finset B) (R : A→B→ℝ) :
    (∑ i, ∑ j, w i*v j*pairing (kernel (S i)) (kernel (T j)) R)=
      pairing (mixture w S) (mixture v T) R := by
  simp only [pairing,mixture,mul_sum,sum_mul]
  calc
    _ = ∑ a, ∑ b, ∑ i, ∑ j,
        w i*v j*(kernel (S i) a*kernel (T j) b*R a b) := by
      calc
        _ = ∑ ij : I×J, ∑ ab : A×B,
            w ij.1*v ij.2*(kernel (S ij.1) ab.1*kernel (T ij.2) ab.2*R ab.1 ab.2) := by
          simp only [Fintype.sum_prod_type]
        _ = ∑ ab : A×B, ∑ ij : I×J,
            w ij.1*v ij.2*(kernel (S ij.1) ab.1*kernel (T ij.2) ab.2*R ab.1 ab.2) := sum_comm
        _ = _ := by simp only [Fintype.sum_prod_type]
    _ = _ := by
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro i _
      ring

theorem independent_pairing_le (w : I→ℝ) (v : J→ℝ)
    (S : I→Finset A) (T : J→Finset B) (R : A→B→ℝ)
    (p : A→ℝ) (q : B→ℝ) (c d : ℝ)
    (hw : ∀ i, 0≤w i) (hv : ∀ j, 0≤v j)
    (hR : ∀ a b, 0≤R a b)
    (hS : ∀ a, mixture w S a≤c*p a) (hT : ∀ b, mixture v T b≤d*q b) :
    (∑ i, ∑ j, w i*v j*pairing (kernel (S i)) (kernel (T j)) R)≤
      c*d*pairing p q R := by
  rw [independent_pairing]
  rw [←pairing_scale]
  apply pairing_mono _ _ _ _ R _ _ hR hS hT
  · intro a
    exact sum_nonneg (fun i _ => mul_nonneg (hw i) (kernel_nonneg _ a))
  · intro b
    exact sum_nonneg (fun j _ => mul_nonneg (hv j) (kernel_nonneg _ b))

lemma one_sided_pairing (w : I→ℝ) (S : I→Finset A) (q : B→ℝ) (R : A→B→ℝ) :
    (∑ i, w i*pairing (kernel (S i)) q R)=pairing (mixture w S) q R := by
  simp only [pairing,mixture,mul_sum,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro i _
  ring

theorem one_sided_pairing_le (w : I→ℝ) (S : I→Finset A)
    (p : A→ℝ) (q : B→ℝ) (R : A→B→ℝ) (c : ℝ)
    (hw : ∀ i,0≤w i) (hq : ∀ b,0≤q b) (hR : ∀ a b,0≤R a b)
    (hS : ∀ a,mixture w S a≤c*p a) :
    (∑ i,w i*pairing (kernel (S i)) q R)≤c*pairing p q R := by
  rw [one_sided_pairing]
  have H := pairing_mono (mixture w S) (fun a => c*p a) q q R
    (fun a => sum_nonneg (fun i _ => mul_nonneg (hw i) (kernel_nonneg _ a)))
      hq hR hS (fun _ => le_rfl)
  have he := pairing_scale p q R c 1
  simp only [one_mul,mul_one] at he
  rwa [he] at H

lemma kernel_incidence (S : Finset A) (T : Finset B) (R : A→B→Prop) :
    pairing (kernel S) (kernel T) (fun a b => if R a b then 1 else 0)=
      (((S×ˢT).filter (fun z => R z.1 z.2)).card:ℝ)/((S.card:ℝ)*(T.card:ℝ)) := by
  classical
  let U := (S×ˢT).filter (fun z => R z.1 z.2)
  have he : pairing (kernel S) (kernel T) (fun a b => if R a b then 1 else 0)=
      ∑ z : A×B, if z∈U then 1/((S.card:ℝ)*(T.card:ℝ)) else 0 := by
    simp only [pairing,Fintype.sum_prod_type]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    by_cases ha : a∈S <;> by_cases hb : b∈T <;> by_cases hr : R a b <;>
      simp [kernel,U,ha,hb,hr,mul_comm]
  rw [he,←sum_filter]
  have hf : univ.filter (fun z => z∈U)=U := by ext; simp
  rw [hf,sum_const,nsmul_eq_mul]
  change (U.card:ℝ)*(1/((S.card:ℝ)*(T.card:ℝ)))=(U.card:ℝ)/_
  ring

end
end SharpLogRamsey.SupportMixtures

end

end OAI
