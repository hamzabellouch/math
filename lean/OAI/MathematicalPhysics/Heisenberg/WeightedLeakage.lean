import OAI.MathematicalPhysics.Heisenberg.RoutedDissipation

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators

open scoped BigOperators Classical
namespace Heisenberg.FiniteLeakage

section

lemma weighted_young {A D b w p : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hb : 0 < b) (hp : p^2 ≤ A*D) :
    2*w*p ≤ b*D+A*w^2/b := by
  by_cases hz : A = 0
  · subst A
    have hp0 : p=0 := by nlinarith [sq_nonneg p]
    simp only [hp0,mul_zero,zero_mul,zero_div,add_zero]
    exact mul_nonneg hb.le hD
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
  have hh : 0 ≤ A*(b^2*D+A*w^2-2*b*w*p) := by
    have h1 := mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hp)
    nlinarith [sq_nonneg (b*p-A*w)]
  have hn : 0 ≤ b^2*D+A*w^2-2*b*w*p := (mul_nonneg_iff_of_pos_left hAp).mp hh
  apply (mul_le_mul_iff_of_pos_right hb).mp
  field_simp
  nlinarith

lemma weighted_suffix {n : ℕ} (w G : Fin n → ℝ) :
    (∑ i, w i*(∑ j, if i ≤ j then G j else 0)) =
      ∑ j, (∑ i, if i ≤ j then w i else 0)*G j := by
  simp only [Finset.mul_sum,Finset.sum_mul,mul_ite,ite_mul,mul_zero,zero_mul]
  exact Finset.sum_comm

theorem weighted_leakage {n : ℕ} (w L err pair energy loss residual : Fin n → ℝ)
    (m final A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1)
    (hW : ∀ i, 0 < ∑ j, if j ≤ i then w j else 0)
    (henergy : ∀ i, 0 ≤ energy i)
    (hpair : ∀ i, (pair i)^2 ≤ A*energy i)
    (hloss : ∀ i, 2*δ*energy i ≤ loss i+residual i)
    (hlower : ∀ i, m-err i-2*pair i+(∑ j, if i ≤ j then loss j else 0) ≤ L i)
    (hfinal : ∀ i, L i ≤ final) :
    m-(∑ i, w i*err i)-
      (∑ i, A*(w i)^2/(2*δ*(∑ j, if j ≤ i then w j else 0)))-
      (∑ i, (∑ j, if j ≤ i then w j else 0)*residual i) ≤ final := by
  let W : Fin n → ℝ := fun i => ∑ j, if j ≤ i then w j else 0
  have hp : ∀ i, 2*w i*pair i ≤ W i*loss i+W i*residual i+
      A*(w i)^2/(2*δ*W i) := by
    intro i
    have hh := weighted_young (w := w i) hA (henergy i) (show 0 < 2*δ*W i from mul_pos (mul_pos (by norm_num) hδ) (hW i)) (hpair i)
    have he := mul_le_mul_of_nonneg_left (hloss i) (hW i).le
    nlinarith
  have hl : (∑ i, w i*(m-err i-2*pair i+(∑ j, if i ≤ j then loss j else 0))) ≤ final := by
    calc
      _ ≤ ∑ i, w i*final := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ((hlower i).trans (hfinal i)) (hw i))
      _ = final := by rw [← Finset.sum_mul,hws,one_mul]
  have he : (∑ i, w i*(m-err i-2*pair i+(∑ j, if i ≤ j then loss j else 0))) =
      m-(∑ i,w i*err i)-(∑ i,2*w i*pair i)+(∑ i,W i*loss i) := by
    simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      weighted_suffix,←Finset.sum_mul,hws,one_mul]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hl
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hp i)
  simp only [Finset.sum_add_distrib] at hs
  change m-(∑ i,w i*err i)-(∑ i,A*(w i)^2/(2*δ*W i))-(∑ i,W i*residual i) ≤ final
  linarith

lemma sum_succ_real (n : ℕ) :
    (∑ i ∈ Finset.range n, ((i:ℝ)+1)) = (n:ℝ)*((n:ℝ)+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; push_cast; ring

lemma fin_prefix_succ {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, if j ≤ i then ((j:ℕ):ℝ)+1 else 0) =
      ((i:ℕ)+1:ℝ)*(((i:ℕ):ℝ)+2)/2 := by
  change (∑ j : Fin n, if (j:ℕ) ≤ (i:ℕ) then ((j:ℕ):ℝ)+1 else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j ≤ (i:ℕ) then (j:ℝ)+1 else 0)]
  have he : (∑ j ∈ Finset.range n, if j ≤ (i:ℕ) then (j:ℝ)+1 else 0) =
      ∑ j ∈ Finset.range ((i:ℕ)+1), ((j:ℝ)+1) := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [he,sum_succ_real]
  push_cast
  ring

def triangle {n : ℕ} (i : Fin n) : ℝ := 2*(((i:ℕ):ℝ)+1)/((n:ℝ)*((n:ℝ)+1))

lemma triangle_nonneg {n : ℕ} (i : Fin n) : 0 ≤ triangle i := by unfold triangle; positivity

lemma triangle_sum {n : ℕ} (hn : 0 < n) : (∑ i : Fin n, triangle i) = 1 := by
  simp only [triangle]
  rw [←Finset.sum_div,←Finset.mul_sum,Fin.sum_univ_eq_sum_range (fun j : ℕ => (j:ℝ)+1),sum_succ_real]
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  field_simp

lemma triangle_prefix {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, if j ≤ i then triangle j else 0) =
      ((((i:ℕ):ℝ)+1)*(((i:ℕ):ℝ)+2))/((n:ℝ)*((n:ℝ)+1)) := by
  have he : ∀ j : Fin n, (if j ≤ i then triangle j else 0) =
      2*(if j ≤ i then ((j:ℕ):ℝ)+1 else 0)/((n:ℝ)*((n:ℝ)+1)) := by
    intro j
    by_cases h : j ≤ i <;> simp [triangle,h]
  simp_rw [he]
  rw [← Finset.sum_div,← Finset.mul_sum,fin_prefix_succ]
  ring

lemma triangle_prefix_pos {n : ℕ} (i : Fin n) : 0 < ∑ j : Fin n, if j ≤ i then triangle j else 0 := by
  rw [triangle_prefix]
  have hn : (0:ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  positivity

theorem triangle_remainder {n : ℕ} (hn : 0 < n) {A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ) :
    (∑ i : Fin n, A*(triangle i)^2/(2*δ*(∑ j : Fin n, if j ≤ i then triangle j else 0))) ≤
      2*A/(δ*(n:ℝ)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hh : ∀ i : Fin n,
      A*(triangle i)^2/(2*δ*(∑ j : Fin n, if j ≤ i then triangle j else 0)) ≤
        2*A/(δ*(n:ℝ)*((n:ℝ)+1)) := by
    intro i
    rw [triangle_prefix]
    dsimp [triangle]
    have hi : (0:ℝ) ≤ (i:ℕ) := Nat.cast_nonneg _
    field_simp
    nlinarith
  calc
    _ ≤ ∑ _i : Fin n, 2*A/(δ*(n:ℝ)*((n:ℝ)+1)) := Finset.sum_le_sum (fun i _ => hh i)
    _ = 2*A/(δ*((n:ℝ)+1)) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

open scoped RealInnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem contraction_loss_lower (C : H →ₗ[ℝ] H) (eta g : H)
    (horth : ⟪eta,g⟫ = 0) (hg : ‖C g‖ ≤ ‖g‖) :
    ‖eta‖^2 - 2*⟪C eta,C (eta+g)⟫ ≤ ‖eta+g‖^2-‖C (eta+g)‖^2 := by
  have h0 := norm_add_sq_real eta g
  have h1 := norm_add_sq_real (C eta) (C g)
  rw [horth,mul_zero,add_zero] at h0
  have hcg : ‖C g‖^2 ≤ ‖g‖^2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hg
  simp only [map_add,inner_add_right,real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖C eta‖]

theorem finite_future_loss {n : ℕ} (hn : 0 < n)
    (partLoss energy loss residual err pair : Fin n → ℝ)
    (m final A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (henergy : ∀ i, 0 ≤ energy i)
    (hpair : ∀ i, (pair i)^2 ≤ A*energy i)
    (hloss : ∀ i, 2*δ*energy i ≤ loss i+residual i)
    (hinitial : ∀ i, m-err i-2*pair i ≤ partLoss i)
    (htelescope : ∀ i, partLoss i+(∑ j, if i ≤ j then loss j else 0) ≤ final) :
    m-(∑ i,triangle i*err i)-2*A/(δ*(n:ℝ))-
      (∑ i,(∑ j,if j ≤ i then triangle j else 0)*residual i) ≤ final := by
  have hh := weighted_leakage (triangle (n:=n)) (fun _ => final) err pair energy loss residual
    m final A δ hA hδ triangle_nonneg (triangle_sum hn) triangle_prefix_pos
    henergy hpair hloss (fun i => by linarith [hinitial i,htelescope i]) (fun _ => le_rfl)
  have ht := triangle_remainder hn hA hδ
  linarith

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
open scoped RealInnerProductSpace

def chain (C : ℕ → H →ₗ[ℝ] H) : ℕ → H →ₗ[ℝ] H
  | 0 => LinearMap.id
  | j+1 => (C j).comp (chain C j)

@[simp] lemma chain_zero (C : ℕ → H →ₗ[ℝ] H) (v : H) : chain C 0 v=v := rfl
@[simp] lemma chain_succ (C : ℕ → H →ₗ[ℝ] H) (j : ℕ) (v : H) :
    chain C (j+1) v=C j (chain C j v) := rfl

lemma chain_contraction (C : ℕ → H →ₗ[ℝ] H) (n : ℕ)
    (hC : ∀ j,j<n → ∀ v,‖C j v‖ ≤ ‖v‖) (v : H) : ‖chain C n v‖ ≤ ‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    exact (hC n (Nat.lt_succ_self n) _).trans (ih (fun j hj => hC j (by omega)))

lemma suffix_telescope (u : ℕ → ℝ) (m n : ℕ) :
    (∑ j ∈ Finset.range n,if m≤j then u j-u (j+1) else 0) =
      if m≤n then u m-u n else 0 := by
  induction n with
  | zero => by_cases hm : m=0 <;> simp [hm]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    by_cases hm : m≤n
    · simp only [ite_eq_left hm,ite_eq_left (show m≤n+1 by omega)]
      ring
    · by_cases he : m=n+1
      · subst m
        simp
      · simp [hm,show ¬m≤n+1 by omega]

lemma suffix_telescope_fin {n : ℕ} (u : ℕ → ℝ) (i : Fin n) :
    (∑ j : Fin n,if i ≤ j then u j-u (j+1) else 0) = u i-u n := by
  have hh := suffix_telescope u (i:ℕ) n
  rw [ite_eq_left (Nat.le_of_lt i.isLt)] at hh
  simpa only [Fin.le_iff_val_le_val] using
    ((Fin.sum_univ_eq_sum_range (fun j : ℕ => if (i:ℕ) ≤ j then u j-u (j+1) else 0) n).trans hh)

theorem contraction_chain_leakage (C : ℕ → H →ₗ[ℝ] H) (n : ℕ) (hn : 0<n)
    (hC : ∀ j,j<n → ∀ v,‖C j v‖ ≤ ‖v‖)
    (eta g : H) (horth : ⟪eta,g⟫=0)
    (energy pair err residual : Fin n → ℝ) (A δ : ℝ) (hA : 0≤A) (hδ : 0<δ)
    (henergy : ∀ i,0≤energy i)
    (hpair : ∀ i,(pair i)^2 ≤ A*energy i)
    (happrox : ∀ i : Fin n,⟪chain C i eta,chain C i (eta+g)⟫ ≤ err i+pair i)
    (henergy_loss : ∀ i,2*δ*energy i ≤
      ‖chain C i (eta+g)‖^2-‖chain C (i+1) (eta+g)‖^2+residual i) :
    ‖eta‖^2-2*(∑ i,triangle i*err i)-2*A/(δ*(n:ℝ))-
      (∑ i,(∑ j,if j ≤ i then triangle j else 0)*residual i) ≤
      ‖eta+g‖^2-‖chain C n (eta+g)‖^2 := by
  let u : ℕ → ℝ := fun j => ‖chain C j (eta+g)‖^2
  have hp : ∀ i : Fin n,‖eta‖^2-2*err i-2*pair i ≤ ‖eta+g‖^2-u i := by
    intro i
    have h := contraction_loss_lower (chain C i) eta g horth
      (chain_contraction C i (fun j hj => hC j (hj.trans i.isLt)) g)
    dsimp only [u]
    linarith [happrox i]
  have ht : ∀ i : Fin n,(‖eta+g‖^2-u i)+
      (∑ j : Fin n,if i ≤ j then u j-u (j+1) else 0) ≤
      ‖eta+g‖^2-u n := by
    intro i
    rw [suffix_telescope_fin]
    linarith
  have h := finite_future_loss hn (fun i => ‖eta+g‖^2-u i) energy
    (fun i => u i-u (i+1)) residual (fun i => 2*err i) pair
    (‖eta‖^2) (‖eta+g‖^2-u n) A δ hA hδ henergy hpair henergy_loss hp ht
  have he : (∑ i : Fin n,triangle i*(2*err i)) = 2*(∑ i,triangle i*err i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at h
  exact h

end Heisenberg.FiniteLeakage

end

end OAI
