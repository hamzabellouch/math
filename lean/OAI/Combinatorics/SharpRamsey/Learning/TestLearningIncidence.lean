import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.TestPointMoments

namespace OAI

section
namespace SharpLogRamsey.ProjectiveDuality
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.Incidence
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
local instance flat_JoinedTestLearningIncidence_1 : Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) := by
  let : Finite (Module.Dual K (Module.Dual K V)) := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem dual_variance_le {n : ℕ} (hdim : Module.finrank K V=n+3)
    (w : Projectivization K (Module.Dual K V) → ℝ) :
    (∑ x : Projectivization K V,
      ((∑ H, if SharpLogRamsey.Incidence.Incident x H then w H else 0) -
        (∑ i ∈ range (n+2), (Nat.card K:ℝ)^i) /
        (∑ i ∈ range (n+3), (Nat.card K:ℝ)^i) * ∑ H, w H)^2) ≤
      (Nat.card K:ℝ)^(n+1) * ∑ H,w H^2 := by
  have hh := projective_variance_le
    (show Module.finrank K (Module.Dual K V)=n+3 from Subspace.dual_finrank_eq.trans hdim) w
  rw [← (bidual (K:=K) (V:=V)).sum_comp] at hh
  simpa only [weightedIncidences,incident_bidual] using hh

end
end SharpLogRamsey.ProjectiveDuality

namespace SharpLogRamsey.RegularPencils
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.Incidence SharpLogRamsey.ProjectiveDuality
noncomputable section
variable {A : Type*} [Fintype A]

lemma square_tail_card (f : A → ℝ) (μ t V : ℝ) (ht : 0 ≤ t)
    (hv : ∑ x,(f x-μ)^2 ≤ V) :
    ((univ.filter (fun x => μ+t ≤ f x)).card:ℝ)*t^2 ≤ V := by
  calc
    _ = ∑ x ∈ univ.filter (fun x => μ+t ≤ f x), t^2 := by simp
    _ ≤ ∑ x ∈ univ.filter (fun x => μ+t ≤ f x), (f x-μ)^2 := by
      apply sum_le_sum
      intro x hx
      have hh := (mem_filter.mp hx).2
      nlinarith
    _ ≤ ∑ x,(f x-μ)^2 := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := hv

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem pencil_weight_tail {n : ℕ} (hdim : Module.finrank K V=n+3)
    (w : Projectivization K (Module.Dual K V) → ℝ)
    (hw : ∀ H, 0≤w H) (hw1 : ∀ H,w H≤1)
    (T : ℝ) (hT : 0≤T)
    (hmean : (∑ i ∈ range (n+2),(Nat.card K:ℝ)^i) /
      (∑ i ∈ range (n+3),(Nat.card K:ℝ)^i) * ∑ H,w H ≤ T/2) :
    ((univ.filter (fun x : Projectivization K V =>
      T ≤ ∑ H,if SharpLogRamsey.Incidence.Incident x H then w H else 0)).card:ℝ) * (T/2)^2 ≤
        (Nat.card K:ℝ)^(n+1) * ∑ H,w H := by
  let μ := (∑ i ∈ range (n+2),(Nat.card K:ℝ)^i) /
      (∑ i ∈ range (n+3),(Nat.card K:ℝ)^i) * ∑ H,w H
  have hnorm : ∑ H,w H^2 ≤ ∑ H,w H := by
    apply sum_le_sum
    intro H _
    nlinarith [hw H,hw1 H]
  have hv := (dual_variance_le hdim w).trans
    (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have ht := square_tail_card (fun x : Projectivization K V =>
    ∑ H,if SharpLogRamsey.Incidence.Incident x H then w H else 0) μ (T/2) _ (by positivity) hv
  apply le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card ?_))
    (sq_nonneg _)) ht
  intro x hx
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  have hh := (mem_filter.mp hx).2
  dsimp [μ]
  linarith

theorem pencil_family_tail {ι : Type*} [Fintype ι] {n : ℕ}
    (hdim : Module.finrank K V=n+3)
    (w : ι → Projectivization K (Module.Dual K V) → ℝ)
    (hw : ∀ i H,0≤w i H) (hw1 : ∀ i H,w i H≤1)
    (T : ℝ) (hT : 0≤T)
    (hmean : ∀ i,(∑ k ∈ range (n+2),(Nat.card K:ℝ)^k) /
      (∑ k ∈ range (n+3),(Nat.card K:ℝ)^k) * ∑ H,w i H ≤ T/2) :
    ((univ.biUnion (fun i => univ.filter (fun x : Projectivization K V =>
      T ≤ ∑ H,if SharpLogRamsey.Incidence.Incident x H then w i H else 0))).card:ℝ) * (T/2)^2 ≤
        (Nat.card K:ℝ)^(n+1) * ∑ i,∑ H,w i H := by
  calc
    _ ≤ (∑ i,((univ.filter (fun x : Projectivization K V =>
      T ≤ ∑ H,if SharpLogRamsey.Incidence.Incident x H then w i H else 0)).card:ℝ)) * (T/2)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast (card_biUnion_le : _ ≤ ∑ i,_)
    _ = ∑ i,((univ.filter (fun x : Projectivization K V =>
      T ≤ ∑ H,if SharpLogRamsey.Incidence.Incident x H then w i H else 0)).card:ℝ)*(T/2)^2 := by rw [sum_mul]
    _ ≤ ∑ i,(Nat.card K:ℝ)^(n+1) * ∑ H,w i H :=
      sum_le_sum (fun i _ => pencil_weight_tail hdim (w i) (hw i) (hw1 i) T hT (hmean i))
    _ = _ := by rw [mul_sum]

end
end SharpLogRamsey.RegularPencils
namespace SharpLogRamsey.PencilContrast
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.Incidence SharpLogRamsey.ProjectiveDuality
noncomputable section
variable {A B : Type*}

def degree (R : A → B → Prop) (Z : Finset B) (x : A) : ℝ :=
  ∑ H∈Z,if R x H then 1 else 0

lemma sum_degree (R : A → B → Prop) (S : Finset A) (Z : Finset B) :
    (∑ x∈S,degree R Z x) = ∑ H∈Z,∑ x∈S,if R x H then (1:ℝ) else 0 := by
  exact sum_comm

theorem support_large_degree (R : A → B → Prop) (S : Finset A) (Z : Finset B)
    (q N z a b : ℝ) (hq : 0 < q) (hN : 0 < N) (hz : 0 < z) (hb : 0 < b)
    (hh : (∑ H∈Z,(q/N)*∑ x∈S,if R x H then (1:ℝ) else 0) ≤ a*z) :
    ((S.filter (fun x => b*z/q ≤ degree R Z x)).card:ℝ) ≤ (a/b)*N := by
  have hid : (∑ H∈Z,(q/N)*∑ x∈S,if R x H then (1:ℝ) else 0) =
      (q/N)*∑ x∈S,degree R Z x := by rw [←mul_sum,sum_degree]
  rw [hid] at hh
  have hsum : (∑ x∈S,degree R Z x) ≤ a*z*N/q := by
    apply (le_div_iff₀ hq).mpr
    have ht := (div_le_iff₀ hN).mp (show q*(∑ x∈S,degree R Z x)/N ≤ a*z from by
      simpa only [div_mul_eq_mul_div] using hh)
    nlinarith
  have hmark : ((S.filter (fun x => b*z/q ≤ degree R Z x)).card:ℝ)*(b*z/q) ≤
      ∑ x∈S,degree R Z x := by
    calc
      _ = ∑ x∈S.filter (fun x => b*z/q ≤ degree R Z x),b*z/q := by simp
      _ ≤ ∑ x∈S.filter (fun x => b*z/q ≤ degree R Z x),degree R Z x :=
        sum_le_sum (fun _ hx => (mem_filter.mp hx).2)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun x _ _ => sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
  have hfin := hmark.trans hsum
  apply (le_of_mul_le_mul_right ?_ (show 0 < b*z/q by positivity))
  calc
    _ ≤ a*z*N/q := hfin
    _ = ((a/b)*N)*(b*z/q) := by field_simp

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem ambient_small_degree {n : ℕ} (hdim : Module.finrank K V=n+3)
    (Z : Finset (Projectivization K (Module.Dual K V))) (hZ : Z.Nonempty)
    (hQ : (10:ℝ) ≤ ∑ i∈range (n+3),(Nat.card K:ℝ)^i) :
    ((univ.filter (fun x : Projectivization K V =>
      degree SharpLogRamsey.Incidence.Incident Z x < (4/5:ℝ)*(Z.card:ℝ)/(Nat.card K:ℝ))).card:ℝ) ≤
        100*(Nat.card K:ℝ)^(n+3)/(Z.card:ℝ) := by
  let q : ℝ := Nat.card K
  let Q : ℝ := ∑ i∈range (n+3),q^i
  let u : ℝ := ∑ i∈range (n+2),q^i
  let z : ℝ := Z.card
  let μ : ℝ := u/Q*z
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hz : 0 < z := by dsimp [z]; exact_mod_cast card_pos.mpr hZ
  have hQ0 : 0 < Q := by dsimp [Q,q]; linarith
  have hgeom : Q=q*u+1 := by dsimp [Q,u]; rw [geom_sum_succ]
  have hmean : (9/10:ℝ)*z/q ≤ μ := by
    apply (div_le_iff₀ hq).mpr
    change (9/10:ℝ)*z ≤ u/Q*z*q
    rw [show u/Q*z*q=(u*z*q)/Q by ring,le_div_iff₀ hQ0]
    change (10:ℝ) ≤ Q at hQ
    have hh : 9*Q ≤ 10*(Q-1) := by linarith
    have ht := mul_le_mul_of_nonneg_right hh hz.le
    have hgz := congrArg (fun a : ℝ => a*z) hgeom
    nlinarith
  let w : Projectivization K (Module.Dual K V) → ℝ := fun H => if H∈Z then 1 else 0
  have hs : ∑ H,w H = z := by dsimp [w,z]; rw [←sum_filter]; simp
  have hs2 : ∑ H,w H^2 = z := by
    have hi : ∀ H,w H^2=w H := by intro H; dsimp [w]; split_ifs <;> norm_num
    simp_rw [hi]; exact hs
  have hdeg (x : Projectivization K V) :
      (∑ H,if SharpLogRamsey.Incidence.Incident x H then w H else 0)=degree SharpLogRamsey.Incidence.Incident Z x := by
    dsimp [w,degree]
    calc
      _ = ∑ H,if H∈Z then (if SharpLogRamsey.Incidence.Incident x H then (1:ℝ) else 0) else 0 := by
        apply sum_congr rfl
        intro H _
        split_ifs <;> rfl
      _ = _ := by rw [←sum_filter]; simp
  have hv := dual_variance_le hdim w
  simp_rw [hdeg,hs,hs2] at hv
  change (∑ x,(degree SharpLogRamsey.Incidence.Incident Z x-μ)^2) ≤ q^(n+1)*z at hv
  let E := univ.filter (fun x : Projectivization K V => degree SharpLogRamsey.Incidence.Incident Z x<(4/5:ℝ)*z/q)
  have he : (E.card:ℝ)*(z/(10*q))^2 ≤ q^(n+1)*z := by
    calc
      _ = ∑ _x∈E,(z/(10*q))^2 := by simp
      _ ≤ ∑ x∈E,(degree SharpLogRamsey.Incidence.Incident Z x-μ)^2 := by
        apply sum_le_sum
        intro x hx
        have hh := (mem_filter.mp hx).2
        have hgap : z/(10*q) ≤ μ-degree SharpLogRamsey.Incidence.Incident Z x := by
          have hi : (9/10:ℝ)*z/q-(4/5:ℝ)*z/q=z/(10*q) := by ring
          linarith
        nlinarith [show 0 ≤ z/(10*q) by positivity]
      _ ≤ ∑ x,(degree SharpLogRamsey.Incidence.Incident Z x-μ)^2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := hv
  change (E.card:ℝ) ≤ 100*q^(n+3)/z
  apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos (show 0 < z/(10*q) by positivity)))
  calc
    _ ≤ q^(n+1)*z := he
    _ = (100*q^(n+3)/z)*(z/(10*q))^2 := by
      rw [show n+3=(n+1)+2 by omega,pow_add]
      field_simp
      ring

end
end SharpLogRamsey.PencilContrast

end

end OAI
