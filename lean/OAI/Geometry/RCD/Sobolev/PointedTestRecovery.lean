import OAI.Geometry.RCD.Sobolev.LipschitzMetricTransfer

namespace OAI

/-! # Lipschitz recovery of Euclidean tests on pointed source balls

The approximation map need not be Lipschitz. Infimum extension repairs its
pullback with the correct radius scaling and a uniform vanishing error.
-/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_lipschitz_test_recovery {n : ℕ} {p : X} {r S ε B : ℝ}
    (hr : 0<r) (hS : 0≤S) (hε : 0≤ε) (hB : 0≤B)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {ψ : Euclidean n → ℝ} {M : ℝ≥0} (hψ : LipschitzWith M ψ)
    (hψb : ∀ z, |ψ z|≤B) :
    ∃ F : X → ℝ, LipschitzWith ⟨(M:ℝ)/r,div_nonneg M.coe_nonneg hr.le⟩ F ∧
      (∀ x, |F x|≤B+M*ε) ∧
      ∀ x, dist x p≤S*r → |F x-ψ (v x)|≤M*ε := by
  let s := closedBall p (S*r)
  let L : ℝ≥0 := ⟨(M:ℝ)/r,div_nonneg M.coe_nonneg hr.le⟩
  have hApprox (x : X) (hx : x∈s) (z : X) (hz : z∈s) :
      |ψ (v x)-ψ (v z)|≤(L:ℝ)*dist x z+M*ε := by
    have hdist := (abs_le.mp (hv.2.1 x z hx hz)).2
    have htest := hψ.dist_le_mul (v x) (v z)
    rw [Real.dist_eq] at htest
    have hm := mul_le_mul_of_nonneg_left hdist M.coe_nonneg
    calc
      _ ≤ (M:ℝ)*dist (v x) (v z) := htest
      _ ≤ (M:ℝ)*(dist x z/r+ε) := by nlinarith only [hm]
      _ = _ := by
        change (M:ℝ)*(dist x z/r+ε)=((M:ℝ)/r)*dist x z+M*ε
        ring
  obtain ⟨f,hf,hfe⟩ := exists_lipschitz_metric_transfer
    (show s.Nonempty from ⟨p,mem_closedBall_self (mul_nonneg hS hr.le)⟩)
    (fun x => ψ (v x)) (fun x : X => x) L (mul_nonneg M.coe_nonneg hε)
    (fun x _ => (neg_le_neg (hψb (v x))).trans (neg_abs_le _)) hApprox
  let A := B+(M:ℝ)*ε
  have hA : 0≤A := add_nonneg hB (mul_nonneg M.coe_nonneg hε)
  have hfA (x : X) (hx : x∈s) : |f x|≤A := by
    have ht := abs_add_le (f x-ψ (v x)) (ψ (v x))
    simp only [sub_add_cancel] at ht
    have he := hfe x hx
    have hb := hψb (v x)
    dsimp only [A]
    linarith
  let F := fun x => min (max (f x) (-A)) A
  have hF : LipschitzWith L F := (hf.max_const (-A)).min_const A
  have hFA (x : X) : |F x|≤A := by
    apply abs_le.mpr
    exact ⟨le_min (le_max_right _ _) (by linarith),min_le_right _ _⟩
  have hFf (x : X) (hx : x∈s) : F x=f x := by
    dsimp only [F]
    rw [max_eq_left (abs_le.mp (hfA x hx)).1,min_eq_left (abs_le.mp (hfA x hx)).2]
  refine ⟨F,hF,hFA,?_⟩
  intro x hx
  rw [hFf x hx]
  exact hfe x hx

end RegularPointCoordinates

end

end OAI
