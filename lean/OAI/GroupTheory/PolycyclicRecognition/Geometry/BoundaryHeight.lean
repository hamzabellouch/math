import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace OAI

/-! # Scalar and vector boundary height estimates

Haar-volume distortion on ray quotients yields additive trace bounds after
taking logarithms. Finitely many spanning traces then bound the full height
error. A linear coefficient compatible with a sublinear error is unique.
-/

namespace PolycyclicRecognition

/-- Uniform multiplicative comparison of positive quantities bounds the
difference of their logarithms. -/
theorem abs_log_sub_le_of_comparison {a b K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hK : 0 < K) (hab : a ≤ K * b) (hba : b ≤ K * a) :
    |Real.log a - Real.log b| ≤ Real.log K := by
  apply abs_sub_le_iff.mpr
  constructor
  · have h := Real.log_le_log ha hab
    rw [Real.log_mul hK.ne' hb.ne'] at h
    linarith
  · have h := Real.log_le_log hb hba
    rw [Real.log_mul hK.ne' ha.ne'] at h
    linarith

/-- Applying the logarithmic comparison to exponential Jacobians. -/
theorem abs_sub_le_log_of_exp_comparison {a b K : ℝ} (hK : 0 < K)
    (hab : Real.exp a ≤ K * Real.exp b) (hba : Real.exp b ≤ K * Real.exp a) :
    |a - b| ≤ Real.log K := by
  simpa only [Real.log_exp] using abs_log_sub_le_of_comparison
    (Real.exp_pos a) (Real.exp_pos b) hK hab hba

/-- A family of real linear forms spanning the dual separates points. -/
theorem separates_of_dual_span {W I : Type*} [AddCommGroup W] [Module ℝ W]
    (α : I → Module.Dual ℝ W)
    (hspan : Submodule.span ℝ (Set.range α) = ⊤)
    (w : W) (hw : ∀ i, α i w = 0) : w = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff ℝ w).mp
  intro φ
  have hzero : ∀ φ ∈ Submodule.span ℝ (Set.range α), φ w = 0 := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ => obtain ⟨i, rfl⟩ := hφ; exact hw i
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  exact hzero φ (hspan ▸ Submodule.mem_top)

/-- Finitely many separating trace bounds control the vector norm by one
constant depending only on those traces. -/
theorem exists_bound_of_separating_forms {W I : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I]
    (α : I → Module.Dual ℝ W)
    (hsep : ∀ w, (∀ i, α i w = 0) → w = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : W) (B : ℝ), 0 ≤ B →
      (∀ i, |α i w| ≤ B) → ‖w‖ ≤ C * B := by
  let L : W →ₗ[ℝ] (I → ℝ) := LinearMap.pi α
  have hker : LinearMap.ker L = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    apply sub_eq_zero.mp
    apply hsep
    intro i
    have hi := congrFun hxy i
    simpa [L, map_sub, sub_eq_zero] using hi
  obtain ⟨C, hC, hL⟩ := L.exists_antilipschitzWith hker
  refine ⟨C, hC, fun w B hB hw => ?_⟩
  apply (ZeroHomClass.bound_of_antilipschitz L hL w).trans
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  simpa only [L, LinearMap.pi_apply, Real.norm_eq_abs] using hw i

/-- In the boundary argument the ray traces span the dual height space. -/
theorem exists_bound_of_dual_span {W I : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I]
    (α : I → Module.Dual ℝ W)
    (hspan : Submodule.span ℝ (Set.range α) = ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : W) (B : ℝ), 0 ≤ B →
      (∀ i, |α i w| ≤ B) → ‖w‖ ≤ C * B :=
  exists_bound_of_separating_forms α (separates_of_dual_span α hspan)

/-- Bounded error plus arbitrarily small linear error cannot hide a nonzero
linear coefficient. This identifies each source trace with its target trace. -/
theorem eq_zero_of_sublinear_linear_bound {c B : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ t : ℝ, R ≤ t → 0 ≤ t →
      |t * c| ≤ B + ε * t) : c = 0 := by
  by_contra hc
  have hcpos : 0 < |c| := abs_pos.mpr hc
  obtain ⟨R, hR⟩ := h (|c| / 2) (by positivity)
  obtain ⟨t, ht⟩ := exists_gt (max (max R 0) (2 * B / |c|))
  have ht0 : 0 < t := lt_of_le_of_lt (le_max_right R 0) ((le_max_left _ _).trans_lt ht)
  have hRt : R ≤ t := (le_max_left R 0).trans ((le_max_left _ _).trans ht.le)
  have hBt : 2 * B < t * |c| :=
    (div_lt_iff₀ hcpos).mp ((le_max_right _ _).trans_lt ht)
  have hb := hR t hRt ht0.le
  rw [abs_mul, abs_of_pos ht0] at hb
  nlinarith

/-- A uniformly bounded trace error determines its linear coefficient once
the vector error is sublinear along every height ray. -/
theorem trace_eq_of_bounded_and_sublinear
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W]
    (α β : Module.Dual ℝ W) (A : W →ₗ[ℝ] W)
    (profile : W → ℝ → W) (B : ℝ)
    (hbound : ∀ w t, 0 ≤ t → |β (profile w t) - t * α w| ≤ B)
    (hsub : ∀ w ε, 0 < ε → ∃ R : ℝ, ∀ t, R ≤ t → 0 ≤ t →
      ‖profile w t - t • A w‖ ≤ ε * t) :
    α = β.comp A := by
  let βc : W →L[ℝ] ℝ := β.toContinuousLinearMap
  ext w
  have hc : β (A w) - α w = 0 := by
    apply eq_zero_of_sublinear_linear_bound (B := B)
    intro ε hε
    have hnorm : 0 < ‖βc‖ + 1 := by positivity
    obtain ⟨R, hR⟩ := hsub w (ε / (‖βc‖ + 1)) (div_pos hε hnorm)
    refine ⟨R, fun t ht ht0 => ?_⟩
    have hop := βc.le_opNorm (profile w t - t • A w)
    have he : |β (profile w t) - t * β (A w)| ≤ ε * t := by
      have hratio : ‖βc‖ * (ε / (‖βc‖ + 1)) ≤ ε := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hnorm).mpr
        nlinarith [norm_nonneg βc]
      calc
        _ = ‖βc (profile w t - t • A w)‖ := by
          simp [βc, map_sub, map_smul, Real.norm_eq_abs]
        _ ≤ ‖βc‖ * ‖profile w t - t • A w‖ := hop
        _ ≤ ‖βc‖ * ((ε / (‖βc‖ + 1)) * t) :=
          mul_le_mul_of_nonneg_left (hR t ht ht0) (norm_nonneg _)
        _ ≤ ε * t := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hratio ht0
    calc
      |t * (β (A w) - α w)| =
          |(β (profile w t) - t * α w) -
            (β (profile w t) - t * β (A w))| := by congr 1; ring
      _ ≤ |β (profile w t) - t * α w| + |β (profile w t) - t * β (A w)| :=
        abs_sub _ _
      _ ≤ B + ε * t := add_le_add (hbound w t ht0) he
  exact (sub_eq_zero.mp hc).symm

end PolycyclicRecognition

end OAI
