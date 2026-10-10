import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! First variation of a real autonomous ODE. These elementary Taylor,
Grönwall and endpoint lemmas are shared by horizontal-frame and cotangent
Hamiltonian flows. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set Asymptotics
open scoped ContDiff Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem taylor_remainder_le (f : E → E) {S : Set E} (hS : Convex ℝ S)
    (hf : ∀ q ∈ S, DifferentiableAt ℝ f q)
    (L : ℝ≥0) (hL : LipschitzOnWith L (fderiv ℝ (f)) S)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖f y - f x -
      (fderiv ℝ (f) x) (y - x)‖ ≤
        (L : ℝ) * ‖y - x‖ ^ 2 := by
  let D := fderiv ℝ f x
  let r : E → E := fun z => f z - D z
  have hsegment : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hd (z : E) (hz : z ∈ segment ℝ x y) :
      HasFDerivWithinAt r (fderiv ℝ f z - D) (segment ℝ x y) z :=
    ((hf z (hsegment hz)).hasFDerivAt.sub D.hasFDerivAt).hasFDerivWithinAt
  have hbound (z : E) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ f z - D‖ ≤ (L : ℝ) * ‖y - x‖ := by
    calc
      _ ≤ (L : ℝ) * ‖z - x‖ := hL.norm_sub_le (hsegment hz) hx
      _ ≤ (L : ℝ) * ‖y - x‖ :=
        mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) L.coe_nonneg
  have hb := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le hd hbound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have heq : r y - r x = f y - f x - D (y - x) := by
    dsimp [r]
    rw [map_sub]
    abel
  rw [heq] at hb
  simpa only [pow_two, mul_assoc] using hb


theorem variation_remainder_derivative (f : E → E) (x y : ℝ → E)
    (V : ℝ → E →L[ℝ] E)
    (h : E) (t : ℝ)
    (hx : HasDerivAt x (f (x t)) t)
    (hy : HasDerivAt y (f (y t)) t)
    (hV : HasDerivAt V
      ((fderiv ℝ (f) (x t)).comp (V t)) t) :
    HasDerivAt (fun s => y s - x s - V s h)
      ((fderiv ℝ (f) (x t)) (y t - x t - V t h) +
        (f (y t) - f (x t) -
          (fderiv ℝ (f) (x t)) (y t - x t))) t := by
  have hv := hV.clm_apply (hasDerivAt_const t h)
  simp only [map_zero, add_zero] at hv
  convert (hy.sub hx).sub hv using 1
  simp only [ContinuousLinearMap.comp_apply, map_sub]
  abel

theorem variation_quadratic_error (f : E → E) (x y : ℝ → E)
    (V : ℝ → E →L[ℝ] E)
    (h : E) (K L T : ℝ) (hL : 0 ≤ L)
    (hx : ∀ t ∈ Icc 0 T, HasDerivAt x (f (x t)) t)
    (hy : ∀ t ∈ Icc 0 T, HasDerivAt y (f (y t)) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V
      ((fderiv ℝ (f) (x t)).comp (V t)) t)
    (hinit : y 0 = x 0 + h) (hVinit : V 0 = ContinuousLinearMap.id ℝ E)
    (hD : ∀ t ∈ Icc 0 T, ‖fderiv ℝ (f) (x t)‖ ≤ K)
    (htraj : ∀ t ∈ Icc 0 T, ‖y t - x t‖ ≤ Real.exp (K * T) * ‖h‖)
    (hTaylor : ∀ t ∈ Icc 0 T,
      ‖f (y t) - f (x t) -
        (fderiv ℝ (f) (x t)) (y t - x t)‖ ≤
          L * ‖y t - x t‖ ^ 2) :
    ∀ t ∈ Icc 0 T, ‖y t - x t - V t h‖ ≤
      gronwallBound 0 K (L * (Real.exp (K * T)) ^ 2 * ‖h‖ ^ 2) t := by
  let r : ℝ → E := fun t => y t - x t - V t h
  let D : ℝ → E →L[ℝ] E :=
    fun t => fderiv ℝ (f) (x t)
  let err : ℝ → E := fun t =>
    f (y t) - f (x t) -
      D t (y t - x t)
  have hr (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt r (D t (r t) + err t) t :=
    variation_remainder_derivative f x y V h t (hx t ht) (hy t ht) (hV t ht)
  have hrc : ContinuousOn r (Icc 0 T) := fun t ht => (hr t ht).continuousAt.continuousWithinAt
  have hr0 : r 0 = 0 := by simp only [r, hinit, hVinit, ContinuousLinearMap.id_apply]; abel
  have hb (t : ℝ) (ht : t ∈ Ico 0 T) :
      ‖D t (r t) + err t‖ ≤ K * ‖r t‖ + L * (Real.exp (K * T)) ^ 2 * ‖h‖ ^ 2 := by
    have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
    have hsq : ‖y t - x t‖ ^ 2 ≤ (Real.exp (K * T) * ‖h‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (htraj t ht') 2
    calc
      _ ≤ ‖D t (r t)‖ + ‖err t‖ := norm_add_le _ _
      _ ≤ K * ‖r t‖ + L * ‖y t - x t‖ ^ 2 := by
        exact add_le_add ((D t).le_of_opNorm_le (hD t ht') _) (hTaylor t ht')
      _ ≤ K * ‖r t‖ + L * (Real.exp (K * T) * ‖h‖) ^ 2 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hsq hL) _
      _ = _ := by ring
  intro t ht
  have hbound := norm_le_gronwallBound_of_norm_deriv_right_le hrc
    (fun s hs => (hr s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by rw [hr0, norm_zero]) hb t ht
  simpa only [sub_zero] using hbound

omit [NormedSpace ℝ E] in
/-- The Grönwall remainder is uniformly quadratic in the initial increment. -/
theorem gronwall_quadratic (K A T : ℝ) (h : E) :
    gronwallBound 0 K (A * ‖h‖ ^ 2) T = gronwallBound 0 K A T * ‖h‖ ^ 2 := by
  by_cases hK : K = 0
  · subst K
    simp only [gronwallBound_K0]
    ring
  · simp only [gronwallBound_of_K_ne_0 hK]
    ring

/-- A quadratic remainder for a local endpoint map proves the claimed
Fréchet derivative; no differentiability premise on that map is needed. -/
theorem hasFDerivAt_of_quadratic_error
    (F : E → E) (p : E)
    (V : E →L[ℝ] E) (C : ℝ)
    (hb : ∀ᶠ q in 𝓝 p, ‖F q - F p - V (q - p)‖ ≤ C * ‖q - p‖ ^ 2) :
    HasFDerivAt F V p := by
  have hbig : (fun q => F q - F p - V (q - p)) =O[𝓝 p]
      (fun q => ‖q - p‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hb] with q hq
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖q - p‖)] using hq
  rw [hasFDerivAt_iff_isLittleO]
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub p (by norm_num : 1 < 2))

/-- The endpoint map of a local family of genuine solutions has the
variational derivative. All quantitative hypotheses concern the local
vector field and its containing convex neighborhood. -/
theorem hasFDerivAt_flow_endpoint (f : E → E) (α : E × ℝ → E)
    (p : E) (S B : Set E) (hS : S ∈ 𝓝 p)
    (hB : Convex ℝ B) (hf : ∀ z ∈ B, DifferentiableAt ℝ f z)
    (K L : ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (hK : LipschitzOnWith K (f) B)
    (hL : LipschitzOnWith L (fderiv ℝ (f)) B)
    (hD : ∀ z ∈ B, ‖fderiv ℝ (f) z‖ ≤ K)
    (hα0 : ∀ q ∈ S, α (q, 0) = q)
    (hα : ∀ q ∈ S, ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => α (q, s)) (f (α (q, t))) t)
    (hαB : ∀ q ∈ S, ∀ t ∈ Icc 0 T, α (q, t) ∈ B)
    (V : ℝ → E →L[ℝ] E)
    (hV0 : V 0 = ContinuousLinearMap.id ℝ E)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V
      ((fderiv ℝ (f) (α (p, t))).comp (V t)) t) :
    HasFDerivAt (fun q => α (q, T)) (V T) p := by
  have hp : p ∈ S := mem_of_mem_nhds hS
  let A : ℝ := (L : ℝ) * (Real.exp ((K : ℝ) * T)) ^ 2
  apply hasFDerivAt_of_quadratic_error _ p (V T) (gronwallBound 0 K A T)
  filter_upwards [hS] with q hq
  have htraj (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖α (q, t) - α (p, t)‖ ≤ Real.exp ((K : ℝ) * T) * ‖q - p‖ := by
    have hb := dist_le_of_trajectories_ODE_of_mem
      (v := fun _ => f) (s := fun _ => B)
      (fun _ _ => hK)
      (fun s hs => (hα q hq s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hα q hq s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (fun s hs => hαB q hq s (Ico_subset_Icc_self hs))
      (fun s hs => (hα p hp s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hα p hp s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (fun s hs => hαB p hp s (Ico_subset_Icc_self hs))
      (le_refl (dist (α (q, 0)) (α (p, 0)))) t ht
    simp only [hα0 q hq, hα0 p hp, dist_eq_norm, sub_zero] at hb
    calc
      _ ≤ ‖q - p‖ * Real.exp ((K : ℝ) * t) := hb
      _ ≤ ‖q - p‖ * Real.exp ((K : ℝ) * T) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have herr := variation_quadratic_error f
    (fun s => α (p, s)) (fun s => α (q, s)) V (q - p) K L T L.coe_nonneg
    (hα p hp) (hα q hq) hV
    (by rw [hα0 q hq, hα0 p hp]; abel) hV0
    (fun s hs => hD _ (hαB p hp s hs)) htraj
    (fun s hs => taylor_remainder_le f hB hf L hL
      (hαB p hp s hs) (hαB q hq s hs)) T ⟨hT, le_rfl⟩
  rw [show (L : ℝ) * (Real.exp ((K : ℝ) * T)) ^ 2 * ‖q - p‖ ^ 2 =
    A * ‖q - p‖ ^ 2 from rfl, gronwall_quadratic] at herr
  exact herr

end
end PositiveEinsteinFour.FlowCalculus

end OAI
