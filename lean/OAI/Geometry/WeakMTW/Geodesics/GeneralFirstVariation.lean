import Mathlib
import OAI.Geometry.WeakMTW.Variations.FirstVariation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter CoordinateGeometry
open scoped Topology ContDiff
namespace FirstVariation
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem geodesic_general_pairing {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {c V : ℝ × ℝ → E} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 c U) (hV : ContDiffOn ℝ 1 V U)
    (hmem : ∀ q ∈ U, c q ∈ S)
    (hct : ∀ q ∈ U, HasDerivAt (fun t => c (t, q.2)) (V q) q.1)
    (hVt : ∀ q ∈ U, HasDerivAt (fun t => V (t, q.2))
      (-christoffel G (c q) (V q) (V q)) q.1)
    {T : ℝ} (hT : 0 ≤ T) {P : Set ℝ} (hP : P ∈ 𝓝 (0 : ℝ))
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ P, (t, s) ∈ U)
    : ∀ t ∈ Icc (0 : ℝ) T,
      G (c (t, 0)) (V (t, 0)) (fderiv ℝ c (t, 0) (0, 1)) =
        G (c (0, 0)) (V (0, 0)) (fderiv ℝ c (0, 0) (0, 1)) +
        t * (fderiv ℝ G (c (0,0)) (fderiv ℝ c (0,0) (0,1)) (V (0,0)) (V (0,0)) / 2 +
          G (c (0,0)) (V (0,0)) (fderiv ℝ V (0,0) (0,1))) := by
  have hP0 : (0 : ℝ) ∈ P := mem_of_mem_nhds hP
  have h00 : (0, (0 : ℝ)) ∈ U := hseg 0 ⟨le_rfl, hT⟩ 0 hP0
  let J : ℝ → E := fun t => fderiv ℝ c (t, 0) (0, 1)
  let W : ℝ → E := fun t => fderiv ℝ V (t, 0) (0, 1)
  have hq : ∀ t ∈ Icc (0 : ℝ) T, (t, (0 : ℝ)) ∈ U := fun t ht => hseg t ht 0 hP0
  have hCdiff : ∀ t ∈ Icc (0 : ℝ) T, DifferentiableAt ℝ c (t, 0) :=
    fun t ht => ((hc _ (hq t ht)).contDiffAt (hU.mem_nhds (hq t ht))).differentiableAt (by norm_num)
  have hVdiff : ∀ t ∈ Icc (0 : ℝ) T, DifferentiableAt ℝ V (t, 0) :=
    fun t ht => ((hV _ (hq t ht)).contDiffAt (hU.mem_nhds (hq t ht))).differentiableAt (by norm_num)
  have hdJ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt J (W t) t := by
    intro t ht
    exact VariationCalculus.parameter_variation_hasDerivAt hU hc hct (hq t ht) (hVdiff t ht)
  have henergy : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ P,
      G (c (t, s)) (V (t, s)) (V (t, s)) = G (c (0,s)) (V (0,s)) (V (0,s)) := by
    intro t ht s hs
    have he := geodesic_energy_constant hS hG hsym hpos
      (fun r hr => hmem _ (hseg r hr s hs))
      (fun r hr => hct _ (hseg r hr s hs)) (fun r hr => hVt _ (hseg r hr s hs)) t ht
    exact he
  have henergyD : ∀ t ∈ Icc (0 : ℝ) T,
      fderiv ℝ G (c (t, 0)) (J t) (V (t, 0)) (V (t, 0)) +
        2 * G (c (t, 0)) (V (t, 0)) (W t) = fderiv ℝ G (c (0,0)) (J 0) (V (0,0)) (V (0,0)) +
        2 * G (c (0,0)) (V (0,0)) (W 0) := by
    intro t ht
    have hGs := (hG _ (hmem _ (hq t ht))).differentiableAt (hS.mem_nhds (hmem _ (hq t ht)))
    have hdL := hasDerivAt_metric_pairing hGs
      (parameter_hasDerivAt (hCdiff t ht)) (parameter_hasDerivAt (hVdiff t ht))
      (parameter_hasDerivAt (hVdiff t ht))
    have hdR := hasDerivAt_metric_pairing
      ((hG _ (hmem _ h00)).differentiableAt (hS.mem_nhds (hmem _ h00)))
      (parameter_hasDerivAt (hCdiff 0 ⟨le_rfl,hT⟩))
      (parameter_hasDerivAt (hVdiff 0 ⟨le_rfl,hT⟩))
      (parameter_hasDerivAt (hVdiff 0 ⟨le_rfl,hT⟩))
    have heq : (fun s => G (c (t, s)) (V (t, s)) (V (t, s))) =ᶠ[𝓝 (0 : ℝ)]
        (fun s => G (c (0,s)) (V (0,s)) (V (0,s))) := by
      filter_upwards [hP] with s hs
      exact henergy t ht s hs
    have he := hdL.unique (hdR.congr_of_eventuallyEq heq)
    rw [hsym _ (hmem _ (hq t ht)) _ (V (t, 0)),
      hsym _ (hmem _ h00) _ (V (0,0))] at he
    dsimp only [J,W] at ⊢
    linarith
  let A : ℝ := fderiv ℝ G (c (0,0)) (J 0) (V (0,0)) (V (0,0)) / 2 +
    G (c (0,0)) (V (0,0)) (W 0)
  have hpair : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun r => G (c (r, 0)) (V (r, 0)) (J r)) A t := by
    intro t ht
    have hm := hmem _ (hq t ht)
    have hd := geodesic_pairing_hasDerivAt (c := fun r => c (r, 0)) (V := fun r => V (r, 0)) (J := J) ((hG _ hm).differentiableAt (hS.mem_nhds hm))
      (hpos _ hm) (hct _ (hq t ht)) (hVt _ (hq t ht)) (hdJ t ht)
    convert! hd using 1
    dsimp [A]
    linarith [henergyD t ht]
  have hconst := constant_of_has_deriv_right_zero
    (f := fun t => G (c (t, 0)) (V (t, 0)) (J t) - t * A)
    (fun t ht => ((hpair t ht).sub ((hasDerivAt_id t).mul_const A)).continuousAt.continuousWithinAt)
    (fun t ht => by
      convert! ((hpair t (Ico_subset_Icc_self ht)).sub
        ((hasDerivAt_id t).mul_const A)).hasDerivWithinAt using 1; simp)
  intro t ht
  have he := hconst t ht
  simp only [zero_mul, sub_zero] at he
  change _ = _ + t * A
  linarith

end
end FirstVariation
end

end WeakMTWGlobalSupport

end OAI
