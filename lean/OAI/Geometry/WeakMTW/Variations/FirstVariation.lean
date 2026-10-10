import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.CoordinateGeometry
import OAI.Geometry.WeakMTW.Variations.CurveVariation

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace FirstVariation
open Set Filter CoordinateGeometry
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem geodesic_pairing_hasDerivAt {G : E → MetricTensor E}
    {c V J : ℝ → E} {t : ℝ} {W : E}
    (hG : DifferentiableAt ℝ G (c t))
    (hpos : ∀ v : E, v ≠ 0 → 0 < G (c t) v v)
    (hc : HasDerivAt c (V t) t)
    (hV : HasDerivAt V (-christoffel G (c t) (V t) (V t)) t)
    (hJ : HasDerivAt J W t) :
    HasDerivAt (fun r => G (c r) (V r) (J r))
      (fderiv ℝ G (c t) (J t) (V t) (V t) / 2 + G (c t) (V t) W) t := by
  have hd := hasDerivAt_metric_pairing hG hc hV hJ
  have hm := metric_christoffel hpos (V t) (V t) (J t)
  convert! hd using 1
  simp only [map_neg, neg_apply]
  linarith

omit [FiniteDimensional ℝ E] in
theorem parameter_hasDerivAt {c : ℝ × ℝ → E} {t s : ℝ}
    (hc : DifferentiableAt ℝ c (t, s)) :
    HasDerivAt (fun r => c (t, r)) (fderiv ℝ c (t, s) (0, 1)) s := by
  convert! hc.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_const s t).prodMk (hasDerivAt_id s)) using 1

theorem geodesic_fan_pairing {G : E → MetricTensor E} {S : Set E}
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
    {x v w : E} (hc0 : ∀ s ∈ P, c (0, s) = x)
    (hV0 : ∀ s ∈ P, V (0, s) = v + s • w) :
    ∀ t ∈ Icc (0 : ℝ) T,
      G (c (t, 0)) (V (t, 0)) (fderiv ℝ c (t, 0) (0, 1)) = t * G x v w := by
  have hP0 : (0 : ℝ) ∈ P := mem_of_mem_nhds hP
  have h00 : (0, (0 : ℝ)) ∈ U := hseg 0 ⟨le_rfl, hT⟩ 0 hP0
  have hx : x ∈ S := by simpa only [hc0 0 hP0] using hmem _ h00
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
      G (c (t, s)) (V (t, s)) (V (t, s)) = G x (v + s • w) (v + s • w) := by
    intro t ht s hs
    have he := geodesic_energy_constant hS hG hsym hpos
      (fun r hr => hmem _ (hseg r hr s hs))
      (fun r hr => hct _ (hseg r hr s hs)) (fun r hr => hVt _ (hseg r hr s hs)) t ht
    simpa only [hc0 s hs, hV0 s hs] using he
  have henergyD : ∀ t ∈ Icc (0 : ℝ) T,
      fderiv ℝ G (c (t, 0)) (J t) (V (t, 0)) (V (t, 0)) +
        2 * G (c (t, 0)) (V (t, 0)) (W t) = 2 * G x v w := by
    intro t ht
    have hGs := (hG _ (hmem _ (hq t ht))).differentiableAt (hS.mem_nhds (hmem _ (hq t ht)))
    have hdL := hasDerivAt_metric_pairing hGs
      (parameter_hasDerivAt (hCdiff t ht)) (parameter_hasDerivAt (hVdiff t ht))
      (parameter_hasDerivAt (hVdiff t ht))
    have hdR := hasDerivAt_metric_pairing ((hG x hx).differentiableAt (hS.mem_nhds hx))
      (hasDerivAt_const (0 : ℝ) x)
      (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v)
      (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v)
    have heq : (fun s => G (c (t, s)) (V (t, s)) (V (t, s))) =ᶠ[𝓝 (0 : ℝ)]
        (fun s => G x (v + s • w) (v + s • w)) := by
      filter_upwards [hP] with s hs
      exact henergy t ht s hs
    have he := hdL.unique (hdR.congr_of_eventuallyEq heq)
    simp only [id_eq, zero_smul, add_zero, map_zero, zero_apply, zero_add, one_smul] at he
    rw [hsym _ (hmem _ (hq t ht)) (W t) (V (t, 0)), hsym x hx w v] at he
    change fderiv ℝ G (c (t, 0)) (J t) (V (t, 0)) (V (t, 0)) +
      G (c (t, 0)) (V (t, 0)) (W t) + G (c (t, 0)) (V (t, 0)) (W t) =
      G x v w + G x v w at he
    linarith
  have hJ0 : J 0 = 0 := by
    have heq : (fun s => c (0, s)) =ᶠ[𝓝 (0 : ℝ)] (fun _ => x) := by
      filter_upwards [hP] with s hs
      exact hc0 s hs
    exact (parameter_hasDerivAt (hCdiff 0 ⟨le_rfl, hT⟩)).unique
      ((hasDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq heq)
  have hpair : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun r => G (c (r, 0)) (V (r, 0)) (J r)) (G x v w) t := by
    intro t ht
    have hm := hmem _ (hq t ht)
    have hd := geodesic_pairing_hasDerivAt (c := fun r => c (r, 0)) (V := fun r => V (r, 0)) (J := J) ((hG _ hm).differentiableAt (hS.mem_nhds hm))
      (hpos _ hm) (hct _ (hq t ht)) (hVt _ (hq t ht)) (hdJ t ht)
    convert! hd using 1
    linarith [henergyD t ht]
  have hconst := constant_of_has_deriv_right_zero
    (f := fun t => G (c (t, 0)) (V (t, 0)) (J t) - t * G x v w)
    (fun t ht => ((hpair t ht).sub ((hasDerivAt_id t).mul_const (G x v w))).continuousAt.continuousWithinAt)
    (fun t ht => by
      convert! ((hpair t (Ico_subset_Icc_self ht)).sub
        ((hasDerivAt_id t).mul_const (G x v w))).hasDerivWithinAt using 1; simp)
  intro t ht
  have he := hconst t ht
  simp only [hJ0, map_zero, zero_mul, sub_zero] at he
  exact sub_eq_zero.mp he

end
end FirstVariation

end

end WeakMTWGlobalSupport

end OAI
