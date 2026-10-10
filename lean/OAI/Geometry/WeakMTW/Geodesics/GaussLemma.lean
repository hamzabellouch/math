import Mathlib
import OAI.Geometry.WeakMTW.Variations.FirstVariation
import OAI.Geometry.WeakMTW.Geodesics.InitialScaling

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace GaussLemma
open Set Filter CoordinateGeometry
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem flow_gauss {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {x v : E} {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x, v)) ∈ U) (w : E) :
    G (Φ (T, (x, v))).1
      (fderiv ℝ Φ (T, (x, v)) (0, (0, v))).1
      (fderiv ℝ Φ (T, (x, v)) (0, (0, w))).1 = T ^ 2 * G x v w := by
  let χ : ℝ × ℝ → ℝ × (E × E) := fun q => (q.1, (x, v + q.2 • w))
  have hχ : ContDiff ℝ ∞ χ :=
    contDiff_fst.prodMk (contDiff_const.prodMk (contDiff_const.add
      (contDiff_snd.smul contDiff_const)))
  let W : Set (ℝ × ℝ) := χ ⁻¹' U
  have hW : IsOpen W := hU.preimage hχ.continuous
  let c : ℝ × ℝ → E := fun q => (Φ (χ q)).1
  let V : ℝ × ℝ → E := fun q => (Φ (χ q)).2
  have hcomp : ContDiffOn ℝ ∞ (Φ ∘ χ) W :=
    hΦ.comp hχ.contDiffOn (fun _ hq => hq)
  have hc : ContDiffOn ℝ 2 c W := hcomp.fst.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hV : ContDiffOn ℝ 1 V W := hcomp.snd.of_le (by simp)
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) T, (t, s) ∈ W := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hm : χ (t, 0) ∈ U := by simpa [χ] using hseg t ht
    have hh := ((hχ.continuous.comp continuous_swap).continuousAt (x := (0, t))).preimage_mem_nhds
      (hU.mem_nhds hm)
    exact hh
  let P : Set ℝ := {s | ∀ t ∈ Icc (0 : ℝ) T, (t, s) ∈ W}
  have hP : P ∈ 𝓝 (0 : ℝ) := hnear
  have hfan := FirstVariation.geodesic_fan_pairing hS
    (hG.differentiableOn (by simp)) hsym hpos hW hc hV
    (fun q hq => (hode (χ q) hq).1)
    (fun q hq => (hode (χ q) hq).2.fst)
    (fun q hq => (hode (χ q) hq).2.snd) hT hP
    (fun t ht s hs => hs t ht)
    (x := x) (v := v) (w := w)
    (fun s hs => congrArg Prod.fst (hzero (x, v + s • w) (hs 0 ⟨le_rfl, hT⟩)))
    (fun s hs => congrArg Prod.snd (hzero (x, v + s • w) (hs 0 ⟨le_rfl, hT⟩)))
    T ⟨hT, le_rfl⟩
  have hterm : (T, (x, v)) ∈ U := hseg T ⟨hT, le_rfl⟩
  have hdΦ := ((hΦ _ hterm).contDiffAt (hU.mem_nhds hterm)).differentiableAt
    (by simp)
  have hdχ : HasFDerivAt χ
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((0 : ℝ × ℝ →L[ℝ] E).prod
          ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w))) (T, 0) := by
    exact (hasFDerivAt_fst (p := (T, (0 : ℝ)))).prodMk
      ((hasFDerivAt_const x (T, (0 : ℝ))).prodMk
        (((hasFDerivAt_snd (p := (T, (0 : ℝ)))).smul_const w).const_add v))
  have hdΦ' : HasFDerivAt Φ (fderiv ℝ Φ (T, (x, v))) (χ (T, 0)) := by
    simpa [χ] using hdΦ.hasFDerivAt
  have hdc : HasFDerivAt c _ (T, (0 : ℝ)) := (hdΦ'.comp (T, (0 : ℝ)) hdχ).fst
  have hdval : fderiv ℝ c (T, 0) (0, 1) =
      (fderiv ℝ Φ (T, (x, v)) (0, (0, w))).1 := by
    rw [hdc.fderiv]
    simp [ContinuousLinearMap.comp_apply]
  have hr := GeodesicScaling.radial_variation hS hG hpos hU hΦ hzero hode hT hseg
  rw [hr, map_smul, smul_apply, smul_eq_mul]
  have hf : G (Φ (T, (x, v))).1 (Φ (T, (x, v))).2
      (fderiv ℝ Φ (T, (x, v)) (0, (0, w))).1 = T * G x v w := by
    simpa only [c, V, χ, zero_smul, add_zero, hdval] using hfan
  rw [hf]
  ring

end
end GaussLemma
end

end WeakMTWGlobalSupport

end OAI
