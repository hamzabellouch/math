import Mathlib
import OAI.Geometry.WeakMTW.Variations.FlowLinearization
import OAI.Geometry.WeakMTW.Geodesics.GeneralFirstVariation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter CoordinateGeometry
open scoped Topology ContDiff
namespace FirstVariation
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem flow_first_variation {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0,q) ∈ U → Φ (0,q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t,q.2)) (geodesicSpray G (Φ q)) q.1)
    {q : E × E} {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t,q) ∈ U) (w : E × E) :
    G (Φ (T,q)).1 (Φ (T,q)).2 (fderiv ℝ Φ (T,q) (0,w)).1 =
      G q.1 q.2 w.1 + T * (fderiv ℝ G q.1 w.1 q.2 q.2 / 2 + G q.1 q.2 w.2) := by
  let χ : ℝ × ℝ → ℝ × (E × E) := fun z => (z.1,q+z.2 • w)
  have hχ : ContDiff ℝ ∞ χ := contDiff_fst.prodMk
    (contDiff_const.add (contDiff_snd.smul contDiff_const))
  let W := χ ⁻¹' U
  have hW : IsOpen W := hU.preimage hχ.continuous
  let c : ℝ × ℝ → E := fun z => (Φ (χ z)).1
  let V : ℝ × ℝ → E := fun z => (Φ (χ z)).2
  have hcomp : ContDiffOn ℝ ∞ (Φ ∘ χ) W := hΦ.comp hχ.contDiffOn (fun _ hz => hz)
  have hcSmooth : ContDiffOn ℝ ∞ c W := hcomp.fst
  have hc : ContDiffOn ℝ 2 c W := hcSmooth.of_le (by simp)
  have hVSmooth : ContDiffOn ℝ ∞ V W := hcomp.snd
  have hV : ContDiffOn ℝ 1 V W := hVSmooth.of_le (by simp)
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) T, (t,s) ∈ W := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hm : χ (t,0) ∈ U := by simpa [χ] using hseg t ht
    exact ((hχ.continuous.comp continuous_swap).continuousAt (x := (0,t))).preimage_mem_nhds
      (hU.mem_nhds hm)
  let P : Set ℝ := {s | ∀ t ∈ Icc (0 : ℝ) T, (t,s) ∈ W}
  have hP : P ∈ 𝓝 (0 : ℝ) := hnear
  have hfan := geodesic_general_pairing hS (hG.differentiableOn (by simp)) hsym hpos
    hW hc hV (fun z hz => (hode (χ z) hz).1)
    (fun z hz => (hode (χ z) hz).2.fst)
    (fun z hz => (hode (χ z) hz).2.snd) hT hP (fun t ht s hs => hs t ht)
    T ⟨hT,le_rfl⟩
  have hdχ (t : ℝ) : HasFDerivAt χ
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w))
      (t,0) :=
    (hasFDerivAt_fst (p := (t,(0 : ℝ)))).prodMk
      (((hasFDerivAt_snd (p := (t,(0 : ℝ)))).smul_const w).const_add q)
  have hfd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      fderiv ℝ c (t,0) (0,1) = (fderiv ℝ Φ (t,q) (0,w)).1 ∧
      fderiv ℝ V (t,0) (0,1) = (fderiv ℝ Φ (t,q) (0,w)).2 := by
    have hm := hseg t ht
    have hd := ((hΦ _ hm).contDiffAt (hU.mem_nhds hm)).differentiableAt (by simp)
    have hd' : HasFDerivAt Φ (fderiv ℝ Φ (t,q)) (χ (t,0)) := by
      simpa [χ] using hd.hasFDerivAt
    have hh := hd'.comp (t,(0 : ℝ)) (hdχ t)
    constructor
    · have hh₁ : HasFDerivAt c _ (t,0) := hh.fst
      rw [hh₁.fderiv]; simp
    · have hh₂ : HasFDerivAt V _ (t,0) := hh.snd
      rw [hh₂.fderiv]; simp
  have hinit := hzero q (hseg 0 ⟨le_rfl,hT⟩)
  have hdinit := FlowLinearization.initial_variation hU (hΦ.of_le (by simp)) hzero
    (w := w) (hseg 0 ⟨le_rfl,hT⟩)
  rw [(hfd T ⟨hT,le_rfl⟩).1,(hfd 0 ⟨le_rfl,hT⟩).1,(hfd 0 ⟨le_rfl,hT⟩).2,hdinit] at hfan
  simpa only [c,V,χ,zero_smul,add_zero,hinit] using hfan

end
end FirstVariation
end

end WeakMTWGlobalSupport

end OAI
