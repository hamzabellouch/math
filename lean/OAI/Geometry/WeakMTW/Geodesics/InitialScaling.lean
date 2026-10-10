import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.CoordinateGeometry
import OAI.Geometry.WeakMTW.Variations.FlowLinearization

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace GeodesicScaling
open Set Filter CoordinateGeometry
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem lowerChristoffel_smul_left (D : E →L[ℝ] MetricTensor E) (a : ℝ) (v w : E) :
    lowerChristoffel D (a • v) w = a • lowerChristoffel D v w := by
  ext z
  simp [lowerChristoffel_apply]
  ring

theorem lowerChristoffel_smul_right (D : E →L[ℝ] MetricTensor E) (a : ℝ) (v w : E) :
    lowerChristoffel D v (a • w) = a • lowerChristoffel D v w := by
  ext z
  simp [lowerChristoffel_apply]
  ring

theorem christoffel_smul_smul (G : E → MetricTensor E) (x : E) (a : ℝ) (v w : E) :
    christoffel G x (a • v) (a • w) = a • a • christoffel G x v w := by
  simp only [christoffel, lowerChristoffel_smul_left, lowerChristoffel_smul_right, map_smul]

def scalePhase (s : ℝ) : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.fst ℝ E E).prod (s • ContinuousLinearMap.snd ℝ E E)

@[simp] theorem scalePhase_apply (s : ℝ) (q : E × E) : scalePhase s q = (q.1, s • q.2) := rfl
@[simp] theorem scalePhase_one (q : E × E) : scalePhase 1 q = q := by simp

theorem scale_spray (G : E → MetricTensor E) (s : ℝ) (q : E × E) :
    scalePhase s (s • geodesicSpray G q) = geodesicSpray G (scalePhase s q) := by
  simp [scalePhase, geodesicSpray, christoffel_smul_smul]

variable [FiniteDimensional ℝ E]

theorem rescale_flow {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {q : E × E} {T s : ℝ} (hT : 0 ≤ T)
    (hseg₁ : ∀ t ∈ Icc (0 : ℝ) T, (t, scalePhase s q) ∈ U)
    (hseg₂ : ∀ t ∈ Icc (0 : ℝ) T, (s * t, q) ∈ U) :
    ∀ t ∈ Icc (0 : ℝ) T, Φ (t, scalePhase s q) = scalePhase s (Φ (s * t, q)) := by
  let u : ℝ → E × E := fun t => Φ (t, scalePhase s q)
  let v : ℝ → E × E := fun t => scalePhase s (Φ (s * t, q))
  have hdu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (geodesicSpray G (u t)) t :=
    fun t ht => (hode _ (hseg₁ t ht)).2
  have hdv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt v (geodesicSpray G (v t)) t := by
    intro t ht
    have hd := (hode _ (hseg₂ t ht)).2.scomp t ((hasDerivAt_id t).const_mul s)
    have he := (scalePhase s).hasFDerivAt.comp_hasDerivAt t hd
    convert! he using 1
    simp only [mul_one, scale_spray, v]
  have hmem : ∀ t ∈ Icc (0 : ℝ) T, (u t).1 ∈ S ∧ (v t).1 ∈ S := by
    intro t ht
    exact ⟨(hode _ (hseg₁ t ht)).1, (hode _ (hseg₂ t ht)).1⟩
  have hf : ∀ z ∈ u '' Icc (0 : ℝ) T ∪ v '' Icc (0 : ℝ) T,
      ContDiffAt ℝ 1 (geodesicSpray G) z := by
    intro z hz
    have hzS : z.1 ∈ S := by
      rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · exact (hmem t ht).1
      · exact (hmem t ht).2
    exact (((contDiffOn_geodesicSpray hS hG hpos) z ⟨hzS, mem_univ _⟩).contDiffAt
      ((hS.prod isOpen_univ).mem_nhds ⟨hzS, mem_univ _⟩)).of_le (by simp)
  have h0 : u 0 = v 0 := by
    simp only [u, v, mul_zero, hzero _ (hseg₁ 0 ⟨le_rfl, hT⟩)]
    rw [hzero q (by simpa using hseg₂ 0 ⟨le_rfl, hT⟩)]
  exact fun t ht => FlowLinearization.unique_Icc
    (fun r hr => (hdu r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hdv r hr).continuousAt.continuousWithinAt) hf
    (fun r hr => (hdu r hr).hasDerivWithinAt) (fun r hr => (hdv r hr).hasDerivWithinAt) h0 ht

theorem radial_variation {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {q : E × E} {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, q) ∈ U) :
    (fderiv ℝ Φ (T, q) (0, (0, q.2))).1 = T • (Φ (T, q)).2 := by
  have hneigh : ∀ᶠ s in 𝓝 (1 : ℝ), ∀ t ∈ Icc (0 : ℝ) T,
      (t, scalePhase s q) ∈ U ∧ (s * t, q) ∈ U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hA : Continuous (fun z : ℝ × ℝ => (z.2, scalePhase z.1 q)) := by
      exact continuous_snd.prodMk (continuous_const.prodMk (continuous_fst.smul continuous_const))
    have hB : Continuous (fun z : ℝ × ℝ => (z.1 * z.2, q)) :=
      (continuous_fst.mul continuous_snd).prodMk continuous_const
    have hmem : (t, q) ∈ U := hseg t ht
    have h₁ := (hA.continuousAt (x := (1, t))).preimage_mem_nhds
      (t := U) (by simpa using hU.mem_nhds hmem)
    have h₂ := (hB.continuousAt (x := (1, t))).preimage_mem_nhds
      (t := U) (by simpa using hU.mem_nhds hmem)
    exact Filter.inter_mem h₁ h₂
  have heq : (fun s => (Φ (T, scalePhase s q)).1) =ᶠ[𝓝 (1 : ℝ)]
      (fun s => (Φ (s * T, q)).1) := by
    filter_upwards [hneigh] with s hs
    have he := rescale_flow hS hG hpos hzero hode hT (fun t ht => (hs t ht).1)
      (fun t ht => (hs t ht).2) T ⟨hT, le_rfl⟩
    simpa only [scalePhase_apply] using congrArg Prod.fst he
  have hpath : HasDerivAt (fun s : ℝ => (T, scalePhase s q)) (0, (0, q.2)) 1 := by
    convert! (hasDerivAt_const (1 : ℝ) T).prodMk
      ((hasDerivAt_const (1 : ℝ) q.1).prodMk ((hasDerivAt_id (1 : ℝ)).smul_const q.2)) using 1
    simp
  have hTx := hseg T ⟨hT, le_rfl⟩
  have hdΦ := (((hΦ _ hTx).contDiffAt (hU.mem_nhds hTx)).differentiableAt (by simp)).hasFDerivAt
  have hdΦ' : HasFDerivAt Φ (fderiv ℝ Φ (T, q)) (T, scalePhase 1 q) := by
    simpa using hdΦ
  have hdL0 := hdΦ'.comp_hasDerivAt (1 : ℝ) hpath
  have hdL : HasDerivAt (fun s => (Φ (T, scalePhase s q)).1)
      (fderiv ℝ Φ (T, q) (0, (0, q.2))).1 1 := by
    convert! hdL0.fst using 1
  have hdPos : HasDerivAt (fun t => (Φ (t, q)).1) (Φ (T, q)).2 T :=
    (hode _ hTx).2.fst
  have hdPos' : HasDerivAt (fun t => (Φ (t, q)).1) (Φ (T, q)).2 (1 * T) := by
    simpa using hdPos
  have hdR := hdPos'.scomp (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).mul_const T)
  simpa only [one_mul, one_smul] using hdL.unique (hdR.congr_of_eventuallyEq heq)

end
end GeodesicScaling

end

end WeakMTWGlobalSupport

end OAI
