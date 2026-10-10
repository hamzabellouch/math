import OAI.Probability.SLE.Geometry.StoppedBoundaryMeasurability
import OAI.Probability.SLE.Geometry.RandomRestartEvents
import OAI.Probability.SLE.Geometry.GeometricTubeSupport

namespace OAI

/-! Measurable continuation tubes whose physical boundary charts depend on
the stopped past. Positivity of each section uses the published geometric
support theorem only for one fixed open tube at a time. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance : LocallyCompactSpace closedHalfPlane :=
  isClosed_closedHalfPlane.locallyCompactSpace

def ClosedPathProperty (p : C(ℝ≥0, ℂ)) : Prop := ∀ t, 0 ≤ (p t).im

theorem isClosed_closedPathProperty : IsClosed {p | ClosedPathProperty p} := by
  have he : {p | ClosedPathProperty p} =
      ⋂ t : ℝ≥0, {p : C(ℝ≥0, ℂ) | 0 ≤ (p t).im} := by
    ext p
    simp only [ClosedPathProperty, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isClosed_iInter fun t =>
    isClosed_le continuous_const (Complex.continuous_im.comp (continuous_eval_const t))

/-- Give arbitrary continuous paths a measurable closed-half-plane version.
On every actual chordal trace this is precisely the original path. -/
def liftClosedPath (p : C(ℝ≥0, ℂ)) : C(ℝ≥0, closedHalfPlane) := by
  classical
  exact if hp : ClosedPathProperty p then
    ⟨fun t => ⟨p t, hp t⟩, p.continuous.subtype_mk _⟩
  else ContinuousMap.const _ ⟨0, by simp [closedHalfPlane]⟩

theorem liftClosedPath_apply (p : C(ℝ≥0, ℂ)) (hp : ClosedPathProperty p)
    (t : ℝ≥0) : (liftClosedPath p t : ℂ) = p t := by
  simp [liftClosedPath, hp]

theorem measurable_liftClosedPath : Measurable liftClosedPath := by
  classical
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hf : Measurable (fun p : {p : C(ℝ≥0, ℂ) | ClosedPathProperty p} =>
      (⟨p.1 t, p.2 t⟩ : closedHalfPlane)) :=
    ((ContinuousMap.measurable_eval t).comp measurable_subtype_coe).subtype_mk
  convert hf.dite (g := fun _ => (⟨0, by simp [closedHalfPlane]⟩ : closedHalfPlane))
    measurable_const isClosed_closedPathProperty.measurableSet using 1
  funext p
  by_cases hp : ClosedPathProperty p <;> simp [liftClosedPath, hp]

def pathTubeEventIn {Y : Type*} [TopologicalSpace Y] (O W : Set Y) :
    Set C(ℝ≥0, Y) :=
  {p | ∃ T : ℝ≥0, 0 < T ∧ MapsTo p (Icc 0 T) O ∧ p T ∈ W}

theorem isOpen_pathTubeEventIn {Y : Type*} [TopologicalSpace Y]
    {O W : Set Y} (hO : IsOpen O) (hW : IsOpen W) :
    IsOpen (pathTubeEventIn O W) := by
  have he : pathTubeEventIn O W = ⋃ T : ℝ≥0, ⋃ (_ : 0 < T),
      {p : C(ℝ≥0, Y) | MapsTo p (Icc 0 T) O} ∩
        (fun p : C(ℝ≥0, Y) => p T) ⁻¹' W := by
    ext p
    simp only [pathTubeEventIn, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    constructor <;> rintro ⟨T, hT, hN, hV⟩ <;> exact ⟨T, hT, hN, hV⟩
  rw [he]
  exact isOpen_iUnion fun T => isOpen_iUnion fun _ =>
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc hO).inter
      (hW.preimage (continuous_eval_const T))

def randomBoundaryTubeSet {Ω : Type*}
    (Fb : Ω → C(closedHalfPlane, OnePoint ℂ)) (O W : Set (OnePoint ℂ)) :
    Set (Ω × C(ℝ≥0, closedHalfPlane)) :=
  {x | (Fb x.1).comp x.2 ∈ pathTubeEventIn O W}

theorem measurableSet_randomBoundaryTubeSet
    {Ω : Type*} [MeasurableSpace Ω]
    (Fb : Ω → C(closedHalfPlane, OnePoint ℂ)) (hFb : Measurable Fb)
    {O W : Set (OnePoint ℂ)} (hO : IsOpen O) (hW : IsOpen W) :
    MeasurableSet (randomBoundaryTubeSet Fb O W) := by
  have hc : Continuous (fun x : C(ℝ≥0, closedHalfPlane) ×
      C(closedHalfPlane, OnePoint ℂ) => x.2.comp x.1) := ContinuousMap.continuous_comp'
  exact (isOpen_pathTubeEventIn hO hW).measurableSet.preimage
    (hc.measurable.comp (measurable_snd.prodMk (hFb.comp measurable_fst)))

/-- Each physical open continuation has positive probability under the
fresh trace law once one simple parameter route lies in it. -/
theorem boundary_tube_positive_of_geometric_support
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (gp : Ω → C(ℝ≥0, ℂ)) (hclosed : ∀ ω, ClosedPathProperty (gp ω))
    (hsupport : PublishedGeometricTubeSupport P (fun ω => gp ω))
    (Fb : C(closedHalfPlane, OnePoint ℂ))
    (O W : Set (OnePoint ℂ)) (hO : IsOpen O) (hW : IsOpen W)
    (z : ℂ) (p : Path (0 : ℂ) z) (hinj : Function.Injective p)
    (hpH : ∀ t, t ≠ 0 → p t ∈ upperHalfPlane)
    (hroute : ∀ t, Fb ⟨p t, by
      by_cases ht : t = 0
      · simp [ht, closedHalfPlane]
      · exact (show 0 < (p t).im from hpH t ht).le⟩ ∈ O)
    (hend : Fb ⟨z, by simpa using (show 0 < (p 1).im from hpH 1 (by norm_num)).le⟩ ∈ W) :
    0 < P {ω | Fb.comp (liftClosedPath (gp ω)) ∈ pathTubeEventIn O W} := by
  obtain ⟨N, hN, hNe⟩ := isOpen_induced_iff.mp (hO.preimage Fb.continuous)
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.mp (hW.preimage Fb.continuous)
  have hpclosed (t : unitInterval) : p t ∈ closedHalfPlane := by
    by_cases ht : t = 0
    · simp [ht, closedHalfPlane]
    · exact (show 0 < (p t).im from hpH t ht).le
  have hNr : range p ⊆ N := by
    rintro _ ⟨t, rfl⟩
    have ht := hroute t
    change (⟨p t, hpclosed t⟩ : closedHalfPlane) ∈ Fb ⁻¹' O at ht
    rw [← hNe] at ht
    exact ht
  have hzV : z ∈ V := by
    change (⟨z, by simpa using (show 0 < (p 1).im from hpH 1 (by norm_num)).le⟩ : closedHalfPlane) ∈
      Fb ⁻¹' W at hend
    rw [← hVe] at hend
    exact hend
  apply (hsupport z p hinj hpH N V hN hV hNr hzV).trans_le
  apply measure_mono
  rintro ω ⟨T, hT, htrace, hlast⟩
  refine ⟨T, hT, ?_, ?_⟩
  · intro t ht
    have hn : liftClosedPath (gp ω) t ∈ Subtype.val ⁻¹' N := by
      change (liftClosedPath (gp ω) t : ℂ) ∈ N
      rw [liftClosedPath_apply _ (hclosed ω)]
      exact htrace ht
    rw [hNe] at hn
    exact hn
  · have hv : liftClosedPath (gp ω) T ∈ Subtype.val ⁻¹' V := by
      change (liftClosedPath (gp ω) T : ℂ) ∈ V
      rw [liftClosedPath_apply _ (hclosed ω)]
      exact hlast
    rw [hVe] at hv
    exact hv

/-- The restricted restart law also holds after applying the measurable
closed-half-plane lift to the fresh path. -/
theorem restart_law_liftClosedPath
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω)
    (Y gp : Ω → C(ℝ≥0, ℂ)) (hY : Measurable[mΩ] Y) (hgp : Measurable[mΩ] gp)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω C(ℝ≥0, ℂ) mΩ _ Y (P.restrict A) =
        P A • @Measure.map Ω C(ℝ≥0, ℂ) mΩ _ gp P) :
    ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω C(ℝ≥0, closedHalfPlane) mΩ _ (liftClosedPath ∘ Y) (P.restrict A) =
        P A • @Measure.map Ω C(ℝ≥0, closedHalfPlane) mΩ _ (liftClosedPath ∘ gp) P := by
  let : MeasurableSpace Ω := mΩ
  intro A hA
  rw [← Measure.map_map measurable_liftClosedPath hY, hlaw A hA,
    Measure.map_smul _ measurable_liftClosedPath.aemeasurable,
    Measure.map_map measurable_liftClosedPath hgp]

/-- No uniform support constant is needed for random pasts. Pointwise
simple access routes imply strictly positive conditional passage probability.
-/
theorem conditional_random_boundary_tube_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y gp : Ω → C(ℝ≥0, ℂ)) (hY : Measurable[mΩ] Y) (hgp : Measurable[mΩ] gp)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω C(ℝ≥0, ℂ) mΩ _ Y (P.restrict A) =
        P A • @Measure.map Ω C(ℝ≥0, ℂ) mΩ _ gp P)
    (hclosed : ∀ ω, ClosedPathProperty (gp ω))
    (hsupport : @PublishedGeometricTubeSupport Ω mΩ P (fun ω => gp ω))
    (Fb : Ω → C(closedHalfPlane, OnePoint ℂ)) (hFb : Measurable[m] Fb)
    (O W : Set (OnePoint ℂ)) (hO : IsOpen O) (hW : IsOpen W)
    (E : Set Ω)
    (hgeometry : ∀ ω ∈ E, ∃ z : ℂ, ∃ p : Path (0 : ℂ) z,
      Function.Injective p ∧
      ∃ hpH : ∀ t, t ≠ 0 → p t ∈ upperHalfPlane,
        (∀ t, Fb ω ⟨p t, by
          by_cases ht : t = 0
          · simp [ht, closedHalfPlane]
          · exact (show 0 < (p t).im from hpH t ht).le⟩ ∈ O) ∧
        Fb ω ⟨z, by simpa using (show 0 < (p 1).im from hpH 1 (by norm_num)).le⟩ ∈ W) :
    ∀ᵐ ω ∂P, ω ∈ E →
      0 < P⁻[({ω | (Fb ω).comp (liftClosedPath (Y ω)) ∈
        pathTubeEventIn O W}).indicator (fun _ => 1) | m] ω := by
  let : MeasurableSpace Ω := mΩ
  let ν := P.map (liftClosedPath ∘ gp)
  have hC := @measurableSet_randomBoundaryTubeSet Ω m Fb hFb O W hO hW
  apply conditional_passage_positive_of_random_sections P ν m hm
    (liftClosedPath ∘ Y) (measurable_liftClosedPath.comp hY)
    (restart_law_liftClosedPath P m Y gp hY hgp hlaw) E
    (randomBoundaryTubeSet Fb O W) hC
  apply Eventually.of_forall
  intro ω hω
  obtain ⟨z, p, hinj, hpH, hroute, hend⟩ := hgeometry ω hω
  have hs : MeasurableSet {x : C(ℝ≥0, closedHalfPlane) |
      (Fb ω).comp x ∈ pathTubeEventIn O W} :=
    hC.preimage measurable_prodMk_left
  change 0 < P.map (liftClosedPath ∘ gp)
    {x | (Fb ω).comp x ∈ pathTubeEventIn O W}
  rw [Measure.map_apply (measurable_liftClosedPath.comp hgp) hs]
  exact boundary_tube_positive_of_geometric_support P gp hclosed hsupport
    (Fb ω) O W hO hW z p hinj hpH hroute hend

end SLEExactGauge

end

end OAI
