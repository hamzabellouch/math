import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowLineAffinity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Separation.Connected

namespace OAI

/-! # Continuity upgrades almost-everywhere affine flow restrictions -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

variable {G V W : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def flowLineBase (U : Set G) (Exp : V → G) (v : V) (T : ℝ) : Set G :=
  {g | ∀ t ∈ Icc 0 T, g * Exp (t • v) ∈ U}

theorem isOpen_flowLineBase (U : Set G) (hU : IsOpen U)
    (Exp : V → G) (hExp : Continuous Exp) (v : V) (T : ℝ) :
    IsOpen (flowLineBase U Exp v T) := by
  let F : G → C(ℝ, G) := fun g =>
    ⟨fun t => g * Exp (t • v), by fun_prop⟩
  have hc : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : G × ℝ => p.1 * Exp (p.2 • v))
    fun_prop
  exact ContinuousMap.continuous_compactOpen.mp hc (Icc 0 T) isCompact_Icc U hU

omit [NormedSpace ℝ W] in
theorem continuousOn_flowLine_evaluation
    {U : Set G} {Exp : V → G} (_hExp : Continuous Exp) {v : V} {T t : ℝ}
    {f : G → W} (hf : ContinuousOn f U) (ht : t ∈ Icc 0 T) :
    ContinuousOn (fun g => f (g * Exp (t • v))) (flowLineBase U Exp v T) :=
  hf.comp (by fun_prop) (fun _ hg => hg t ht)

omit [Group G] [IsTopologicalGroup G] [NormedSpace ℝ W] in
theorem mapsTo_closed_of_ae
    [MeasurableSpace G] (μ : Measure G) [μ.IsOpenPosMeasure]
    {U : Set G} (hU : IsOpen U) {f : G → W} (hf : ContinuousOn f U)
    {E : Set W} (hE : IsClosed E)
    (hae : ∀ᵐ g ∂μ, g ∈ U → f g ∈ E) : MapsTo f U E := by
  have ho : IsOpen (U ∩ f ⁻¹' Eᶜ) := hf.isOpen_inter_preimage hU hE.isOpen_compl
  have hz : μ (U ∩ f ⁻¹' Eᶜ) = 0 := by
    apply measure_mono_null (fun g hg => ?_) hae
    exact fun h => hg.2 (h hg.1)
  have he := ho.eq_empty_of_measure_zero hz
  intro g hg
  by_contra hn
  have : g ∈ U ∩ f ⁻¹' Eᶜ := ⟨hg, hn⟩
  rw [he] at this
  exact this

def flowLineSlope (f : G → W) (Exp : V → G) (v : V) (T : ℝ) (g : G) : W :=
  T⁻¹ • (f (g * Exp (T • v)) - f g)

theorem continuousOn_flowLineSlope
    {U : Set G} {Exp : V → G} (hExp : Continuous Exp) (hExp0 : Exp 0 = 1)
    {v : V} {T : ℝ} (hT : 0 ≤ T) {f : G → W} (hf : ContinuousOn f U) :
    ContinuousOn (flowLineSlope f Exp v T) (flowLineBase U Exp v T) := by
  have hbase : flowLineBase U Exp v T ⊆ U := by
    intro g hg
    simpa [hExp0] using hg 0 ⟨le_rfl, hT⟩
  exact ((continuousOn_flowLine_evaluation hExp hf ⟨hT, le_rfl⟩).sub
    (hf.mono hbase)).const_smul T⁻¹

theorem flowLine_affinity_of_ae
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [μ.IsOpenPosMeasure]
    {U : Set G} (hU : IsOpen U) {Exp : V → G} (hExp : Continuous Exp)
    (hExp0 : Exp 0 = 1) {v : V} {T : ℝ} (hT : 0 < T)
    {f : G → W} (hf : ContinuousOn f U)
    (hae : ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∃ u : W, ∀ t ∈ Icc 0 T, f (g * Exp (t • v)) = f g + t • u) :
    ∀ g ∈ flowLineBase U Exp v T, ∀ t ∈ Icc 0 T,
      f (g * Exp (t • v)) = f g + t • flowLineSlope f Exp v T g := by
  have hbase : flowLineBase U Exp v T ⊆ U := by
    intro g hg
    simpa [hExp0] using hg 0 ⟨le_rfl, hT.le⟩
  intro g hg t ht
  apply eqOn_open_of_ae_eq (μ := μ) (U := flowLineBase U Exp v T) ?_
    (isOpen_flowLineBase U hU Exp hExp v T)
    (continuousOn_flowLine_evaluation hExp hf ht)
    ((hf.mono hbase).add ((continuousOn_flowLineSlope hExp hExp0 hT.le hf).const_smul t)) hg
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem
    (isOpen_flowLineBase U hU Exp hExp v T).measurableSet] with x hx hxB
  obtain ⟨u, hu⟩ := hx hxB
  have hs : flowLineSlope f Exp v T x = u := by
    simp [flowLineSlope, hu T ⟨hT.le, le_rfl⟩, smul_smul, hT.ne']
  change f (x * Exp (t • v)) = f x + t • flowLineSlope f Exp v T x
  rw [hs]
  exact hu t ht

theorem flowLineSlope_mem_of_ae
    [MeasurableSpace G] (μ : Measure G) [μ.IsOpenPosMeasure]
    {U : Set G} (hU : IsOpen U) {Exp : V → G} (hExp : Continuous Exp)
    (hExp0 : Exp 0 = 1) {v : V} {T : ℝ} (hT : 0 < T)
    {f : G → W} (hf : ContinuousOn f U) {E : Set W} (hE : IsClosed E)
    (hae : ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∃ u ∈ E, ∀ t ∈ Icc 0 T, f (g * Exp (t • v)) = f g + t • u) :
    MapsTo (flowLineSlope f Exp v T) (flowLineBase U Exp v T) E := by
  apply mapsTo_closed_of_ae μ (isOpen_flowLineBase U hU Exp hExp v T)
    (continuousOn_flowLineSlope hExp hExp0 hT.le hf) hE
  filter_upwards [hae] with g hg hbase
  obtain ⟨u, huE, hu⟩ := hg hbase
  simpa [flowLineSlope, hu T ⟨hT.le, le_rfl⟩, smul_smul, hT.ne'] using huE

theorem flowLineSlope_eq_on_preconnected
    {U : Set G} {Exp : V → G} (hExp : Continuous Exp) (hExp0 : Exp 0 = 1)
    {v : V} {T : ℝ} (hT : 0 ≤ T) {f : G → W} (hf : ContinuousOn f U)
    {E : Set W} (hE : E.Finite)
    (hmem : MapsTo (flowLineSlope f Exp v T) (flowLineBase U Exp v T) E)
    {S : Set G} (hS : IsPreconnected S) (hSB : S ⊆ flowLineBase U Exp v T)
    {x y : G} (hx : x ∈ S) (hy : y ∈ S) :
    flowLineSlope f Exp v T x = flowLineSlope f Exp v T y := by
  have hc := (continuousOn_flowLineSlope hExp hExp0 hT hf).mono hSB
  have hfinite : (flowLineSlope f Exp v T '' S).Finite :=
    hE.subset (fun _ ⟨g, hg, he⟩ => he ▸ hmem (hSB hg))
  have hsub : (flowLineSlope f Exp v T '' S).Subsingleton := by
    apply not_nontrivial_iff.mp
    intro hn
    exact hfinite.not_infinite ((hS.image _ hc).infinite_of_nontrivial hn)
  exact hsub ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

end PolycyclicRecognition

end

end OAI
