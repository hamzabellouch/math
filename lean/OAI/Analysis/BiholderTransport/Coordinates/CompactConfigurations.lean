import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ActiveCompact
import OAI.Analysis.BiholderTransport.Convexity.UniformEnvelope

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section CompactConfigurations
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma tangent_chart_symm_eq {a : M} {b : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target) (p : Model n) :
    (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).symm (b,p) =
      ⟨(extChartAt 𝓘(ℝ,Model n) a).symm b, chartFiberInverse a b p⟩ := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  have hx : x ∈ (chartAt (Model n) a).source := by
    simpa only [x,extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  change (⟨x,tangentCoordChange 𝓘(ℝ,Model n) a x x p⟩ : TangentBundle 𝓘(ℝ,Model n) M) = _
  congr 1
  rw [chartFiberInverse,TangentBundle.symmL_trivializationAt_eq_core hx]
  rfl

lemma isCompact_active_coordinates {v : M → ℝ} (hv : Continuous v)
    {a : M} {K : Set M} (hK : IsCompact K)
    (hKa : K ⊆ (extChartAt 𝓘(ℝ,Model n) a).source) :
    IsCompact ((extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)) ''
        {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ activeLogs v z.1 ∧ z.1 ∈ K}) := by
  have hk : IsCompact {z : TangentBundle 𝓘(ℝ,Model n) M |
      z.2 ∈ activeLogs v z.1 ∧ z.1 ∈ K} :=
    (isCompact_total_activeLogs hv).inter_right
      (hK.isClosed.preimage (FiberBundle.continuous_proj _ _))
  apply hk.image_of_continuousOn
  apply (continuousOn_extChartAt _).mono
  intro z hz
  exact (tangent_chart_source_iff _ z).mpr (hKa hz.2)

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma mem_active_coordinates {v : M → ℝ} {a : M} {K : Set M}
    (hKa : K ⊆ (extChartAt 𝓘(ℝ,Model n) a).source)
    {b p : Model n}
    (h : (b,p) ∈ (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)) ''
        {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ activeLogs v z.1 ∧ z.1 ∈ K}) :
    b ∈ (extChartAt 𝓘(ℝ,Model n) a).target ∧
    chartFiberInverse a b p ∈ activeLogs v ((extChartAt 𝓘(ℝ,Model n) a).symm b) ∧
    (extChartAt 𝓘(ℝ,Model n) a).symm b ∈ K := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  obtain ⟨z,hz,he⟩ := h
  have hzS : z ∈ χ.source := (tangent_chart_source_iff _ z).mpr (hKa hz.2)
  have hbp : (b,p) ∈ χ.target := by
    rw [←he]
    exact χ.map_source hzS
  have hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target :=
    (tangent_chart_target_iff _ (b,p)).mp hbp
  have hzinv : χ.symm (b,p) = z := by
    rw [←he]
    exact χ.left_inv hzS
  have heq : (⟨(extChartAt 𝓘(ℝ,Model n) a).symm b,
      chartFiberInverse a b p⟩ : TangentBundle 𝓘(ℝ,Model n) M) = z := by
    exact (tangent_chart_symm_eq hb p).symm.trans hzinv
  refine ⟨hb,?_⟩
  have hh := congrArg (fun z : TangentBundle 𝓘(ℝ,Model n) M =>
    z.2 ∈ activeLogs v z.1 ∧ z.1 ∈ K) heq
  exact hh.mpr hz

end CompactConfigurations

lemma compact_common_base_configurations {E : Type*} [TopologicalSpace E] [T2Space E]
    {ι : Type*} [Fintype ι] [Nonempty ι] {C : Set (E×E)} (hC : IsCompact C)
    (T : ℝ) :
    IsCompact {q : EnvelopeData E ι | (∀ i, (q.1.1, q.1.2 i) ∈ C) ∧
      (∀ i, 0 ≤ q.2.1 i) ∧ (∑ i, q.2.1 i = 1) ∧ q.2.2 ∈ Icc 0 T} := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  let Q := {z : (ι → C) × (Convexity.StdSimplex ℝ ι × Icc (0:ℝ) T) |
    ∀ i, (z.1 i).1.1 = (z.1 i₀).1.1}
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hQ : IsCompact Q := by
    have he : Q = ⋂ i, {z : (ι → C) × (Convexity.StdSimplex ℝ ι × Icc (0:ℝ) T) |
        (z.1 i).1.1 = (z.1 i₀).1.1} := by ext; simp [Q]
    rw [he]
    exact (isClosed_iInter (fun i => isClosed_eq
      (continuous_fst.comp (continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)))
      (continuous_fst.comp (continuous_subtype_val.comp ((continuous_apply i₀).comp continuous_fst))))).isCompact
  let F : ((ι → C) × (Convexity.StdSimplex ℝ ι × Icc (0:ℝ) T)) → EnvelopeData E ι :=
    fun z => (((z.1 i₀).1.1, fun i => (z.1 i).1.2),(z.2.1.weights,z.2.2.1))
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have he : F '' Q = {q : EnvelopeData E ι | (∀ i, (q.1.1, q.1.2 i) ∈ C) ∧
      (∀ i, 0 ≤ q.2.1 i) ∧ (∑ i, q.2.1 i = 1) ∧ q.2.2 ∈ Icc 0 T} := by
    ext q
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨?_,z.2.1.weights_nonneg,z.2.1.total_of_fintype,z.2.2.2⟩
      intro i
      change ((z.1 i₀).1.1,(z.1 i).1.2) ∈ C
      rw [←hz i]
      exact (z.1 i).2
    · rintro ⟨hc,hw,hsum,ht⟩
      let weights : Convexity.StdSimplex ℝ ι := {
        weights := Finsupp.equivFunOnFinite.symm q.2.1
        nonneg index := by simpa using hw index
        total := by simpa [Finsupp.sum_fintype] using hsum }
      refine ⟨(fun i => ⟨(q.1.1,q.1.2 i),hc i⟩,weights,⟨q.2.2,ht⟩),?_,?_⟩
      · intro i
        rfl
      · rfl
  rw [←he]
  exact hQ.image hF

end WeakMTWTransport

end

end OAI
