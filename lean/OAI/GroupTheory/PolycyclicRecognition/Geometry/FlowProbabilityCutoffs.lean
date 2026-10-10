import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactProbabilityDensity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactFlowNeighborhood
import OAI.GroupTheory.PolycyclicRecognition.Algebra.OccupationDomination

namespace OAI

/-! # Fixed probability cutoffs for converging horizontal segments -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- A segment in the open chart admits one starting density and one
occupation density. The domination constant works for every time on the
segment and all sufficiently late scaled flows, before choosing a mesh. -/
theorem exists_flow_probability_cutoffs
    {X ι : Type*} [MetricSpace X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (m : Measure X) [m.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts m]
    {l : Filter ι} (Fs : ι → C(X × ℝ, X)) (F : C(X × ℝ, X))
    (hF : Tendsto Fs l (𝓝 F)) (z : X) {T : ℝ} (hT : 0 ≤ T)
    {U : Set X} (hU : IsOpen U) (hseg : ∀ t ∈ Icc 0 T, F (z, t) ∈ U) :
    ∃ (η ρ : C(X, ℝ)) (c : ℝ≥0),
      HasCompactSupport η ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U ∧
      (∀ x, 0 ≤ η x) ∧ (∀ x, 0 ≤ ρ x) ∧ 0 < η z ∧
      Integrable η m ∧ Integrable ρ m ∧
      (∫ x, η x ∂m) = 1 ∧ (∫ x, ρ x ∂m) = 1 ∧
      ∀ᶠ i in l, ∀ t ∈ Icc 0 T, ∀ x, η x ≤ (c : ℝ) * ρ (Fs i (x, t)) := by
  obtain ⟨O, V, hO, _, hzO, hIV, hprod⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({z} : Set X)) isCompact_Icc
    (hU.preimage F.continuous) (by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      have hxz : x = z := mem_singleton_iff.mp hx
      subst x
      exact hseg t ht)
  obtain ⟨η, A, hA, hηcomp, hηO, hηbound, hηz, hηi, hηmass⟩ :=
    exists_compact_probability_density m isCompact_singleton (singleton_nonempty z)
      hO hzO
  have hηz' : η z = A := hηz z (mem_singleton z)
  have hzsup : z ∈ tsupport η := subset_tsupport η (by
    change η z ≠ 0
    rw [hηz']
    exact hA.ne')
  have hcompact : IsCompact (tsupport η ×ˢ Icc 0 T) := hηcomp.prod isCompact_Icc
  have himage : F '' (tsupport η ×ˢ Icc 0 T) ⊆ U := by
    rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact hprod ⟨hηO hx, hIV ht⟩
  have hunif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hF)
    (tsupport η ×ˢ Icc 0 T) hcompact
  obtain ⟨Q, hQ, hQU, hFQ, hFsQ⟩ := exists_compact_eventual_flow_image
    hcompact F.continuous.continuousOn hU himage hunif
  have hQne : Q.Nonempty := ⟨F (z, 0), hFQ (mem_image_of_mem F ⟨hzsup, le_rfl, hT⟩)⟩
  obtain ⟨ρ, b, hb, hρcomp, hρU, hρbound, hρQ, hρi, hρmass⟩ :=
    exists_compact_probability_density m hQ hQne hU hQU
  let c : ℝ≥0 := ⟨A / b, div_nonneg hA.le hb.le⟩
  refine ⟨η, ρ, c, hηcomp, hρcomp, hρU, fun x => (hηbound x).1,
    fun x => (hρbound x).1, by simpa only [hηz'] using hA,
    hηi, hρi, hηmass, hρmass, ?_⟩
  filter_upwards [hFsQ] with i hi
  intro t ht
  exact density_bound_on_swept_support η ρ (fun x => Fs i (x, t)) Q hA.le hb
    (fun x => (hηbound x).2) (fun x => (hρbound x).1)
    (fun x hx => hi (mem_image_of_mem (Fs i) ⟨subset_tsupport η hx, ht⟩))
    (fun x hx => (hρQ x hx).ge)

end PolycyclicRecognition

end

end OAI
