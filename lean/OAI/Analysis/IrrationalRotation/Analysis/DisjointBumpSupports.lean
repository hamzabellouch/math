import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Invariant233.BackgroundConstruction

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]

theorem exists_open_pairwise_disjoint_images [Finite ι]
    (F : ι → X → X) (hF : ∀ i, Continuous (F i)) (x₀ : X)
    (hdistinct : Function.Injective (fun i => F i x₀)) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ Pairwise (fun i j => Disjoint (F i '' V) (F j '' V)) := by
  classical
  obtain ⟨U, hU, hdisj⟩ := (Set.finite_range (fun i => F i x₀)).t2_separation
  let V : Set X := ⋂ i, F i ⁻¹' U (F i x₀)
  have hVo : IsOpen V := isOpen_iInter_of_finite fun i => (hU _).2.preimage (hF i)
  have hx : x₀ ∈ V := Set.mem_iInter.mpr fun i => (hU _).1
  refine ⟨V, hVo, hx, ?_⟩
  intro i j hij
  have hsub (k : ι) : F k '' V ⊆ U (F k x₀) := by
    rintro _ ⟨x, hx, rfl⟩
    exact Set.mem_iInter.mp hx k
  exact (hdisj (Set.mem_range_self i) (Set.mem_range_self j)
    (fun h => hij (hdistinct h))).mono (hsub i) (hsub j)

theorem exists_small_bump_pairwise_disjoint_images [Finite ι] [LocallyCompactSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.OuterRegular]
    (F : ι → X → X) (hF : ∀ i, Continuous (F i)) (x₀ : X)
    (hdistinct : Function.Injective (fun i => F i x₀)) (hzero : μ {x₀} = 0)
    (O : Set X) (hOo : IsOpen O) (hxO : x₀ ∈ O)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ v : C(X, ℝ), v x₀ = 1 ∧ (∀ x, v x ∈ Set.Icc 0 1) ∧
      IsCompact (tsupport v) ∧ tsupport v ⊆ O ∧ μ (tsupport v) < ε ∧
      Pairwise (fun i j => Disjoint (F i '' tsupport v) (F j '' tsupport v)) := by
  obtain ⟨V, hVo, hxV, hdisj⟩ := exists_open_pairwise_disjoint_images F hF x₀ hdistinct
  obtain ⟨U, hxU, hUo, hUμ⟩ :=
    Set.exists_isOpen_lt_of_lt (μ := μ) ({x₀} : Set X) ε (by rwa [hzero])
  have hx : x₀ ∈ V ∩ U ∩ O := ⟨⟨hxV, hxU (by simp)⟩, hxO⟩
  obtain ⟨v, hv1, hvcompact, hvsub, hvrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen isCompact_singleton
      ((hVo.inter hUo).inter hOo) (Set.singleton_subset_iff.mpr hx)
  refine ⟨v, ?_, hvrange, hvcompact, ?_, ?_, ?_⟩
  · exact hv1 (Set.mem_singleton x₀)
  · exact hvsub.trans Set.inter_subset_right
  · exact (measure_mono (hvsub.trans (Set.inter_subset_left.trans Set.inter_subset_right))).trans_lt hUμ
  · intro i j hij
    exact (hdisj hij).mono
      (Set.image_mono (hvsub.trans (Set.inter_subset_left.trans Set.inter_subset_left)))
      (Set.image_mono (hvsub.trans (Set.inter_subset_left.trans Set.inter_subset_left)))

end Invariant233.BackgroundConstruction

end OAI
