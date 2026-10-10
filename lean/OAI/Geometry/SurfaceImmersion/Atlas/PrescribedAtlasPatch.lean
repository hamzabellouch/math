import OAI.Geometry.SurfaceImmersion.Correction.CircularSmoothingAtlas

namespace OAI

/-! A fixed compact primitive disk can be placed in one positive atlas
patch with support in any prescribed coordinate neighborhood. -/
noncomputable section
open Set Function Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem exists_smoothingAtlas_prescribed_patch (q : M) {K U : Set M}
    (hK : IsCompact K) (hqK : q ∈ K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUs : U ⊆ (chart q).source) :
    ∃ (A : SmoothingAtlas M) (i : A.centers), (i : M) = q ∧
      (∀ p ∈ K, 0 < A.weight i p) ∧ tsupport (A.weight i) ⊆ U ∧
      (∀ j p, 0 ≤ A.weight j p) ∧
      ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1) := by
  classical
  let V : M → Set M := fun p => if p = q then U else (chart p).source \ {q}
  have hV : ∀ p, IsOpen (V p) := by
    intro p
    by_cases hp : p = q
    · simpa only [V,ite_eq_left hp] using hU
    · simpa only [V,ite_eq_right hp] using (chart p).open_source.sdiff isClosed_singleton
  have hpV : ∀ p, p ∈ V p := by
    intro p
    by_cases hp : p = q
    · subst p; simpa only [V,ite_eq_left rfl] using hKU hqK
    · simp only [V,ite_eq_right hp,mem_sdiff,mem_singleton_iff]
      exact ⟨by rw [chart_source]; exact mem_chart_source Plane p,hp⟩
  obtain ⟨t,ψ,hψ,hsupp,_,hnon,hpart⟩ := exists_finite_smooth_square_partition
    (E := Plane) V hV hpV
  have hψ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (ψ i) := by
    intro i
    simpa only [planeModel] using hψ i
  have hqt : q ∈ t := by
    by_contra hnot
    have hz (i : t) : ψ i q = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hh
      have hi : (i : M) ≠ q := fun he => hnot (he ▸ i.2)
      have hm := hsupp i hh
      simp only [V,ite_eq_right hi,mem_sdiff,mem_singleton_iff] at hm
      exact hm.2 trivial
    have he := hpart q
    simp only [hz,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at he
    norm_num at he
  let iq : t := ⟨q,hqt⟩
  obtain ⟨W,hW,hKW,hWU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨β,hβ,_,hβs,hβone⟩ := exists_contMDiff_support_eq_eq_one_iff
    (I := planeModel) (n := (⊤ : ℕ∞)) hW hK.isClosed hKW
  have hβU : tsupport β ⊆ U := by
    change closure (support β) ⊆ U
    rw [hβs]
    exact hWU
  let f : t → M → ℝ := fun i p => ψ i p + if i = iq then (β p)^2 else 0
  have hf : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (f i) := by
    intro i
    by_cases hi : i = iq
    · have heq : f i = ψ i + fun p => (β p)^2 := by
        funext p; simp only [f,ite_eq_left hi,Pi.add_apply]
      rw [heq]
      exact (hψ i).add (hβ.pow 2)
    · simpa only [f,ite_eq_right hi,add_zero] using hψ i
  have hfnon : ∀ i p, 0 ≤ f i p := by
    intro i p
    exact add_nonneg (hnon i p) (by split_ifs <;> positivity)
  have hfle : ∀ i p, ψ i p ≤ f i p := by
    intro i p
    exact le_add_of_nonneg_right (by split_ifs <;> positivity)
  have hfcover (p : M) : ∃ i, 0 < f i p := by
    by_contra hh
    have hz : ∀ i, ψ i p = 0 := by
      intro i
      have hni : ¬ 0 < f i p := fun h => hh ⟨i,h⟩
      exact le_antisymm ((hfle i p).trans (le_of_not_gt hni)) (hnon i p)
    have hp := hpart p
    simp only [hz,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hp
    norm_num at hp
  have hfV : ∀ i, tsupport (f i) ⊆ V i := by
    intro i
    by_cases hi : i = iq
    · subst i
      have hs : tsupport (f iq) ⊆ tsupport (ψ iq) ∪ tsupport β := by
        have heq : f iq = ψ iq + fun p => (β p)^2 := by
          funext p; simp [f]
        rw [heq]
        exact (tsupport_add _ _).trans (union_subset_union_right _ (show tsupport (fun p => (β p)^2) ⊆ tsupport β from by
          apply closure_mono
          intro p hp
          exact fun hz => hp (by change (β p)^2 = 0; rw [hz,zero_pow (by decide : 2 ≠ 0)])))
      apply hs.trans
      apply union_subset (hsupp iq)
      simpa only [V,show (iq : M) = q from rfl,ite_eq_left rfl] using hβU
    · simpa only [f,ite_eq_right hi,add_zero] using hsupp i
  obtain ⟨w,hw,hwnon,hwpos,hwsupp,hwsum⟩ := normalize_finite_positive_cutoffs f hf hfnon hfcover
  have hwV (i : t) : tsupport (w i) ⊆ V i := by rw [hwsupp]; exact hfV i
  have hwchart (i : t) : tsupport (w i) ⊆ (chart (i : M)).source := by
    intro p hp
    have hv := hwV i hp
    by_cases hi : (i : M) = q
    · have hu : p ∈ U := by simpa only [V,ite_eq_left hi] using hv
      simpa only [hi] using hUs hu
    · have hh : p ∈ (chart (i : M)).source ∧ p ∉ ({q} : Set M) := by
        simpa only [V,ite_eq_right hi,mem_sdiff] using hv
      exact hh.1
  have hout : ∀ i : t, ∃ chi : M → ℝ,
      ContMDiff planeModel 𝓘(ℝ) ∞ chi ∧ tsupport chi ⊆ (chart (i : M)).source ∧
      ∀ p ∈ tsupport (w i), chi =ᶠ[𝓝 p] (fun _ => 1) := by
    intro i
    have hc : IsCompact (tsupport (w i)) := (isClosed_tsupport _).isCompact
    obtain ⟨B,hB,hKB,hBc⟩ := hc.exists_isOpen_closure_subset
      ((chart (i : M)).open_source.mem_nhdsSet.mpr (hwchart i))
    obtain ⟨O,hO,hKO,hOc⟩ := hc.exists_isOpen_closure_subset (hB.mem_nhdsSet.mpr hKB)
    obtain ⟨chi,hchi,_,hchis,hchione⟩ := exists_contMDiff_support_eq_eq_one_iff
      (I := planeModel) (n := (⊤ : ℕ∞)) hB isClosed_closure hOc
    refine ⟨chi,hchi,?_,?_⟩
    · change closure (support chi) ⊆ _
      rw [hchis]
      exact hBc
    · intro p hp
      filter_upwards [hO.mem_nhds (hKO hp)] with y hy
      exact (hchione y).mp (subset_closure hy)
  choose chi hchi hchis hchione using hout
  let A : SmoothingAtlas M :=
    ⟨t,w,chi,hw,hwchart,hchi,hchis,fun i p hp => (hchione i p hp).eq_of_nhds,hwsum⟩
  refine ⟨A,iq,rfl,?_,?_,hwnon,hchione⟩
  · intro p hp
    apply (hwpos iq p).mpr
    change 0 < ψ iq p + if iq = iq then (β p)^2 else 0
    rw [ite_eq_left rfl,(hβone p).mp hp]
    linarith [hnon iq p]
  · simpa only [V,show (iq : M) = q from rfl,ite_eq_left rfl] using hwV iq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
