import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierNuclearBarrier
import OAI.Analysis.CoulombIonization.ThomasFermi.WeakSommerfeldBoundsBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_RetainedNeighborhood_barrier_scope

open Set Filter
open scoped Topology

theorem retained_neighborhood {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (hs : s.Nonempty) (v : ι → X → ℝ) (x : X)
    (hv : ∀ i ∈ s, ContinuousAt (v i) x) {ε : ℝ} (hε : 0 < ε) :
    ∃ (t : Finset ι) (ht : t.Nonempty) (U : Set X), t ⊆ s ∧ IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U,
        s.sup' hs (fun i => v i y) = t.sup' ht (fun i => v i y) ∧
        ∀ i ∈ t, s.sup' hs (fun i => v i y) - v i y < 2*ε := by
  classical
  let M : X → ℝ := fun y => s.sup' hs (fun i => v i y)
  let t := s.filter (fun i => M x-v i x ≤ ε)
  obtain ⟨k,hks,hk⟩ := Finset.exists_mem_eq_sup' hs (fun i => v i x)
  have hkt : k ∈ t := by
    simp only [t,Finset.mem_filter]
    exact ⟨hks,by change s.sup' hs (fun i => v i x)-v k x ≤ ε; rw [hk]; linarith⟩
  have ht : t.Nonempty := ⟨k,hkt⟩
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hM : ContinuousAt M x := by
    exact ContinuousAt.finset_sup'_apply hs hv
  have hr : ∀ᶠ y in 𝓝 x, ∀ i ∈ t, M y-v i y < 2*ε := by
    change ∀ᶠ y in 𝓝 x, ∀ i ∈ (↑t : Set ι), M y-v i y < 2*ε
    rw [t.finite_toSet.eventually_all]
    intro i hi
    have his := hts hi
    have hie : M x-v i x ≤ ε := (Finset.mem_filter.mp hi).2
    exact (hM.sub (hv i his)).eventually (gt_mem_nhds (show M x-v i x < 2*ε by linarith))
  have hd : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, i ∉ t → v i y < v k y := by
    change ∀ᶠ y in 𝓝 x, ∀ i ∈ (↑s : Set ι), i ∉ t → v i y < v k y
    rw [s.finite_toSet.eventually_all]
    intro i hi
    by_cases hit : i ∈ t
    · exact Eventually.of_forall fun _ h => False.elim (h hit)
    · have hgap : ε < M x-v i x := lt_of_not_ge (by
        intro he
        exact hit (Finset.mem_filter.mpr ⟨hi,he⟩))
      have hlt : v i x < v k x := by change ε < s.sup' hs (fun i => v i x)-v i x at hgap; rw [hk] at hgap; linarith
      filter_upwards [(hv i hi).eventually_lt (hv k hks) hlt] with y hy _
      exact hy
  let U := interior {y | (∀ i ∈ t, M y-v i y < 2*ε) ∧
    (∀ i ∈ s, i ∉ t → v i y < v k y)}
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr (hr.and hd)
  refine ⟨t,ht,U,hts,isOpen_interior,hxU,?_⟩
  intro y hy
  have hy' := interior_subset hy
  refine ⟨le_antisymm ?_ ?_,hy'.1⟩
  · apply Finset.sup'_le hs
    intro i hi
    by_cases hit : i ∈ t
    · exact Finset.le_sup' (fun i => v i y) hit
    · exact (hy'.2 i hi hit).le.trans (Finset.le_sup' (fun i => v i y) hkt)
  · apply Finset.sup'_le ht
    intro i hi
    exact Finset.le_sup' (fun i => v i y) (hts hi)

end Work_RetainedNeighborhood_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology BigOperators

open CoulombAnalysis CoulombPDE CoulombAtom

theorem retained_weak_maximum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {U : Set TFSpace} (hU : IsOpen U) (u h : ι → TFSpace → ℝ)
    (hu : ∀ i ∈ s, Continuous (u i)) (hh : ∀ i ∈ s, LocallyIntegrable (h i))
    {g χ : TFSpace → ℝ} {F : TFSpace → ℝ → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2))
    {ε : ℝ} (hε : 0 < ε)
    (hw : ∀ i ∈ s, WeakLaplacianLowerOn U (u i) (h i))
    (hdom : ∀ᵐ x, ∀ i ∈ s, x ∈ U → s.sup' hs (fun k => u k x)-u i x < 2*ε →
      g x+χ x*F x (u i x) ≤ h i x) :
    WeakLaplacianLowerOn U (fun x => s.sup' hs (fun i => u i x))
      (fun x => g x+χ x*F x (s.sup' hs (fun i => u i x))) := by
  classical
  have hM := Continuous.finset_sup'_apply hs hu
  have hgM := spatial_source_locallyIntegrable hg hχ hbχ hF hM
  apply weak_lower_local hM.locallyIntegrable hgM
  intro x hx
  obtain ⟨t,ht,V,hts,hV,hxV,hnear⟩ := retained_neighborhood s hs u x
    (fun i hi => (hu i hi).continuousAt) hε
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have htu : ∀ i ∈ t, Continuous (u i) := fun i hi => hu i (hts hi)
  have htM := Continuous.finset_sup'_apply ht htu
  have hgw := spatial_source_locallyIntegrable hg hχ hbχ hF htM
  have htw : ∀ i ∈ t, WeakLaplacianLowerOn W (u i)
      (fun y => g y+χ y*F y (u i y)) := by
    intro i hi
    apply ((hw i (hts hi)).mono_set inter_subset_left).source_mono_ae
      (hh i (hts hi)) (spatial_source_locallyIntegrable hg hχ hbχ hF (htu i hi))
    filter_upwards [hdom] with y hy
    intro hyW
    exact hy i (hts hi) hyW.1 ((hnear y hyW.2).2 i hi)
  have htweak := weak_finset_maximum_spatial t ht hW u htu hg hχ hbχ hF htw
  have he : ∀ y ∈ W, t.sup' ht (fun i => u i y) = s.sup' hs (fun i => u i y) :=
    fun y hy => (hnear y hy.2).1.symm
  refine ⟨W,hW,⟨hx,hxV⟩,?_⟩
  apply (htweak.congr_field he).source_mono hgw hgM
  intro y hy
  rw [he y hy]

theorem nuclear_retained_weak_maximum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {U : Set TFSpace} (hU : IsOpen U) (Z : ℝ) {R κ ε : ℝ} (hR : 0 < R)
    (u h : ι → TFSpace → ℝ) (hu : ∀ i ∈ s, Continuous (u i))
    (hh : ∀ i ∈ s, LocallyIntegrable (h i))
    {g χ : TFSpace → ℝ} (hg : LocallyIntegrable g)
    (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hzero : ∀ x, ‖x‖ < R → χ x = 0) (hε : 0 < ε)
    (hw : ∀ i ∈ s, WeakNuclearLowerOn U Z
      (fun x => nuclearField Z x+u i x) (h i))
    (hdom : ∀ᵐ x, ∀ i ∈ s, x ∈ U → s.sup' hs (fun k => u k x)-u i x < 2*ε →
      g x+χ x*reaction κ (nuclearField Z x+u i x) ≤ h i x) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+s.sup' hs (fun i => u i x))
      (fun x => g x+χ x*reaction κ (nuclearField Z x+s.sup' hs (fun i => u i x))) := by
  rw [weakNuclearLower_add_iff Z (Continuous.finset_sup'_apply hs hu).locallyIntegrable]
  simp_rw [weighted_clipped_reaction Z R hzero]
  apply retained_weak_maximum s hs hU u h hu hh hg hχ hbχ
    (F := fun x t => reaction κ (clippedNuclearField Z R x+t))
    ((reaction_continuous κ).comp
      (((clippedNuclearField_continuous Z hR).comp continuous_fst).add continuous_snd)) hε
  · exact fun i hi => (weakNuclearLower_add_iff Z (hu i hi).locallyIntegrable).mp (hw i hi)
  · simpa only [weighted_clipped_reaction Z R hzero] using hdom

end CoulombBarrier

end

end OAI
