import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevGluing
import OAI.Analysis.CircleDomains.Rigidity.LocalTraceMaskSobolev
import OAI.Analysis.CircleDomains.Rigidity.TraceMaskPlateauSobolev
import OAI.Analysis.CircleDomains.Topology.RectangleNeighborhoods
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-! The local smooth and plateau witnesses join on the actual open union.
The source differential is charged only on the original domain, and
balloon derivatives are charged to the constructed global L² density. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem trace_mask_open_sobolev
    {cutoff : ℕ → (ℝ × ℝ) → ℝ} (hs : ∀ j, ContDiff ℝ 1 (cutoff j))
    (hc : ∀ j p, cutoff j p ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    (hconv : ∀ j, OrdConnected (I j)) (β : ℕ → ℝ) (hβ : ∀ j, β j ∈ I j)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {b : ℝ × ℝ → ℝ} (hb : ContDiffOn ℝ 1 b Ω)
    (hb2 : MemLp (fderiv ℝ b) 2 (volume.restrict Ω))
    (V : ℕ → Set (ℝ × ℝ)) (hV : ∀ j, IsOpen (V j))
    (hv : ∀ j p, p ∈ V j → cutoff j p = 0 ∧ b p ∈ I j)
    {P : ℝ × ℝ → ℝ} (hPm : Measurable P) (hP0 : ∀ p, 0 ≤ P p) (hP2 : MemLp P 2 volume)
    (hdom : ∀ n, ∀ᵐ p ∂volume,
      ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) p‖ ≤ P p)
    (a : ℝ) (hu : Continuous (fun p => infiniteTracePrimitive cutoff I a p (b p)))
    (hus : HasCompactSupport (fun p => infiniteTracePrimitive cutoff I a p (b p))) :
    ∃ W : DeGiorgi.MemW1pWitness 2
      ((fun p => infiniteTracePrimitive cutoff I a p (b p)) ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ω ∪ ⋃ j, V j)),
      ∀ k : Fin 2, ∀ᵐ x ∂volume.restrict (euclideanPlaneCoordinates ⁻¹' (Ω ∪ ⋃ j, V j)),
        |W.weakGrad x k| ≤
          Ω.indicator (fun p => ‖fderiv ℝ b p‖) (euclideanPlaneCoordinates x)+P (euclideanPlaneCoordinates x) := by
  let O := Ω ∪ ⋃ j, V j
  let Q := Ω.indicator (fun p => ‖fderiv ℝ b p‖)
  let U := fun p => infiniteTracePrimitive cutoff I a p (b p)
  have hO : IsOpen O := hΩ.union (isOpen_iUnion hV)
  have hQm : Measurable Q := (measurable_fderiv ℝ b).norm.indicator hΩ.measurableSet
  have hQ0 (p : ℝ × ℝ) : 0 ≤ Q p := indicator_nonneg (fun _ _ => norm_nonneg _) p
  have hQ2 : MemLp Q 2 volume := (memLp_indicator_iff_restrict hΩ.measurableSet).mpr hb2.norm
  have hEopen : IsOpen (euclideanPlaneCoordinates ⁻¹' O) := hO.preimage euclideanPlaneCoordinates.continuous
  have hUE : MemLp (U ∘ euclideanPlaneCoordinates) 2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' O)) :=
    ((hu.comp euclideanPlaneCoordinates.continuous).memLp_of_hasCompactSupport
      (hus.comp_homeomorph euclideanPlaneCoordinates.toHomeomorph)).restrict _
  have hPE : MemLp (fun x => Q (euclideanPlaneCoordinates x)+P (euclideanPlaneCoordinates x))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' O)) :=
    ((hQ2.add hP2).comp_measurePreserving euclideanPlaneCoordinates_measurePreserving).restrict _
  have hloc : ∀ x ∈ euclideanPlaneCoordinates ⁻¹' O, ∃ T : Set EuclideanPlane,
      IsOpen T ∧ x ∈ T ∧ T ⊆ euclideanPlaneCoordinates ⁻¹' O ∧
      ∃ W : DeGiorgi.MemW1pWitness 2 (U ∘ euclideanPlaneCoordinates) T,
        ∀ k : Fin 2, ∀ᵐ y ∂volume.restrict T,
          |W.weakGrad y k| ≤ Q (euclideanPlaneCoordinates y)+P (euclideanPlaneCoordinates y) := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨a₁,a₂,b₁,b₂,ha,hb',hxp,hbox⟩ := exists_closed_rectangle_inside_open hΩ hx
      let T := euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)
      have hT : IsOpen T := (isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous
      have hTΩ : ∀ y ∈ T, euclideanPlaneCoordinates y ∈ Ω :=
        fun y hy => hbox ((Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hy)
      obtain ⟨W,hW⟩ := local_masked_scalar_rectangle_sobolev hs hc hI hIf hΩ hb hPm hP0
        ha.le hb'.le hbox (hP2.restrict _) (fun n => ae_restrict_of_ae (hdom n)) a
      refine ⟨T,hT,hxp,(fun y hy => Or.inl (hTΩ y hy)),W,?_⟩
      intro k
      filter_upwards [hW k,ae_restrict_mem hT.measurableSet] with y hy hyT
      simpa only [Q,indicator_of_mem (hTΩ y hyT)] using hy
    · obtain ⟨j,hxj⟩ := mem_iUnion.mp hx
      obtain ⟨a₁,a₂,b₁,b₂,ha,hb',hxp,hbox⟩ := exists_closed_rectangle_inside_open (hV j) hxj
      let T := euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)
      have hT : IsOpen T := (isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous
      have hTV : ∀ y ∈ T, euclideanPlaneCoordinates y ∈ V j :=
        fun y hy => hbox ((Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hy)
      obtain ⟨W,hW⟩ := plateau_mask_rectangle_sobolev hs hc hI hIf hPm hP0
        ha.le hb'.le (hP2.restrict _) (fun n => ae_restrict_of_ae (hdom n))
        (hconv j) (hβ j) (fun p hp => hv j p (hbox ((Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hp))) a
      refine ⟨T,hT,hxp,(fun y hy => Or.inr (mem_iUnion.mpr ⟨j,hTV y hy⟩)),W,?_⟩
      intro k
      filter_upwards [hW k] with y hy
      exact hy.trans (le_add_of_nonneg_left (hQ0 _))
  obtain ⟨W,hW,_⟩ := exists_local_sobolev_gluing hEopen hUE hPE hloc
  exact ⟨W,hW⟩

end CircleDomainRigidity

end

end OAI
