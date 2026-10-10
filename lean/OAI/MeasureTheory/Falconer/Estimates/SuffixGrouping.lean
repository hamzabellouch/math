import OAI.MeasureTheory.Falconer.Estimates.SuffixCollision
import OAI.MeasureTheory.Falconer.Geometry.FiniteBinComparison

namespace OAI

/-! # Coarse grouping of the actual all-dimensional distance cells

Two fine distance distributions sharing one bin force all distances of
their full cell pairs into a common coarse collision band. The width
constant retains the ambient dimension explicitly.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def cellDistance (μ ν : Measure (Space d)) (P Q : DyadicCube d) : Measure ℝ :=
  Measure.map (fun z : Space d × Space d => dist z.1 z.2)
    ((μ.restrict P.carrier).prod (ν.restrict Q.carrier))

instance cellDistance_finite (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : DyadicCube d) : IsFiniteMeasure (cellDistance μ ν P Q) := by
  unfold cellDistance
  infer_instance

theorem cellDistance_mass (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : DyadicCube d) : cellDistance μ ν P Q univ = μ P.carrier*ν Q.carrier := by
  rw [cellDistance,Measure.map_apply (by fun_prop) MeasurableSet.univ,preimage_univ,
    ← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ,Measure.restrict_apply_univ]

theorem cellDistance_bin_witness (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (w : ℝ) (k : ℤ) (hm : cellDistance μ ν P Q (PlanarFalconer.realBin w k) ≠ 0) :
    ∃ x ∈ P.carrier, ∃ y ∈ Q.carrier, dist x y ∈ PlanarFalconer.realBin w k := by
  rw [cellDistance,Measure.map_apply (by fun_prop) (PlanarFalconer.realBin_measurable w k)] at hm
  have hae : ∀ᵐ z ∂(μ.restrict P.carrier).prod (ν.restrict Q.carrier),
      z.1 ∈ P.carrier ∧ z.2 ∈ Q.carrier := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem P.measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem Q.measurable)] with z hx hy
    exact ⟨hx,hy⟩
  obtain ⟨z,hz,hmem⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm (ae_restrict_of_ae hae)
  exact ⟨z.1,hmem.1,z.2,hmem.2,hz⟩

theorem cell_distance_variation (P Q : DyadicCube d) (hP : 0 ≤ P.side)
    (hQ : Q.side = P.side) {x x' y y' : Space d}
    (hx : x ∈ P.carrier) (hx' : x' ∈ P.carrier)
    (hy : y ∈ Q.carrier) (hy' : y' ∈ Q.carrier) :
    |dist x y-dist x' y'| ≤ 2*Real.sqrt d*P.side := by
  have h₁ := P.dist_le hP hx hx'
  have h₂ := Q.dist_le (by rwa [hQ]) hy hy'
  rw [hQ] at h₂
  have hh := dist_dist_dist_le x y x' y'
  rw [Real.dist_eq] at hh
  exact hh.trans ((add_le_add h₁ h₂).trans_eq (by ring))

theorem shared_bin_full_cell_collision
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q P' Q' : DyadicCube d) (hP : 0 ≤ P.side)
    (hQ : Q.side = P.side) (hP' : P'.side = P.side) (hQ' : Q'.side = P.side)
    (α β : Measure ℝ) (hα : α ≤ cellDistance μ ν P Q)
    (hβ : β ≤ cellDistance μ ν P' Q') {w : ℝ} (hw : w ≤ P.side)
    (hbin : ∃ k : ℤ, α (PlanarFalconer.realBin w k) ≠ 0 ∧
      β (PlanarFalconer.realBin w k) ≠ 0) :
    ((cellDistance μ ν P Q).prod (cellDistance μ ν P' Q'))
      {z : ℝ × ℝ | |z.1-z.2| ≤ (1+4*Real.sqrt d)*P.side} =
      (cellDistance μ ν P Q univ)*(cellDistance μ ν P' Q' univ) := by
  obtain ⟨k,hk₁,hk₂⟩ := hbin
  have hfull₁ : cellDistance μ ν P Q (PlanarFalconer.realBin w k) ≠ 0 := by
    intro hz
    exact hk₁ (le_antisymm ((hα _).trans_eq hz) bot_le)
  have hfull₂ : cellDistance μ ν P' Q' (PlanarFalconer.realBin w k) ≠ 0 := by
    intro hz
    exact hk₂ (le_antisymm ((hβ _).trans_eq hz) bot_le)
  obtain ⟨x,hx,y,hy,hxy⟩ := cellDistance_bin_witness μ ν P Q w k hfull₁
  obtain ⟨x',hx',y',hy',hx'y'⟩ := cellDistance_bin_witness μ ν P' Q' w k hfull₂
  have hdist := PlanarFalconer.realBin_diameter w k hxy hx'y'
  have hmem (A B : DyadicCube d) :
      ∀ᵐ z ∂(μ.restrict A.carrier).prod (ν.restrict B.carrier),
        z.1 ∈ A.carrier ∧ z.2 ∈ B.carrier := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem A.measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem B.measurable)] with z hz₁ hz₂
    exact ⟨hz₁,hz₂⟩
  have hgood : ∀ᵐ z ∂((μ.restrict P.carrier).prod (ν.restrict Q.carrier)).prod
      ((μ.restrict P'.carrier).prod (ν.restrict Q'.carrier)),
      |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ (1+4*Real.sqrt d)*P.side := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hmem P Q),
      Measure.quasiMeasurePreserving_snd.ae (hmem P' Q')] with z hz hz'
    have h₁ := cell_distance_variation P Q hP hQ hz.1 hx hz.2 hy
    have h₂ := cell_distance_variation P' Q' (by rwa [hP'])
      (hQ'.trans hP'.symm) hz'.1 hx' hz'.2 hy'
    rw [hP'] at h₂
    obtain ⟨h₁l,h₁r⟩ := abs_le.mp h₁
    obtain ⟨h₂l,h₂r⟩ := abs_le.mp h₂
    obtain ⟨h₃l,h₃r⟩ := abs_le.mp hdist
    apply abs_le.mpr
    constructor <;> nlinarith
  rw [cellDistance,cellDistance,Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (by measurability)]
  change (((μ.restrict P.carrier).prod (ν.restrict Q.carrier)).prod
      ((μ.restrict P'.carrier).prod (ν.restrict Q'.carrier)))
      {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ (1+4*Real.sqrt d)*P.side} = _
  rw [measure_congr (Filter.eventuallyEqSet_univ.mpr hgood),← univ_prod_univ,Measure.prod_prod]
  simp only [Measure.map_apply (continuous_fst.dist continuous_snd).measurable
    MeasurableSet.univ,preimage_univ]

/-- The full suffix cell grouping. Local projection tests apply to the
entire second conditional cell; the selected submeasure may be arbitrary. -/
theorem finite_suffix_cell_comparison {ι : Type*} (S : Finset ι)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : ι → DyadicCube d) (e : ι → Space d)
    (α : ι → Measure ℝ) [∀ i, IsFiniteMeasure (α i)]
    {s w : ℝ} (hs : 0 ≤ s) (hw : 0 < w) (hws : w ≤ s)
    (hP : ∀ i ∈ S, (P i).side = s) (hQ : ∀ i ∈ S, (Q i).side = s)
    (hα : ∀ i ∈ S, α i ≤ cellDistance μ ν (P i) (Q i))
    (haff : ∀ i ∈ S, ∀ x ∈ (P i).carrier, ∀ y ∈ (Q i).carrier,
      |dist x y-inner ℝ (e i) (x-y)| ≤ w)
    (F : ℝ≥0∞)
    (hproj : ∀ i ∈ S, ((ν.restrict (Q i).carrier).prod (ν.restrict (Q i).carrier))
      {z : Space d × Space d | |inner ℝ (e i) (z.1-z.2)| ≤ w} ≤
        F*(ν (Q i).carrier)^2) :
    (PlanarFalconer.binL2Norm (∑ i ∈ S, α i) w)^2 ≤
      (((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞)*F) *
        ((∑ i ∈ S, cellDistance μ ν (P i) (Q i)).prod
          (∑ i ∈ S, cellDistance μ ν (P i) (Q i)))
          {z : ℝ × ℝ | |z.1-z.2| ≤ (1+4*Real.sqrt d)*s} := by
  apply PlanarFalconer.finite_bin_collision_comparison S α
    (fun i => cellDistance μ ν (P i) (Q i)) w _ _
  · intro i hi
    have hlocal := local_distance_collision_bound μ ν (P i) (Q i) (e i) hw
      (haff i hi) (hproj i hi)
    rw [pow_two,PlanarFalconer.binL2Norm_mul_self]
    apply (PlanarFalconer.real_bin_collision_bound (α i) hw).trans
    apply (Measure.prod_mono (hα i hi) (hα i hi) _).trans
    rw [cellDistance,Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Measure.map_apply (by fun_prop) (by measurability)]
    apply hlocal.trans_eq
    change μ (P i).carrier ^ 2 *
      (((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞) * (F * ν (Q i).carrier ^ 2)) =
      (((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞) * F) *
        (cellDistance μ ν (P i) (Q i) univ)^2
    rw [cellDistance_mass]
    ring
  · intro i hi j hj hbin
    have hP0 : 0 ≤ (P i).side := by rwa [hP i hi]
    have he := shared_bin_full_cell_collision μ ν (P i) (Q i) (P j) (Q j) hP0
      ((hQ i hi).trans (hP i hi).symm)
      ((hP j hj).trans (hP i hi).symm)
      ((hQ j hj).trans (hP i hi).symm)
      (α i) (α j) (hα i hi) (hα j hj) (by rwa [hP i hi]) hbin
    simpa only [hP i hi] using he

end Falconer

end OAI
