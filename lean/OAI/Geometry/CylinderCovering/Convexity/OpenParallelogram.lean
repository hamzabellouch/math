import OAI.Geometry.CylinderCovering.Convexity.ConvexOpenEnlargement
import OAI.Geometry.CylinderCovering.Convexity.ParallelogramGeometry

namespace OAI

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Topology

namespace RuledApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem IsParallelogram.exists_openParallelogram_superset
    (μ : Measure E) [IsAddHaarMeasure μ] (hd : Module.finrank ℝ E = 2)
    {P : Set E} (hP : IsParallelogram P) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set E, IsOpenParallelogram U ∧ P ⊆ U ∧
      IsOpen U ∧ Bornology.IsBounded U ∧ MeasurableSet U ∧
      μ.real U < μ.real P + ε := by
  obtain ⟨c,hc⟩ := hP.interior_nonempty hd
  obtain ⟨r,hr,hPU,hUo,hUb,hUm,harea⟩ :=
    CylinderCovering.OpenEnlargement.exists_homothetic_open_enlargement μ
      hP.compact hP.convex hc hε
  refine ⟨interior (AffineMap.homothety c r '' P), ?_, hPU,hUo,hUb,hUm,harea⟩
  exact (hP.homothety c (by linarith)).isOpenParallelogram_interior hd

theorem IsParallelogram.exists_openParallelogram_superset_exact
    (μ : Measure E) [IsAddHaarMeasure μ] (hd : Module.finrank ℝ E = 2)
    {P : Set E} (hP : IsParallelogram P) {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : E) (r : ℝ) (U : Set E), c ∈ interior P ∧ 1 < r ∧
      U = interior (AffineMap.homothety c r '' P) ∧
      IsOpenParallelogram U ∧ P ⊆ U ∧ IsOpen U ∧ Bornology.IsBounded U ∧
      MeasurableSet U ∧ μ.real U = r^2 * μ.real P ∧ μ.real U < μ.real P + ε := by
  obtain ⟨c,hc⟩ := hP.interior_nonempty hd
  obtain ⟨r,hr,hPU,hUo,hUb,hUm,harea⟩ :=
    CylinderCovering.OpenEnlargement.exists_homothetic_open_enlargement μ
      hP.compact hP.convex hc hε
  refine ⟨c,r,interior (AffineMap.homothety c r '' P),hc,hr,rfl,
    (hP.homothety c (by linarith)).isOpenParallelogram_interior hd,
    hPU,hUo,hUb,hUm,?_,harea⟩
  simpa only [hd, abs_of_nonneg (sq_nonneg r)] using
    CylinderCovering.OpenEnlargement.measureReal_interior_homothety μ hP.convex c r

theorem Cylinder.basePlane_finrank (C : Cylinder) :
    Module.finrank ℝ ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ) = 2 := by
  have hne : C.axis ≠ 0 := by
    intro h
    have := C.unit_axis
    simp [h] at this
  have hd := (Submodule.span ℝ ({C.axis} : Set Space)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hne, finrank_euclideanSpace_fin] at hd
  omega

theorem Cylinder.enlarge_openParallelogram {C : Cylinder} (hC : C.parallelogram)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : Cylinder, D.axis = C.axis ∧ D.openParallelogram ∧ D.openBounded ∧
      C.carrier ⊆ D.carrier ∧ D.area < C.area + ε := by
  obtain ⟨U,hUP,hCU,hUo,hUb,hUm,harea⟩ :=
    hC.exists_openParallelogram_superset volume C.basePlane_finrank hε
  refine ⟨⟨C.axis,C.unit_axis,U⟩,rfl,hUP,⟨hUo,hUb,hUm⟩,?_,harea⟩
  rintro x ⟨b,hb,t,hx⟩
  exact ⟨b,hCU hb,t,hx⟩

theorem finite_enlarge_openParallelogram {n : ℕ} (C : Fin n → Cylinder)
    (hC : ∀ i, (C i).parallelogram) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : Fin n → Cylinder, (∀ i, (D i).axis = (C i).axis) ∧
      (∀ i, (D i).openParallelogram ∧ (D i).openBounded) ∧
      familySet C ⊆ familySet D ∧ familyArea D < familyArea C + ε := by
  classical
  have hn : 0 < (n+1 : ℝ) := by positivity
  have hδ : 0 < ε / (n+1 : ℝ) := div_pos hε hn
  choose D haxis hshape hopen hcover harea using
    fun i => (C i).enlarge_openParallelogram (hC i) hδ
  refine ⟨D,haxis,fun i => ⟨hshape i,hopen i⟩,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i,hcover i hi⟩
  · have herror : (n : ℝ) * (ε / (n+1 : ℝ)) < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ hn]
      nlinarith
    calc
      familyArea D ≤ ∑ i, ((C i).area + ε / (n+1 : ℝ)) :=
        Finset.sum_le_sum (fun i _ => (harea i).le)
      _ = familyArea C + (n : ℝ) * (ε / (n+1 : ℝ)) := by
        simp [familyArea, Finset.sum_add_distrib]
      _ < familyArea C + ε := by linarith

theorem openParallelogramEnlargement_result : OpenParallelogramEnlargementStatement := by
  intro n C hC ε hε
  exact finite_enlarge_openParallelogram C hC hε

end RuledApproximation

end

end OAI
