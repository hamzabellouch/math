import OAI.Analysis.CoulombTransport.ExistenceFromLocalGeometry
import OAI.Analysis.CoulombTransport.FiveComponentGeometry
import OAI.Analysis.CoulombTransport.CommonBranches
import OAI.Analysis.CoulombTransport.ComponentRegions
import OAI.Analysis.CoulombTransport.ContactSelection
import OAI.Analysis.CoulombTransport.FiveComponentGlobal
import OAI.Analysis.CoulombTransport.CoulombSupportSeparated

namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry

open LocalGeometry CenterCertificate

theorem ennreal_graph_contact {a : E3} (C : ChartsAt a) {s : E3}
    (hs : s ∈ C.charts.central.source)
    (hxy : 0 < dist (C.charts.central s) s)
    (hxz : 0 < dist (C.charts.central s) (C.charts.opposite s))
    (hyz : 0 < dist s (C.charts.opposite s)) :
    ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖C.charts.central s‖ ^ 2) + C.value s +
      ((5 : ℝ) / 4 * ⟪a, C.charts.opposite s + a⟫_ℝ -
        10 * ‖C.charts.opposite s + a‖ ^ 2)) =
      coulombCost (C.charts.central s, (s, C.charts.opposite s)) := by
  have ht := C.charts.mapsTo_state hs
  rw [C.state_ball, ← ball_prod_same] at ht
  exact (ennreal_local_certificate C (C.source_ball ▸ hs) ht.1 ht.2 hxy hxz hyz).2.mpr
    ⟨rfl, rfl⟩

/-- The actual five-component certificate discharges every local-geometry
input, after choosing a sufficiently small common central ball. -/
theorem fullConclusion_of_five_component_certificate
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (hout₁ : ∀ s ∈ C₁.charts.central.source,
      s ∉ ball (0 : E3) (1 / 4) ∧ C₁.charts.opposite s ∉ ball (0 : E3) (1 / 4))
    (hout₂ : ∀ s ∈ C₂.charts.central.source,
      s ∉ ball (0 : E3) (1 / 4) ∧ C₂.charts.opposite s ∉ ball (0 : E3) (1 / 4))
    {R : ℝ} (hR : 0 < R)
    (hdisj : Pairwise (fun i j : Fin 5 => Disjoint (ball (point i) R) (ball (point j) R)))
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x, |u x| ≤ M)
    (hueq : ∀ i x, x ∈ ball (point i) R → u x = potentials C₁ C₂ i x)
    (hcert : ∀ x ∈ ⋃ i : Fin 5, ball (point i) R,
      ∀ y ∈ ⋃ i : Fin 5, ball (point i) R, ∀ z ∈ ⋃ i : Fin 5, ball (point i) R,
      ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
      (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
        branchContact C₁ C₂ (x, (y, z)))) :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by
  let X : Fin 2 → OpenPartialHomeomorph E3 E3 := ![C₁.charts.central, C₂.charts.central]
  let Z : Fin 2 → OpenPartialHomeomorph E3 E3 := ![C₁.charts.opposite, C₂.charts.opposite]
  let a : Fin 2 → E3 := ![point 1, point 3]
  let P : Fin 2 → Set E3 := ![ball (point 1) R, ball (point 3) R]
  let Q : Fin 2 → Set E3 := ![ball (point 2) R, ball (point 4) R]
  have haX : ∀ i, a i ∈ (X i).source := by
    intro i; fin_cases i
    · exact C₁.charts.point_mem
    · exact C₂.charts.point_mem
  have haZ : ∀ i, a i ∈ (Z i).source := by
    intro i; fin_cases i
    · exact C₁.charts.source_eq ▸ C₁.charts.point_mem
    · exact C₂.charts.source_eq ▸ C₂.charts.point_mem
  have hcenter : ∀ i, X i (a i) = 0 := by
    intro i; fin_cases i
    · exact C₁.charts.central_value
    · exact C₂.charts.central_value
  have hP : ∀ i, IsOpen (P i) := by intro i; fin_cases i <;> exact isOpen_ball
  have hQ : ∀ i, IsOpen (Q i) := by intro i; fin_cases i <;> exact isOpen_ball
  have haP : ∀ i, a i ∈ P i := by intro i; fin_cases i <;> exact mem_ball_self hR
  have haQ : ∀ i, Z i (a i) ∈ Q i := by
    intro i; fin_cases i
    · change C₁.charts.opposite (point 1) ∈ ball (point 2) R
      rw [C₁.charts.opposite_value, point_two_eq_neg]
      exact mem_ball_self hR
    · change C₂.charts.opposite (point 3) ∈ ball (point 4) R
      rw [C₂.charts.opposite_value, point_four_eq_neg]
      exact mem_ball_self hR
  obtain ⟨r, hr, hsub, hlocal⟩ := CommonBranches.exists_common_central_ball_in_components
    X Z a 0 haX haZ hcenter P Q hP hQ haP haQ
    (isOpen_ball.inter isOpen_ball)
    (show (0 : E3) ∈ ball 0 R ∩ ball 0 (1 / 4) from
      ⟨mem_ball_self hR, mem_ball_self (by norm_num)⟩)
  let e := CommonBranches.four X Z
  have hBS : ∀ i, ball (0 : E3) r ⊆ (CommonBranches.outer (X i) (Z i)).source :=
    fun i x hx => (hlocal i x hx).1
  have hsource : ∀ i, ball (0 : E3) r ⊆ (e i).source :=
    CommonBranches.subset_four_sources X Z hBS
  have hB0 : ball (0 : E3) r ⊆ ball (point 0) R := by
    have hp0 : point 0 = (0 : E3) := by
      ext i; fin_cases i <;> rfl
    rw [hp0]
    exact fun x hx => (hsub hx).1
  have himages : ∀ i, e i '' ball (0 : E3) r ⊆ ball (point i.succ) R := by
    rintro i _ ⟨x, hx, rfl⟩
    fin_cases i
    · exact (hlocal 0 x hx).2.1
    · exact (hlocal 0 x hx).2.2
    · exact (hlocal 1 x hx).2.1
    · exact (hlocal 1 x hx).2.2
  have he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source := by
    apply CommonBranches.contDiffOn_four
    · intro i; fin_cases i
      · exact C₁.charts.central_inverse_analytic.of_le (by simp)
      · exact C₂.charts.central_inverse_analytic.of_le (by simp)
    · intro i; fin_cases i
      · exact C₁.charts.opposite_analytic.of_le (by simp)
      · exact C₂.charts.opposite_analytic.of_le (by simp)
  have he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target := by
    apply CommonBranches.contDiffOn_four_symm
    · intro i; fin_cases i
      · exact C₁.charts.central_analytic.of_le (by simp)
      · exact C₂.charts.central_analytic.of_le (by simp)
    · intro i; fin_cases i
      · exact C₁.charts.opposite_inverse_analytic.of_le (by simp)
      · exact C₂.charts.opposite_inverse_analytic.of_le (by simp)
  have hmem (i : Fin 4) {x : E3} (hx : x ∈ ball (0 : E3) r) :
      e i x ∈ ball (point i.succ) R := himages i ⟨x, hx, rfl⟩
  have hdist {i j : Fin 5} (hij : i ≠ j) {x y : E3}
      (hx : x ∈ ball (point i) R) (hy : y ∈ ball (point j) R) : 0 < dist x y := by
    apply dist_pos.mpr
    intro heq
    exact Set.disjoint_left.mp (hdisj hij) hx (heq ▸ hy)
  have hcontact (i : Fin 2) (x : E3) (hx : x ∈ ball (0 : E3) r) :
      ENNReal.ofReal (u x + u ((X i).symm x) + u (CommonBranches.outer (X i) (Z i) x)) =
        coulombCost (x, ((X i).symm x, CommonBranches.outer (X i) (Z i) x)) := by
    have hprop := CommonBranches.outer_source_properties (X i) (Z i) (hBS i hx)
    fin_cases i
    · change ENNReal.ofReal (u x + u (C₁.charts.central.symm x) +
          u (C₁.charts.opposite (C₁.charts.central.symm x))) =
        coulombCost (x, (C₁.charts.central.symm x, C₁.charts.opposite (C₁.charts.central.symm x)))
      have hy : C₁.charts.central.symm x ∈ ball (point 1) R := hmem 0 hx
      have hz : C₁.charts.opposite (C₁.charts.central.symm x) ∈ ball (point 2) R := hmem 1 hx
      have hinv : C₁.charts.central (C₁.charts.central.symm x) = x := hprop.2.2.2.2
      rw [hueq 0 x (hB0 hx), hueq 1 _ hy, hueq 2 _ hz]
      have hc := ennreal_graph_contact C₁ (s := C₁.charts.central.symm x) hprop.2.1
        (by rw [hinv]; exact hdist (by decide : (0 : Fin 5) ≠ 1) (hB0 hx) hy)
        (by rw [hinv]; exact hdist (by decide : (0 : Fin 5) ≠ 2) (hB0 hx) hz)
        (hdist (by decide : (1 : Fin 5) ≠ 2) hy hz)
      simpa [potentials, hinv] using hc
    · change ENNReal.ofReal (u x + u (C₂.charts.central.symm x) +
          u (C₂.charts.opposite (C₂.charts.central.symm x))) =
        coulombCost (x, (C₂.charts.central.symm x, C₂.charts.opposite (C₂.charts.central.symm x)))
      have hy : C₂.charts.central.symm x ∈ ball (point 3) R := hmem 2 hx
      have hz : C₂.charts.opposite (C₂.charts.central.symm x) ∈ ball (point 4) R := hmem 3 hx
      have hinv : C₂.charts.central (C₂.charts.central.symm x) = x := hprop.2.2.2.2
      rw [hueq 0 x (hB0 hx), hueq 3 _ hy, hueq 4 _ hz]
      have hc := ennreal_graph_contact C₂ (s := C₂.charts.central.symm x) hprop.2.1
        (by rw [hinv]; exact hdist (by decide : (0 : Fin 5) ≠ 3) (hB0 hx) hy)
        (by rw [hinv]; exact hdist (by decide : (0 : Fin 5) ≠ 4) (hB0 hx) hz)
        (hdist (by decide : (3 : Fin 5) ≠ 4) hy hz)
      simpa [potentials, hinv] using hc
  apply exists_fullCoulombConclusion_of_local_geometry 0 hr e hsource
    (SmoothBranchMarginal.componentRegion_pairwise_of_subsets hdisj hB0 himages) he he'
    (MeasurableSet.iUnion fun _ => isOpen_ball.measurableSet)
    (fun x hx => mem_iUnion.mpr ⟨0, hB0 hx⟩)
    (fun i x hx => mem_iUnion.mpr ⟨i.succ, himages i hx⟩)
    hu hM (fun x _ => abs_le.mp (hubound x))
    (fun t h1 h2 h3 => (hcert _ h1 _ h2 _ h3).1)
    (hcontact 0) (hcontact 1)
  intro x y z hx hy hz hc
  have hc' := (hcert x (mem_iUnion.mpr ⟨0, hB0 hx⟩) y hy z hz).2 hc
  rcases hc' with ⟨s, hs, hp⟩ | ⟨s, hs, hp⟩
  · have hy' := ContactSelection.second_selects_inverse_branch hp hx hs
      (fun s hs => ⟨fun h => (hout₁ s hs).1 (hsub h).2,
        fun h => (hout₁ s hs).2 (hsub h).2⟩)
      (fun s hs => C₁.charts.central.left_inv hs)
      (show ∀ w ∈ ball (0 : E3) r,
        CommonBranches.outer C₁.charts.central C₁.charts.opposite w =
          C₁.charts.opposite (C₁.charts.central.symm w) from fun _ _ => rfl)
    rcases hy' with hy' | hy'
    · exact ⟨0, hy'⟩
    · exact ⟨1, hy'⟩
  · have hy' := ContactSelection.second_selects_inverse_branch hp hx hs
      (fun s hs => ⟨fun h => (hout₂ s hs).1 (hsub h).2,
        fun h => (hout₂ s hs).2 (hsub h).2⟩)
      (fun s hs => C₂.charts.central.left_inv hs)
      (show ∀ w ∈ ball (0 : E3) r,
        CommonBranches.outer C₂.charts.central C₂.charts.opposite w =
          C₂.charts.opposite (C₂.charts.central.symm w) from fun _ _ => rfl)
    rcases hy' with hy' | hy'
    · exact ⟨2, hy'⟩
    · exact ⟨3, hy'⟩

/-- The unconditional witness: the actual separated local Coulomb charts
and their global certificate supply all inputs of the construction. -/
theorem exists_full_coulomb_conclusion :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by
  have hp1 : point 1 = CoulombCalculus.axisVector 0 := by
    ext i; fin_cases i <;> norm_num [point, CoulombCalculus.axisVector]
  have hp3 : point 3 = CoulombCalculus.axisVector 1 := by
    change (!₂[0, 1, 0] : E3) = CoulombCalculus.axisVector 1
    ext i; fin_cases i <;> norm_num [CoulombCalculus.axisVector]
  have h₁ := CoulombSupportExistence.exists_coulombLocalSupportingCharts_separated 0
  have h₂ := CoulombSupportExistence.exists_coulombLocalSupportingCharts_separated 1
  rw [← hp1] at h₁
  rw [← hp3] at h₂
  obtain ⟨C₁, hout₁⟩ := h₁
  obtain ⟨C₂, hout₂⟩ := h₂
  obtain ⟨R, M, hR, hM, _, hdisj, hu, _, hubound, hcert⟩ :=
    exists_global_certificate C₁ C₂
  apply fullConclusion_of_five_component_certificate C₁ C₂ hout₁ hout₂ hR hdisj hu
    hM.le hubound ?_ hcert
  intro i x hx
  exact ComponentPotential.glue_eq hdisj hx

end Problem356.FiveComponentGeometry

end

end OAI
