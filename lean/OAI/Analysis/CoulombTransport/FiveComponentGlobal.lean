import OAI.Analysis.CoulombTransport.FiveComponentGeometry
import OAI.Analysis.CoulombTransport.FiveComponentCanonical
import OAI.Analysis.CoulombTransport.GoodTypePermutation
import OAI.Analysis.CoulombTransport.GluedCertificateForward

namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry
open CenterCertificate GoodTypePermutation

/-- The actual two canonical local certificates glue into one globally bounded
potential on the five disjoint component balls. -/
theorem exists_global_certificate_of_canonical
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (W : Fin 5 → Set E3) (hW : ∀ i, IsOpen (W i))
    (hpW : ∀ i, point i ∈ W i) (hWD : ∀ i, W i ⊆ domains C₁ C₂ i)
    (h012 : LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 1 2)
    (h034 : LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 3 4) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (point i) r
      let u := ComponentPotential.glue U (potentials C₁ C₂)
      (∀ i, U i ⊆ W i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
          branchContact C₁ C₂ (x, (y, z)))) := by
  apply exists_glued_component_certificate_forward point point_injective W hW hpW
    (potentials C₁ C₂)
    (fun i => (continuousOn_potentials C₁ C₂ i).mono (hWD i))
    (fun a => Good a.1 a.2.1 a.2.2) (branchContact C₁ C₂)
  · intro a ha
    exact eventually_certificate_of_good point (fun i => (hW i).mem_nhds (hpW i))
      (fun hp hc => (branchContact_perm C₁ C₂ hp).mp hc)
      h012 h034 a.1 a.2.1 a.2.2 ha
  · intro a ha
    exact strict_center_gap C₁ C₂ a.1 a.2.1 a.2.2 ha

/-- Every collision-free raw branch triple saturates the local potential. -/
lemma ennreal_graph_equality {a : E3} (C : ChartsAt a) {y : E3}
    (hy : y ∈ C.charts.central.source)
    (hxy : 0 < dist (C.charts.central y) y)
    (hxz : 0 < dist (C.charts.central y) (C.charts.opposite y))
    (hyz : 0 < dist y (C.charts.opposite y)) :
    ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖C.charts.central y‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, C.charts.opposite y + a⟫_ℝ -
        10 * ‖C.charts.opposite y + a‖ ^ 2)) =
      coulombCost (C.charts.central y, (y, C.charts.opposite y)) := by
  have hs := C.charts.mapsTo_state hy
  rw [C.state_ball, ← ball_prod_same] at hs
  exact (ennreal_local_certificate C (C.source_ball ▸ hy) hs.1 hs.2 hxy hxz hyz).2.mpr
    ⟨rfl, rfl⟩

private lemma ne_of_disjoint_components {U : Fin 5 → Set E3}
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    {i j : Fin 5} (hij : i ≠ j) {x y : E3} (hx : x ∈ U i) (hy : y ∈ U j) :
    x ≠ y := by
  intro h
  subst y
  exact Set.disjoint_left.mp (hdisj hij) hx hy

/-- Saturation on the first raw branch, after gluing. -/
theorem glued_saturation_left (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    {U : Fin 5 → Set E3} (hUD : ∀ i, U i ⊆ domains C₁ C₂ i)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    {x y z : E3} (hx : x ∈ U 0) (hy : y ∈ U 1) (hz : z ∈ U 2)
    (hX : x = C₁.charts.central y) (hZ : z = C₁.charts.opposite y) :
    let u := ComponentPotential.glue U (potentials C₁ C₂)
    ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) := by
  dsimp only
  rw [ComponentPotential.glue_eq hdisj hx, ComponentPotential.glue_eq hdisj hy,
    ComponentPotential.glue_eq hdisj hz]
  have hxy := dist_pos.mpr (ne_of_disjoint_components hdisj (by decide : (0 : Fin 5) ≠ 1) hx hy)
  have hxz := dist_pos.mpr (ne_of_disjoint_components hdisj (by decide : (0 : Fin 5) ≠ 2) hx hz)
  have hyz := dist_pos.mpr (ne_of_disjoint_components hdisj (by decide : (1 : Fin 5) ≠ 2) hy hz)
  subst x
  subst z
  exact ennreal_graph_equality C₁ (hUD 1 hy) hxy hxz hyz

/-- Saturation on the second raw branch, after gluing. -/
theorem glued_saturation_right (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    {U : Fin 5 → Set E3} (hUD : ∀ i, U i ⊆ domains C₁ C₂ i)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    {x y z : E3} (hx : x ∈ U 0) (hy : y ∈ U 3) (hz : z ∈ U 4)
    (hX : x = C₂.charts.central y) (hZ : z = C₂.charts.opposite y) :
    let u := ComponentPotential.glue U (potentials C₁ C₂)
    ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) := by
  dsimp only
  rw [ComponentPotential.glue_eq hdisj hx, ComponentPotential.glue_eq hdisj hy,
    ComponentPotential.glue_eq hdisj hz]
  have hxy := dist_pos.mpr (ne_of_disjoint_components hdisj (by decide : (0 : Fin 5) ≠ 3) hx hy)
  have hxz := dist_pos.mpr (ne_of_disjoint_components hdisj (by decide : (0 : Fin 5) ≠ 4) hx hz)
  have hyz := dist_pos.mpr (ne_of_disjoint_components hdisj (by decide : (3 : Fin 5) ≠ 4) hy hz)
  subst x
  subst z
  exact ennreal_graph_equality C₂ (hUD 3 hy) hxy hxz hyz

/-- The concrete two Coulomb charts admit a globally bounded measurable
certificate on five disjoint component balls, with contact only on their
actual symmetric graph union. -/
theorem exists_global_certificate
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (point i) r
      let u := ComponentPotential.glue U (potentials C₁ C₂)
      (∀ i, U i ⊆ domains C₁ C₂ i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
          branchContact C₁ C₂ (x, (y, z)))) := by
  obtain ⟨W, hW, h012, h034⟩ := exists_canonical_neighborhoods C₁ C₂
  apply exists_glued_component_certificate_forward point point_injective
    (domains C₁ C₂) (domains_open C₁ C₂) (point_mem_domains C₁ C₂)
    (potentials C₁ C₂) (continuousOn_potentials C₁ C₂)
    (fun a => Good a.1 a.2.1 a.2.2) (branchContact C₁ C₂)
  · intro a ha
    exact eventually_certificate_of_good point hW
      (fun hp hc => (branchContact_perm C₁ C₂ hp).mp hc)
      h012 h034 a.1 a.2.1 a.2.2 ha
  · intro a ha
    exact strict_center_gap C₁ C₂ a.1 a.2.1 a.2.2 ha

end Problem356.FiveComponentGeometry

end

end OAI
