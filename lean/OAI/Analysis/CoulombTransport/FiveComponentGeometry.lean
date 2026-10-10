import OAI.Analysis.CoulombTransport.GluedCertificate
import OAI.Analysis.CoulombTransport.CoulombLocalCertificate
import OAI.Analysis.CoulombTransport.CenterCertificate
import OAI.Analysis.CoulombTransport.CoulombEstimates

namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry

open LocalGeometry StationaryMap CenterCertificate

abbrev ChartsAt (a : E3) :=
  LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a)

/-- The actual five local potentials of the Coulomb construction, with the
same central quadratic for both branches. -/
def potentials (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    Fin 5 → E3 → ℝ :=
  ![fun x => (5 : ℝ) / 2 - 10 * ‖x‖ ^ 2,
    C₁.value,
    fun z => (5 : ℝ) / 4 * ⟪point 1, z + point 1⟫_ℝ - 10 * ‖z + point 1‖ ^ 2,
    C₂.value,
    fun z => (5 : ℝ) / 4 * ⟪point 3, z + point 3⟫_ℝ - 10 * ‖z + point 3‖ ^ 2]

/-- Preliminary domains are unrestricted for the polynomial potentials and
are the actual chart sources for the two supporting-value potentials. -/
def domains (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) : Fin 5 → Set E3 :=
  ![univ, C₁.charts.central.source, univ, C₂.charts.central.source, univ]

lemma norm_point_one : ‖point 1‖ = 1 := by
  change ‖(!₂[1, 0, 0] : E3)‖ = 1
  norm_num [point, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

lemma norm_point_three : ‖point 3‖ = 1 := by
  change ‖(!₂[0, 1, 0] : E3)‖ = 1
  norm_num [point, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

lemma point_two_eq_neg : point 2 = -point 1 := by
  change (!₂[-1, 0, 0] : E3) = -(!₂[1, 0, 0] : E3)
  ext i
  fin_cases i <;> norm_num [point]

lemma point_four_eq_neg : point 4 = -point 3 := by
  change (!₂[0, -1, 0] : E3) = -(!₂[0, 1, 0] : E3)
  ext i
  fin_cases i <;> norm_num [point]

lemma domains_open (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∀ i, IsOpen (domains C₁ C₂ i) := by
  intro i
  fin_cases i
  · exact isOpen_univ
  · exact C₁.charts.central.open_source
  · exact isOpen_univ
  · exact C₂.charts.central.open_source
  · exact isOpen_univ

lemma point_mem_domains (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∀ i, point i ∈ domains C₁ C₂ i := by
  intro i
  fin_cases i
  · exact mem_univ _
  · exact C₁.charts.point_mem
  · exact mem_univ _
  · exact C₂.charts.point_mem
  · exact mem_univ _

lemma continuousOn_potentials (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∀ i, ContinuousOn (potentials C₁ C₂ i) (domains C₁ C₂ i) := by
  intro i
  fin_cases i
  · exact (by fun_prop : Continuous (fun x : E3 => (5 : ℝ) / 2 - 10 * ‖x‖ ^ 2)).continuousOn
  · exact C₁.value_analytic.continuousOn
  · exact (by fun_prop : Continuous (fun z : E3 =>
      (5 : ℝ) / 4 * ⟪point 1, z + point 1⟫_ℝ - 10 * ‖z + point 1‖ ^ 2)).continuousOn
  · exact C₂.value_analytic.continuousOn
  · exact (by fun_prop : Continuous (fun z : E3 =>
      (5 : ℝ) / 4 * ⟪point 3, z + point 3⟫_ℝ - 10 * ‖z + point 3‖ ^ 2)).continuousOn

lemma potentials_center_values (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∀ i, potentials C₁ C₂ i (point i) = if i = 0 then (5 / 2 : ℝ) else 0 := by
  intro i
  fin_cases i
  · norm_num [potentials, point]
  · exact localSupporting_value_center norm_point_one C₁
  · change (5 : ℝ) / 4 * ⟪point 1, point 2 + point 1⟫_ℝ -
      10 * ‖point 2 + point 1‖ ^ 2 = 0
    rw [point_two_eq_neg]
    simp
  · exact localSupporting_value_center norm_point_three C₂
  · change (5 : ℝ) / 4 * ⟪point 3, point 4 + point 3⟫_ℝ -
      10 * ‖point 4 + point 3‖ ^ 2 = 0
    rw [point_four_eq_neg]
    simp

/-- The actual potentials have the strict bad-type gap supplied by the
finite center certificate. -/
lemma strict_center_gap (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (i j k : Fin 5) (h : ¬ Good i j k) :
    ENNReal.ofReal (potentials C₁ C₂ i (point i) +
      potentials C₁ C₂ j (point j) + potentials C₁ C₂ k (point k)) <
      coulombCost (point i, (point j, point k)) := by
  have he (l : Fin 5) : ENNReal.ofReal (potentials C₁ C₂ l (point l)) = potential l := by
    rw [potentials_center_values]
    by_cases hl : l = 0
    · simp only [hl, ite_eq_left, potential]
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    · simp [potential, hl]
  have hn (l : Fin 5) : 0 ≤ potentials C₁ C₂ l (point l) := by
    rw [potentials_center_values]
    split_ifs <;> norm_num
  rw [ENNReal.ofReal_add (add_nonneg (hn i) (hn j)) (hn k),
    ENNReal.ofReal_add (hn i) (hn j), he i, he j, he k]
  exact strict_of_not_good i j k h

/-- The real local certificate has the exact extended-valued interpretation
on any collision-free triple in its three component balls. -/
theorem ennreal_local_certificate {a : E3} (C : ChartsAt a) {x y z : E3}
    (hy : y ∈ ball a C.parameterRadius)
    (hx : x ∈ ball (0 : E3) C.stateRadius)
    (hz : z ∈ ball (-a) C.stateRadius)
    (hxy : 0 < dist x y) (hxz : 0 < dist x z) (hyz : 0 < dist y z) :
    ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2)) ≤ coulombCost (x, (y, z)) ∧
    (ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2)) = coulombCost (x, (y, z)) ↔
      x = C.charts.central y ∧ z = C.charts.opposite y) := by
  let R : ℝ := ‖x - y‖⁻¹ + ‖x - z‖⁻¹ + ‖y - z‖⁻¹
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hc : coulombCost (x, (y, z)) = ENNReal.ofReal R := by
    simpa only [CoulombEstimates.realCost, dist_eq_norm] using
      CoulombEstimates.coulombCost_eq_ofReal_realCost hxy hxz hyz
  refine ⟨?_, ?_⟩
  · rw [hc]
    exact ENNReal.ofReal_le_ofReal (local_coulomb_supporting C hy hx hz)
  · constructor
    · intro heq
      have hs := (ENNReal.ofReal_pos.mp (heq.symm ▸ coulombCost_pos (x, (y, z)))).le
      have heqR := (ENNReal.ofReal_eq_ofReal_iff hs hR).mp (heq.trans hc)
      exact (local_coulomb_contact C hy hx hz).mp heqR.symm
    · intro hbranch
      have heqR := (local_coulomb_contact C hy hx hz).mpr hbranch
      exact (congrArg ENNReal.ofReal heqR).symm.trans hc.symm

/-- Symmetric union of the two actual local branch graphs. The parameter
remains in the corresponding chart source. -/
def branchContact (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) (t : Triple) : Prop :=
  (∃ y ∈ C₁.charts.central.source,
    List.Perm [t.1, t.2.1, t.2.2] [C₁.charts.central y, y, C₁.charts.opposite y]) ∨
  (∃ y ∈ C₂.charts.central.source,
    List.Perm [t.1, t.2.1, t.2.2] [C₂.charts.central y, y, C₂.charts.opposite y])

lemma branchContact_perm (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    {x y z x' y' z' : E3} (hp : List.Perm [x, y, z] [x', y', z']) :
    branchContact C₁ C₂ (x, (y, z)) ↔ branchContact C₁ C₂ (x', (y', z')) := by
  constructor
  · intro h
    rcases h with ⟨w, hw, hperm⟩ | ⟨w, hw, hperm⟩
    · exact Or.inl ⟨w, hw, hp.symm.trans hperm⟩
    · exact Or.inr ⟨w, hw, hp.symm.trans hperm⟩
  · intro h
    rcases h with ⟨w, hw, hperm⟩ | ⟨w, hw, hperm⟩
    · exact Or.inl ⟨w, hw, hp.trans hperm⟩
    · exact Or.inr ⟨w, hw, hp.trans hperm⟩

end Problem356.FiveComponentGeometry

end

end OAI
