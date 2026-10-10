import OAI.MeasureTheory.Falconer.Estimates.ProfilePacking
import OAI.MeasureTheory.Falconer.Graphs.GraphGeometry
import OAI.MeasureTheory.Falconer.Radial.RadialContinuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

noncomputable def stripCount {ι : Type*} (S : Finset ι) (v : ι → Plane)
    (W : ℝ) (ω : Plane) : ℕ := by
  classical
  exact (S.filter fun i => |planeDot (v i) ω| ≤ W).card

theorem measurable_stripCount {ι : Type*} (S : Finset ι) (v : ι → Plane) (W : ℝ) :
    Measurable (fun ω : Plane => stripCount S v W ω) := by
  classical
  have he : (fun ω : Plane => stripCount S v W ω) =
      fun ω => ∑ i ∈ S, if |planeDot (v i) ω| ≤ W then (1:ℕ) else 0 := by
    funext ω
    simp [stripCount]
  rw [he]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  apply measurableSet_le _ measurable_const
  have hc : Continuous (fun ω : Plane => |planeDot (v i) ω|) := by
    unfold planeDot
    fun_prop
  exact hc.measurable

theorem stripCount_neg {ι : Type*} (S : Finset ι) (v : ι → Plane) (W : ℝ) (ω : Plane) :
    stripCount S v W (-ω) = stripCount S v W ω := by
  classical
  have he (i : ι) : planeDot (v i) (-ω) = -planeDot (v i) ω := by simp [planeDot]; ring
  simp only [stripCount,he,abs_neg]

theorem stripCount_transfer {ι : Type*} (S : Finset ι) (v : ι → Plane)
    {W W' D d : ℝ} (hD : 0 ≤ D) (hv : ∀ i ∈ S, ‖v i‖ ≤ D)
    {ω ω' : Plane} (hd : dist ω ω' ≤ d) (hgap : W'+D*d ≤ W) :
    stripCount S v W' ω' ≤ stripCount S v W ω := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,hstrip⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hi,?_⟩
  have he : planeDot (v i) ω = planeDot (v i) ω' + planeDot (v i) (ω-ω') := by
    simp [planeDot]; ring
  have hn : ‖ω-ω'‖ ≤ d := by simpa only [dist_eq_norm] using hd
  calc
    |planeDot (v i) ω| ≤ |planeDot (v i) ω'|+|planeDot (v i) (ω-ω')| := by
      rw [he]; exact abs_add_le _ _
    _ ≤ W'+D*d := add_le_add hstrip ((planeDot_abs_le _ _).trans
      (mul_le_mul (hv i hi) hn (norm_nonneg _) hD))
    _ ≤ W := hgap

noncomputable def parallelTestCells (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) : Finset CellPath := by
  classical
  exact (dyadicPaths p).filter fun c => 0 < ρ (Q.descendant c).carrier ∧
    (Q.descendant c).center ∈ ball (Q.descendant P).center (10/(2:ℝ)^g)

noncomputable def projectionTestCells (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) : Finset CellPath := by
  classical
  exact (dyadicPaths u).filter fun c => 0 < ρ (Q.descendant c).carrier ∧ c.take p = P

noncomputable def parallelTestCount (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) : ℕ :=
  stripCount (parallelTestCells Q ρ g p P)
    (fun c => (Q.descendant c).center-(Q.descendant P).center) W (quarterTurn ω)

noncomputable def projectionTestCount (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) : ℕ :=
  let S := projectionTestCells Q ρ p u P
  stripCount (S.product S) (fun cc => (Q.descendant cc.1).center-(Q.descendant cc.2).center) W ω

noncomputable def parallelGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W threshold : ℝ) : Set UnitCircle :=
  {ω | (parallelTestCount Q ρ g p P W (ω:Plane):ℝ) ≤ threshold}

noncomputable def projectionGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) (W threshold : ℝ) : Set UnitCircle :=
  {ω | (projectionTestCount Q ρ p u P W (ω:Plane):ℝ) ≤ threshold}

theorem continuous_quarterTurn : Continuous quarterTurn := by
  unfold quarterTurn
  fun_prop

theorem norm_quarterTurn (v : Plane) : ‖quarterTurn v‖ = ‖v‖ := by
  simpa using norm_quarterTurn_add 0 v

theorem quarterTurn_sub (v w : Plane) : quarterTurn (v-w) = quarterTurn v-quarterTurn w := by
  ext i
  fin_cases i <;> simp [quarterTurn]
  ring

theorem measurable_parallelGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W threshold : ℝ) : MeasurableSet (parallelGoodSet Q ρ g p P W threshold) := by
  apply measurableSet_le _ measurable_const
  apply (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
  exact (measurable_stripCount _ _ W).comp
    (continuous_quarterTurn.measurable.comp continuous_subtype_val.measurable)

theorem measurable_projectionGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) (W threshold : ℝ) : MeasurableSet (projectionGoodSet Q ρ p u P W threshold) := by
  apply measurableSet_le _ measurable_const
  apply (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
  exact (measurable_stripCount _ _ W).comp continuous_subtype_val.measurable

theorem parallelTestCount_neg (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) :
    parallelTestCount Q ρ g p P W (-ω) = parallelTestCount Q ρ g p P W ω := by
  have he : quarterTurn (-ω) = -quarterTurn ω := by ext i; fin_cases i <;> simp [quarterTurn]
  unfold parallelTestCount
  rw [he,stripCount_neg]

theorem projectionTestCount_neg (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) :
    projectionTestCount Q ρ p u P W (-ω) = projectionTestCount Q ρ p u P W ω :=
  stripCount_neg _ _ _ _

theorem parallelTestCount_transfer (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) {W W' d : ℝ} {ω ω' : Plane}
    (hd : dist ω ω' ≤ d) (hgap : W'+(10/(2:ℝ)^g)*d ≤ W) :
    parallelTestCount Q ρ g p P W' ω' ≤ parallelTestCount Q ρ g p P W ω := by
  classical
  apply stripCount_transfer _ _ (by positivity : 0 ≤ 10/(2:ℝ)^g) _ _ hgap
  · intro c hc
    have hh : ‖(Q.descendant c).center-(Q.descendant P).center‖ < 10/(2:ℝ)^g := by
      simpa only [mem_ball,dist_eq_norm] using (Finset.mem_filter.mp hc).2.2
    exact hh.le
  · simpa only [dist_eq_norm,← quarterTurn_sub,norm_quarterTurn] using hd

theorem projectionTestCount_transfer (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (p u : ℕ) {P : CellPath} (hP : P.length = p) {W W' d : ℝ} {ω ω' : Plane}
    (hd : dist ω ω' ≤ d) (hgap : W'+(2*Q.side/(2:ℝ)^p)*d ≤ W) :
    projectionTestCount Q ρ p u P W' ω' ≤ projectionTestCount Q ρ p u P W ω := by
  classical
  apply stripCount_transfer _ _ (by positivity : 0 ≤ 2*Q.side/(2:ℝ)^p) _ hd hgap
  intro cc hcc
  have hmem {c : CellPath} (hc : c ∈ projectionTestCells Q ρ p u P) :
      (Q.descendant c).center ∈ (Q.descendant P).carrier := by
    rw [← (Finset.mem_filter.mp hc).2.2]
    exact Q.descendant_subset_take hQ c p ((Q.descendant c).center_mem (Q.descendant_side_pos hQ c))
  have hh := (Q.descendant P).dist_le (Q.descendant_side_pos hQ P).le
    (hmem (Finset.mem_product.mp hcc).1) (hmem (Finset.mem_product.mp hcc).2)
  simpa only [dist_eq_norm,Q.descendant_side,hP,mul_div_assoc] using hh

end PlanarFalconer

end OAI
