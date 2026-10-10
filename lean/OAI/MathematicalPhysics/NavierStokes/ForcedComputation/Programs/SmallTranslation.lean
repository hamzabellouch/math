import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RationalLoader
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.Subprogram

namespace OAI

/-! A translation can be inserted at any sufficiently small rational scale
inside the existing processor chart. -/

namespace ForcedComputation
open ShearFlows

def translationInstruction (p q : Fin 2 → ℚ) (r : ℚ) : Instruction :=
  ⟨centeredBox p r, centeredBox q r, 1⟩

theorem translationInstruction_image (p q : Fin 2 → ℚ) (r : ℚ) :
    (translationInstruction p q r).affine '' (translationInstruction p q r).source.carrier =
      (translationInstruction p q r).target.carrier := by
  apply Instruction.image_eq_of_halfWidths _ (by norm_num [translationInstruction])
  · simp only [translationInstruction, centeredBox_halfWidth, Rat.cast_one, one_mul]
  · simp only [translationInstruction, centeredBox_halfWidth, Rat.cast_one, div_one]

theorem translationInstruction_singleton_valid {d : Input} (hd : ValidInput d)
    (p q : Fin 2 → ℚ) {r : ℚ} (hr : 0 < r) (hrh : r ≤ d.h)
    (hp : (fun j => (p j : ℝ)) ∈ d.centers.carrier)
    (hq : (fun j => (q j : ℝ)) ∈ d.centers.carrier) :
    ValidInput (d.withInstructions [translationInstruction p q r]) := by
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hrhr : (r : ℝ) ≤ d.h := by exact_mod_cast hrh
  have hpbox (a : Fin 2 → ℚ) : (centeredBox a r).positive := by
    intro j
    change a j - r < a j + r
    linarith
  have hin (a : Fin 2 → ℚ) (ha : (fun j => (a j : ℝ)) ∈ d.centers.carrier) :
      (centeredBox a r).carrier ⊆ d.inPlanarChart := by
    intro x hx j
    have hj := hx j
    change ((a j - r : ℚ) : ℝ) ≤ x j ∧ x j ≤ ((a j + r : ℚ) : ℝ) at hj
    simp only [Rat.cast_sub, Rat.cast_add] at hj
    have hm := hd.chartMargin j
    change (d.chart.lower j.castSucc : ℝ) < x j ∧ x j < (d.chart.upper j.castSucc : ℝ)
    constructor <;> linarith [(ha j).1, (ha j).2, hm.1, hm.2]
  have hc (a : Fin 2 → ℚ) : (centeredBox a r).center = fun j => (a j : ℝ) := by
    funext j
    exact centeredBox_center a r j
  refine {
    period_pos := hd.period_pos
    chart_positive := hd.chart_positive
    chart_length := hd.chart_length
    h_pos := hd.h_pos
    centers_nonempty := hd.centers_nonempty
    chartMargin := hd.chartMargin
    height_inside := hd.height_inside
    source_positive := ?_
    target_positive := ?_
    source_in_chart := ?_
    target_in_chart := ?_
    factor_pos := ?_
    image_eq := ?_
    source_separation := ?_
    target_separation := ?_
    halfWidths := ?_
    source_centers := ?_
    target_centers := ?_ }
  · intro b hb
    have he : b = translationInstruction p q r := List.mem_singleton.mp hb
    subst b
    exact hpbox p
  · intro b hb
    have he : b = translationInstruction p q r := List.mem_singleton.mp hb
    subst b
    exact hpbox q
  · intro b hb
    have he : b = translationInstruction p q r := List.mem_singleton.mp hb
    subst b
    exact hin p hp
  · intro b hb
    have he : b = translationInstruction p q r := List.mem_singleton.mp hb
    subst b
    exact hin q hq
  · intro b hb
    have he : b = translationInstruction p q r := List.mem_singleton.mp hb
    subst b
    norm_num [translationInstruction]
  · intro b hb
    have he : b = translationInstruction p q r := List.mem_singleton.mp hb
    subst b
    exact translationInstruction_image p q r
  · intro i j hij
    change Fin 1 at i j
    exact False.elim (hij (Subsingleton.elim i j))
  · intro i j hij
    change Fin 1 at i j
    exact False.elim (hij (Subsingleton.elim i j))
  · intro b hb j
    have he : b = translationInstruction p q r := List.mem_singleton.mp hb
    subst b
    simpa only [translationInstruction, centeredBox_halfWidth, Input.withInstructions]
      using And.intro hrhr hrhr
  · intro b hb
    have he : b = translationInstruction p q r := List.mem_singleton.mp hb
    subst b
    exact (hc p).symm ▸ hp
  · intro b hb
    have he : b = translationInstruction p q r := List.mem_singleton.mp hb
    subst b
    exact (hc q).symm ▸ hq

end ForcedComputation

end OAI
