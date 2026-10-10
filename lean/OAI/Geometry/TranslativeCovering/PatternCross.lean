import OAI.Geometry.TranslativeCovering.CrossDiagram

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3

namespace PatternCross
abbrev Space (n : ℕ) := SphericalLaw.Space n
open Set MeasureTheory SphericalLaw CapCost PatternGeometry PatternWitness ResidualCaps PoissonDiagrams
open scoped BigOperators

noncomputable def activity {n : ℕ} {J : Type u_1} [Fintype J] {e : Sphere n}
    {p : J → Space n} {x : Space n} {a K A C : ℝ} (W : Certificate e p x a K A C) : ℝ :=
  ∏ S,(intensity e (1/a)).real (W.slot S)

theorem fine {a l u₀ u K : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) (hK : 0 ≤ K) :
    ∃ H : ℝ,0 < H ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n],
    ∀ {J : Type u_2} [Fintype J] (e : Sphere n) (p : J → Space n) (x y : Space n) (D A C : ℝ),
    0 < RadialShell.low a n →
    x ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C →
    y ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C →
    (x,y) ∉ TargetGeometry.bad p (RadialShell.high a n) (H*Real.sqrt (Real.log n/(n:ℝ))) →
    ∀ (W : Certificate e p x a K A C) (V : Certificate e p y a K A C),
    diagram (intensity e (1/a)) W.slot V.slot ≤ (n:ℝ)⁻¹^3*activity W*activity V := by
  obtain ⟨H,hH,n₀,hn₀⟩ := CrossDeployment.fine ha hl hlt hu₀ hu hu1 hK
  refine ⟨H,hH,max n₀ 2,?_⟩
  intro n hn _ J _ e p x y D A C hlo hx hy hsep W V
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hratio : ∀ S T,(intensity e (1/a)).real (W.slot S ∩ V.slot T)/
      ((intensity e (1/a)).real (W.slot S)*(intensity e (1/a)).real (V.slot T)) ≤ (n:ℝ)⁻¹^8 := by
    intro S T
    let i := W.anchor S
    let j := V.anchor T
    have hx0 : x-p i ≠ 0 := norm_pos_iff.mp (hlo.trans_le (hx.2.1 i))
    have hy0 : y-p j ≠ 0 := norm_pos_iff.mp (hlo.trans_le (hy.2.1 j))
    apply hn₀ n ((le_max_left _ _).trans hn) e (unit (x-p i) hx0) (unit (y-p j) hy0)
      ‖x-p i‖ ‖y-p j‖ (hx.2.1 i) (Finset.mem_filter.mp i.property).2
      (hy.2.1 j) (Finset.mem_filter.mp j.property).2 (W.slot S) (V.slot T)
    · rw [cap_unit]; exact W.subset_cap S
    · rw [cap_unit]; exact V.subset_cap T
    · rw [cap_unit]; exact W.thinned S
    · rw [cap_unit]; exact V.thinned T
    · rw [angle_unit]
      exact (separated p hlo hx.2.1 hy.2.1 hsep i j).le
  have hcross := CrossDiagram.small (by omega : 0 < n) (intensity e (1/a)) W.slot V.slot
    (by simpa using W.card_le) (by simpa using V.card_le) hratio
  apply hcross.trans
  have hprod : 0 ≤ activity W*activity V :=
    mul_nonneg (Finset.prod_nonneg fun S _ => (W.positive S).le)
      (Finset.prod_nonneg fun S _ => (V.positive S).le)
  have hh := mul_le_mul_of_nonneg_left (CrossDiagram.inverse_scale hn2) hprod
  simpa only [activity,mul_assoc,mul_comm,mul_left_comm] using hh

lemma coarse {n : ℕ} {J : Type u_3} [Fintype J] (e : Sphere n) (p : J → Space n)
    (x y : Space n) {a K A C D ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hlo : 0 < RadialShell.low a n)
    (hthreshold : 1/Real.sqrt (1+4*ε) ≤ (1+3*RadialShell.η n)/RadialShell.high a n)
    (hx : x ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C)
    (hy : y ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C)
    (hsep : (x,y) ∉ TargetGeometry.bad p (RadialShell.high a n) (4*Real.sqrt ε))
    (W : Certificate e p x a K A C) (V : Certificate e p y a K A C) :
    diagram (intensity e (1/a)) W.slot V.slot = 0 := by
  apply DiagramActivity.cross_zero
  intro S T
  let i := W.anchor S
  let j := V.anchor T
  have hi : 0 < ‖x-p i‖ := hlo.trans_le (hx.2.1 i)
  have hj : 0 < ‖y-p j‖ := hlo.trans_le (hy.2.1 j)
  have hnum : 0 ≤ 1+3*RadialShell.η n := by unfold RadialShell.η; positivity
  apply CrossDeployment.coarse hε hε1 e (unit (x-p i) (norm_pos_iff.mp hi))
    (unit (y-p j) (norm_pos_iff.mp hj))
  · rw [cap_unit]; exact W.subset_cap S
  · rw [cap_unit]; exact V.subset_cap T
  · exact hthreshold.trans (div_le_div_of_nonneg_left hnum hi (Finset.mem_filter.mp i.property).2)
  · exact hthreshold.trans (div_le_div_of_nonneg_left hnum hj (Finset.mem_filter.mp j.property).2)
  · rw [angle_unit]
    exact separated p hlo hx.2.1 hy.2.1 hsep i j
end PatternCross

end OAI
