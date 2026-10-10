import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserInverse
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.Cubature
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearCoordinates

namespace OAI

/-! The actual tensor Gauss nodes on a cubic lattice are separated before
transport, after transport, and after rational rounding. The enclosing finite
set of cells will determine the nucleus count in the final construction. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb

abbrev GaussLatticeIndex := (Fin 3 → ℤ) × (Fin 3 → Fin 2)

def gaussLatticePoint (h : ℝ) (i : GaussLatticeIndex) : Position :=
  WithLp.toLp 2 (fun a => h * ((i.1 a : ℝ) + gaussNode (i.2 a) / 2))

theorem gaussAbscissa_bounds : (1 / 2 : ℝ) < gaussAbscissa ∧ gaussAbscissa < 2 / 3 := by
  have hp := gaussAbscissa_pos
  have hs := gaussAbscissa_sq
  constructor <;> nlinarith

theorem gaussNode_bounds (b : Fin 2) :
    -gaussAbscissa ≤ gaussNode b ∧ gaussNode b ≤ gaussAbscissa := by
  fin_cases b <;> norm_num [gaussNode, gaussAbscissa_pos.le]

theorem gauss_lattice_coordinate_separation {h : ℝ} (hh : 0 < h)
    (k l : ℤ) (b c : Fin 2) (hne : k ≠ l ∨ b ≠ c) :
    h / 3 ≤ |h * ((k : ℝ) + gaussNode b / 2) -
      h * ((l : ℝ) + gaussNode c / 2)| := by
  have hb := gaussNode_bounds b
  have hc := gaussNode_bounds c
  have ha := gaussAbscissa_bounds
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · have hi : (k : ℝ) + 1 ≤ l := by exact_mod_cast (show k + 1 ≤ l by omega)
    have hprod := mul_nonneg hh.le (show 0 ≤ gaussNode c - gaussNode b + 2 * gaussAbscissa by linarith)
    have hscale := mul_pos hh (show 0 < (2 / 3 : ℝ) - gaussAbscissa by linarith)
    have hInt := mul_nonneg hh.le (show 0 ≤ (l : ℝ) - k - 1 by linarith)
    nlinarith [neg_le_abs (h * ((k : ℝ) + gaussNode b / 2) -
      h * ((l : ℝ) + gaussNode c / 2))]
  · subst l
    have hbc : b ≠ c := hne.resolve_left (not_not.mpr rfl)
    have hplus := le_abs_self (h * ((k : ℝ) + gaussNode b / 2) -
      h * ((k : ℝ) + gaussNode c / 2))
    have hminus := neg_le_abs (h * ((k : ℝ) + gaussNode b / 2) -
      h * ((k : ℝ) + gaussNode c / 2))
    have hscale := mul_pos hh (show 0 < gaussAbscissa - (1 / 3 : ℝ) by linarith)
    fin_cases b <;> fin_cases c <;> norm_num [gaussNode] at * <;> nlinarith
  · have hi : (l : ℝ) + 1 ≤ k := by exact_mod_cast (show l + 1 ≤ k by omega)
    have hprod := mul_nonneg hh.le (show 0 ≤ gaussNode b - gaussNode c + 2 * gaussAbscissa by linarith)
    have hscale := mul_pos hh (show 0 < (2 / 3 : ℝ) - gaussAbscissa by linarith)
    have hInt := mul_nonneg hh.le (show 0 ≤ (k : ℝ) - l - 1 by linarith)
    nlinarith [le_abs_self (h * ((k : ℝ) + gaussNode b / 2) -
      h * ((l : ℝ) + gaussNode c / 2))]

theorem gaussLatticePoint_separation {h : ℝ} (hh : 0 < h)
    (i j : GaussLatticeIndex) (hne : i ≠ j) :
    h / 3 ≤ ‖gaussLatticePoint h i - gaussLatticePoint h j‖ := by
  have hex : ∃ a, i.1 a ≠ j.1 a ∨ i.2 a ≠ j.2 a := by
    by_contra hn
    push Not at hn
    exact hne (Prod.ext (funext (fun a => (hn a).1)) (funext (fun a => (hn a).2)))
  obtain ⟨a, ha⟩ := hex
  have hcoord := gauss_lattice_coordinate_separation hh (i.1 a) (j.1 a) (i.2 a) (j.2 a) ha
  have hb := PiLp.norm_apply_le (gaussLatticePoint h i - gaussLatticePoint h j) a
  change |h * ((i.1 a : ℝ) + gaussNode (i.2 a) / 2) -
    h * ((j.1 a : ℝ) + gaussNode (j.2 a) / 2)| ≤ _ at hb
  exact hcoord.trans hb

/-- The inverse Lipschitz estimate gives a quantitative separation suitable
for rational nuclear placement, for any finite selection of cells. -/
theorem transportedGauss_rounding_injective {m denominator : ℕ}
    (hdenom : 0 < denominator) {h : ℝ} (hh : 0 < h)
    (index : Fin m → GaussLatticeIndex) (hindex : Function.Injective index)
    (G : Position → Position) {C : ℝ≥0} (hC : 0 < C)
    (hG : AntilipschitzWith C G)
    (hprecision : 6 / (denominator : ℝ) < h / (3 * (C : ℝ))) :
    Function.Injective (fun i => roundPosition denominator (G (gaussLatticePoint h (index i)))) := by
  apply roundPosition_injective hdenom
  intro i j hij
  have hbase := gaussLatticePoint_separation hh (index i) (index j) (fun h => hij (hindex h))
  have htrans := hG.le_mul_dist (gaussLatticePoint h (index i)) (gaussLatticePoint h (index j))
  simp only [dist_eq_norm] at htrans
  have hdiv : h / (3 * (C : ℝ)) ≤
      ‖G (gaussLatticePoint h (index i)) - G (gaussLatticePoint h (index j))‖ := by
    apply (div_le_iff₀ (show 0 < 3 * (C : ℝ) by positivity)).mpr
    nlinarith
  exact hprecision.trans_le hdiv

end ContinuumCoulomb

end

end OAI
