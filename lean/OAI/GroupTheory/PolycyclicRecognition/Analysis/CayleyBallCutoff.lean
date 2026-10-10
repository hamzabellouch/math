import OAI.GroupTheory.PolycyclicRecognition.Algebra.CayleyWordLength
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CayleyCaccioppoli

namespace OAI

/-! # Explicit word-ball cutoffs and the reverse Poincare inequality -/
noncomputable section
namespace PolycyclicRecognition

def unitClamp (a : ℝ) : ℝ := max 0 (min 1 a)

theorem unitClamp_eq_one {a : ℝ} (ha : 1 ≤ a) : unitClamp a = 1 := by
  simp only [unitClamp, min_eq_left ha, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem unitClamp_pos_of_ne_zero {a : ℝ} (ha : unitClamp a ≠ 0) : 0 < a := by
  by_contra! h
  exact ha (max_eq_left ((min_le_right 1 a).trans h))

theorem unitClamp_nonexpansive (a b : ℝ) : |unitClamp a - unitClamp b| ≤ |a - b| := by
  calc
    _ = |max (min 1 a) 0 - max (min 1 b) 0| := by simp only [unitClamp, max_comm]
    _ ≤ |min 1 a - min 1 b| := abs_max_sub_max_le_abs _ _ _
    _ ≤ |a - b| := by
      simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (a - b))] using
        abs_min_sub_min_le_max (1 : ℝ) a 1 b

variable {G : Type*} [Group G] [DecidableEq G]
variable (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
  (hgen : Subgroup.closure (S : Set G) = ⊤)

def cayleyBallCutoff (R : ℕ) (x : G) : ℝ :=
  unitClamp ((2 * (R : ℝ) - cayleyWordLength S hS hgen x) / R)

theorem cayleyBallCutoff_eq_one {R : ℕ} (hR : 0 < R) {x : G}
    (hx : x ∈ wordBall S R) : cayleyBallCutoff S hS hgen R x = 1 := by
  apply unitClamp_eq_one
  apply (le_div_iff₀ (show (0 : ℝ) < R by exact_mod_cast hR)).mpr
  have hn := (cayleyWordLength_le_iff S hS hgen x R).mpr hx
  have hn' : (cayleyWordLength S hS hgen x : ℝ) ≤ R := by exact_mod_cast hn
  linarith

theorem cayleyBallCutoff_support_neighbor {R : ℕ} (hR : 0 < R) {x : G}
    (hx : cayleyBallCutoff S hS hgen R x ≠ 0) {s : G} (hs : s ∈ S) :
    x * s ∈ wordBall S (2 * R) := by
  have hr : (0 : ℝ) < R := by exact_mod_cast hR
  have hpos := unitClamp_pos_of_ne_zero hx
  have hlen' : (cayleyWordLength S hS hgen x : ℝ) < 2 * (R : ℝ) := by
    have := (div_pos_iff_of_pos_right hr).mp hpos
    linarith
  have hlen : cayleyWordLength S hS hgen x < 2 * R := by exact_mod_cast hlen'
  apply (cayleyWordLength_le_iff S hS hgen _ _).mp
  exact (cayleyWordLength_mul_le S hS hgen x s).trans
    ((Nat.add_le_add_left (cayleyWordLength_generator_le S hS hgen hs) _).trans
      (by omega))

theorem cayleyBallCutoff_gradient {R : ℕ} (hR : 0 < R) (x : G) {s : G} (hs : s ∈ S) :
    |cayleyBallCutoff S hS hgen R (x * s) - cayleyBallCutoff S hS hgen R x| ≤
      1 / (R : ℝ) := by
  have hr : (0 : ℝ) < R := by exact_mod_cast hR
  have he : ((2 * (R : ℝ) - cayleyWordLength S hS hgen (x * s)) / R -
      (2 * (R : ℝ) - cayleyWordLength S hS hgen x) / R) =
      -((cayleyWordLength S hS hgen (x * s) : ℝ) - cayleyWordLength S hS hgen x) / R := by
    ring
  exact (unitClamp_nonexpansive _ _).trans (by
    rw [he, abs_div, abs_neg, abs_of_pos hr]
    exact div_le_div_of_nonneg_right (cayleyWordLength_edge_difference S hS hgen x hs) hr.le)

include hS hgen in
theorem cayley_wordBall_reverse_poincare (f : G → ℝ) (hf : CayleyHarmonic S f)
    {R : ℕ} (hR : 0 < R) :
    cayleyDirichletEnergy S (wordBall S R) f ≤
      4 * (S.card : ℝ) * (1 / (R : ℝ)) ^ 2 * ∑ x ∈ wordBall S (2 * R), f x ^ 2 := by
  apply cayley_cutoff_dirichlet_bound S hS (wordBall S R) (wordBall S (2 * R))
    (wordBall_mono S (by omega)) f (cayleyBallCutoff S hS hgen R) hf
  · intro x _ hx s hs
    exact cayleyBallCutoff_support_neighbor S hS hgen hR hx hs
  · exact fun _ hx => cayleyBallCutoff_eq_one S hS hgen hR hx
  · intro x hx s hs
    apply cayleyBallCutoff_support_neighbor S hS hgen hR _ hs
    rw [cayleyBallCutoff_eq_one S hS hgen hR hx]
    exact one_ne_zero
  · positivity
  · exact fun x _ s hs => cayleyBallCutoff_gradient S hS hgen hR x hs

end PolycyclicRecognition

end

end OAI
