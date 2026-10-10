import Mathlib
import OAI.Combinatorics.UniformKServer.Basic

namespace OAI

namespace UniformKServer
/-- Final labeled positions after the specified legal one-label service. -/
def finish {n k : ℕ} : Configuration n k → History n k → Configuration n k
  | s, [] => s
  | s, (r,j) :: h => finish (serve s r j) h

/-- Same-label mismatch, not a minimum matching; repetitions are allowed. -/
def mismatch {n k : ℕ} (d : RationalMetric n) (u s : Configuration n k) : ℝ :=
  ∑ j, (d.distance (u j) (s j) : ℝ)

private theorem distance_nonneg {n : ℕ} (d : RationalMetric n) (x y : Fin n) :
    (0 : ℝ) ≤ d.distance x y := by exact_mod_cast d.nonneg x y

private theorem distance_triangle {n : ℕ} (d : RationalMetric n) (x y z : Fin n) :
    (d.distance x z : ℝ) ≤ d.distance x y + d.distance y z := by
  exact_mod_cast d.triangle x y z

private theorem distance_self {n : ℕ} (d : RationalMetric n) (x : Fin n) :
    (d.distance x x : ℝ) = 0 := by
  exact_mod_cast (d.eq_zero x x).2 rfl

private theorem mismatch_nonneg {n k : ℕ} (d : RationalMetric n)
    (u s : Configuration n k) : 0 ≤ mismatch d u s :=
  Finset.sum_nonneg (fun _ _ => distance_nonneg d _ _)

private theorem mismatch_le_diameter {n k : ℕ} (d : RationalMetric n)
    (u s : Configuration n k) (D : ℝ)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D) : mismatch d u s ≤ k * D := by
  calc
    mismatch d u s ≤ ∑ _j : Fin k, D := Finset.sum_le_sum (fun j _ => hdiam (u j) (s j))
    _ = k * D := by simp

private theorem mismatch_skip {n k : ℕ} (d : RationalMetric n)
    (u s : Configuration n k) (r : Fin n) (j : Fin k) :
    mismatch d u (serve s r j) ≤ mismatch d u s + (d.distance (s j) r : ℝ) := by
  classical
  unfold mismatch
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have he : (∑ i ∈ Finset.univ.erase j, (d.distance (u i) (serve s r j i) : ℝ)) =
      ∑ i ∈ Finset.univ.erase j, (d.distance (u i) (s i) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [serve, Finset.ne_of_mem_erase hi]
  rw [he]
  simp only [serve, Function.update_self]
  have hs := Finset.sum_erase_add Finset.univ (fun i => (d.distance (u i) (s i) : ℝ))
    (Finset.mem_univ j)
  have ht := distance_triangle d (u j) (s j) r
  linarith

private theorem mismatch_keep {n k : ℕ} (d : RationalMetric n)
    (u s : Configuration n k) (r : Fin n) (j : Fin k) :
    (d.distance (u j) r : ℝ) + mismatch d (serve u r j) (serve s r j) ≤
      (d.distance (s j) r : ℝ) + mismatch d u s := by
  classical
  unfold mismatch
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have he : (∑ i ∈ Finset.univ.erase j,
      (d.distance (serve u r j i) (serve s r j i) : ℝ)) =
      ∑ i ∈ Finset.univ.erase j, (d.distance (u i) (s i) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [serve, Finset.ne_of_mem_erase hi]
  rw [he]
  simp only [serve, Function.update_self, distance_self, add_zero]
  have hs := Finset.sum_erase_add Finset.univ (fun i => (d.distance (u i) (s i) : ℝ))
    (Finset.mem_univ j)
  have ht := distance_triangle d (u j) (s j) r
  linarith

/-- Skipped virtual visits are paid by triangle inequality; retained visits
synchronize the relevant actual and virtual labels. -/
theorem sublist_potential {n k : ℕ} (d : RationalMetric n)
    {g h : History n k} (hsub : g.Sublist h) (u s : Configuration n k) :
    costAlong d u g + mismatch d (finish u g) (finish s h) ≤
      costAlong d s h + mismatch d u s := by
  induction hsub generalizing u s with
  | slnil => simp [costAlong, finish]
  | cons a hsub ih =>
    rcases a with ⟨r,j⟩
    have hi := ih u (serve s r j)
    have ht := mismatch_skip d u s r j
    simp only [costAlong, finish]
    linarith
  | cons_cons a hsub ih =>
    rcases a with ⟨r,j⟩
    have hi := ih (serve u r j) (serve s r j)
    have ht := mismatch_keep d u s r j
    simp only [costAlong, finish]
    linarith

theorem costAlong_nonneg {n k : ℕ} (d : RationalMetric n)
    (s : Configuration n k) (h : History n k) : 0 ≤ costAlong d s h := by
  induction h generalizing s with
  | nil => rfl
  | cons a h ih =>
    rcases a with ⟨r,j⟩
    exact add_nonneg (distance_nonneg d _ _) (ih _)

/-- The infimum definition of OPT is bounded below even before selecting a
minimizer. Every explicit legal label history gives an upper bound. -/
theorem offlineCost_le_history {n k : ℕ} (d : RationalMetric n)
    (s : Configuration n k) (h : History n k) :
    offlineCost d s (h.map Prod.fst) ≤ costAlong d s h := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨g, _, rfl⟩
    exact costAlong_nonneg d s g
  · exact ⟨h, rfl, rfl⟩

end UniformKServer

/-- Exact pathwise transfer needed at every restart and for deleting requests.
Source: Section 03, equations actual-virtual and subsequence-comparison. -/
theorem subsequence_cost_transfer {n k : ℕ} (d : UniformKServer.RationalMetric n)
    (u s : UniformKServer.Configuration n k) (g h : UniformKServer.History n k)
    (hsub : g.Sublist h) (D : ℝ)
    (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D) :
    UniformKServer.costAlong d u g +
      UniformKServer.mismatch d (UniformKServer.finish u g) (UniformKServer.finish s h) ≤
      UniformKServer.costAlong d s h + UniformKServer.mismatch d u s ∧
    UniformKServer.costAlong d u g ≤ UniformKServer.costAlong d s h + k * D ∧
    UniformKServer.offlineCost d u (g.map Prod.fst) ≤
      UniformKServer.costAlong d s h + k * D := by
  have hp := UniformKServer.sublist_potential d hsub u s
  have hn := UniformKServer.mismatch_nonneg d (UniformKServer.finish u g)
    (UniformKServer.finish s h)
  have hu := UniformKServer.mismatch_le_diameter d u s D hdiam
  have hb : UniformKServer.costAlong d u g ≤ UniformKServer.costAlong d s h + k * D :=
    by linarith
  exact ⟨hp, hb, (UniformKServer.offlineCost_le_history d u g).trans hb⟩



end OAI
