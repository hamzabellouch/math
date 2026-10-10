import OAI.NumberTheory.CubicMoment.Decomposition.StoppingFailedStage

namespace OAI

/-! The exact location of the first crossing relative to a bin boundary.
This connects the manuscript's high-bin stage to the actual stopping
labels, without imposing the boundary condition on the other variable. -/
noncomputable section
namespace CubicFirstMoment

lemma selected_crossing_before_prefix_iff (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    {R Z : ℝ} (hR : 0 ≤ R) {j k h : ℕ} {t : Finset Eisenstein}
    (ht : t ∈ (primeBin s bin j).powersetCard k) (hk : 1 ≤ k)
    (hprev : R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z)
    (hhit : Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) :
    j < h ↔ Z ≤ R*primeSurrogate (primeBinPrefix s bin h) bin ell := by
  have hc := selected_crossing_implies_bin_crossing s bin ell hell hR ht hk hprev hhit
  have hm := prime_prefix_monotone s bin ell hell hR
  constructor
  · intro hj
    exact hc.2.trans (hm (by omega : j+1 ≤ h))
  · intro hh
    by_contra hn
    have hle := hh.trans (hm (by omega : h ≤ j))
    exact (not_lt_of_ge hle) hc.1

lemma selected_crossing_after_prefix_iff (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    {R Z : ℝ} (hR : 0 ≤ R) {j k h : ℕ} {t : Finset Eisenstein}
    (ht : t ∈ (primeBin s bin j).powersetCard k) (hk : 1 ≤ k)
    (hprev : R*primeSurrogate (stoppingSelected s bin j t) bin ell/ell j < Z)
    (hhit : Z ≤ R*primeSurrogate (stoppingSelected s bin j t) bin ell) :
    h ≤ j ↔ R*primeSurrogate (primeBinPrefix s bin h) bin ell < Z := by
  have he := selected_crossing_before_prefix_iff s bin ell hell hR ht hk hprev hhit (h := h)
  constructor
  · intro hj
    apply lt_of_not_ge
    intro hz
    exact (not_lt_of_ge hj) (he.mpr hz)
  · intro hz
    by_contra hn
    exact (not_lt_of_ge (he.mp (by omega : j < h))) hz

end CubicFirstMoment

end

end OAI
