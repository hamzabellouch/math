import OAI.Probability.InvariantIsing.Spectral.SpectralExtremeLimits

namespace OAI

/-! The extreme eigenvalues control a random spectrum without moment hypotheses. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

def spectralRadius {n : ℕ} (eig : Fin (n+1) → ℝ) : ℝ :=
  max |spectralMinimum eig| |spectralMaximum eig|

lemma abs_le_spectralRadius {n : ℕ} (eig : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    |eig i| ≤ spectralRadius eig := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left _ _)).trans
      ((neg_abs_le (spectralMinimum eig)).trans (spectralMinimum_le eig i))
  · exact (le_spectralMaximum eig i).trans
      ((le_abs_self _).trans (le_max_right _ _))

lemma spectralRadius_le_iff {n : ℕ} (eig : Fin (n+1) → ℝ) (K : ℝ) :
    spectralRadius eig ≤ K ↔ ∀ i, |eig i| ≤ K := by
  constructor
  · intro h i
    exact (abs_le_spectralRadius eig i).trans h
  · intro h
    apply max_le
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.min'_mem
        (Finset.univ.image eig) (Finset.image_nonempty.mpr Finset.univ_nonempty))
      simpa only [spectralMinimum,← hi] using h i
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.max'_mem
        (Finset.univ.image eig) (Finset.image_nonempty.mpr Finset.univ_nonempty))
      simpa only [spectralMaximum,← hi] using h i

lemma spectralRadius_eventually_bounded (eig : (N : ℕ) → Fin N → ℝ) (a b : ℝ)
    (hmin : Tendsto (fun k => spectralMinimum (eig (k+1))) atTop (𝓝 a))
    (hmax : Tendsto (fun k => spectralMaximum (eig (k+1))) atTop (𝓝 b)) :
    ∃ K : ℝ, ∀ᶠ k in atTop, spectralRadius (eig (k+1)) ≤ K := by
  refine ⟨max |a| |b|+1,?_⟩
  have ht := hmin.abs.max hmax.abs
  exact (ht.eventually (Iio_mem_nhds (lt_add_one _))).mono fun _ h => h.le

lemma spectralRadius_eventually_bounded_of_no_outliers
    (eig : (N : ℕ) → Fin N → ℝ) (a b : ℝ)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε) :
    ∃ K : ℝ, ∀ᶠ k in atTop, spectralRadius (eig (k+1)) ≤ K := by
  refine ⟨max |a| |b|+1,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (hno 1 zero_lt_one)] with k hk
  apply (spectralRadius_le_iff _ _).mpr
  intro i
  apply abs_le.mpr
  have ha := neg_abs_le a
  have hb := le_abs_self b
  have hma := le_max_left |a| |b|
  have hmb := le_max_right |a| |b|
  constructor <;> linarith [(hk i).1,(hk i).2]

end InvariantIsing

end

end OAI
