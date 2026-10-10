import OAI.Probability.InvariantIsing.Spectral.SpectralClipping

namespace OAI

/-! The finite spectral excess vanishes under the no-outlier condition. -/

noncomputable section
open Filter
open scoped Topology Classical

namespace InvariantIsing

def spectralExcess {N : ℕ} (eig : Fin N → ℝ) (a b : ℝ) : ℝ :=
  (insert 0 (Finset.univ.image (fun i => max (a-eig i) (eig i-b)))).max'
    (Finset.insert_nonempty 0 _)

lemma spectralExcess_nonneg {N : ℕ} (eig : Fin N → ℝ) (a b : ℝ) :
    0 ≤ spectralExcess eig a b := Finset.le_max' _ _ (Finset.mem_insert_self _ _)

lemma spectralExcess_bounds {N : ℕ} (eig : Fin N → ℝ) (a b : ℝ) (i : Fin N) :
    a-spectralExcess eig a b ≤ eig i ∧ eig i ≤ b+spectralExcess eig a b := by
  have hh : max (a-eig i) (eig i-b) ≤ spectralExcess eig a b := by
    unfold spectralExcess
    exact Finset.le_max' (insert (0 : ℝ) (Finset.univ.image (fun j => max (a-eig j) (eig j-b))))
      (max (a-eig i) (eig i-b)) (by
        rw [Finset.mem_insert]
        exact Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))
  have hl := (le_max_left (a-eig i) (eig i-b)).trans hh
  have hu := (le_max_right (a-eig i) (eig i-b)).trans hh
  constructor <;> linarith

lemma spectralExcess_le {N : ℕ} (eig : Fin N → ℝ) (a b ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ i, a-ε ≤ eig i ∧ eig i ≤ b+ε) : spectralExcess eig a b ≤ ε := by
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hε
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact max_le (by linarith [(h i).1]) (by linarith [(h i).2])

lemma spectralExcess_tendsto (eig : (N : ℕ) → Fin N → ℝ) (a b : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε) :
    Tendsto (fun N => spectralExcess (eig N) a b) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h (ε/2) (by positivity)] with N hN
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (spectralExcess_nonneg _ _ _)]
  exact (spectralExcess_le _ _ _ _ (by positivity) hN).trans_lt (by linarith)

end InvariantIsing

end

end OAI
