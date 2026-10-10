import OAI.Probability.InvariantIsing.Spectral.SpectralExcess

namespace OAI

/-! Convergence of the actual extreme eigenvalues implies the uniform
no-outlier formulation used by the pressure theorem. -/

noncomputable section
open Filter
open scoped Topology Classical

namespace InvariantIsing

def spectralMinimum {n : ℕ} (eig : Fin (n+1) → ℝ) : ℝ :=
  (Finset.univ.image eig).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)

def spectralMaximum {n : ℕ} (eig : Fin (n+1) → ℝ) : ℝ :=
  (Finset.univ.image eig).max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

lemma spectralMinimum_le {n : ℕ} (eig : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    spectralMinimum eig ≤ eig i :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)

lemma le_spectralMaximum {n : ℕ} (eig : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    eig i ≤ spectralMaximum eig :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)

lemma spectral_no_outliers_of_extreme_limits
    (eig : (N : ℕ) → Fin N → ℝ) (a b : ℝ)
    (hmin : Tendsto (fun k => spectralMinimum (eig (k+1))) atTop (𝓝 a))
    (hmax : Tendsto (fun k => spectralMaximum (eig (k+1))) atTop (𝓝 b)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε := by
  intro ε hε
  have hh : ∀ᶠ k in atTop, ∀ i, a-ε ≤ eig (k+1) i ∧ eig (k+1) i ≤ b+ε := by
    filter_upwards [hmin.eventually (Ioi_mem_nhds (by linarith : a-ε < a)),
      hmax.eventually (Iio_mem_nhds (by linarith : b < b+ε))] with k hl hu i
    exact ⟨hl.le.trans (spectralMinimum_le _ i),(le_spectralMaximum _ i).trans hu.le⟩
  obtain ⟨M,hM⟩ := eventually_atTop.mp hh
  apply eventually_atTop.mpr
  refine ⟨M+1,fun N hN => ?_⟩
  have hn : N-1+1=N := by omega
  have hs := hM (N-1) (by omega)
  rw [hn] at hs
  exact hs

end InvariantIsing

end

end OAI
