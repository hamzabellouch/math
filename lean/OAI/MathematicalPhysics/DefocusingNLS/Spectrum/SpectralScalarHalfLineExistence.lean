import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarUniqueness

namespace OAI

/-! Compatible finite-interval solutions give a comparison solution on the
entire right half-line. No uniform bound on the coefficient is needed. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralScalar_halfLine_exists (T : ℝ) (V : ℝ → ℂ)
    (hV : Continuous V) (x : ℂ × ℂ) :
    ∃ q : ℝ → ℂ × ℂ, Continuous q ∧ q T = x ∧
      ∀ t, T ≤ t → HasDerivAt q (spectralScalarField (V t) (q t)) t := by
  have hex (n : ℕ) := spectralScalar_local_exists T (T + (n : ℝ) + 1)
    (by linarith [(show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]) V hV.continuousOn x
  choose U hUc hUT hUD using hex
  have hcompat (n m : ℕ) (t : ℝ) (ht : T ≤ t)
      (htn : t ≤ T + (n : ℝ) + 1) (htm : t ≤ T + (m : ℝ) + 1) :
      U n t = U m t := by
    apply spectralScalar_unique_right T t ht V hV.continuousOn (U n) (U m)
      (hUc n).continuousOn (hUc m).continuousOn
    · intro s hs
      exact hUD n s ⟨hs.1.le,hs.2.le.trans htn⟩
    · intro s hs
      exact hUD m s ⟨hs.1.le,hs.2.le.trans htm⟩
    · rw [hUT,hUT]
  let idx : ℝ → ℕ := fun t => Classical.choose (exists_nat_gt (t - T))
  have hidx (t : ℝ) : t < T + (idx t : ℝ) + 1 := by
    have hi := Classical.choose_spec (exists_nat_gt (t - T))
    change t - T < (idx t : ℝ) at hi
    linarith
  let q := fun t => if t < T then U 0 t else U (idx t) t
  have heq (n : ℕ) (t : ℝ) (ht : T ≤ t) (htn : t ≤ T + (n : ℝ) + 1) :
      q t = U n t := by
    dsimp only [q]
    rw [ite_eq_right (not_lt_of_ge ht)]
    exact hcompat (idx t) n t ht (hidx t).le htn
  have hlocal (t : ℝ) : ∃ n : ℕ, q =ᶠ[𝓝 t] U n := by
    by_cases ht : t ≤ T
    · refine ⟨0,?_⟩
      filter_upwards [Iio_mem_nhds (show t < T + 1 by linarith)] with s hs
      by_cases hsT : s < T
      · simp only [q,ite_eq_left hsT]
      · exact heq 0 s (le_of_not_gt hsT) (by simpa using hs.le)
    · have hTt : T < t := lt_of_not_ge ht
      refine ⟨idx t,?_⟩
      filter_upwards [Ioo_mem_nhds hTt (hidx t)] with s hs
      exact heq (idx t) s hs.1.le hs.2.le
  have hqc : Continuous q := by
    apply continuous_iff_continuousAt.mpr
    intro t
    obtain ⟨n,hn⟩ := hlocal t
    exact ((hUc n).continuousAt).congr_of_eventuallyEq hn
  refine ⟨q,hqc,?_,?_⟩
  · rw [heq 0 T le_rfl (by simp),hUT]
  · intro t ht
    by_cases he : t = T
    · subst t
      have hnear : q =ᶠ[𝓝 T] U 0 := by
        filter_upwards [Iio_mem_nhds (show T < T + 1 by linarith)] with s hs
        by_cases hsT : s < T
        · simp only [q,ite_eq_left hsT]
        · exact heq 0 s (le_of_not_gt hsT) (by simpa using hs.le)
      rw [heq 0 T le_rfl (by simp)]
      exact (hUD 0 T ⟨le_rfl,by simp⟩).congr_of_eventuallyEq hnear
    · have hTt : T < t := lt_of_le_of_ne ht (Ne.symm he)
      have hnear : q =ᶠ[𝓝 t] U (idx t) := by
        filter_upwards [Ioo_mem_nhds hTt (hidx t)] with s hs
        exact heq (idx t) s hs.1.le hs.2.le
      rw [heq (idx t) t ht (hidx t).le]
      exact (hUD (idx t) t ⟨ht,(hidx t).le⟩).congr_of_eventuallyEq hnear

end DefocusingNLS

end OAI
