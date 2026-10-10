import OAI.Probability.InvariantIsing.Spectral.SpectralDiagonalPerturbation

namespace OAI

/-! The actual diagonal perturbation preserves spectral blocks and vanishes
in their limiting eigenvalues even when its minimizing coordinates vary. -/

noncomputable section
open MeasureTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma diagonalPerturbedEigenvalues_block {N m : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (v : Fin m → ℝ) (t : ℝ) (lam : Fin m → ℝ)
    (hlam : ∀ a i, i ∈ I a → eig i = lam a) (a : Fin m) (i : Fin N) (hi : i ∈ I a) :
    diagonalPerturbedEigenvalues eig I v t i = t * lam a + 2 * perturbationScale N * v a := by
  classical
  have hs : (∑ b, if i ∈ I b then v b else 0) = v a := by
    rw [Finset.sum_eq_single a]
    · simp only [ite_eq_left hi]
    · intro b _ hba
      have hn : i ∉ I b := fun hib =>
        Finset.disjoint_left.mp (hdis (Set.mem_univ b) (Set.mem_univ a) hba) hib hi
      simp only [ite_eq_right hn]
    · exact fun ha => False.elim (ha (Finset.mem_univ a))
  simp only [diagonalPerturbedEigenvalues, hs, hlam a i hi]

lemma perturbedBlockEigenvalues_tendsto {m : ℕ} (N : ℕ → ℕ)
    (hNlim : Tendsto N atTop atTop) (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a| ≤ 2)
    (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀)) (lam : Fin m → ℝ) :
    Tendsto (fun k a => t k * lam a + 2 * perturbationScale (N k) * v k a) atTop
      (𝓝 (fun a => t₀ * lam a)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  have hz : Tendsto (fun k => 2 * perturbationScale (N k) * v k a) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => ?_)
      (show Tendsto (fun k => 4 * perturbationScale (N k)) atTop (𝓝 0) by
        simpa only [mul_zero, Function.comp_apply] using (perturbationScale_tendsto.comp hNlim).const_mul 4)
    have hp : 0 ≤ perturbationScale (N k) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hp)]
    exact (mul_le_mul_of_nonneg_left (hv k a) (by positivity)).trans_eq (by ring)
  simpa only [add_zero] using (ht.mul_const (lam a)).add hz

end InvariantIsing

end

end OAI
