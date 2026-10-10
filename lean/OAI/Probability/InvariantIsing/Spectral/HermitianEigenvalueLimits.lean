import OAI.Probability.InvariantIsing.Spectral.HermitianEigenvalueRoots

namespace OAI

/-! Limits of ordered Hermitian roots, with multiplicities retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Polynomial Filter Set
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace InvariantIsing

lemma hermitian_eigenvalues₀_limit_unique {N : ℕ}
    (A : ℕ → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ n, (A n).IsHermitian)
    (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.IsHermitian)
    (hAB : Tendsto A atTop (𝓝 B)) (e : Fin (Fintype.card (Fin N)) → ℝ)
    (he : Tendsto (fun n => (hA n).eigenvalues₀) atTop (𝓝 e)) : e = hB.eigenvalues₀ := by
  have heord : Antitone e := by
    intro i j hij
    exact le_of_tendsto_of_tendsto ((continuous_apply j).tendsto e |>.comp he)
      ((continuous_apply i).tendsto e |>.comp he)
      (Eventually.of_forall fun n => (hA n).eigenvalues₀_antitone hij)
  apply (hermitian_eigenvalues₀_unique B hB e heord ?_).symm
  intro t
  have hp : Tendsto (fun n => ∏ i, (t-(hA n).eigenvalues₀ i)) atTop (𝓝 (∏ i, (t-e i))) := by
    apply tendsto_finsetProd
    intro i _
    exact tendsto_const_nhds.sub ((continuous_apply i).tendsto e |>.comp he)
  have hq := hermitian_eval_tendsto hAB t
  have hfn : (fun n => (A n).charpoly.eval t) =
      (fun n => ∏ i, (t-(hA n).eigenvalues₀ i)) :=
    funext fun n => hermitian_eigenvalues₀_eval (A n) (hA n) t
  rw [hfn] at hq
  exact tendsto_nhds_unique hq hp

theorem hermitian_eigenvalues₀_tendsto {N : ℕ}
    (A : ℕ → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ n, (A n).IsHermitian)
    (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.IsHermitian)
    (hAB : Tendsto A atTop (𝓝 B)) :
    Tendsto (fun n => (hA n).eigenvalues₀) atTop (𝓝 hB.eigenvalues₀) := by
  obtain ⟨R,hR,hAR⟩ := (Metric.isBounded_range_of_tendsto A hAB).exists_pos_norm_le
  have hb (n : ℕ) : ‖(hA n).eigenvalues₀‖ ≤ R := by
    apply (pi_norm_le_iff_of_nonneg hR.le).mpr
    intro i
    exact (hermitian_eigenvalues₀_norm_le (A n) (hA n) i).trans (hAR (A n) (mem_range_self n))
  by_contra ht
  simp only [Metric.tendsto_nhds] at ht
  push Not at ht
  obtain ⟨ε,hε,hfreq⟩ := ht
  let K : Set (Fin (Fintype.card (Fin N)) → ℝ) :=
    Metric.closedBall 0 R ∩ {e | ε ≤ dist e hB.eigenvalues₀}
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hmem : ∃ᶠ n in atTop, (hA n).eigenvalues₀ ∈ K := by
    apply hfreq.mono
    intro n hn
    exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hb n,hn⟩
  obtain ⟨e,heK,φ,hφ,hφe⟩ := hK.tendsto_subseq' hmem
  have heq : e = hB.eigenvalues₀ := hermitian_eigenvalues₀_limit_unique
    (fun n => A (φ n)) (fun n => hA (φ n)) B hB (hAB.comp hφ.tendsto_atTop) e hφe
  have hz : ε ≤ dist e hB.eigenvalues₀ := heK.2
  rw [heq,dist_self] at hz
  exact (not_le_of_gt hε) hz

end InvariantIsing

end

end OAI
