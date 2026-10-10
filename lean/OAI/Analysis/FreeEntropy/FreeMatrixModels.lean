import OAI.Analysis.FreeEntropy.MicrostatesLogLower

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FiniteEntropySeparation
 theorem gueMatrix_isHermitian {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) : (gueMatrix x i).IsHermitian := by
  change (((Real.sqrt d:ℂ)⁻¹) • hermitianMatrix (WithLp.toLp 2 x) i).IsHermitian
  simp only [Matrix.IsHermitian,Matrix.conjTranspose_smul,map_inv₀,Complex.star_def,Complex.conj_ofReal]
  rw [show (hermitianMatrix (WithLp.toLp 2 x) i).conjTranspose=hermitianMatrix (WithLp.toLp 2 x) i from hermitianMatrix_isHermitian _ _]
 theorem exists_free_matrix_models (n : ℕ) :
    ∃ (D : ℕ → ℕ) (A : (k : ℕ) → Fin n → Matrix (Fin (D k)) (Fin (D k)) ℂ),
      (∀ k,0<D k) ∧ Tendsto D atTop atTop ∧
      (∀ k i,matrixOpNorm (A k i)≤64) ∧ (∀ k i,(A k i).IsHermitian) ∧
      ∀ w : List (Fin n), Tendsto (fun k => matrixTraceWord (A k) w) atTop (𝓝 (FreeSeries.fockMoments n w)) := by
  have hex (k : ℕ) := exists_gue_model n k k (ε := 1/((k:ℝ)+1)) (by positivity)
  choose D hD x hx hm using hex
  refine ⟨D,fun k => gueMatrix (x k),fun k => lt_of_le_of_lt (Nat.zero_le _) (hD k),?_,hx,fun k i => gueMatrix_isHermitian _ _,?_⟩
  · exact tendsto_atTop_mono (fun k => (hD k).le) tendsto_id
  · intro w
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ (tendsto_one_div_add_atTop_nhds_zero_nat)
    filter_upwards [eventually_ge_atTop w.length] with k hk
    exact (hm k w hk).le
end FiniteEntropySeparation

end

end OAI
