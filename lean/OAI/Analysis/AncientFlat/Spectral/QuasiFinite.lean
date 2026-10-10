import OAI.Analysis.AncientFlat.Spectral.EigenFlag

namespace OAI
noncomputable section
open Set Metric Module.End
namespace FlatSpectral
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma finite_eigenvalues_of_small_remainder (T R : X →L[ℂ] X)
    (hK : IsCompactOperator (T-R)) (r : ℝ) (hr : 4*‖R‖<r) :
    {z : ℂ | r≤‖z‖ ∧ Module.End.HasEigenvalue (T : Module.End ℂ X) z}.Finite := by
  classical
  by_contra hfin
  let A := {z : ℂ | r≤‖z‖ ∧ Module.End.HasEigenvalue (T : Module.End ℂ X) z}
  let e : ℕ ↪ A := Set.Infinite.natEmbedding A hfin
  let μ : ℕ → ℂ := fun n => e n
  have hμ : Function.Injective μ := Subtype.coe_injective.comp e.injective
  have hμr (n : ℕ) : r≤‖μ n‖ := (e n).property.1
  have hev (n : ℕ) : ∃ v : X, Module.End.HasEigenvector (T : Module.End ℂ X) (μ n) v :=
    (e n).property.2.exists_hasEigenvector
  choose v hv using hev
  have hvi : LinearIndependent ℂ v := Module.End.eigenvectors_linearIndependent' (T : Module.End ℂ X) μ hμ v hv
  have hve (n : ℕ) : T (v n)=μ n • v n := (hv n).apply_eq_smul
  obtain ⟨x,hxm,hxn,hxr⟩ := eigenFlag_riesz v hvi
  let K := T-R
  let ε := r/2-2*‖R‖
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsep (m n : ℕ) (hmn : m<n) : ε≤‖K (x n)-K (x m)‖ := by
    have hm : x m ∈ eigenFlag v n := eigenFlag_mono v (by omega : m+1≤n) (hxm m)
    have hTm := eigenFlag_invariant T μ v hve n (x m) hm
    have hTn := eigenFlag_triangular T μ v hve n (x n) (hxm n)
    have hμn : μ n≠0 := by
      intro he
      have := hμr n
      rw [he,norm_zero] at this
      have := norm_nonneg R
      linarith
    let y : X := (μ n)⁻¹ • (T (x m)-(T (x n)-μ n • x n))
    have hy : y∈eigenFlag v n := (eigenFlag v n).smul_mem _ ((eigenFlag v n).sub_mem hTm hTn)
    have he : μ n • (x n-y)=T (x n)-T (x m) := by
      dsimp [y]
      rw [smul_sub,smul_inv_smul₀ hμn]
      abel
    have hlarge : r/2≤‖T (x n)-T (x m)‖ := by
      rw [←he,norm_smul]
      exact (by nlinarith [hμr n,hxr n y hy,norm_nonneg (μ n)] : r/2≤‖μ n‖*‖x n-y‖)
    have hdiff : ‖R (x n)-R (x m)‖≤2*‖R‖ := by
      calc
        _≤‖R (x n)‖+‖R (x m)‖ := norm_sub_le _ _
        _≤‖R‖*‖x n‖+‖R‖*‖x m‖ := add_le_add (R.le_opNorm _) (R.le_opNorm _)
        _=_ := by rw [hxn n,hxn m]; ring
    have hid : T (x n)-T (x m)=(K (x n)-K (x m))+(R (x n)-R (x m)) := by
      simp only [K,sub_apply]
      abel
    have hnorm := norm_add_le (K (x n)-K (x m)) (R (x n)-R (x m))
    rw [←hid] at hnorm
    dsimp [ε]
    linarith
  obtain ⟨C,hC,hCK⟩ := hK.image_closedBall_subset_compact 1
  obtain ⟨y,hy,ψ,hψ,hconv⟩ := hC.tendsto_subseq (fun n => hCK ⟨x n,by simp [hxn n],rfl⟩)
  have hcauchy := hconv.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨N,hN⟩ := hcauchy ε hε
  have hh := hN (N+1) (by omega)
  have hlo := hsep (ψ N) (ψ (N+1)) (hψ (by omega))
  have hhi : ‖K (x (ψ (N+1)))-K (x (ψ N))‖<ε := by
    simpa only [dist_eq_norm,Function.comp_apply,ContinuousLinearMap.coe_coe,K] using hh
  exact (not_lt_of_ge hlo) hhi
end FlatSpectral

end

end OAI
