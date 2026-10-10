import Mathlib
import OAI.Analysis.Commutator.CyclicColumnFactorization
import OAI.Analysis.Commutator.CyclicMatrix

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H F ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

local instance cyclicCbDecidableEq : DecidableEq ι := Classical.decEq ι

omit [PartialOrder A] [StarOrderedRing A] in
lemma derivation_matrix_column (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (Δ : A →L[ℂ] (H →L[ℂ] F))
    (hΔ : ∀ a b, Δ (a*b)=(Δ a).comp (σ b)+(lam a).comp (Δ b))
    (X : CStarMatrix ι ι A) (v : ι → A) (ζ : H) :
    matrixAction (fun i j => Δ (X i j)) (WithLp.toLp 2 (fun i => σ (v i) ζ)) =
      WithLp.toLp 2 (fun i => Δ (∑ j, X i j*v j) ζ)-
        matrixAction (fun i j => lam (X i j)) (WithLp.toLp 2 (fun i => Δ (v i) ζ)) := by
  ext i
  simp only [matrixAction_apply,PiLp.sub_apply,map_sum,hΔ,
    sum_apply,add_apply,ContinuousLinearMap.comp_apply]
  simp only [Finset.sum_add_distrib,add_sub_cancel_right]

theorem cyclic_matrix_bound (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (Δ : A →L[ℂ] (H →L[ℂ] F))
    (hΔ : ∀ a b, Δ (a*b)=(Δ a).comp (σ b)+(lam a).comp (Δ b))
    (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω)) (c : ℝ) (hc : 0≤c)
    (hcol : ∀ (v : ι → A) (ζ : H),
      ‖WithLp.toLp 2 (fun i => Δ (v i) ζ)‖ ≤ c*columnNorm v*‖ζ‖)
    (X : CStarMatrix ι ι A) :
    ‖matrixAction (fun i j => Δ (X i j))‖ ≤ 4*c*‖X‖ := by
  let D := matrixAction (fun i j => Δ (X i j))
  have hbound (ζ : H) (v : ι → A) (hζ : ‖ζ‖≤2) (hv : (∑ i,star (v i)*v i)≤1) :
      ‖D (WithLp.toLp 2 (fun i => σ (v i) ζ))‖ ≤ 4*c*‖X‖ := by
    have hn : columnNorm v≤1 := columnNorm_le_one v hv
    have hm : columnNorm (fun i => ∑ j,X i j*v j)≤‖X‖ := by
      exact (columnNorm_matmul_le X v).trans (by simpa using mul_le_mul_of_nonneg_left hn (norm_nonneg X))
    have hdv : ‖WithLp.toLp 2 (fun i => Δ (v i) ζ)‖≤2*c := by
      calc _ ≤ c*columnNorm v*‖ζ‖ := hcol v ζ
        _ ≤ c*1*2 := by gcongr
        _ = 2*c := by ring
    have hdxv : ‖WithLp.toLp 2 (fun i => Δ (∑ j, X i j*v j) ζ)‖≤2*c*‖X‖ := by
      calc _ ≤ c*columnNorm (fun i => ∑ j, X i j*v j)*‖ζ‖ := hcol _ ζ
        _ ≤ c*‖X‖*2 := by gcongr
        _ = 2*c*‖X‖ := by ring
    have hlam : ‖matrixAction (fun i j => lam (X i j))
        (WithLp.toLp 2 (fun i => Δ (v i) ζ))‖≤2*c*‖X‖ := by
      calc _ ≤ ‖matrixRepresentation lam X‖*‖WithLp.toLp 2 (fun i => Δ (v i) ζ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖X‖*(2*c) := by gcongr; exact matrixRepresentation_norm_le lam X
        _ = 2*c*‖X‖ := by ring
    dsimp only [D]
    rw [derivation_matrix_column σ lam Δ hΔ]
    exact (norm_sub_le _ _).trans (by linarith)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro ξ hξ
  have hclosed : IsClosed {x : PiLp 2 (fun _ : ι => H) | ‖D x‖≤4*c*‖X‖} :=
    isClosed_le (D.continuous.norm) continuous_const
  apply hclosed.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨ζ,v,hζ,hv,ha⟩ := approximate_unit_column σ Ω hΩ ξ hξ ε hε
  exact ⟨WithLp.toLp 2 (fun i => σ (v i) ζ),hbound ζ v hζ hv,by rwa [dist_eq_norm]⟩

end Kadison.CyclicColumns

end

end
end

end OAI
