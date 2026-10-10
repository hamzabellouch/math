import OAI.Analysis.Pureness.Tensor.SpatialSymbolPolynomial
import OAI.Analysis.Pureness.Operators.DenseOperatorConvergence

namespace OAI
noncomputable section
namespace CuntzPureness
local instance spatialSymbolMultiplierDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
open scoped TensorProduct InnerProductSpace
open Filter Topology
variable {A H G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

def spatialSymbolMultiplier (c : G → ℂ) :
    representedSpatialTensor α (reducedGroupAlgebra G).subtype →L[ℂ]
      representedSpatialTensor α (reducedGroupAlgebra G).subtype :=
  ((spatialGroupPolynomialMap (G := G) α).comp (groupPolynomialWeight c)).extendOfNorm
    (spatialGroupPolynomialMap (G := G) α)

lemma spatialSymbolMultiplier_polynomial (c : G → ℂ) (C : ℝ)
    (hb : ∀ a : G →₀ A, ‖spatialGroupPolynomialMap (G := G) α (groupPolynomialWeight c a)‖ ≤
      C * ‖spatialGroupPolynomialMap (G := G) α a‖) (a : G →₀ A) :
    spatialSymbolMultiplier α c (spatialGroupPolynomialMap (G := G) α a) =
      spatialGroupPolynomialMap (G := G) α (groupPolynomialWeight c a) :=
  LinearMap.extendOfNorm_eq (spatialGroupPolynomialMap_denseRange (G := G) α) ⟨C, hb⟩ a

lemma spatialSymbolMultiplier_norm_le (c : G → ℂ) (C : ℝ)
    (hb : ∀ a : G →₀ A, ‖spatialGroupPolynomialMap (G := G) α (groupPolynomialWeight c a)‖ ≤
      C * ‖spatialGroupPolynomialMap (G := G) α a‖)
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    ‖spatialSymbolMultiplier α c x‖ ≤ C * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le (spatialGroupPolynomialMap_denseRange (G := G) α) C hb x

lemma spatialSymbolMultiplier_generator (c : G → ℂ) (C : ℝ)
    (hb : ∀ a : G →₀ A, ‖spatialGroupPolynomialMap (G := G) α (groupPolynomialWeight c a)‖ ≤
      C * ‖spatialGroupPolynomialMap (G := G) α a‖) (a : A) (g : G) :
    spatialSymbolMultiplier α c (spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (a ⊗ₜ[ℂ] (reducedGroupUnitary G g : reducedGroupAlgebra G))) =
    c g • spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (a ⊗ₜ[ℂ] (reducedGroupUnitary G g : reducedGroupAlgebra G)) := by
  have he := spatialSymbolMultiplier_polynomial α c C hb (Finsupp.single g a)
  refine (congrArg (spatialSymbolMultiplier α c) (spatialGroupPolynomialMap_single α g a)).symm.trans
    (he.trans ?_)
  have hw : groupPolynomialWeight c (Finsupp.single g a) = c g • Finsupp.single g a :=
    (groupPolynomialWeight_single c g a).trans (Finsupp.smul_single _ _ _).symm
  exact (congrArg (spatialGroupPolynomialMap (G := G) α) hw).trans
    ((map_smul (spatialGroupPolynomialMap (G := G) α) (c g) (Finsupp.single g a)).trans
      (congrArg (fun x => c g • x) (spatialGroupPolynomialMap_single α g a)))

include hα in
lemma spatialSymbolMultiplier_fourier (c : G → ℂ) (C : ℝ)
    (hb : ∀ a : G →₀ A, ‖spatialGroupPolynomialMap (G := G) α (groupPolynomialWeight c a)‖ ≤
      C * ‖spatialGroupPolynomialMap (G := G) α a‖) (g : G)
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    spatialGroupFourier α g (spatialSymbolMultiplier α c x) = c g • spatialGroupFourier α g x := by
  refine (spatialGroupPolynomialMap_denseRange (G := G) α).induction_on x ?_ ?_
  · apply isClosed_eq
    · exact (spatialGroupFourier α g).continuous.comp (spatialSymbolMultiplier α c).continuous
    · exact continuous_const.smul (spatialGroupFourier α g).continuous
  · intro a
    exact (congrArg (spatialGroupFourier α g) (spatialSymbolMultiplier_polynomial α c C hb a)).trans
      ((spatialGroupPolynomialMap_fourier α hα (groupPolynomialWeight c a) g).trans
        ((groupPolynomialWeight_apply c a g).trans
          (congrArg (fun z => c g • z) (spatialGroupPolynomialMap_fourier α hα a g)).symm))

theorem spatialSymbolMultiplier_tendsto (c : ℕ → G → ℂ) (C : ℝ)
    (hb : ∀ n (a : G →₀ A), ‖spatialGroupPolynomialMap (G := G) α (groupPolynomialWeight (c n) a)‖ ≤
      C * ‖spatialGroupPolynomialMap (G := G) α a‖)
    (hc : ∀ g, Tendsto (fun n => c n g) atTop (nhds 1))
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    Tendsto (fun n => spatialSymbolMultiplier α (c n) x) atTop (nhds x) := by
  apply boundedOperators_tendsto_of_dense_span
    (fun p : A × G => spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (p.1 ⊗ₜ[ℂ] (reducedGroupUnitary G p.2 : reducedGroupAlgebra G)))
    (spatialGroupPolynomial_dense (G := G) α) (fun n => spatialSymbolMultiplier α (c n)) C
    (fun n x => spatialSymbolMultiplier_norm_le α (c n) C (hb n) x)
  intro p
  simp only [spatialSymbolMultiplier_generator α _ C (hb _)]
  simpa only [one_smul] using (hc p.2).smul_const
    (spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (p.1 ⊗ₜ[ℂ] (reducedGroupUnitary G p.2 : reducedGroupAlgebra G)))
end CuntzPureness

end

end OAI
