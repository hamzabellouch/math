import OAI.Analysis.PlanarPacking.FiniteCoordinates
import OAI.Analysis.PlanarPacking.Indices

namespace OAI

/-!
# Finite decompositions of ℓ¹ coordinates

The central and exterior coordinate blocks give an additive decomposition of the ℓ¹ norm.
-/

namespace SharpPlanar
open scoped BigOperators
section
variable {ι κ : Type*}
noncomputable def l1Left (x : L1Finite (ι ⊕ κ)) : L1Finite ι :=
  WithLp.toLp 1 (fun i => x (Sum.inl i))
noncomputable def l1Right (x : L1Finite (ι ⊕ κ)) : L1Finite κ :=
  WithLp.toLp 1 (fun i => x (Sum.inr i))
lemma l1Left_apply (x : L1Finite (ι ⊕ κ)) (i : ι) : l1Left x i = x (Sum.inl i) := rfl
lemma l1Right_apply (x : L1Finite (ι ⊕ κ)) (i : κ) : l1Right x i = x (Sum.inr i) := rfl
lemma l1Split_norm [Fintype ι] [Fintype κ] (x : L1Finite (ι ⊕ κ)) :
    ‖x‖ = ‖l1Left x‖+‖l1Right x‖ := by
  classical
  rw [l1Finite_norm, l1Finite_norm, l1Finite_norm, Fintype.sum_sum_type]
  rfl
end
end SharpPlanar
namespace SharpPlanar.Numerical
lemma finiteEmbedding_split (x : L1Finite FiniteIndex) :
    finiteEmbedding finiteIndex x = finiteEmbedding centralIndex (l1Left x) +
      finiteEmbedding exteriorIndex (l1Right x) := by
  ext k
  change finiteEmbedding finiteIndex x k = finiteEmbedding centralIndex (l1Left x) k + finiteEmbedding exteriorIndex (l1Right x) k
  simp only [finiteEmbedding_apply]
  change (∑ j, if finiteIndex j=k then x j else 0) =
    (∑ j, if centralIndex j=k then l1Left x j else 0)+
    (∑ j, if exteriorIndex j=k then l1Right x j else 0)
  rw [Fintype.sum_sum_type]
  rfl
lemma finiteRestriction_left (x : X) :
    l1Left (finiteRestriction finiteIndex finiteIndex_injective x) =
      finiteRestriction centralIndex centralIndex_injective x := by ext i; rfl
lemma finiteRestriction_right (x : X) :
    l1Right (finiteRestriction finiteIndex finiteIndex_injective x) =
      finiteRestriction exteriorIndex exteriorIndex_injective x := by ext i; rfl
end SharpPlanar.Numerical

end OAI
