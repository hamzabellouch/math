import Mathlib
import OAI.Analysis.Commutator.Regroup
import OAI.Analysis.Commutator.FreeActionCovariance
import OAI.Analysis.Commutator.TracialConjugation

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι)

def mapBlockD (T : letterSpace t S i → letterSpace t S i) :
    ∀ n, BlockParams t S i j n → BlockParams t S i j n
  | 0,x => x
  | n+1,x => ((x.1.1,T x.1.2),mapBlockD T n x.2)

lemma paramD_mapBlockD (T : letterSpace t S i → letterSpace t S i) :
    ∀ n (x : BlockParams t S i j n) (k : Fin n),
      paramD t S n (mapBlockD t S i j T n x) k=T (paramD t S n x k)
  | 0,_,k => Fin.elim0 k
  | n+1,x,k => by
      refine Fin.cases ?_ (fun k => ?_) k
      · rfl
      · exact paramD_mapBlockD T n x.2 k

lemma paramJ_mapBlockD (T : letterSpace t S i → letterSpace t S i) :
    ∀ n (x : BlockParams t S i j n),
      paramJ t S n (mapBlockD t S i j T n x)=paramJ t S n x
  | 0,_ => rfl
  | n+1,x => by
      change x.1.1 ⊗ₜ[ℂ] paramJ t S n (mapBlockD t S i j T n x.2)=_
      rw [paramJ_mapBlockD T n x.2]
      rfl

variable (α : ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ k a, a∈S k → α k a∈S k)
  (hτ : ∀ k a, t.functional (α k a)=t.functional a)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma action_left_apply (k : ι) (a : A) (ha : a∈S k) (x : t.functional.GNS) :
    action t S α hmem hτ hfree hgen (t.functional.gnsStarAlgHom a x)=
      t.functional.gnsStarAlgHom (α k a) (action t S α hmem hτ hfree hgen x) :=
  congrArg (fun T : t.functional.GNS →L[ℂ] t.functional.GNS => T x)
    (action_left t S α hmem hτ hfree hgen k a ha)

lemma action_algebra_of_mem (k : ι) (a : A) (ha : a∈S k) :
    action t S α hmem hτ hfree hgen (TracialGNS.algebraVector t.functional a)=
      TracialGNS.algebraVector t.functional (α k a) := by
  simpa only [word_nil,List.map_nil,mul_one] using
    action_generator_word t S α hmem hτ hfree hgen k a ha [] reduced_nil

lemma action_vector_mul (k : ι) (a : A) (ha : a∈S k) (b : A) :
    action t S α hmem hτ hfree hgen (TracialGNS.algebraVector t.functional (a*b))=
      t.functional.gnsStarAlgHom (α k a)
        (action t S α hmem hτ hfree hgen (TracialGNS.algebraVector t.functional b)) := by
  simpa only [TracialGNS.algebraVector_apply,TracialGNS.left_coe] using (action_left_apply t S α hmem hτ hfree hgen k a ha
    (TracialGNS.algebraVector t.functional b))

include hfree hgen in
lemma action_blockRead_pure (hj : ∀ a∈S j, α j a=a) :
    ∀ n (x : BlockParams t S i j n),
      action t S α hmem hτ hfree hgen
        (TracialGNS.algebraVector t.functional (blockRead t S n (blockPure t S n x))) =
      TracialGNS.algebraVector t.functional
        (blockRead t S n (blockPure t S n
          (mapBlockD t S i j (letterIso t S α hmem hτ i) n x)))
  | 0,x => by
      change action t S α hmem hτ hfree hgen
        (TracialGNS.algebraVector t.functional (factorValue t S j x))=_
      rw [action_algebra_of_mem t S α hmem hτ hfree hgen j (factorValue t S j x) (show factorValue t S j x ∈ S j from x.property),
        hj (factorValue t S j x) (show factorValue t S j x ∈ S j from x.property)]
      rfl
  | n+1,x => by
      change action t S α hmem hτ hfree hgen
        (TracialGNS.algebraVector t.functional
          (letterValue t S j x.1.1 * (letterValue t S i x.1.2 *
            blockRead t S n (blockPure t S n x.2))))=_
      rw [action_vector_mul t S α hmem hτ hfree hgen j (letterValue t S j x.1.1) (show letterValue t S j x.1.1∈S j from x.1.1.property.1),
        action_vector_mul t S α hmem hτ hfree hgen i (letterValue t S i x.1.2) (show letterValue t S i x.1.2∈S i from x.1.2.property.1),
        action_blockRead_pure hj n x.2,hj (letterValue t S j x.1.1) (show letterValue t S j x.1.1∈S j from x.1.1.property.1)]
      simp only [TracialGNS.algebraVector_apply,TracialGNS.left_coe]
      rfl

end Kadison.FreeBlocks

end

end
end

end OAI
