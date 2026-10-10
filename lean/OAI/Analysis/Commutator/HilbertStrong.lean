import Mathlib
import OAI.Analysis.Commutator.FreeSymmetry16
import OAI.Analysis.Commutator.StrongContinuity

namespace OAI

noncomputable section

section

noncomputable section

open scoped TensorProduct InnerProductSpace Topology CStarAlgebra ComplexOrder

open UniformSpace

namespace Kadison

namespace StrongContinuity

variable {X E F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma completion (T : X → E →ₗᵢ[ℂ] E)
    (hT : ∀ x, Continuous fun g => T g x) (x : Completion E) :
    Continuous fun g => completionIsometry (T g) x := by
  apply of_denseRange _ (fun x : E => (x : Completion E)) Completion.denseRange_coe _ x
  intro y
  simpa only [completionIsometry_coe, Function.comp_def] using (Completion.continuous_coe E).comp (hT y)

lemma tensor (T : X → E →ₗᵢ[ℂ] E) (S : X → F →ₗᵢ[ℂ] F)
    (hT : ∀ x, Continuous fun g => T g x) (hS : ∀ x, Continuous fun g => S g x)
    (x : E ⊗[ℂ] F) : Continuous fun g => TensorProduct.mapIsometry (T g) (S g) x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    convert hx.add hy using 1
    ext g
    exact map_add (TensorProduct.mapIsometry (T g) (S g)) x y
  | tmul x y =>
    simpa only [TensorProduct.mapIsometry_apply,TensorProduct.map_tmul,LinearIsometry.coe_toLinearMap,Function.comp_def]
      using (TensorProduct.continuous_tmul (𝕜:=ℂ) (E:=E) (F:=F)).comp ((hT x).prodMk (hS y))

lemma hilbertSum {ι H : Type*} {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)] [∀ i, CompleteSpace (V i)]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : ∀ i, V i →ₗᵢ[ℂ] H) (hU : IsHilbertSum ℂ V U)
    (T : X → H →ₗᵢ[ℂ] H) (hT : ∀ i x, Continuous fun g => T g (U i x))
    (x : H) : Continuous fun g => T g x := by
  have hs : (⨆ i, LinearMap.range (U i).toLinearMap) ≤ vectors T := by
    apply iSup_le
    rintro i _ ⟨x,rfl⟩
    exact hT i x
  have ht := Submodule.topologicalClosure_minimal _ hs (isClosed_vectors T)
  rw [← hU.OrthogonalFamily.range_linearIsometry,
    LinearMap.range_eq_top.mpr hU.surjective_isometry] at ht
  exact ht (Submodule.mem_top : x∈(⊤:Submodule ℂ H))

end StrongContinuity

namespace PreHilbert

variable {X : Type*} [TopologicalSpace X]

lemma powerMap_continuous (E : PreHilbert) (T : X → E →ₗᵢ[ℂ] E)
    (hT : ∀ x, Continuous fun g => T g x) (n : ℕ) (x : power E n) :
    Continuous fun g => powerMap E (T g) n x := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact StrongContinuity.tensor T (fun g => powerMap E (T g) n) hT ih x

lemma wordMap_continuous (E F : PreHilbert) (T : X → E →ₗᵢ[ℂ] E) (S : X → F →ₗᵢ[ℂ] F)
    (hT : ∀ x, Continuous fun g => T g x) (hS : ∀ x, Continuous fun g => S g x)
    (n : ℕ) (x : wordSpace E F n) : Continuous fun g => wordMap E F (T g) (S g) n x :=
  StrongContinuity.completion _
    (StrongContinuity.tensor T (fun g => powerMap F (S g) n) hT (powerMap_continuous F S hS n)) x

end PreHilbert

namespace TracialGNS

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

lemma conjugation_continuous (x : τ.GNS) : Continuous fun u : unitary A => conjugation τ hτ u x := by
  change Continuous fun u : unitary A => τ.gnsStarAlgHom (u:A)
    (rightStarAlgHom τ hτ (MulOpposite.op (star (u:A))) x)
  have hL : Continuous fun u : unitary A => τ.gnsStarAlgHom (u:A) :=
    (map_continuous τ.gnsStarAlgHom).comp continuous_subtype_val
  have hR : Continuous fun u : unitary A => rightStarAlgHom τ hτ (MulOpposite.op (star (u:A))) :=
    (map_continuous (rightStarAlgHom τ hτ)).comp (MulOpposite.continuous_op.comp continuous_subtype_val.star)
  exact hL.clm_apply (hR.clm_apply continuous_const)

lemma centeredConjugation_continuous (x : zeroSpace τ) : Continuous fun u : unitary A =>
    centeredIsometry (vacuum τ) (conjugation τ hτ u) (conjugation_vacuum τ hτ u) x := by
  apply Continuous.subtype_mk
  exact conjugation_continuous τ hτ x

lemma wordConjugation_continuous (n : ℕ) (x : PreHilbert.wordSpace (fullSpace τ) (zeroSpace τ) n) :
    Continuous fun u : unitary A => wordConjugation τ hτ u n x :=
  PreHilbert.wordMap_continuous (fullSpace τ) (zeroSpace τ) _ _
    (conjugation_continuous τ hτ) (centeredConjugation_continuous τ hτ) n x

variable (J : ℕ → Type*) [∀ n, NormedAddCommGroup (J n)] [∀ n, InnerProductSpace ℂ (J n)]

lemma sumConjugation_continuous (n : ℕ) (x : sumLevel τ J n) :
    Continuous fun u : unitary A => sumConjugationIso τ hτ J u n x :=
  StrongContinuity.completion _ (StrongContinuity.tensor _ _
    (wordConjugation_continuous τ hτ n) (fun _ => continuous_const)) x

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : ∀ k, sumLevel τ J k →ₗᵢ[ℂ] H) (hU : IsHilbertSum ℂ (sumLevel τ J) U)

lemma freeConjugation_continuous (x : H) :
    Continuous fun u : unitary A => freeConjugation τ hτ J U hU u x := by
  apply StrongContinuity.hilbertSum U hU _ _ x
  intro n y
  have he : (fun u => freeConjugation τ hτ J U hU u (U n y)) =
      fun u => U n (sumConjugationIso τ hτ J u n y) := by
    funext u
    exact congrArg (fun T : sumLevel τ J n →L[ℂ] H => T y)
      ((freeConjugation_comp τ hτ J U hU u n).trans
        (congrArg ((U n).toContinuousLinearMap.comp) (sumConjugationIso_toCLM τ hτ J u n).symm))
  rw [he]
  exact (U n).continuous.comp (sumConjugation_continuous τ hτ J n y)

end TracialGNS

end Kadison

end

end
end

end OAI
