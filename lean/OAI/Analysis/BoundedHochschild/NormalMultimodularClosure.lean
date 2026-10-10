import OAI.Analysis.BoundedHochschild.CountableMatrixPrimitives
import OAI.Analysis.TracialCohomology.HilbertFactorization

namespace OAI

/-! Separate normality extends the adjacent-input module identities from
the algebraic matrix algebra to its weak-star closure. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma normal_maps_eq_on_linearClosure (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (A : StarSubalgebra ℂ M) (T U : M →L[ℂ] M)
    (hT : HasPreadjoint e T) (hU : HasPreadjoint e U)
    (h : ∀ a ∈ A, T a = U a) {a : M}
    (ha : (WeakAlgebra.weakEquiv e).symm a ∈ WeakAlgebra.linearClosure e A) : T a = U a := by
  have hclosed : IsClosed {F : WeakDual ℂ X |
      (WeakAlgebra.weakEquiv e).symm (T (WeakAlgebra.weakEquiv e F)) =
      (WeakAlgebra.weakEquiv e).symm (U (WeakAlgebra.weakEquiv e F))} :=
    isClosed_eq (WeakAlgebra.normal_continuous e T hT) (WeakAlgebra.normal_continuous e U hU)
  have hs : (WeakAlgebra.linearClosure e A : Set (WeakDual ℂ X)) ⊆
      {F | (WeakAlgebra.weakEquiv e).symm (T (WeakAlgebra.weakEquiv e F)) =
      (WeakAlgebra.weakEquiv e).symm (U (WeakAlgebra.weakEquiv e F))} := by
    apply closure_minimal _ hclosed
    rintro F ⟨b, hb, rfl⟩
    change (WeakAlgebra.weakEquiv e).symm
        (T (WeakAlgebra.weakEquiv e ((WeakAlgebra.weakEquiv e).symm b))) =
      (WeakAlgebra.weakEquiv e).symm
        (U (WeakAlgebra.weakEquiv e ((WeakAlgebra.weakEquiv e).symm b)))
    rw [LinearEquiv.apply_symm_apply, h b hb]
  simpa only [LinearEquiv.apply_symm_apply] using (WeakAlgebra.weakEquiv e).symm.injective (hs ha)

def updateSlice {n : ℕ} (f : Cochain M (n + 1)) (i : Fin (n + 1))
    (v : Fin (n + 1) → M) : M →L[ℂ] M := sliceAt f i (i.removeNth v)

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma updateSlice_apply {n : ℕ} (f : Cochain M (n + 1)) (i : Fin (n + 1))
    (v : Fin (n + 1) → M) (a : M) : updateSlice f i v a = f (Function.update v i a) := by
  simp only [updateSlice, sliceAt_apply, Fin.insertNth_removeNth]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma updateSlice_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (f : Cochain M (n + 1)) (hn : SeparatelyNormal e f) (i : Fin (n + 1))
    (v : Fin (n + 1) → M) : HasPreadjoint e (updateSlice f i v) := by
  intro z
  obtain ⟨w, hw⟩ := hn i v z
  exact ⟨w, fun a => by simpa only [updateSlice_apply] using hw a⟩

omit [PartialOrder M] [StarOrderedRing M] in
theorem normal_multimodular_countable_closure (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → HochschildComparison.PartialIso M) {n : ℕ} (f : Cochain M (n + 1))
    (hn : SeparatelyNormal e f) (hf : MultimodularOver (countableMatrixAlgebra c) f) :
    MultimodularOver (countableMatrixClosure e c) f := by
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  have hR := (HochschildSakai.abstract_multiplication_normal e).2
  constructor
  · intro r hr x
    have h := normal_maps_eq_on_linearClosure e (countableMatrixAlgebra c)
      ((updateSlice f 0 x).comp ((ContinuousLinearMap.mul ℂ M).flip (x 0)))
      ((ContinuousLinearMap.mul ℂ M).flip (f x))
      ((updateSlice_normal e f hn 0 x).comp e (hR (x 0))) (hR (f x))
      (fun a ha => by simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using hf.left a ha x) hr
    simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using h
  · intro r hr x
    have h := normal_maps_eq_on_linearClosure e (countableMatrixAlgebra c)
      ((updateSlice f (Fin.last n) x).comp (ContinuousLinearMap.mul ℂ M (x (Fin.last n))))
      (ContinuousLinearMap.mul ℂ M (f x))
      ((updateSlice_normal e f hn (Fin.last n) x).comp e (hL (x (Fin.last n)))) (hL (f x))
      (fun a ha => by simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
        ContinuousLinearMap.mul_apply'] using hf.right a ha x) hr
    simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
      ContinuousLinearMap.mul_apply'] using h
  · intro r hr x j
    have h := normal_maps_eq_on_linearClosure e (countableMatrixAlgebra c)
      ((updateSlice f j.castSucc x).comp (ContinuousLinearMap.mul ℂ M (x j.castSucc)))
      ((updateSlice f j.succ x).comp ((ContinuousLinearMap.mul ℂ M).flip (x j.succ)))
      ((updateSlice_normal e f hn j.castSucc x).comp e (hL (x j.castSucc)))
      ((updateSlice_normal e f hn j.succ x).comp e (hR (x j.succ)))
      (fun a ha => by simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using hf.balance a ha x j) hr
    simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using h

theorem primitive_of_normal_matrix_multimodular [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (c : ℕ → HochschildComparison.PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) Filter.atTop 1)
    {n : ℕ} (f : Cochain M (n + 1)) (hn : SeparatelyNormal e f)
    (hf : MultimodularOver (countableMatrixAlgebra c) f)
    (hcocycle : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x :=
  primitive_of_countableMatrix_multimodular e hno c hi ho ht f
    (normal_multimodular_countable_closure e c f hn hf) hcocycle

end BoundedHochschild.KadisonRingrose

end

end OAI
