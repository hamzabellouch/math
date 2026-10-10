import OAI.Analysis.BoundedHochschild.CountableMatrixSpan
import OAI.Analysis.BoundedHochschild.NormalMultimodularClosure

namespace OAI

/-! It suffices to verify the module identities on matrix units: their
linearity gives the algebraic identities, and normality gives the weak-star
identities used in the primitive construction. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

structure MultimodularAt {n : ℕ} (f : Cochain M (n + 1)) (r : M) : Prop where
  left : ∀ x, f (Function.update x 0 (r * x 0)) = r * f x
  right : ∀ x, f (Function.update x (Fin.last n) (x (Fin.last n) * r)) = f x * r
  balance : ∀ x (j : Fin n),
    f (Function.update x j.castSucc (x j.castSucc * r)) =
      f (Function.update x j.succ (r * x j.succ))

lemma multimodularAt_one {n : ℕ} (f : Cochain M (n + 1)) : MultimodularAt f 1 := by
  constructor <;> intros <;> simp

lemma linear_maps_eq_on_span (S : Set M) (T U : M →L[ℂ] M)
    (h : ∀ r ∈ S, T r = U r) {a : M} (ha : a ∈ Submodule.span ℂ S) : T a = U a := by
  have hker : Submodule.span ℂ S ≤ (T - U).ker := by
    apply Submodule.span_le.mpr
    intro r hr
    change T r - U r = 0
    exact sub_eq_zero.mpr (h r hr)
  have hzero := hker ha
  change T a - U a = 0 at hzero
  exact sub_eq_zero.mp hzero

lemma multimodularAt_of_span {n : ℕ} (f : Cochain M (n + 1)) (S : Set M)
    (hS : ∀ r ∈ S, MultimodularAt f r) {a : M} (ha : a ∈ Submodule.span ℂ S) :
    MultimodularAt f a := by
  constructor
  · intro x
    have h := linear_maps_eq_on_span S
      ((updateSlice f 0 x).comp ((ContinuousLinearMap.mul ℂ M).flip (x 0)))
      ((ContinuousLinearMap.mul ℂ M).flip (f x))
      (fun r hr => by simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using (hS r hr).left x) ha
    simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using h
  · intro x
    have h := linear_maps_eq_on_span S
      ((updateSlice f (Fin.last n) x).comp (ContinuousLinearMap.mul ℂ M (x (Fin.last n))))
      (ContinuousLinearMap.mul ℂ M (f x))
      (fun r hr => by simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
        ContinuousLinearMap.mul_apply'] using (hS r hr).right x) ha
    simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
      ContinuousLinearMap.mul_apply'] using h
  · intro x j
    have h := linear_maps_eq_on_span S
      ((updateSlice f j.castSucc x).comp (ContinuousLinearMap.mul ℂ M (x j.castSucc)))
      ((updateSlice f j.succ x).comp ((ContinuousLinearMap.mul ℂ M).flip (x j.succ)))
      (fun r hr => by simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using (hS r hr).balance x j) ha
    simpa only [ContinuousLinearMap.comp_apply, updateSlice_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using h

theorem multimodular_of_matrixUnits (c : ℕ → HochschildComparison.PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1)) (hf : ∀ i j, MultimodularAt f (countableMatrixUnit c i j)) :
    MultimodularOver (countableMatrixAlgebra c) f := by
  have hS : ∀ r ∈ ({1} ∪ Set.range (fun p : ℕ × ℕ => countableMatrixUnit c p.1 p.2)),
      MultimodularAt f r := by
    intro r hr
    rcases hr with hr | ⟨⟨i, j⟩, rfl⟩
    · have hr1 : r = 1 := Set.mem_singleton_iff.mp hr
      subst r
      exact multimodularAt_one f
    · exact hf i j
  have hA : ∀ r ∈ countableMatrixAlgebra c, MultimodularAt f r := by
    intro r hr
    apply multimodularAt_of_span f _ hS
    rw [← countableMatrixAlgebra_eq_span c hi ho]
    exact hr
  exact ⟨fun r hr => (hA r hr).left, fun r hr => (hA r hr).right,
    fun r hr => (hA r hr).balance⟩

universe u
variable {N Y : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

theorem primitive_of_normal_matrix_units [Nontrivial N]
    (e : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N) (hno : NoFiniteCentralSummand N)
    (c : ℕ → HochschildComparison.PartialIso N) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) Filter.atTop 1)
    {n : ℕ} (f : Cochain N (n + 1)) (hn : SeparatelyNormal e f)
    (hf : ∀ i j, MultimodularAt f (countableMatrixUnit c i j))
    (hcocycle : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain N n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x :=
  primitive_of_normal_matrix_multimodular e hno c hi ho ht f hn
    (multimodular_of_matrixUnits c hi ho f hf) hcocycle

end BoundedHochschild.KadisonRingrose

end

end OAI
