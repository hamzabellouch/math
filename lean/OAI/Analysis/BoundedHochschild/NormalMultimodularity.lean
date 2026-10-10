import OAI.Analysis.BoundedHochschild.NormalCochainTransport
import OAI.Analysis.BoundedHochschild.MultimodularGenerators

namespace OAI

/-! Input normalization respects the usual module identities. Only left
and right multiplication are needed for this naturality statement. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

private def multiplyBoth (a b : M) : M →L[ℂ] M :=
  ((ContinuousLinearMap.mul ℂ M).flip b).comp (ContinuousLinearMap.mul ℂ M a)

private lemma multiplyBoth_apply (a b x : M) : multiplyBoth a b x = a * x * b := rfl

private lemma multiplyBoth_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a b : M) :
    HasPreadjoint e (multiplyBoth a b) :=
  ((HochschildSakai.abstract_multiplication_normal e).2 b).comp e
    ((HochschildSakai.abstract_multiplication_normal e).1 a)

def cochainSandwich {n : ℕ} (a b : Fin n → M) (c d : M) (f : Cochain M n) : Cochain M n :=
  (multiplyBoth c d).compContinuousMultilinearMap
    (f.compContinuousLinearMap (fun i => multiplyBoth (a i) (b i)))

@[simp] lemma cochainSandwich_apply {n : ℕ} (a b : Fin n → M) (c d : M)
    (f : Cochain M n) (x : Fin n → M) :
    cochainSandwich a b c d f x = c * f (fun i => a i * x i * b i) * d := rfl

private lemma sandwich_update {n : ℕ} (a b x : Fin (n + 1) → M) (i : Fin (n + 1)) (z : M) :
    (fun j => a j * Function.update x i z j * b j) =
      Function.update (fun j => a j * x j * b j) i (a i * z * b i) := by
  ext j
  by_cases hji : j = i <;> simp [hji]

private lemma sandwich_slice {n : ℕ} (a b : Fin (n + 1) → M) (c d : M)
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) (x : Fin (n + 1) → M) :
    updateSlice (cochainSandwich a b c d f) i x =
      (multiplyBoth c d).comp
        ((updateSlice f i (fun j => a j * x j * b j)).comp (multiplyBoth (a i) (b i))) := by
  ext z
  simp only [updateSlice_apply, cochainSandwich_apply, sandwich_update,
    ContinuousLinearMap.comp_apply, multiplyBoth_apply]

lemma normalAt_value (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) (x : Fin (n + 1) → M) :
    normalAt e f i x = HochschildNormalPart.operatorNormalPart e (updateSlice f i x) (x i) := by
  calc
    _ = normalAt e f i (i.insertNth (x i) (i.removeNth x)) :=
      congrArg (normalAt e f i) (Fin.insertNth_self_removeNth i x).symm
    _ = _ := normalAt_insert e f i (i.removeNth x) (x i)

lemma normalAt_cochainSandwich (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (a b : Fin (n + 1) → M) (c d : M) (f : Cochain M (n + 1)) (i : Fin (n + 1)) :
    normalAt e (cochainSandwich a b c d f) i = cochainSandwich a b c d (normalAt e f i) := by
  ext x
  rw [normalAt_value, sandwich_slice,
    HochschildNormalPart.operatorNormalPart_comp_normal e _ _ (multiplyBoth_normal e c d)]
  have hin (T : M →L[ℂ] M) :
      HochschildNormalPart.operatorNormalPart e (T.comp (multiplyBoth (a i) (b i))) =
        (HochschildNormalPart.operatorNormalPart e T).comp (multiplyBoth (a i) (b i)) := by
    unfold multiplyBoth
    rw [← ContinuousLinearMap.comp_assoc,
      HochschildNormalPart.operatorNormalPart_comp_left,
      HochschildNormalPart.operatorNormalPart_comp_right,
      ContinuousLinearMap.comp_assoc]
  rw [hin]
  simp only [cochainSandwich_apply, normalAt_value,
    ContinuousLinearMap.comp_apply, multiplyBoth_apply]

lemma cochainSandwich_leftInput {n : ℕ} (f : Cochain M (n + 1)) (k : Fin (n + 1))
    (r : M) (x : Fin (n + 1) → M) :
    cochainSandwich (Function.update (fun _ => 1) k r) (fun _ => 1) 1 1 f x =
      f (Function.update x k (r * x k)) := by
  rw [cochainSandwich_apply, one_mul, mul_one]
  congr 1
  ext j
  by_cases hj : j = k <;> simp [hj]

lemma cochainSandwich_rightInput {n : ℕ} (f : Cochain M (n + 1)) (k : Fin (n + 1))
    (r : M) (x : Fin (n + 1) → M) :
    cochainSandwich (fun _ => 1) (Function.update (fun _ => 1) k r) 1 1 f x =
      f (Function.update x k (x k * r)) := by
  rw [cochainSandwich_apply, one_mul, mul_one]
  congr 1
  ext j
  by_cases hj : j = k <;> simp [hj]

lemma cochainSandwich_leftOutput {n : ℕ} (f : Cochain M n) (r : M) (x : Fin n → M) :
    cochainSandwich (fun _ => 1) (fun _ => 1) r 1 f x = r * f x := by
  simp only [cochainSandwich_apply, one_mul, mul_one]

lemma cochainSandwich_rightOutput {n : ℕ} (f : Cochain M n) (r : M) (x : Fin n → M) :
    cochainSandwich (fun _ => 1) (fun _ => 1) 1 r f x = f x * r := by
  simp only [cochainSandwich_apply, one_mul, mul_one]

lemma normalAt_multimodularAt (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (f : Cochain M (n + 1)) (i : Fin (n + 1)) (r : M) (hf : MultimodularAt f r) :
    MultimodularAt (normalAt e f i) r := by
  constructor
  · intro x
    have h : cochainSandwich (Function.update (fun _ => 1) 0 r) (fun _ => 1) 1 1 f =
        cochainSandwich (fun _ => 1) (fun _ => 1) r 1 f := by
      ext y
      simpa only [cochainSandwich_leftInput, cochainSandwich_leftOutput] using hf.left y
    have hh := congrArg (fun F : Cochain M (n + 1) => normalAt e F i) h
    simp only [normalAt_cochainSandwich] at hh
    simpa only [cochainSandwich_leftInput, cochainSandwich_leftOutput] using
      congrArg (fun F : Cochain M (n + 1) => F x) hh
  · intro x
    have h : cochainSandwich (fun _ => 1) (Function.update (fun _ => 1) (Fin.last n) r) 1 1 f =
        cochainSandwich (fun _ => 1) (fun _ => 1) 1 r f := by
      ext y
      simpa only [cochainSandwich_rightInput, cochainSandwich_rightOutput] using hf.right y
    have hh := congrArg (fun F : Cochain M (n + 1) => normalAt e F i) h
    simp only [normalAt_cochainSandwich] at hh
    simpa only [cochainSandwich_rightInput, cochainSandwich_rightOutput] using
      congrArg (fun F : Cochain M (n + 1) => F x) hh
  · intro x j
    have h : cochainSandwich (fun _ => 1) (Function.update (fun _ => 1) j.castSucc r) 1 1 f =
        cochainSandwich (Function.update (fun _ => 1) j.succ r) (fun _ => 1) 1 1 f := by
      ext y
      simpa only [cochainSandwich_rightInput, cochainSandwich_leftInput] using hf.balance y j
    have hh := congrArg (fun F : Cochain M (n + 1) => normalAt e F i) h
    simp only [normalAt_cochainSandwich] at hh
    simpa only [cochainSandwich_rightInput, cochainSandwich_leftInput] using
      congrArg (fun F : Cochain M (n + 1) => F x) hh

lemma normalAt_multimodularOver (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {n : ℕ}
    (R : StarSubalgebra ℂ M) (f : Cochain M (n + 1)) (i : Fin (n + 1))
    (hf : MultimodularOver R f) : MultimodularOver R (normalAt e f i) := by
  have h (r : M) (hr : r ∈ R) := normalAt_multimodularAt e f i r
    ⟨hf.left r hr, hf.right r hr, hf.balance r hr⟩
  exact ⟨fun r hr => (h r hr).left, fun r hr => (h r hr).right,
    fun r hr => (h r hr).balance⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
