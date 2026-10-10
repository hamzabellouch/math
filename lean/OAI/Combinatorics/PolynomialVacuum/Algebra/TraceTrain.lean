import OAI.Combinatorics.PolynomialVacuum.Algebra.RowCircuit

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

def DependsBefore (N : ℕ) (W : SpinTensor ℕ ℂ) : Prop :=
  ∀ s r, (∀ j, j<N → s j=r j) → W s=W r

theorem siteR_depends {N k : ℕ} {W : SpinTensor ℕ ℂ} (hW : DependsBefore N W)
    (hk : k+1<N) (x y : ℂ) : DependsBefore N (siteR k x y W) := by
  intro s r h
  simp only [siteR,pairLinear,LinearMap.coe_mk,AddHom.coe_mk,pairAction,h k (by omega),h (k+1) hk]
  apply Finset.sum_congr rfl
  intro ab _
  congr 1
  apply hW
  intro j hj
  simp only [replacePair,Function.update_apply]
  split_ifs <;> first | rfl | exact h j hj

theorem braidTrain_depends {N k m : ℕ} {W : SpinTensor ℕ ℂ} (hW : DependsBefore N W)
    (hk : k+m<N) (c : ℂ) (X : ℕ → ℂ) : DependsBefore N (braidTrain c X k m W) := by
  induction m generalizing k W with
  | zero => exact hW
  | succ m ih =>
    exact ih (siteR_depends hW (by omega) c (X k)) (by omega)

theorem insertZero_skipOne {α : Type*} (s : ℕ → α) : insertOne 0 (s 0) (skipOne 0 s)=s := by
  funext j
  simp only [insertOne,skipOne,not_lt_zero,ite_false]
  split_ifs with h
  · subst j; rfl
  · congr 1; omega

theorem replacePair_insertZero (h : Spin) (s : ℕ → Spin) (k : ℕ) (ab : Pair) :
    replacePair (insertOne 0 h s) (k+1) (k+1+1) ab=
      insertOne 0 h (replacePair s k (k+1) ab) := by
  funext j
  simp only [replacePair,insertOne,Function.update_apply,not_lt_zero,ite_false]
  split_ifs <;> first | rfl | omega

noncomputable def headFiber (h : Spin) (W : SpinTensor ℕ ℂ) : SpinTensor ℕ ℂ :=
  fun s => W (insertOne 0 h s)

theorem headFiber_siteR (h : Spin) (W : SpinTensor ℕ ℂ) (k : ℕ) (x y : ℂ) :
    headFiber h (siteR (k+1) x y W)=siteR k x y (headFiber h W) := by
  funext s
  simp only [headFiber,siteR,pairLinear,LinearMap.coe_mk,AddHom.coe_mk,pairAction,
    replacePair_insertZero]
  have h1 : insertOne 0 h s (k+1)=s k := by simp [insertOne]
  have h2 : insertOne 0 h s (k+1+1)=s (k+1) := by simp [insertOne]
  rw [h1,h2]

theorem headFiber_braidTrain (h : Spin) (W : SpinTensor ℕ ℂ) (k m : ℕ) (c : ℂ) (X : ℕ → ℂ) :
    headFiber h (braidTrain c X (k+1) m W)=
      braidTrain c (skipOne 0 X) k m (headFiber h W) := by
  induction m generalizing k W with
  | zero => rfl
  | succ m ih =>
    simpa only [braidTrain,Module.End.mul_apply,headFiber_siteR,skipOne,not_lt_zero,ite_false] using
      ih (siteR (k+1) c (X (k+1)) W) (k+1)

theorem braidTrain_head_evaluate (W : SpinTensor ℕ ℂ) (m : ℕ) (c : ℂ) (X : ℕ → ℂ)
    (s : ℕ → Spin) :
    braidTrain c X 1 m W s=
      braidTrain c (skipOne 0 X) 0 m (headFiber (s 0) W) (skipOne 0 s) := by
  rw [← headFiber_braidTrain]
  simp [headFiber,insertZero_skipOne]

noncomputable def auxiliaryInput (h : Spin) (W : SpinTensor ℕ ℂ) : SpinTensor ℕ ℂ :=
  fun s => if s 0=h then W (skipOne 0 s) else 0

theorem auxiliaryInput_depends {N : ℕ} {W : SpinTensor ℕ ℂ} (hW : DependsBefore N W) (h : Spin) :
    DependsBefore (N+1) (auxiliaryInput h W) := by
  intro s r he
  simp only [auxiliaryInput,he 0 (by omega)]
  split_ifs
  · apply hW
    intro j hj; exact he (j+1) (by omega)
  · rfl

theorem cup_headFiber (h : Spin) (W : SpinTensor ℕ ℂ) :
    headFiber h (cupLinear 0 W)=∑ a : Spin,cup (h,a) • auxiliaryInput a W := by
  funext s
  simp only [headFiber,cupLinear,LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,smul_eq_mul,
    Finset.sum_apply,auxiliaryInput,insertOne_self,insertOne_next]
  have hs : skipTwo 0 (insertOne 0 h s)=skipOne 0 s := by
    funext j; simp [skipTwo,insertOne,skipOne]
  rw [hs]
  simp

noncomputable def tracedTrain (N : ℕ) (c : ℂ) (X : ℕ → ℂ) (W : SpinTensor ℕ ℂ) : SpinTensor ℕ ℂ :=
  fun s => ∑ h : Spin,zeta^charge h * braidTrain c X 0 N (auxiliaryInput h W) (insertOne N h s)

end PolynomialVacuumAlgebra

end OAI
