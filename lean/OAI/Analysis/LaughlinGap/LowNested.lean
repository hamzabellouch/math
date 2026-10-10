import Mathlib
import OAI.Analysis.LaughlinGap.FourSpin
import OAI.Analysis.LaughlinGap.NestedAveraging

namespace OAI

/-! Low Nested. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

abbrev LowNestedIndex (T : ℕ) := (D : Fin (T+1)) × Fin (D.val+1)

lemma lowNested_valid {Q T D r : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (hD : D ≤ T) (hr : r ≤ D) :
    r ≤ Q ∧ D-r ≤ min (2*Q-2) (Q+Q-2*r) ∧
      T-D ≤ (2*Q-2)+(Q+Q-2*r)-2*(D-r) := by omega

noncomputable def lowNestedInclusion {Q T : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (a : LowNestedIndex T) : NestedIndex (2*Q-2) Q Q :=
  ⟨⟨a.2.val, by have := a.1.isLt; have := a.2.isLt; omega⟩,
    ⟨⟨a.1.val-a.2.val, (lowNested_valid hQ hT (by have := a.1.isLt; omega)
      (by have := a.2.isLt; exact Nat.le_of_lt_succ this)).2.1 |> Nat.lt_succ_of_le⟩,
    ⟨T-a.1.val, (lowNested_valid hQ hT (by have := a.1.isLt; omega)
      (by have := a.2.isLt; exact Nat.le_of_lt_succ this)).2.2 |> Nat.lt_succ_of_le⟩⟩⟩

lemma lowNestedInclusion_injective {Q T : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q) :
    Function.Injective (lowNestedInclusion hQ hT) := by
  intro a b h
  have hr := congrArg (fun x : NestedIndex (2*Q-2) Q Q => x.1.val) h
  have hz := congrArg (fun x : NestedIndex (2*Q-2) Q Q => x.2.1.val) h
  dsimp [lowNestedInclusion] at hr hz
  have hD : a.1=b.1 := Fin.ext (by have := a.2.isLt; have := b.2.isLt; omega)
  rcases a with ⟨D,r⟩
  rcases b with ⟨D',r'⟩
  dsimp at hD
  subst D'
  have : r=r' := Fin.ext hr
  subst r'
  rfl

lemma lowNested_coefficient {Q D T r : ℕ} (hrD : r ≤ D)
    (hDT : D ≤ T) (hT : T ≤ Q)
    (a : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1))) :
    Real.sqrt 2 * nestedTensor (2*Q-2) Q Q r (D-r) (T-D) a =
      fourBodyCoefficient Q D T r a.1.val a.2.1.val a.2.2.val := by
  classical
  unfold nestedTensor fourBodyCoefficient
  by_cases hw : r ≤ a.2.1.val+a.2.2.val ∧ a.1.val+a.2.1.val+a.2.2.val=T
  · rw [ite_eq_left hw]
    let l : Fin (Q+Q-2*r+1) := ⟨a.2.1.val+a.2.2.val-r, by omega⟩
    rw [Finset.sum_eq_single l]
    · simp only [coupledTensor]
      rw [ite_eq_left (by dsimp [l]; omega), ite_eq_left (by dsimp [l]; omega)]
      dsimp [l]
      rw [show Q+Q=2*Q by omega]
      ring
    · intro k hk hkl
      have he : a.2.1.val+a.2.2.val ≠ r+k.val := by
        intro he
        apply hkl
        apply Fin.ext
        dsimp [l]
        omega
      simp only [coupledTensor, ite_eq_right he, mul_zero]
    · simp
  · rw [ite_eq_right hw]
    have he : (∑ k : Fin (Q+Q-2*r+1),
        coupledTensor (2*Q-2) (Q+Q-2*r) (D-r) (T-D) (a.1,k) *
          coupledTensor Q Q r k.val a.2) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [coupledTensor]
      split_ifs with h₁ h₂ h₂ <;> try simp
      exfalso
      exact hw ⟨by omega, by omega⟩
    rw [he, mul_zero]

lemma nestedTensor_low_expansion {Q T : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (a : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1)))
    (ha : a.1.val+a.2.1.val+a.2.2.val=T) :
    ∑ b : LowNestedIndex T,
      nestedTensor (2*Q-2) Q Q b.2.val (b.1.val-b.2.val) (T-b.1.val) a •
        nestedTensor (2*Q-2) Q Q b.2.val (b.1.val-b.2.val) (T-b.1.val) =
      Pi.single a 1 := by
  classical
  have hex := nestedTensor_expansion (2*Q-2) Q Q (Pi.single a 1)
  simp only [dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hex
  rw [← hex]
  apply Finset.sum_bij_ne_zero (fun b _ _ => lowNestedInclusion hQ hT b)
  · simp
  · intro b hb hb0 c hc hc0 he
    exact lowNestedInclusion_injective hQ hT he
  · intro b hb hb0
    have hw : b.1.val+b.2.1.val+b.2.2.val=T := by
      by_contra he
      have hz := nestedTensor_weight_support (2*Q-2) Q Q b.1.val b.2.1.val b.2.2.val a
        (by omega)
      exact hb0 (by rw [hz, zero_smul])
    let c : LowNestedIndex T := ⟨⟨b.1.val+b.2.1.val, by omega⟩,⟨b.1.val, by dsimp; omega⟩⟩
    have hc : lowNestedInclusion hQ hT c=b := by
      rcases b with ⟨r,⟨z,l⟩⟩
      dsimp at hw
      have hr : (lowNestedInclusion hQ hT c).1=r := Fin.ext rfl
      apply Sigma.ext hr
      apply heq_of_eq
      apply Sigma.ext (Fin.ext (by dsimp [lowNestedInclusion,c]; omega))
      apply (Fin.heq_ext_iff (by dsimp [lowNestedInclusion,c]; omega)).mpr
      dsimp [lowNestedInclusion,c]
      omega
    refine ⟨c, Finset.mem_univ _, ?_, hc⟩
    have hc0 : nestedTensor (2*Q-2) Q Q c.2.val (c.1.val-c.2.val) (T-c.1.val) a •
      nestedTensor (2*Q-2) Q Q c.2.val (c.1.val-c.2.val) (T-c.1.val) ≠ 0 := by
      change nestedTensor (2*Q-2) Q Q (lowNestedInclusion hQ hT c).1.val
        (lowNestedInclusion hQ hT c).2.1.val (lowNestedInclusion hQ hT c).2.2.val a •
        nestedTensor (2*Q-2) Q Q (lowNestedInclusion hQ hT c).1.val
        (lowNestedInclusion hQ hT c).2.1.val (lowNestedInclusion hQ hT c).2.2.val ≠ 0
      rw [hc]
      exact hb0
    exact hc0
  · intros
    rfl

end LaughlinGap.Spin

end

end OAI
