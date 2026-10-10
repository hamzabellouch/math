import OAI.Analysis.CircleDomains.Topology.ClippedPaths

namespace OAI

/-! The fixed dyadic time partitions used to assemble physical-domain length. -/

open Set
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def dyadicReal (n i : ℕ) : ℝ := (i : ℝ) / (2 : ℝ) ^ n

theorem dyadicReal_nonneg (n i : ℕ) : 0 ≤ dyadicReal n i := by
  unfold dyadicReal
  positivity

theorem dyadicReal_le_one {n i : ℕ} (hi : i ≤ 2 ^ n) : dyadicReal n i ≤ 1 := by
  rw [dyadicReal, div_le_one (by positivity)]
  exact_mod_cast hi

theorem dyadicReal_mono (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    dyadicReal n i ≤ dyadicReal n j := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)

theorem dyadicReal_even (n i : ℕ) : dyadicReal (n + 1) (2 * i) = dyadicReal n i := by
  unfold dyadicReal
  push_cast
  rw [pow_succ]
  field_simp

def dyadicTime (n : ℕ) (i : Fin (2 ^ n + 1)) : PathTime :=
  ⟨dyadicReal n i.val, dyadicReal_nonneg n i.val, dyadicReal_le_one (by omega)⟩

def dyadicLeft (n : ℕ) (i : Fin (2 ^ n)) : PathTime := dyadicTime n i.castSucc

def dyadicRight (n : ℕ) (i : Fin (2 ^ n)) : PathTime := dyadicTime n i.succ

theorem dyadicLeft_le_right (n : ℕ) (i : Fin (2 ^ n)) : dyadicLeft n i ≤ dyadicRight n i :=
  dyadicReal_mono n (Nat.le_succ i.val)

def dyadicEven (n : ℕ) (i : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) :=
  ⟨2 * i.val, by rw [pow_succ]; omega⟩

def dyadicOdd (n : ℕ) (i : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) :=
  ⟨2 * i.val + 1, by rw [pow_succ]; omega⟩

theorem dyadicLeft_even (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicLeft (n + 1) (dyadicEven n i) = dyadicLeft n i := by
  apply Subtype.ext
  exact dyadicReal_even n i.val

theorem dyadicRight_odd (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicRight (n + 1) (dyadicOdd n i) = dyadicRight n i := by
  apply Subtype.ext
  change dyadicReal (n + 1) (2 * i.val + 1 + 1) = dyadicReal n (i.val + 1)
  rw [show 2 * i.val + 1 + 1 = 2 * (i.val + 1) by omega]
  exact dyadicReal_even n (i.val + 1)

theorem dyadicRight_even (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicRight (n + 1) (dyadicEven n i) = dyadicLeft (n + 1) (dyadicOdd n i) := rfl

theorem dyadicCell_split (n : ℕ) (i : Fin (2 ^ n)) :
    Icc (dyadicLeft n i) (dyadicRight n i) =
      Icc (dyadicLeft (n + 1) (dyadicEven n i)) (dyadicRight (n + 1) (dyadicEven n i)) ∪
      Icc (dyadicLeft (n + 1) (dyadicOdd n i)) (dyadicRight (n + 1) (dyadicOdd n i)) := by
  have hmid : dyadicRight (n + 1) (dyadicEven n i) ≤ dyadicRight (n + 1) (dyadicOdd n i) := by
    rw [dyadicRight_even]
    exact dyadicLeft_le_right _ _
  rw [← dyadicRight_even, Icc_union_Icc_eq_Icc (dyadicLeft_le_right _ _) hmid,
    dyadicLeft_even, dyadicRight_odd]

def dyadicChildrenEquiv (n : ℕ) : Fin (2 ^ n) × Fin 2 ≃ Fin (2 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ 2 n).symm)

theorem dyadicChildrenEquiv_zero (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicChildrenEquiv n (i, 0) = dyadicEven n i := by
  apply Fin.ext
  simp [dyadicChildrenEquiv, dyadicEven, finProdFinEquiv]

theorem dyadicChildrenEquiv_one (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicChildrenEquiv n (i, 1) = dyadicOdd n i := by
  apply Fin.ext
  simp [dyadicChildrenEquiv, dyadicOdd, finProdFinEquiv, Nat.add_comm]

theorem sum_dyadic_children {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : Fin (2 ^ (n + 1)) → M) :
    ∑ j, f j = ∑ i, (f (dyadicEven n i) + f (dyadicOdd n i)) := by
  rw [← (dyadicChildrenEquiv n).sum_comp f, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, dyadicChildrenEquiv_zero, dyadicChildrenEquiv_one]

end CircleDomainRigidity

end

end OAI
