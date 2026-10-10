import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedFourIndex

namespace OAI

/-! Entrywise perturbation bounds needed when applying the actual symmetric
Gram correction to the two- and four-index orbital coefficients. Polynomial
site-count losses suffice for the logarithmic spacing used here. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem product_two_perturb {a b c d eta : ℝ}
    (hb : |b| ≤ 2) (hc : |c| ≤ 2)
    (he : 0 ≤ eta) (hac : |a - c| ≤ eta) (hbd : |b - d| ≤ eta) :
    |a * b - c * d| ≤ 4 * eta := by
  have hid : a * b - c * d = (a - c) * b + c * (b - d) := by ring
  rw [hid]
  calc
    _ ≤ |a - c| * |b| + |c| * |b - d| := by simpa only [abs_mul] using abs_add_le ((a-c)*b) (c*(b-d))
    _ ≤ eta * 2 + 2 * eta := add_le_add
      (mul_le_mul hac hb (abs_nonneg _) he)
      (mul_le_mul hc hbd (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem product_four_perturb {a b c d a' b' c' d' eta : ℝ}
    (hb : |b| ≤ 2) (hc : |c| ≤ 2) (hd : |d| ≤ 2)
    (ha' : |a'| ≤ 2) (hb' : |b'| ≤ 2) (hc' : |c'| ≤ 2)
    (he : 0 ≤ eta) (haa : |a-a'| ≤ eta) (hbb : |b-b'| ≤ eta)
    (hcc : |c-c'| ≤ eta) (hdd : |d-d'| ≤ eta) :
    |(a*b)*(c*d) - (a'*b')*(c'*d')| ≤ 32 * eta := by
  have hab := product_two_perturb hb ha' he haa hbb
  have hcd := product_two_perturb hd hc' he hcc hdd
  have hcd4 : |c*d| ≤ 4 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hc hd (abs_nonneg d) (by norm_num : (0:ℝ) ≤ 2)]
  have hab4 : |a'*b'| ≤ 4 := by
    rw [abs_mul]
    nlinarith [mul_le_mul ha' hb' (abs_nonneg b') (by norm_num : (0:ℝ) ≤ 2)]
  have hid : (a*b)*(c*d) - (a'*b')*(c'*d') =
      (a*b-a'*b')*(c*d) + (a'*b')*(c*d-c'*d') := by ring
  rw [hid]
  calc
    _ ≤ |a*b-a'*b'| * |c*d| + |a'*b'| * |c*d-c'*d'| := by
      simpa only [abs_mul] using abs_add_le ((a*b-a'*b')*(c*d)) ((a'*b')*(c*d-c'*d'))
    _ ≤ (4*eta)*4 + 4*(4*eta) := add_le_add
      (mul_le_mul hab hcd4 (abs_nonneg _) (by positivity))
      (mul_le_mul hab4 hcd (abs_nonneg _) (by norm_num))
    _ = _ := by ring

def finiteTwoIndexChange {m : ℕ} (A : Fin m → Fin m → ℝ)
    (F : Fin m → Fin m → ℝ) (i j : Fin m) : ℝ :=
  ∑ p, ∑ q, (A i p * A j q) * F p q

theorem finiteTwoIndexChange_identity {m : ℕ}
    (F : Fin m → Fin m → ℝ) (i j : Fin m) :
    finiteTwoIndexChange (fun a b => if a=b then 1 else 0) F i j = F i j := by
  classical
  simp only [finiteTwoIndexChange, ite_mul, mul_ite, one_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem finiteTwoIndexChange_bound {m : ℕ} (A : Fin m → Fin m → ℝ)
    (F : Fin m → Fin m → ℝ) {eta B : ℝ}
    (he : 0 ≤ eta) (_hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ 2)
    (hnear : ∀ i j, |A i j - if i=j then 1 else 0| ≤ eta)
    (hF : ∀ i j, |F i j| ≤ B) (i j : Fin m) :
    |finiteTwoIndexChange A F i j - F i j| ≤ (m : ℝ)^2 * (4*eta*B) := by
  classical
  let I : Fin m → Fin m → ℝ := fun a b => if a=b then 1 else 0
  have hI (a b : Fin m) : |I a b| ≤ 2 := by dsimp [I]; split_ifs <;> norm_num
  have hc (p q : Fin m) : |(A i p*A j q-I i p*I j q)*F p q| ≤ 4*eta*B := by
    rw [abs_mul]
    exact mul_le_mul (product_two_perturb (hA j q) (hI i p) he (hnear i p) (hnear j q))
      (hF p q) (abs_nonneg _) (by positivity)
  rw [← finiteTwoIndexChange_identity F i j]
  change |finiteTwoIndexChange A F i j - finiteTwoIndexChange I F i j| ≤ _
  unfold finiteTwoIndexChange
  simp only [← Finset.sum_sub_distrib, ← sub_mul]
  calc
    _ ≤ ∑ p, ∑ q, |(A i p*A j q-I i p*I j q)*F p q| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun p _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _p : Fin m, ∑ _q : Fin m, 4*eta*B :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => hc p q))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

def finiteFourIndexChange {m : ℕ} (A : Fin m → Fin m → ℝ)
    (F : Fin m → Fin m → Fin m → Fin m → ℝ) (i j k l : Fin m) : ℝ :=
  ∑ p, ∑ q, ∑ r, ∑ s, ((A i p * A j q) * (A k r * A l s)) * F p q r s

theorem finiteFourIndexChange_identity {m : ℕ}
    (F : Fin m → Fin m → Fin m → Fin m → ℝ) (i j k l : Fin m) :
    finiteFourIndexChange (fun a b => if a = b then 1 else 0) F i j k l = F i j k l := by
  classical
  simp only [finiteFourIndexChange, ite_mul, mul_ite, one_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem finiteFourIndexChange_bound {m : ℕ} (A : Fin m → Fin m → ℝ)
    (F : Fin m → Fin m → Fin m → Fin m → ℝ) {eta B : ℝ}
    (he : 0 ≤ eta) (_hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ 2)
    (hnear : ∀ i j, |A i j - if i = j then 1 else 0| ≤ eta)
    (hF : ∀ i j k l, |F i j k l| ≤ B) (i j k l : Fin m) :
    |finiteFourIndexChange A F i j k l - F i j k l| ≤ (m : ℝ)^4 * (32 * eta * B) := by
  classical
  let I : Fin m → Fin m → ℝ := fun a b => if a = b then 1 else 0
  have hI (a b : Fin m) : |I a b| ≤ 2 := by dsimp [I]; split_ifs <;> norm_num
  have hc (p q r s : Fin m) :
      |((A i p*A j q)*(A k r*A l s) - (I i p*I j q)*(I k r*I l s)) * F p q r s| ≤ 32*eta*B := by
    rw [abs_mul]
    exact mul_le_mul
      (product_four_perturb (hA j q) (hA k r) (hA l s)
        (hI i p) (hI j q) (hI k r) he
        (hnear i p) (hnear j q) (hnear k r) (hnear l s))
      (hF p q r s) (abs_nonneg _) (by positivity)
  rw [← finiteFourIndexChange_identity F i j k l]
  change |finiteFourIndexChange A F i j k l - finiteFourIndexChange I F i j k l| ≤ _
  unfold finiteFourIndexChange
  simp only [← Finset.sum_sub_distrib, ← sub_mul]
  calc
    _ ≤ ∑ p, ∑ q, ∑ r, ∑ s,
        |((A i p*A j q)*(A k r*A l s) - (I i p*I j q)*(I k r*I l s)) * F p q r s| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro p _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro q _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro r _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin m, ∑ _q : Fin m, ∑ _r : Fin m, ∑ _s : Fin m, 32*eta*B :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ =>
        Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun s _ => hc p q r s))))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end ContinuumCoulomb

end

end OAI
