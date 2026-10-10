import OAI.Algebra.AuslanderReiten.Ext.TExplicitGenerator

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)
variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD
variable (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q)
include hq hq1 h

def tPMul (n : ℕ) : TSelfExt q n →ₗ[k] TSelfExt q (n + 3) :=
  Abelian.Ext.bilinearCompOfLinear k S S S 3 n (n + 3) (by omega) (tExplicitP q)

def tPMulEquiv (n : ℕ) : TSelfExt q n ≃ₗ[k] TSelfExt q (n + 3) :=
  LinearEquiv.ofBijective (tPMul q n) (tExplicitP_multiply_bijective q hq hq1 h n)

def tExplicitCoefficientEquiv : (n : ℕ) → k ≃ₗ[k] TSelfExt q (3 * n)
  | 0 => tSimpleExtZeroEquiv q hq1
  | n + 1 => (tExplicitCoefficientEquiv n).trans (tPMulEquiv q hq hq1 h (3 * n))

def tExplicitPower (n : ℕ) : TSelfExt q (3 * n) := tExplicitCoefficientEquiv q hq hq1 h n 1

@[simp] theorem tExplicitPower_zero : tExplicitPower q hq hq1 h 0 = Abelian.Ext.mk₀ (𝟙 S) :=
  tSimpleExtZeroEquiv_one q hq1

@[simp] theorem tExplicitPower_succ (n : ℕ) :
    tExplicitPower q hq hq1 h (n + 1) =
      (tExplicitP q).comp (tExplicitPower q hq hq1 h n) (by omega) := rfl

theorem tExplicitPower_ne_zero (n : ℕ) : tExplicitPower q hq hq1 h n ≠ 0 := by
  intro hz
  have hh : (1 : k) = 0 := (tExplicitCoefficientEquiv q hq hq1 h n).injective
    (hz.trans (map_zero _).symm)
  exact one_ne_zero hh

theorem tExplicit_coefficient (n : ℕ) (x : TSelfExt q (3 * n)) :
    ∃! a : k, a • tExplicitPower q hq hq1 h n = x := by
  let e := tExplicitCoefficientEquiv q hq hq1 h n
  refine ⟨e.symm x, ?_, ?_⟩
  · change e.symm x • e 1 = x
    rw [← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]
  · intro a ha
    apply e.injective
    rw [e.apply_symm_apply]
    have he : e a = a • e 1 := by simpa using e.map_smul a (1 : k)
    exact he.trans ha

theorem tExplicit_zero_of_not_dvd (n : ℕ) (hn : ¬ 3 ∣ n) (x : TSelfExt q n) : x = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn3 : n < 3
    · exact tSelfExt_low_zero q hq hq1 h n (by omega) hn3 x
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      obtain ⟨y, rfl⟩ := (tExplicitP_multiply_bijective q hq hq1 h m).surjective x
      have hm : ¬ 3 ∣ m := by
        intro hm
        exact hn (dvd_add hm (dvd_refl 3))
      rw [ih m (by omega) hm y]
      exact Abelian.Ext.comp_zero _ _ _ _ _

private theorem tExplicitPower_mul_aux (n m r : ℕ) (hr : n + m = r) :
    (tExplicitPower q hq hq1 h n).comp (tExplicitPower q hq hq1 h m)
      (by omega : 3 * n + 3 * m = 3 * r) = tExplicitPower q hq hq1 h r := by
  induction n generalizing r with
  | zero =>
    obtain rfl : r = m := by omega
    rw [tExplicitPower_zero]
    exact Abelian.Ext.mk₀_id_comp _
  | succ n ih =>
    obtain rfl : r = (n + m) + 1 := by omega
    rw [tExplicitPower_succ, tExplicitPower_succ]
    rw [Abelian.Ext.comp_assoc (tExplicitP q) (tExplicitPower q hq hq1 h n)
      (tExplicitPower q hq hq1 h m) (by omega) (by omega : 3 * n + 3 * m = 3 * (n + m)) (by omega)]
    rw [ih (n + m) rfl]

theorem tExplicitPower_mul (n m : ℕ) :
    (tExplicitPower q hq hq1 h n).comp (tExplicitPower q hq hq1 h m)
      (by omega : 3 * n + 3 * m = 3 * (n + m)) = tExplicitPower q hq hq1 h (n + m) :=
  tExplicitPower_mul_aux q hq hq1 h n m (n + m) rfl

end ArExplicit.Resolution

end

end OAI
