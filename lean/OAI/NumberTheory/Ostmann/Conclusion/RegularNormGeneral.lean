import OAI.NumberTheory.Ostmann.Conclusion.RegularNormAP

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open scoped BigOperators
open Ostmann.Arithmetic.PrimeCellReplacement Ostmann.Arithmetic.PrimeProgression

def regularResidueTestValue {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (g : ∀ i, ZMod (p i) → ℂ) (a : ∀ i, ZMod (p i))
    (x : ∀ i, (ZMod (p i))ˣ) : ℝ :=
  ∏ i, ‖g i (a i*((x i : ZMod (p i))⁻¹))‖^2

theorem regularResidueTestValue_nonneg {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (g : ∀ i, ZMod (p i) → ℂ) (a : ∀ i, ZMod (p i)) (x) :
    0 ≤ regularResidueTestValue p g a x :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem prime_unit_norm_sum_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg0 : g 0 = 0)
    (hgnorm : ∑ x : ZMod p, ‖g x‖^2 = (p : ℝ)) (a : ZMod p) :
    ∑ x : (ZMod p)ˣ, ‖g (a*((x : ZMod p)⁻¹))‖^2 ≤ p := by
  by_cases ha : a=0
  · simp only [ha,zero_mul,hg0,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
    exact Nat.cast_nonneg p
  · let u : (ZMod p)ˣ := Units.mk0 a ha
    have hh := prime_unit_norm_sum g hg0 hgnorm u
    simpa only [u,Units.val_mul,Units.val_inv_eq_inv_val,Units.val_mk0] using hh.le

theorem regularResidueTestValue_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (hg0 : ∀ i, g i 0 = 0)
    (hgnorm : ∀ i, ∑ x : ZMod (p i), ‖g i x‖^2 = (p i : ℝ))
    (a : ∀ i, ZMod (p i)) :
    ∑ x : (∀ i, (ZMod (p i))ˣ), regularResidueTestValue p g a x ≤
      ((∏ i, p i : ℕ) : ℝ) := by
  unfold regularResidueTestValue
  rw [←Fintype.prod_sum (fun i (x : (ZMod (p i))ˣ) => ‖g i (a i*((x : ZMod (p i))⁻¹))‖^2)]
  simp only [Nat.cast_prod]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · intro i hi
    exact prime_unit_norm_sum_le (g i) (hg0 i) (hgnorm i) (a i)

theorem regularResidueTestValue_crt_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (hg0 : ∀ i, g i 0 = 0)
    (hgnorm : ∀ i, ∑ x : ZMod (p i), ‖g i x‖^2 = (p i : ℝ))
    (a : ∀ i, ZMod (p i)) :
    (∑ x : (ZMod (∏ i, p i))ˣ,
      regularResidueTestValue p g a (Ostmann.Supply.crtUnitsEquiv p hcop x)) ≤
        ((∏ i, p i : ℕ) : ℝ) := by
  exact ((Ostmann.Supply.crtUnitsEquiv p hcop).toEquiv.sum_comp _).le.trans
    (regularResidueTestValue_sum_le p g hg0 hgnorm a)

end Ostmann.Conclusion

end

end OAI
