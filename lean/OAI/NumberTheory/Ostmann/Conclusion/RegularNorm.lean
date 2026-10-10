import OAI.NumberTheory.Ostmann.Arithmetic.ResidueHaar
import OAI.NumberTheory.Ostmann.Supply.CRTPrimitiveEnergy
import OAI.NumberTheory.Ostmann.Supply.FiniteParseval

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion

theorem sum_units_eq_sum {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (F : K → ℝ) (hzero : F 0 = 0) :
    ∑ u : Kˣ, F u = ∑ x : K, F x := by
  calc
    (∑ u : Kˣ, F u) = ∑ x : {x : K // x ≠ 0}, F x :=
      (unitsEquivNeZero : Kˣ ≃ {x : K // x ≠ 0}).sum_comp (fun x => F x)
    _ = ∑ x ∈ Finset.univ.erase (0 : K), F x :=
      (Finset.sum_subtype (Finset.univ.erase (0 : K)) (by simp) F).symm
    _ = ∑ x : K, F x := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x hx hn
      have hx0 : x = 0 := by simpa using hn
      simpa only [hx0] using hzero

theorem sum_unit_inverse_translate {G : Type*} [Group G] [Fintype G]
    (a : G) (F : G → ℝ) : ∑ x : G, F (a*x⁻¹) = ∑ x : G, F x := by
  exact ((Equiv.inv G).trans (Equiv.mulLeft a)).sum_comp F

theorem prime_unit_norm_sum {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg0 : g 0 = 0)
    (hgnorm : ∑ x : ZMod p, ‖g x‖^2 = (p : ℝ)) (a : (ZMod p)ˣ) :
    ∑ x : (ZMod p)ˣ, ‖g ((a*x⁻¹ : (ZMod p)ˣ) : ZMod p)‖^2 = p := by
  rw [sum_unit_inverse_translate a (fun x : (ZMod p)ˣ => ‖g (x : ZMod p)‖^2)]
  exact (sum_units_eq_sum (fun x => ‖g x‖^2) (by simp [hg0])).trans hgnorm

def regularResidueTest {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (g : ∀ i, ZMod (p i) → ℂ) (a x : ∀ i, (ZMod (p i))ˣ) : ℝ :=
  ∏ i, ‖g i ((a i*(x i)⁻¹ : (ZMod (p i))ˣ) : ZMod (p i))‖^2

theorem regularResidueTest_nonneg {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (g : ∀ i, ZMod (p i) → ℂ) (a x : ∀ i, (ZMod (p i))ˣ) :
    0 ≤ regularResidueTest p g a x := by
  exact Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem regularResidueTest_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
    (hg0 : ∀ i, g i 0 = 0)
    (hgnorm : ∀ i, ∑ x : ZMod (p i), ‖g i x‖^2 = (p i : ℝ))
    (a : ∀ i, (ZMod (p i))ˣ) :
    ∑ x : (∀ i, (ZMod (p i))ˣ), regularResidueTest p g a x = ∏ i, (p i : ℝ) := by
  unfold regularResidueTest
  calc
    _ = ∏ i, ∑ x : (ZMod (p i))ˣ,
        ‖g i ((a i*x⁻¹ : (ZMod (p i))ˣ) : ZMod (p i))‖^2 :=
      (Fintype.prod_sum (fun i (x : (ZMod (p i))ˣ) =>
        ‖g i ((a i*x⁻¹ : (ZMod (p i))ˣ) : ZMod (p i))‖^2)).symm
    _ = ∏ i, (p i : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact prime_unit_norm_sum (g i) (hg0 i) (hgnorm i) (a i)

theorem regularResidueTest_crt_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (hg0 : ∀ i, g i 0 = 0)
    (hgnorm : ∀ i, ∑ x : ZMod (p i), ‖g i x‖^2 = (p i : ℝ))
    (a : ∀ i, (ZMod (p i))ˣ) :
    ∑ x : (ZMod (∏ i, p i))ˣ,
      regularResidueTest p g a (Ostmann.Supply.crtUnitsEquiv p hcop x) =
        (∏ i, p i : ℕ) := by
  calc
    _ = ∑ x : (∀ i, (ZMod (p i))ˣ), regularResidueTest p g a x :=
      (Ostmann.Supply.crtUnitsEquiv p hcop).toEquiv.sum_comp _
    _ = ∏ i, (p i : ℝ) := regularResidueTest_sum p g hg0 hgnorm a
    _ = _ := by simp

theorem additiveTransform_unit_norm_sum {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hpos : 0 < Ostmann.Supply.density S)
    (hlt : Ostmann.Supply.density S < 1) (a : (ZMod p)ˣ) :
    ∑ x : (ZMod p)ˣ,
      ‖Ostmann.Supply.additiveTransform S ((a*x⁻¹ : (ZMod p)ˣ) : ZMod p)‖^2 = p :=
  prime_unit_norm_sum _ (Ostmann.Supply.additiveTransform_zero S)
    (Ostmann.Supply.additiveTransform_parseval S hpos hlt) a

theorem positive_residue_average_bound {ι : Type*} [Fintype ι]
    (F w : ι → ℝ) {C I φ ε Z : ℝ} (hF : ∀ i, 0 ≤ F i)
    (hsum : ∑ i, F i = C) (hZ : 0 < Z)
    (hw : ∀ i, w i ≤ 2*I/φ+ε) :
    (∑ i, w i*F i)/Z ≤ 2*(C/φ)*(I/Z)+C*ε/Z := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hw i) (hF i))
  rw [← Finset.mul_sum, hsum] at h
  calc
    (∑ i, w i*F i)/Z ≤ ((2*I/φ+ε)*C)/Z := div_le_div_of_nonneg_right h hZ.le
    _ = 2*(C/φ)*(I/Z)+C*ε/Z := by ring

theorem prime_ratio_product_le_exp {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, 2 ≤ p i) :
    ∏ i, ((p i : ℝ)/(p i-1)) ≤ Real.exp (∑ i, 1/((p i : ℝ)-1)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro i hi
    have h : (1 : ℝ) < p i := by exact_mod_cast (hp i)
    positivity
  · intro i hi
    have h : (1 : ℝ) < p i := by exact_mod_cast (hp i)
    have hden : (p i : ℝ)-1 ≠ 0 := by linarith
    have heq : (p i : ℝ)/(p i-1) = 1+1/((p i : ℝ)-1) := by field_simp; ring
    rw [heq]
    simpa [add_comm] using Real.add_one_le_exp (1/((p i : ℝ)-1))

end Ostmann.Conclusion

end

end OAI
