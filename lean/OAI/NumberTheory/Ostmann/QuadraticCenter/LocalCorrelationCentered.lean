import OAI.NumberTheory.Ostmann.QuadraticCenter.Amplifier
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationBound

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

theorem norm_unitaryDFT_le_sqrt {d : ℕ} [NeZero d]
    (f : ZMod d → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (v : ZMod d) :
    ‖Supply.unitaryDFT f v‖ ≤ Real.sqrt d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hsum : ‖ZMod.dft f v‖ ≤ d := by
    rw [ZMod.dft_apply]
    calc
      _ ≤ ∑ x : ZMod d, ‖ZMod.stdAddChar (-(x * v)) * f x‖ := norm_sum_le _ _
      _ ≤ ∑ x : ZMod d, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        rw [norm_mul, show ‖ZMod.stdAddChar (-(x * v))‖ = 1 from Circle.norm_coe _, one_mul]
        exact hf x
      _ = _ := by simp
  rw [Supply.unitaryDFT, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  simpa only [← pow_two, Real.sq_sqrt hd.le] using hsum

theorem norm_centeredIndicator_le_one {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p) :
    ‖(Supply.centeredIndicator S x : ℂ)‖ ≤ 1 := by
  have hd := residue_density_bounds S
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  unfold Supply.centeredIndicator
  split_ifs <;> constructor <;> linarith

def centeredProduct {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (x : ZMod (∏ i, p i)) : ℂ :=
  ∏ i, (Supply.centeredIndicator (S i) (ZMod.prodEquivPi p hcop x i) : ℂ)

theorem norm_centeredProduct_le_one {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (x : ZMod (∏ i, p i)) :
    ‖centeredProduct p hcop S x‖ ≤ 1 := by
  unfold centeredProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ _i : ι, (1 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => norm_centeredIndicator_le_one (S i) _)
    _ = 1 := by simp

def centeredProductTransform {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) : ZMod (∏ i, p i) → ℂ :=
  Supply.unitaryDFT (centeredProduct p hcop S)

theorem norm_centeredProductTransform_le_sqrt {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (v : ZMod (∏ i, p i)) :
    ‖centeredProductTransform p hcop S v‖ ≤ Real.sqrt ((∏ i, p i : ℕ) : ℝ) := by
  exact norm_unitaryDFT_le_sqrt _ (norm_centeredProduct_le_one p hcop S) v

end Ostmann.QuadraticCenter

end

end OAI
