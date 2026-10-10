import Mathlib.Data.ZMod.QuotientRing
import OAI.NumberTheory.Ostmann.Supply.Fourier

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def amplifier {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ) (x : ZMod (∏ i, p i)) : ℝ :=
  ∏ i, (1 + lam * Supply.centeredIndicator (S i) (ZMod.prodEquivPi p hcop x i))

theorem sum_amplifier_factor {p : ℕ} [NeZero p] (S : Finset (ZMod p)) (lam : ℝ) :
    (∑ x : ZMod p, (1 + lam * Supply.centeredIndicator S x)) = (p : ℝ) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Supply.sum_centeredIndicator]
  simp

theorem sum_amplifier {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, NeZero (p i)]
    [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ) :
    (∑ x : ZMod (∏ i, p i), amplifier p hcop S lam x) = ((∏ i, p i : ℕ) : ℝ) := by
  classical
  calc
    _ = ∑ x : (∀ i, ZMod (p i)), ∏ i, (1 + lam * Supply.centeredIndicator (S i) (x i)) :=
      Fintype.sum_equiv (ZMod.prodEquivPi p hcop).toEquiv _ _ (fun _ => rfl)
    _ = ∏ i, ∑ x : ZMod (p i), (1 + lam * Supply.centeredIndicator (S i) x) :=
      (Fintype.prod_sum (κ := fun i => ZMod (p i))
        (fun i x => 1 + lam * Supply.centeredIndicator (S i) x)).symm
    _ = _ := by simp only [sum_amplifier_factor, Nat.cast_prod]

theorem residue_density_bounds {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    0 ≤ Supply.density S ∧ Supply.density S ≤ 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Nat.pos_of_neZero p)
  simp only [Supply.density, ZMod.card]
  refine ⟨by positivity, (div_le_one hp).mpr ?_⟩
  exact_mod_cast (show S.card ≤ p by simpa using S.card_le_univ)

theorem amplifier_factor_pos {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) (x : ZMod p) :
    0 < 1 + lam * Supply.centeredIndicator S x := by
  have hd := residue_density_bounds S
  unfold Supply.centeredIndicator
  split_ifs <;> nlinarith [mul_nonneg hlam hd.1, mul_nonneg hlam (sub_nonneg.mpr hd.2)]

theorem amplifier_pos {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (x : ZMod (∏ i, p i)) : 0 < amplifier p hcop S lam x := by
  exact Finset.prod_pos (fun i _ => amplifier_factor_pos (S i) hlam hlam1 _)

theorem amplifier_lower_on_support {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam c : ℝ} (hlam : 0 ≤ lam) (hc : 0 ≤ c)
    (hbal : ∀ i, Supply.density (S i) ≤ 1 - c)
    (x : ZMod (∏ i, p i)) (hx : ∀ i, ZMod.prodEquivPi p hcop x i ∈ S i) :
    (1 + lam * c) ^ Fintype.card ι ≤ amplifier p hcop S lam x := by
  have he : (1 + lam * c) ^ Fintype.card ι = ∏ i : ι, (1 + lam * c) := by simp
  rw [he]
  unfold amplifier
  apply Finset.prod_le_prod₀
  · intro i hi
    positivity
  · intro i hi
    simp only [Supply.centeredIndicator, ite_eq_left (hx i)]
    have hm := mul_le_mul_of_nonneg_left (hbal i) hlam
    linarith

end Ostmann.QuadraticCenter

end

end OAI
