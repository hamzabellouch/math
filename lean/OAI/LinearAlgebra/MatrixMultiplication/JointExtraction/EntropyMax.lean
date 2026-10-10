import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity
import Mathlib.Tactic.Linarith

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.JointEntropyMax

theorem entropy_nonneg {A : Type*} [Fintype A] (p : FiniteLaw A) :
    0 ≤ finiteEntropy p.mass :=
  FiniteLaw.entropy_nonneg p

theorem map_entropy_le {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (f : A → B) :
    finiteEntropy (p.map f).mass ≤ finiteEntropy p.mass :=
  FiniteLaw.map_entropy_le p f

theorem entropy_sub_map_nonneg {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (f : A → B) :
    0 ≤ finiteEntropy p.mass - finiteEntropy (p.map f).mass :=
  sub_nonneg.mpr (map_entropy_le p f)

theorem entropyTerm_le_crossEntropyTerm {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    entropyTerm q ≤ -q * Real.log p + p - q := by
  by_cases hzero : q = 0
  · simpa [hzero] using hp.le
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp hqpos)
  rw [Real.log_div hp.ne' hqpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hq
  have hcancel : q * (p / q - 1) = p - q := by
    field_simp
  rw [hcancel] at hmul
  unfold entropyTerm
  linarith

theorem entropy_le_crossEntropy {A : Type*} [Fintype A]
    (p q : FiniteLaw A) (hp : ∀ a, 0 < p.mass a) :
    finiteEntropy q.mass ≤ ∑ a, -q.mass a * Real.log (p.mass a) := by
  calc
    finiteEntropy q.mass ≤
        ∑ a, (-q.mass a * Real.log (p.mass a) + p.mass a - q.mass a) :=
      Finset.sum_le_sum fun a _ => entropyTerm_le_crossEntropyTerm (hp a) (q.nonneg a)
    _ = ∑ a, -q.mass a * Real.log (p.mass a) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, p.total, q.total]
      ring

theorem sum_mass_mul_coordinate {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (f : A → B) (v : B → ℝ) :
    (∑ a, p.mass a * v (f a)) = ∑ b, (p.map f).mass b * v b := by
  classical
  simp_rw [FiniteLaw.map_mass, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem sum_mass_mul_coordinate_eq {A B : Type*} [Fintype A] [Fintype B]
    (p q : FiniteLaw A) (f : A → B) (v : B → ℝ)
    (hmarginal : (q.map f).mass = (p.map f).mass) :
    (∑ a, q.mass a * v (f a)) = ∑ a, p.mass a * v (f a) := by
  rw [sum_mass_mul_coordinate q f v, sum_mass_mul_coordinate p f v, hmarginal]

theorem entropy_le_of_three_marginals
    {A X Y Z : Type*} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    (p q : FiniteLaw A) (fX : A → X) (fY : A → Y) (fZ : A → Z)
    (u : X → ℝ) (v : Y → ℝ) (w : Z → ℝ) (c : ℝ)
    (hp : ∀ a, 0 < p.mass a)
    (hlog : ∀ a, Real.log (p.mass a) = u (fX a) + v (fY a) + w (fZ a) - c)
    (hX : (q.map fX).mass = (p.map fX).mass)
    (hY : (q.map fY).mass = (p.map fY).mass)
    (hZ : (q.map fZ).mass = (p.map fZ).mass) :
    finiteEntropy q.mass ≤ finiteEntropy p.mass := by
  have hx := sum_mass_mul_coordinate_eq p q fX u hX
  have hy := sum_mass_mul_coordinate_eq p q fY v hY
  have hz := sum_mass_mul_coordinate_eq p q fZ w hZ
  have hexpand (r : FiniteLaw A) :
      (∑ a, r.mass a * (u (fX a) + v (fY a) + w (fZ a) - c)) =
        (∑ a, r.mass a * u (fX a)) + (∑ a, r.mass a * v (fY a)) +
          (∑ a, r.mass a * w (fZ a)) - c := by
    simp_rw [mul_sub, mul_add]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, r.total, one_mul]
  have hexpect : (∑ a, q.mass a * Real.log (p.mass a)) =
      ∑ a, p.mass a * Real.log (p.mass a) := by
    simp_rw [hlog]
    rw [hexpand q, hexpand p, hx, hy, hz]
  calc
    finiteEntropy q.mass ≤ ∑ a, -q.mass a * Real.log (p.mass a) :=
      entropy_le_crossEntropy p q hp
    _ = -(∑ a, q.mass a * Real.log (p.mass a)) := by
      simp only [neg_mul, Finset.sum_neg_distrib]
    _ = -(∑ a, p.mass a * Real.log (p.mass a)) := by rw [hexpect]
    _ = finiteEntropy p.mass := by
      simp only [finiteEntropy, entropyTerm, neg_mul, Finset.sum_neg_distrib]

def normalizedPositiveLaw {A : Type*} [Fintype A] [Nonempty A]
    (weight : A → ℝ) (hweight : ∀ a, 0 < weight a) : FiniteLaw A where
  mass a := weight a / ∑ b, weight b
  nonneg a := div_nonneg (hweight a).le
    (Finset.sum_nonneg fun b _ => (hweight b).le)
  total := by
    have htotal : 0 < ∑ b, weight b :=
      Finset.sum_pos (fun b _ => hweight b) Finset.univ_nonempty
    rw [← Finset.sum_div, div_self htotal.ne']

theorem normalizedPositiveLaw_mass_pos {A : Type*} [Fintype A] [Nonempty A]
    (weight : A → ℝ) (hweight : ∀ a, 0 < weight a) (a : A) :
    0 < (normalizedPositiveLaw weight hweight).mass a := by
  exact div_pos (hweight a)
    (Finset.sum_pos (fun b _ => hweight b) Finset.univ_nonempty)

theorem entropy_le_normalized_product
    {A X Y Z : Type*} [Fintype A] [Nonempty A]
    [Fintype X] [Fintype Y] [Fintype Z]
    (fX : A → X) (fY : A → Y) (fZ : A → Z)
    (wx : X → ℝ) (wy : Y → ℝ) (wz : Z → ℝ)
    (hx : ∀ x, 0 < wx x) (hy : ∀ y, 0 < wy y) (hz : ∀ z, 0 < wz z)
    (q : FiniteLaw A)
    (hX : (q.map fX).mass =
      ((normalizedPositiveLaw (fun a => wx (fX a) * wy (fY a) * wz (fZ a))
        (fun _ => mul_pos (mul_pos (hx _) (hy _)) (hz _))).map fX).mass)
    (hY : (q.map fY).mass =
      ((normalizedPositiveLaw (fun a => wx (fX a) * wy (fY a) * wz (fZ a))
        (fun _ => mul_pos (mul_pos (hx _) (hy _)) (hz _))).map fY).mass)
    (hZ : (q.map fZ).mass =
      ((normalizedPositiveLaw (fun a => wx (fX a) * wy (fY a) * wz (fZ a))
        (fun _ => mul_pos (mul_pos (hx _) (hy _)) (hz _))).map fZ).mass) :
    finiteEntropy q.mass ≤
      finiteEntropy (normalizedPositiveLaw
        (fun a => wx (fX a) * wy (fY a) * wz (fZ a))
        (fun _ => mul_pos (mul_pos (hx _) (hy _)) (hz _))).mass := by
  let weight : A → ℝ := fun a => wx (fX a) * wy (fY a) * wz (fZ a)
  have hweight : ∀ a, 0 < weight a := fun a => mul_pos (mul_pos (hx _) (hy _)) (hz _)
  let p := normalizedPositiveLaw weight hweight
  have htotal : 0 < ∑ a, weight a :=
    Finset.sum_pos (fun a _ => hweight a) Finset.univ_nonempty
  apply entropy_le_of_three_marginals p q fX fY fZ
    (fun x => Real.log (wx x)) (fun y => Real.log (wy y))
    (fun z => Real.log (wz z)) (Real.log (∑ a, weight a))
    (normalizedPositiveLaw_mass_pos weight hweight)
  · intro a
    change Real.log (weight a / ∑ b, weight b) = _
    rw [Real.log_div (hweight a).ne' htotal.ne']
    dsimp only [weight]
    rw [Real.log_mul (mul_pos (hx _) (hy _)).ne' (hz _).ne',
      Real.log_mul (hx _).ne' (hy _).ne']
  · exact hX
  · exact hY
  · exact hZ

end MatrixMultiplication.JointEntropyMax

end

end OAI
