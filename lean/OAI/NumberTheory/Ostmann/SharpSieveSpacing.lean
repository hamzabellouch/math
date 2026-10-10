import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Tactic

namespace OAI

namespace Ostmann.SharpSieve

theorem reduced_nat_fraction_cross_injective
    {a q b r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (ha : Nat.Coprime a q) (hb : Nat.Coprime b r)
    (h : a * r = b * q) : a = b ∧ q = r := by
  have hqr : q ∣ r := ha.symm.dvd_of_dvd_mul_left (by
    rw [h]
    exact dvd_mul_left q b)
  have hrq : r ∣ q := hb.symm.dvd_of_dvd_mul_left (by
    rw [← h]
    exact dvd_mul_left r a)
  have heq : q = r := Nat.dvd_antisymm hqr hrq
  subst r
  constructor
  · nlinarith
  · rfl

theorem reduced_nat_fraction_real_injective
    {a q b r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (ha : Nat.Coprime a q) (hb : Nat.Coprime b r)
    (h : (a : ℝ) / q = (b : ℝ) / r) : a = b ∧ q = r := by
  apply reduced_nat_fraction_cross_injective hq hr ha hb
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hcross := (div_eq_div_iff hq0 hr0).mp h
  exact_mod_cast hcross

theorem reduced_nat_fraction_rat_injective
    {a q b r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (ha : Nat.Coprime a q) (hb : Nat.Coprime b r)
    (h : (a : ℚ) / q = (b : ℚ) / r) : a = b ∧ q = r := by
  apply reduced_nat_fraction_cross_injective hq hr ha hb
  have hq0 : (q : ℚ) ≠ 0 := by positivity
  have hr0 : (r : ℚ) ≠ 0 := by positivity
  have hcross := (div_eq_div_iff hq0 hr0).mp h
  exact_mod_cast hcross

theorem rational_spacing_mod_one {Q a b q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (ha : a < q) (hb : b < r)
    (hne : (a : ℝ) / q ≠ (b : ℝ) / r) (k : ℤ) :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / q - (b : ℝ) / r - k| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hq.trans_le hqQ
  have hqR0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hrR0 : (r : ℝ) ≠ 0 := ne_of_gt hrR
  have hx0 : (0 : ℝ) ≤ (a : ℝ) / q := div_nonneg (Nat.cast_nonneg _) hqR.le
  have hy0 : (0 : ℝ) ≤ (b : ℝ) / r := div_nonneg (Nat.cast_nonneg _) hrR.le
  have hx1 : (a : ℝ) / q < 1 := (div_lt_one hqR).mpr (by exact_mod_cast ha)
  have hy1 : (b : ℝ) / r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast hb)
  let z : ℤ := (a : ℤ) * r - (b : ℤ) * q - k * q * r
  have hzR : (z : ℝ) = ((a : ℝ) / q - (b : ℝ) / r - k) * (q * r) := by
    dsimp [z]
    push_cast
    field_simp
  have hz : z ≠ 0 := by
    intro hz0
    have heq : (a : ℝ) / q - (b : ℝ) / r = k := by
      have hz0R : (z : ℝ) = 0 := by simp [hz0]
      rw [hzR] at hz0R
      have hsub := (mul_eq_zero.mp hz0R).resolve_right (mul_ne_zero hqR0 hrR0)
      linarith
    have hkltR : (-1 : ℝ) < k ∧ (k : ℝ) < 1 := by constructor <;> linarith
    have hklt : (-1 : ℤ) < k ∧ k < 1 := by exact_mod_cast hkltR
    have hk0 : k = 0 := by omega
    apply hne
    simpa [hk0, sub_eq_zero] using heq
  have hone : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz
  have hprod : (0 : ℝ) < q * r := mul_pos hqR hrR
  have hden : (q : ℝ) * r ≤ (Q : ℝ) ^ 2 := by
    have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hrQR : (r : ℝ) ≤ Q := by exact_mod_cast hrQ
    nlinarith
  calc
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * r) :=
      one_div_le_one_div_of_le hprod hden
    _ ≤ |(a : ℝ) / q - (b : ℝ) / r - k| := by
      apply (div_le_iff₀ hprod).mpr
      simpa only [hzR, abs_mul, abs_of_pos hprod] using hone

theorem rational_spacing_circle {Q a b q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (ha : a < q) (hb : b < r)
    (hne : (a : ℝ) / q ≠ (b : ℝ) / r) :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤
      dist (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ))
        (((b : ℝ) / r : ℝ) : AddCircle (1 : ℝ)) := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, AddCircle.norm_eq]
  simpa only [inv_one, one_mul, mul_one] using
    rational_spacing_mod_one hq hr hqQ hrQ ha hb hne
      (round ((a : ℝ) / q - (b : ℝ) / r))

def ReducedFrequency (Q : ℕ) :=
  {p : ℕ × ℕ // 0 < p.1 ∧ p.1 ≤ Q ∧ p.2 < p.1 ∧ Nat.Coprime p.2 p.1}

instance (Q : ℕ) : Fintype (ReducedFrequency Q) := by
  change Fintype {p : ℕ × ℕ | 0 < p.1 ∧ p.1 ≤ Q ∧ p.2 < p.1 ∧ Nat.Coprime p.2 p.1}
  apply Fintype.ofFinset
    (((Finset.range (Q + 1)).product (Finset.range (Q + 1))).filter
      (fun p => 0 < p.1 ∧ p.1 ≤ Q ∧ p.2 < p.1 ∧ Nat.Coprime p.2 p.1))
  intro p
  simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.2
  · intro hp
    exact ⟨⟨by omega, by omega⟩, hp⟩

namespace ReducedFrequency

def denominator {Q : ℕ} (f : ReducedFrequency Q) : ℕ := f.val.1

def numerator {Q : ℕ} (f : ReducedFrequency Q) : ℕ := f.val.2

noncomputable def value {Q : ℕ} (f : ReducedFrequency Q) : ℝ :=
  (f.numerator : ℝ) / f.denominator

noncomputable def point {Q : ℕ} (f : ReducedFrequency Q) : AddCircle (1 : ℝ) :=
  (f.value : AddCircle (1 : ℝ))

theorem denominator_pos {Q : ℕ} (f : ReducedFrequency Q) : 0 < f.denominator := f.property.1

theorem denominator_le {Q : ℕ} (f : ReducedFrequency Q) : f.denominator ≤ Q := f.property.2.1

theorem numerator_lt {Q : ℕ} (f : ReducedFrequency Q) : f.numerator < f.denominator :=
  f.property.2.2.1

theorem coprime {Q : ℕ} (f : ReducedFrequency Q) : Nat.Coprime f.numerator f.denominator :=
  f.property.2.2.2

theorem value_nonneg {Q : ℕ} (f : ReducedFrequency Q) : 0 ≤ f.value := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem value_lt_one {Q : ℕ} (f : ReducedFrequency Q) : f.value < 1 := by
  exact (div_lt_one (by exact_mod_cast f.denominator_pos)).mpr
    (by exact_mod_cast f.numerator_lt)

theorem value_injective {Q : ℕ} : Function.Injective (@value Q) := by
  intro f g h
  obtain ⟨hnum, hden⟩ := reduced_nat_fraction_real_injective
    f.denominator_pos g.denominator_pos f.coprime g.coprime h
  apply Subtype.ext
  exact Prod.ext hden hnum

theorem mod_one_spacing {Q : ℕ} {f g : ReducedFrequency Q} (hfg : f ≠ g) (k : ℤ) :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤ |f.value - g.value - k| := by
  exact rational_spacing_mod_one f.denominator_pos g.denominator_pos
    f.denominator_le g.denominator_le f.numerator_lt g.numerator_lt
    (fun h => hfg (value_injective h)) k

theorem dist_spacing {Q : ℕ} {f g : ReducedFrequency Q} (hfg : f ≠ g) :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤ dist f.point g.point := by
  exact rational_spacing_circle f.denominator_pos g.denominator_pos
    f.denominator_le g.denominator_le f.numerator_lt g.numerator_lt
    (fun h => hfg (value_injective h))

theorem point_injective {Q : ℕ} : Function.Injective (@point Q) := by
  intro f g h
  by_contra hfg
  have hs := dist_spacing hfg
  rw [h, dist_self] at hs
  have hQ : (0 : ℝ) < Q := by exact_mod_cast f.denominator_pos.trans_le f.denominator_le
  have hp : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  linarith

theorem pairwise_dist (Q : ℕ) :
    Pairwise (fun f g : ReducedFrequency Q => (1 : ℝ) / (Q : ℝ) ^ 2 ≤ dist f.point g.point) := by
  intro f g hfg
  exact dist_spacing hfg

end ReducedFrequency
end Ostmann.SharpSieve

end OAI
