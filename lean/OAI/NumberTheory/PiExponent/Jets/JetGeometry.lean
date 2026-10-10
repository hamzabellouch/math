import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPowerSeries.Order

namespace OAI

namespace PiExponent.JetGeometry

noncomputable section

open MvPowerSeries

variable {σ R : Type*} [CommRing R]

def weightedIdeal (w : σ → ℕ) (N : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {f | (N : ℕ∞) ≤ f.weightedOrder w}
  zero_mem' := by simp
  add_mem' hf hg := (le_min hf hg).trans (min_weightedOrder_le_add w)
  smul_mem' a f hf := by
    change (N : ℕ∞) ≤ weightedOrder w (a * f)
    exact hf.trans (le_add_self.trans (le_weightedOrder_mul w))

@[simp] theorem mem_weightedIdeal (w : σ → ℕ) (N : ℕ)
    (f : MvPowerSeries σ R) :
    f ∈ weightedIdeal w N ↔ (N : ℕ∞) ≤ f.weightedOrder w := Iff.rfl

theorem mem_weightedIdeal_iff (w : σ → ℕ) (N : ℕ)
    (f : MvPowerSeries σ R) :
    f ∈ weightedIdeal w N ↔ ∀ d, Finsupp.weight w d < N → coeff d f = 0 := by
  constructor
  · intro hf d hd
    have hd' : (Finsupp.weight w d : ℕ∞) < (N : ℕ∞) := by exact_mod_cast hd
    exact coeff_eq_zero_of_lt_weightedOrder w (hd'.trans_le hf)
  · intro hf
    exact nat_le_weightedOrder w hf

theorem weightedIdeal_mul_le (w : σ → ℕ) (M N : ℕ) :
    (weightedIdeal w M : Ideal (MvPowerSeries σ R)) * weightedIdeal w N ≤
      weightedIdeal w (M + N) := by
  apply Ideal.mul_le.mpr
  intro f hf g hg
  change ((M + N : ℕ) : ℕ∞) ≤ weightedOrder w (f * g)
  rw [Nat.cast_add]
  exact (add_le_add hf hg).trans (le_weightedOrder_mul w)

theorem ideal_pow_le_weightedIdeal (w : σ → ℕ) (I : Ideal (MvPowerSeries σ R))
    (R₀ : ℕ) (hI : I ≤ weightedIdeal w R₀) (n : ℕ) :
    I ^ n ≤ weightedIdeal w (n * R₀) := by
  induction n with
  | zero =>
      intro f hf
      change ((0 * R₀ : ℕ) : ℕ∞) ≤ weightedOrder w f
      simp
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      apply Ideal.mul_le.mpr
      intro f hf g hg
      exact (Ideal.mul_le.mp (weightedIdeal_mul_le w (n * R₀) R₀)) f (ih hf) g (hI hg)

def coordinatePowerIdeal (e : σ → ℕ) : Ideal (MvPowerSeries σ R) :=
  Ideal.span (Set.range (fun i => (X i : MvPowerSeries σ R) ^ e i))

theorem X_pow_mem_weightedIdeal (w e : σ → ℕ) (R₀ : ℕ)
    (he : ∀ i, R₀ ≤ e i * w i) (i : σ) :
    (X i : MvPowerSeries σ R) ^ e i ∈ weightedIdeal w R₀ := by
  classical
  apply (mem_weightedIdeal_iff w R₀ _).mpr
  intro d hd
  rw [coeff_X_pow]
  split_ifs with h
  · subst d
    have hweight : Finsupp.weight w (Finsupp.single i (e i)) = e i * w i := by
      simp [Finsupp.weight]
    rw [hweight] at hd
    exact False.elim ((not_lt_of_ge (he i)) hd)
  · rfl

theorem coordinatePowerIdeal_pow_le (w e : σ → ℕ) (R₀ : ℕ)
    (he : ∀ i, R₀ ≤ e i * w i) (n : ℕ) :
    (coordinatePowerIdeal e : Ideal (MvPowerSeries σ R)) ^ n ≤
      weightedIdeal w (n * R₀) := by
  apply ideal_pow_le_weightedIdeal w _ R₀ _ n
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact X_pow_mem_weightedIdeal w e R₀ he i

theorem quotient_surjective_of_le {A α : Type*} [CommRing A]
    (I J : Ideal A) (hIJ : I ≤ J) (f : α → A)
    (hf : Function.Surjective (fun a => Ideal.Quotient.mk I (f a))) :
    Function.Surjective (fun a => Ideal.Quotient.mk J (f a)) := by
  intro y
  obtain ⟨x, hx⟩ := Ideal.Quotient.factor_surjective hIJ y
  obtain ⟨a, ha⟩ := hf x
  refine ⟨a, ?_⟩
  rw [← hx, ← ha]
  exact (Ideal.Quotient.factor_mk hIJ (f a)).symm

def CoefficientPacket (w : σ → ℕ) (N : ℕ) :=
  {d : σ →₀ ℕ // Finsupp.weight w d < N} → R

def coefficientPacket (w : σ → ℕ) (N : ℕ) (f : MvPowerSeries σ R) :
    CoefficientPacket (R := R) w N := fun d => coeff d.val f

theorem coefficientPacket_surjective_of_quotient {α : Type*}
    (w : σ → ℕ) (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : I ≤ weightedIdeal w N) (f : α → MvPowerSeries σ R)
    (hf : Function.Surjective (fun a => Ideal.Quotient.mk I (f a))) :
    Function.Surjective (fun a => coefficientPacket w N (f a)) := by
  classical
  intro packet
  let F : MvPowerSeries σ R := fun d =>
    if hd : Finsupp.weight w d < N then packet ⟨d, hd⟩ else 0
  obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mk I F)
  have hdiff : f a - F ∈ weightedIdeal w N :=
    hI (Ideal.Quotient.eq.mp ha)
  refine ⟨a, ?_⟩
  funext d
  have hzero := (mem_weightedIdeal_iff w N (f a - F)).mp hdiff d.val d.property
  rw [map_sub, sub_eq_zero] at hzero
  change coeff d.val (f a) = packet d
  rw [hzero]
  change (if hd : Finsupp.weight w d.val < N then packet ⟨d.val, hd⟩ else 0) = packet d
  simp only [dite_eq_left d.property]

theorem coefficientPacket_surjective_of_coordinatePowerIdeal {α : Type*}
    (w e : σ → ℕ) (R₀ : ℕ) (he : ∀ i, R₀ ≤ e i * w i)
    (n : ℕ) (f : α → MvPowerSeries σ R)
    (hf : Function.Surjective (fun a =>
      Ideal.Quotient.mk ((coordinatePowerIdeal e : Ideal (MvPowerSeries σ R)) ^ n) (f a))) :
    Function.Surjective (fun a => coefficientPacket w (n * R₀) (f a)) :=
  coefficientPacket_surjective_of_quotient w (n * R₀) _
    (coordinatePowerIdeal_pow_le w e R₀ he n) f hf

theorem rational_weight_nonneg (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (d : σ →₀ ℕ) : 0 ≤ Finsupp.weight v d := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_nonneg (fun i _ => nsmul_nonneg (hv i) (d i))

def rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ) :
    Ideal (MvPowerSeries σ R) where
  carrier := {f | ∀ d, Finsupp.weight v d < H → coeff d f = 0}
  zero_mem' := by simp
  add_mem' hf hg := by
    intro d hd
    rw [map_add, hf d hd, hg d hd, add_zero]
  smul_mem' a f hf := by
    classical
    intro d hd
    change coeff d (a * f) = 0
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have he : ij.1 + ij.2 = d := Finset.mem_antidiagonal.mp hij
    have hw : Finsupp.weight v ij.2 ≤ Finsupp.weight v d := by
      rw [← he, map_add]
      exact le_add_of_nonneg_left (rational_weight_nonneg v hv ij.1)
    rw [hf ij.2 (hw.trans_lt hd), mul_zero]

@[simp] theorem mem_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries σ R) :
    f ∈ rationalWeightedIdeal v hv H ↔
      ∀ d, Finsupp.weight v d < H → coeff d f = 0 := Iff.rfl

theorem rationalWeightedIdeal_mul_le (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (H K : ℚ) :
    (rationalWeightedIdeal v hv H : Ideal (MvPowerSeries σ R)) *
      rationalWeightedIdeal v hv K ≤ rationalWeightedIdeal v hv (H + K) := by
  classical
  apply Ideal.mul_le.mpr
  intro f hf g hg d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he : ij.1 + ij.2 = d := Finset.mem_antidiagonal.mp hij
  by_cases hfirst : Finsupp.weight v ij.1 < H
  · rw [hf ij.1 hfirst, zero_mul]
  · have hsecond : Finsupp.weight v ij.2 < K := by
      apply lt_of_not_ge
      intro hsecond
      have hsum := add_le_add (le_of_not_gt hfirst) hsecond
      rw [← map_add, he] at hsum
      exact (not_le_of_gt hd) hsum
    rw [hg ij.2 hsecond, mul_zero]

theorem ideal_pow_le_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (I : Ideal (MvPowerSeries σ R)) (H : ℚ)
    (hI : I ≤ rationalWeightedIdeal v hv H) (n : ℕ) :
    I ^ n ≤ rationalWeightedIdeal v hv (n * H) := by
  induction n with
  | zero =>
      intro f hf d hd
      have hzero := rational_weight_nonneg v hv d
      simp only [Nat.cast_zero, zero_mul] at hd
      exact False.elim ((not_lt_of_ge hzero) hd)
  | succ n ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      apply Ideal.mul_le.mpr
      intro f hf g hg
      exact (Ideal.mul_le.mp (rationalWeightedIdeal_mul_le v hv (n * H) H))
        f (ih hf) g (hI hg)

theorem coordinatePowerIdeal_pow_le_rational (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (e : σ → ℕ) (H : ℚ) (he : ∀ i, H ≤ (e i : ℚ) * v i) (n : ℕ) :
    (coordinatePowerIdeal e : Ideal (MvPowerSeries σ R)) ^ n ≤
      rationalWeightedIdeal v hv (n * H) := by
  classical
  apply ideal_pow_le_rationalWeightedIdeal v hv _ H _ n
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩ d hd
  rw [coeff_X_pow]
  split_ifs with h
  · subst d
    rw [Finsupp.weight_single, nsmul_eq_mul] at hd
    exact False.elim ((not_lt_of_ge (he i)) hd)
  · rfl

def RationalCoefficientPacket (v : σ → ℚ) (H : ℚ) :=
  {d : σ →₀ ℕ // Finsupp.weight v d < H} → R

def rationalCoefficientPacket (v : σ → ℚ) (H : ℚ) (f : MvPowerSeries σ R) :
    RationalCoefficientPacket (R := R) v H := fun d => coeff d.val f

theorem rationalCoefficientPacket_surjective_of_coordinatePowerIdeal {α : Type*}
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (e : σ → ℕ) (H : ℚ)
    (he : ∀ i, H ≤ (e i : ℚ) * v i) (n : ℕ)
    (f : α → MvPowerSeries σ R)
    (hf : Function.Surjective (fun a =>
      Ideal.Quotient.mk ((coordinatePowerIdeal e : Ideal (MvPowerSeries σ R)) ^ n) (f a))) :
    Function.Surjective (fun a => rationalCoefficientPacket v (n * H) (f a)) := by
  classical
  intro packet
  let F : MvPowerSeries σ R := fun d =>
    if hd : Finsupp.weight v d < n * H then packet ⟨d, hd⟩ else 0
  obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mk _ F)
  have hdiff : f a - F ∈ rationalWeightedIdeal v hv (n * H) :=
    coordinatePowerIdeal_pow_le_rational v hv e H he n (Ideal.Quotient.eq.mp ha)
  refine ⟨a, ?_⟩
  funext d
  have hzero := hdiff d.val d.property
  rw [map_sub, sub_eq_zero] at hzero
  change coeff d.val (f a) = packet d
  rw [hzero]
  change (if hd : Finsupp.weight v d.val < n * H then packet ⟨d.val, hd⟩ else 0) = packet d
  simp only [dite_eq_left d.property]

theorem rationalCoefficientPackets_surjective_of_coordinatePowerIdeal {α J : Type*}
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (e : σ → ℕ) (H : ℚ)
    (he : ∀ i, H ≤ (e i : ℚ) * v i) (n : ℕ)
    (f : α → J → MvPowerSeries σ R)
    (hf : Function.Surjective (fun a j =>
      Ideal.Quotient.mk ((coordinatePowerIdeal e : Ideal (MvPowerSeries σ R)) ^ n) (f a j))) :
    Function.Surjective (fun a j => rationalCoefficientPacket v (n * H) (f a j)) := by
  classical
  intro packets
  let F : J → MvPowerSeries σ R := fun j d =>
    if hd : Finsupp.weight v d < n * H then packets j ⟨d, hd⟩ else 0
  obtain ⟨a, ha⟩ := hf (fun j => Ideal.Quotient.mk _ (F j))
  refine ⟨a, ?_⟩
  funext j d
  have hdiff : f a j - F j ∈ rationalWeightedIdeal v hv (n * H) :=
    coordinatePowerIdeal_pow_le_rational v hv e H he n
      (Ideal.Quotient.eq.mp (congrFun ha j))
  have hzero := hdiff d.val d.property
  rw [map_sub, sub_eq_zero] at hzero
  change coeff d.val (f a j) = packets j d
  rw [hzero]
  change (if hd : Finsupp.weight v d.val < n * H then packets j ⟨d.val, hd⟩ else 0) = packets j d
  simp only [dite_eq_left d.property]

end

end PiExponent.JetGeometry

end OAI
