import OAI.NumberTheory.Ostmann.Arithmetic.MovingSplitModulusBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantBounds

namespace OAI

/-! # The full modulus of the actual sampled histories at the giant scale -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

private theorem list_nat_prod_exp_bound (s : List ℕ) (U : ℝ)
    (h : ∀ q ∈ s, (q : ℝ) ≤ Real.exp U) :
    (s.prod : ℝ) ≤ Real.exp (s.length * U) := by
  induction s with
  | nil => simp
  | cons q s ih =>
    simp only [List.prod_cons, List.length_cons, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ Real.exp U * Real.exp (s.length * U) :=
        mul_le_mul (h q (by simp)) (ih (fun q hq => h q (by simp [hq])))
          (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem movingSample_pair_modulus_bound {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (hout : 1 ≤ outside.prod)
    (childBound pivotBound : ℕ → ℕ) (n r₀ m P V : ℕ)
    (hP : 1 ≤ P) (hV : 1 ≤ V) (hvalueP : ∀ i, value i ≤ P)
    (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List σ) n)
    (samples : Bool → MovingSampleSlots σ n)
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r₀)
    (hbulk : ∀ b, MovingLeafLengthLE n (bulk b) m)
    (hf : ∀ b, (buildMovingSlotData n (t b) (small b) (bulk b) (samples b)).Frequencies (· ≠ 0))
    (hfreq : ∀ b, (buildMovingSlotData n (t b) (small b) (bulk b) (samples b)).Frequencies
      (fun s => s.natAbs ≤ V)) (q : I → ℕ) (S : Finset I) :
    movingFullPairModulus value hvalue outside childBound pivotBound
      (fun b => buildMovingSlotData n (t b) (small b) (bulk b) (samples b)) hf q S ≤
      ((V * P ^ (2 ^ n * (r₀ + m + 4 * n) + 4 * 2 ^ n) * outside.prod) ^
        movingFullModulusExponent n * ∏ i ∈ S, q i) ^ 4 := by
  let D := 2 ^ n * (r₀ + m + 4 * n)
  let K := V * P ^ (D + 4 * 2 ^ n) * outside.prod
  have hpow : 1 ≤ P ^ (D + 4 * 2 ^ n) := Nat.one_le_pow _ _ hP
  have hVK : V ≤ K := by
    change V ≤ V * P ^ (D + 4 * 2 ^ n) * outside.prod
    calc
      V = V * 1 * 1 := by simp
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left V hpow) hout
  have hPK : P ^ (D + 4 * 2 ^ n) ≤ K := by
    change P ^ (D + 4 * 2 ^ n) ≤ V * P ^ (D + 4 * 2 ^ n) * outside.prod
    calc
      _ = 1 * P ^ (D + 4 * 2 ^ n) * 1 := by simp
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hV) hout
  have hOK : outside.prod ≤ K := by
    change outside.prod ≤ V * P ^ (D + 4 * 2 ^ n) * outside.prod
    simpa only [one_mul] using Nat.mul_le_mul_right outside.prod (Nat.mul_le_mul hV hpow)
  apply movingFullPairModulus_bound value hvalue outside childBound pivotBound _ hf q S K
    (hV.trans hVK) (fun b => (hfreq b).mono (fun _ hs => hs.trans hVK))
  · intro b
    exact (buildMovingSlotData_compensation_bound value P hP hvalueP n (t b)
      (small b) (bulk b) (samples b)).mono value
      ((Nat.pow_le_pow_right hP (Nat.le_add_left _ _)).trans hPK)
  · intro b
    exact MovingSlotData.RegularBound.mono _ value
      (MovingSlotData.RegularLengthLE.product_bound _
        (buildMovingSlotData_regular_length n (t b) (small b) (bulk b) (samples b)
          r₀ m (hsmall b) (hbulk b)) value P hP hvalueP)
      ((Nat.pow_le_pow_right hP (Nat.le_add_right _ _)).trans hPK)
  · exact hOK

private theorem sampled_modulus_exponent_bound (n r₀ k : ℕ) (A L : ℝ)
    (hA : 0 ≤ A) (hL : 1 ≤ L) :
    let m := spectatorBulkCount k L
    let D : ℝ := (2 ^ n * (r₀ + m + 4 * n) + 4 * 2 ^ n : ℕ)
    let K : ℝ := (k : ℝ) ^ 4
    let D₀ : ℝ := (2 ^ n : ℕ) * (r₀ + K + 4 * n) + 4 * (2 ^ n : ℕ)
    4 * ((movingFullModulusExponent n : ℝ) *
      (A * m + D * Real.exp ((11 / 1000 : ℝ) * L) +
        m * Real.exp ((1 / 1000 : ℝ) * L)) + m * Real.exp ((1 / 1000 : ℝ) * L)) ≤
      (4 * ((movingFullModulusExponent n : ℝ) * (A * K + D₀ + K) + K)) *
        L * Real.exp ((11 / 1000 : ℝ) * L) := by
  dsimp only
  let K : ℝ := (k : ℝ) ^ 4
  let D₀ : ℝ := (2 ^ n : ℕ) * (r₀ + K + 4 * n) + 4 * (2 ^ n : ℕ)
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hm := spectatorBulkCount_upper k L hL0
  have hsmall : Real.exp ((1 / 1000 : ℝ) * L) ≤ Real.exp ((11 / 1000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith only [hL0])
  have hone : 1 ≤ Real.exp ((11 / 1000 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hD : ((2 ^ n * (r₀ + spectatorBulkCount k L + 4 * n) + 4 * 2 ^ n : ℕ) : ℝ) ≤ D₀ * L := by
    have hr := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg r₀ : (0 : ℝ) ≤ r₀)
    have hn := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 4 * n by positivity)
    have hfour := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 4 * (2 ^ n : ℕ) by positivity)
    have hadd : (r₀ : ℝ) + spectatorBulkCount k L + 4 * n ≤ ((r₀ : ℝ) + K + 4 * n) * L := by
      dsimp only [K]
      linarith only [hr, hn, hm]
    have hh := mul_le_mul_of_nonneg_left hadd (show (0 : ℝ) ≤ (2 ^ n : ℕ) by positivity)
    push_cast
    dsimp only [D₀]
    push_cast
    push_cast at hh hfour
    nlinarith only [hh, hfour]
  have hfreq : A * (spectatorBulkCount k L : ℝ) ≤ A * K * L * Real.exp ((11 / 1000 : ℝ) * L) := by
    apply (mul_le_mul_of_nonneg_left hm hA).trans
    simpa only [mul_assoc, K] using le_mul_of_one_le_right
      (show 0 ≤ A * ((k : ℝ) ^ 4 * L) by positivity) hone
  have hcomp := mul_le_mul_of_nonneg_right hD (Real.exp_nonneg ((11 / 1000 : ℝ) * L))
  have hspec : (spectatorBulkCount k L : ℝ) * Real.exp ((1 / 1000 : ℝ) * L) ≤
      K * L * Real.exp ((11 / 1000 : ℝ) * L) :=
    mul_le_mul hm hsmall (Real.exp_nonneg _) (by positivity)
  have hE : (0 : ℝ) ≤ movingFullModulusExponent n := Nat.cast_nonneg _
  dsimp only [D₀, K] at hcomp hfreq hspec ⊢
  nlinarith only [mul_le_mul_of_nonneg_left (add_le_add (add_le_add hfreq hcomp) hspec) hE, hspec]

/-- The cutoff is uniform in the actual histories and all sampled prime
values. It permits the full `.011` internal range and the original bulk size. -/
theorem movingSample_pair_modulus_giant_range (n r₀ k : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (σ : Type) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
        (outside : List ℕ) (P V : ℕ),
      1 ≤ outside.prod → outside.length ≤ m →
      (∀ q ∈ outside, (q : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      1 ≤ P → 1 ≤ V → (∀ i, value i ≤ P) →
      (P : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L)) →
      (V : ℝ) ≤ Real.exp (A * m) →
      ∀ (childBound pivotBound : ℕ → ℕ) (t : Bool → FrequencyTree ℤ n)
        (small bulk : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
        (hf : ∀ b, (buildMovingSlotData n (t b) (small b) (bulk b) (samples b)).Frequencies (· ≠ 0)),
      (∀ b, MovingLeafLengthLE n (small b) r₀) →
      (∀ b, MovingLeafLengthLE n (bulk b) m) →
      (∀ b, (buildMovingSlotData n (t b) (small b) (bulk b) (samples b)).Frequencies
        (fun s => s.natAbs ≤ V)) →
      ∀ p : Fin m → ℕ,
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      movingFullPairModulus value hvalue outside childBound pivotBound
        (fun b => buildMovingSlotData n (t b) (small b) (bulk b) (samples b)) hf p Finset.univ ≤
        giantProgressionCutoff L := by
  let K : ℝ := (k : ℝ) ^ 4
  let D₀ : ℝ := (2 ^ n : ℕ) * (r₀ + K + 4 * n) + 4 * (2 ^ n : ℕ)
  let C : ℝ := 4 * ((movingFullModulusExponent n : ℝ) * (A * K + D₀ + K) + K)
  have hC : 0 ≤ C := by dsimp only [C, D₀, K]; positivity
  filter_upwards [arithmetic_exponent_absorption (11 / 1000) (12 / 1000) 0 C 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  dsimp only
  intro σ value hvalue outside P V hout hlen houtP hP hV hvalueP hPexp hVexp
    childBound pivotBound t small bulk samples hf hsmall hbulk hfreq p hp
  let m := spectatorBulkCount k L
  let D := 2 ^ n * (r₀ + m + 4 * n) + 4 * 2 ^ n
  have houtExp : (outside.prod : ℝ) ≤ Real.exp (m * Real.exp ((1 / 1000 : ℝ) * L)) := by
    calc
      _ ≤ Real.exp (outside.length * Real.exp ((1 / 1000 : ℝ) * L)) := by
        exact list_nat_prod_exp_bound outside _ houtP
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr hlen) (Real.exp_nonneg _))
  have hpExp : ((∏ i, p i : ℕ) : ℝ) ≤ Real.exp (m * Real.exp ((1 / 1000 : ℝ) * L)) := by
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _i : Fin m, Real.exp (Real.exp ((1 / 1000 : ℝ) * L)) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hp i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  have hB : ((V * P ^ D * outside.prod : ℕ) : ℝ) ≤
      Real.exp (A * m + D * Real.exp ((11 / 1000 : ℝ) * L) +
        m * Real.exp ((1 / 1000 : ℝ) * L)) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
    calc
      _ ≤ (Real.exp (A * m) * Real.exp (Real.exp ((11 / 1000 : ℝ) * L)) ^ D) *
          Real.exp (m * Real.exp ((1 / 1000 : ℝ) * L)) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  apply Nat.le_floor
  have hb := movingSample_pair_modulus_bound value hvalue outside hout childBound pivotBound
    n r₀ m P V hP hV hvalueP t small bulk samples hsmall hbulk hf hfreq p Finset.univ
  have hb' : ((movingFullPairModulus value hvalue outside childBound pivotBound
      (fun b => buildMovingSlotData n (t b) (small b) (bulk b) (samples b)) hf p Finset.univ : ℕ) : ℝ) ≤
      (((V * P ^ D * outside.prod : ℕ) : ℝ) ^ movingFullModulusExponent n *
        ((∏ i, p i : ℕ) : ℝ)) ^ 4 := by exact_mod_cast hb
  apply hb'.trans
  calc
    _ ≤ (Real.exp (A * m + D * Real.exp ((11 / 1000 : ℝ) * L) +
        m * Real.exp ((1 / 1000 : ℝ) * L)) ^ movingFullModulusExponent n *
        Real.exp (m * Real.exp ((1 / 1000 : ℝ) * L))) ^ 4 := by gcongr
    _ = Real.exp (4 * ((movingFullModulusExponent n : ℝ) *
        (A * m + D * Real.exp ((11 / 1000 : ℝ) * L) +
          m * Real.exp ((1 / 1000 : ℝ) * L)) + m * Real.exp ((1 / 1000 : ℝ) * L))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
    _ ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) := by
      apply Real.exp_le_exp.mpr
      have hh := sampled_modulus_exponent_bound n r₀ k A L hA hL
      dsimp only at hh
      simp only [pow_one, zero_mul, Real.exp_zero, one_mul] at hrate
      have hCL : 0 ≤ C * L := mul_nonneg hC (le_trans zero_le_one hL)
      exact hh.trans (by dsimp only [C, D₀, K] at hrate hCL ⊢; linarith only [hrate, hCL])
    _ = _ := by congr 2; ring

end Ostmann

end OAI
