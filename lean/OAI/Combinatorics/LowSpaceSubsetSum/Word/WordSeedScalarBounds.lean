import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedFactorExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedCompressionExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordWidthBounds

namespace OAI

/-! # Application-scale bounds for measured scalar samplers

Only the actual prime tests incur the half-exponential factor. Permutation
range tests, retained candidate buffers and tuple assembly remain polynomial.
-/

namespace LowSpaceSubsetSum.WordSeedScalarBounds

open WordSeedMeasured

private theorem self_le_pow {u : ℕ} (hu : 1 ≤ u) {k : ℕ} (hk : 1 ≤ k) : u ≤ u^k := by
  simpa only [Nat.pow_one] using Nat.pow_le_pow_right hu hk

private theorem multiple_power {u c k : ℕ} (hc : c ≤ u) : c*u^k ≤ u^(k+1) := by
  simpa only [Nat.pow_succ,Nat.mul_comm] using Nat.mul_le_mul_right (u^k) hc

private theorem small_tail {u : ℕ} (hu : 10000 ≤ u) :
    5*u+64 ≤ u^3 := by
  have hsq : 10000*u ≤ u^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right u hu
  have hcube : u^2 ≤ u^3 := Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith

private theorem factor_numeric {n ell u H : ℕ} (hu : 10000 ≤ u)
    (hnu : n+2 ≤ u) (hell : ell ≤ n) (hH : 1 ≤ H)
    (hexp : 2^((ell+1)/2) ≤ H) : factorWork n ell ≤ u^5*H := by
  have hn3 : n^3 ≤ u^3 := Nat.pow_le_pow_left (by omega) 3
  have hu4 : u ≤ u^4 := self_le_pow (by omega) (by decide)
  have hsmall : 3*ell+21 ≤ 5*u := by omega
  have hinner : 12*2^((ell+1)/2)+12*(ell+1)+11 ≤ 35*u*H := by
    have ht := Nat.mul_le_mul_left (12*u+11) hH
    have he := Nat.mul_le_mul_left 12 hexp
    have hl : ell+1 ≤ u := by omega
    have hc : 12+12*u+11 ≤ 35*u := by omega
    have hm := Nat.mul_le_mul_right H hc
    nlinarith
  have hmain : n^3*(12*2^((ell+1)/2)+12*(ell+1)+11) ≤ 35*u^4*H := by
    calc
      _ ≤ u^3*(35*u*H) := Nat.mul_le_mul hn3 hinner
      _ = _ := by ring
  have htail : 3*ell+21 ≤ 5*u^4*H := by
    have ht := Nat.mul_le_mul_right (5*u^4) hH
    have hm := Nat.mul_le_mul_left 5 hu4
    nlinarith
  have hscale : 40*u^4*H ≤ u^5*H :=
    Nat.mul_le_mul_right H (multiple_power (by omega : 40 ≤ u))
  unfold factorWork
  nlinarith

private theorem permutation_numeric {n k u : ℕ} (hu : 10000 ≤ u)
    (hnu : n+2 ≤ u) (hk : k ≤ n) :
    k*(13*n^3+5*k+64)+1 ≤ u^5 ∧
    (k+1)*(2*n^3+256) ≤ u^5 ∧ (k+1)*(n^3+64) ≤ u^5 := by
  have hn3 : n^3 ≤ u^3 := Nat.pow_le_pow_left (by omega) 3
  have hu3 : u ≤ u^3 := self_le_pow (by omega) (by decide)
  have hu4 : 1 ≤ u^4 := (show 1 ≤ u by omega).trans
    (self_le_pow (by omega) (by decide))
  have hlow := small_tail hu
  have hinner : 13*n^3+5*k+64 ≤ 14*u^3 := by omega
  have hw : k*(13*n^3+5*k+64) ≤ 14*u^4 := by
    calc
      _ ≤ u*(14*u^3) := Nat.mul_le_mul (by omega) hinner
      _ = _ := by ring
  have hW : k*(13*n^3+5*k+64)+1 ≤ u^5 := by
    have hs := multiple_power (k := 4) (by omega : 15 ≤ u)
    nlinarith
  have hc : (k+1)*(2*n^3+256) ≤ 3*u^4 := by
    calc
      _ ≤ u*(3*u^3) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hr : (k+1)*(n^3+64) ≤ 2*u^4 := by
    calc
      _ ≤ u*(2*u^3) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  exact ⟨hW,hc.trans (multiple_power (by omega : 3 ≤ u)),
    hr.trans (multiple_power (by omega : 2 ≤ u))⟩

variable {n : ℕ}

/-- The executed modulus itself fits, using strict width slack in the application. -/
theorem prime_modulus_fits (I : Instance n) {ell : ℕ} (hell : ell ≤ n) :
    (WordSeedPowerExecution.run ell).1 < 2^wordWidth I := by
  rw [WordSeedPowerExecution.run_value]
  exact Nat.pow_lt_pow_right (by decide) (by unfold wordWidth inputScale; omega)

theorem factorWork_le (I : Instance n) (hn : 10000 ≤ n) {ell : ℕ} (hell : ell ≤ n) :
    factorWork n ell ≤ inputScale I^5*2^((n+1)/2) := by
  exact factor_numeric (by unfold inputScale; omega) (by unfold inputScale; omega)
    hell Nat.one_le_two_pow (Nat.pow_le_pow_right (by decide) (by omega))

theorem prime_work_le (I : Instance n) (hn : 10000 ≤ n) {ell : ℕ} (hell : ell ≤ n) :
    n^3*(12*2^((ell+1)/2)+12*(ell+1)+11)+3*ell+17 ≤
      inputScale I^5*2^((n+1)/2) := by
  have h := factorWork_le I hn hell
  unfold factorWork at h
  omega

theorem permutation_bounds (I : Instance n) (hn : 10000 ≤ n) {k : ℕ} (hk : k ≤ n) :
    k*(13*n^3+5*k+64)+1 ≤ inputScale I^5 ∧
    (k+1)*(2*n^3+256) ≤ inputScale I^5 ∧
    (k+1)*(n^3+64) ≤ inputScale I^5 :=
  permutation_numeric (by unfold inputScale; omega) (by unfold inputScale; omega) hk

theorem permutation_bounded_scale (I : Instance n) (hn : 10000 ≤ n) {k : ℕ}
    (hk : k ≤ n) (w : ℕ) (hw : Nat.clog 2 k ≤ w) :
    (permutation w n k hw).Bounded (inputScale I^5) (inputScale I^5) (inputScale I^5) :=
  bounded_mono _ (permutation_bounded w n k hw)
    (permutation_bounds I hn hk).1 (permutation_bounds I hn hk).2.1
    (permutation_bounds I hn hk).2.2

theorem scalar_cells_le (I : Instance n) (hn : 10000 ≤ n) :
    2*n^3+124 ≤ inputScale I^5 ∧ n^3+28 ≤ inputScale I^5 := by
  let u := inputScale I
  have hu : 10000 ≤ u := by dsimp only [u,inputScale]; omega
  have hn3 : n^3 ≤ u^3 := Nat.pow_le_pow_left (by dsimp only [u,inputScale]; omega) 3
  have hu3 : u ≤ u^3 := self_le_pow (by omega) (by decide)
  have hu2 : 3 ≤ u^2 := by nlinarith
  have hp : 3*u^3 ≤ u^5 := by
    calc
      _ ≤ u^2*u^3 := Nat.mul_le_mul_right _ hu2
      _ = _ := by ring
  constructor <;> change _ ≤ u^5 <;> omega

theorem factor_bounded_scale (I : Instance n) (hn : 10000 ≤ n) {ell : ℕ}
    (hell : ell ≤ n) (w : ℕ) (hw : ell ≤ w) :
    (factor w n ell hw).Bounded (inputScale I^5*2^((n+1)/2))
      (inputScale I^5) (inputScale I^5) :=
  bounded_mono _ (factor_bounded w n ell hw) (factorWork_le I hn hell)
    (scalar_cells_le I hn).1 (scalar_cells_le I hn).2

theorem prime_bounded_scale (I : Instance n) (hn : 10000 ≤ n) {ell : ℕ}
    (hell : ell ≤ n) (hfour : 4 ≤ ell) (w : ℕ) (hw : ell ≤ w) :
    (primeInitialized w n ell hfour hw).Bounded (inputScale I^5*2^((n+1)/2))
      (inputScale I^5) (inputScale I^5) :=
  bounded_mono _ (primeInitialized_bounded w n ell hfour hw) (prime_work_le I hn hell)
    (scalar_cells_le I hn).1 ((show n^3+18 ≤ n^3+28 by omega).trans (scalar_cells_le I hn).2)

theorem compression_bounds (I : Instance n) (hn : 10000 ≤ n) :
    compressionWork n ≤ inputScale I^6*2^((n+1)/2) ∧
    (n+3)*(2*n^3+256) ≤ inputScale I^5 ∧
    (n+2)*(n^3+64) ≤ inputScale I^5 := by
  let u := inputScale I
  let H := 2^((n+1)/2)
  have hu : 10000 ≤ u := by dsimp only [u,inputScale]; omega
  have hH : 1 ≤ H := Nat.one_le_two_pow
  have hp := (permutation_bounds I hn (le_refl n)).1
  have hq := prime_work_le I hn (show compressionPrimeExponent n ≤ n by
    unfold compressionPrimeExponent; omega)
  have hwork : compressionWork n ≤ u^6*H := by
    change n*(13*n^3+5*n+64)+1 ≤ u^5 at hp
    change n^3*(12*2^((compressionPrimeExponent n+1)/2)+
      12*(compressionPrimeExponent n+1)+11)+3*compressionPrimeExponent n+17 ≤ u^5*H at hq
    have hph := Nat.mul_le_mul_left (u^5) hH
    have hu5 : 8 ≤ u^5 := (show 8 ≤ u by omega).trans (self_le_pow (by omega) (by decide))
    have hscale : 3*u^5*H ≤ u^6*H :=
      Nat.mul_le_mul_right _ (multiple_power (by omega : 3 ≤ u))
    unfold compressionWork
    nlinarith
  have hn3 : n^3 ≤ u^3 := Nat.pow_le_pow_left (by dsimp only [u,inputScale]; omega) 3
  have hu3 : u ≤ u^3 := self_le_pow (by omega) (by decide)
  have hc : (n+3)*(2*n^3+256) ≤ 6*u^4 := by
    calc
      _ ≤ (2*u)*(3*u^3) := Nat.mul_le_mul (by dsimp only [u,inputScale]; omega) (by omega)
      _ = _ := by ring
  have hr : (n+2)*(n^3+64) ≤ 2*u^4 := by
    calc
      _ ≤ u*(2*u^3) := Nat.mul_le_mul (by dsimp only [u,inputScale]; omega) (by omega)
      _ = _ := by ring
  exact ⟨hwork,hc.trans (multiple_power (by omega : 6 ≤ u)),
    hr.trans (multiple_power (by omega : 2 ≤ u))⟩

theorem compression_bounded_scale (I : Instance n) (D : CompressionData n)
    (hn : 168000000 ≤ n) (w : ℕ) (hp : Nat.clog 2 n ≤ w)
    (hq : compressionPrimeExponent n ≤ w) :
    (compression D hn w hp hq).Bounded (inputScale I^6*2^((n+1)/2))
      (inputScale I^5) (inputScale I^5) := by
  have h := compression_bounds I (by omega : 10000 ≤ n)
  exact bounded_mono _ (compression_bounded D hn w hp hq) h.1 h.2.1 h.2.2

end LowSpaceSubsetSum.WordSeedScalarBounds

end OAI
