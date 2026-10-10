import OAI.Analysis.OInfinity.ZeroCornerRows

namespace OAI

/-! # Finite anticommutation relations inside a relative Cuntz corner

The Jordan–Wigner recursion is carried out in the explicit corner unit `q`.
No infinite CAR representation is used. Its even products have exact shift
covariance, which is the algebraic input for finite cyclic partitions.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def zeroCornerShift (a b x : E) : E := a * x * star a + b * x * star b

def zeroCornerParity (a b : E) : E := a * star a - b * star b

def zeroCornerCAR (a b : E) : ℕ → E
  | 0 => a * star b
  | n + 1 => zeroCornerParity a b * zeroCornerShift a b (zeroCornerCAR a b n)

lemma zeroCornerShift_star (a b x : E) :
    star (zeroCornerShift a b x) = zeroCornerShift a b (star x) := by
  simp only [zeroCornerShift, star_add, star_mul, star_star, mul_assoc]

lemma zeroCornerShift_add (a b x y : E) :
    zeroCornerShift a b (x + y) = zeroCornerShift a b x + zeroCornerShift a b y := by
  unfold zeroCornerShift
  noncomm_ring

lemma zeroCornerShift_zero (a b : E) : zeroCornerShift a b 0 = 0 := by
  simp only [zeroCornerShift, mul_zero, zero_mul, add_zero]

section Pair
variable (q a b : E) (hqstar : star q = q) (hqq : q * q = q)
  (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
  (hsum : a * star a + b * star b = q)

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerShift_support (x : E) :
    q * zeroCornerShift a b x = zeroCornerShift a b x ∧
      zeroCornerShift a b x * q = zeroCornerShift a b x := by
  obtain ⟨hqa, haq, hqb, hbq⟩ := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  have hasq : star a * q = star a := by
    simpa only [star_mul, hqstar] using congrArg star hqa
  have hbsq : star b * q = star b := by
    simpa only [star_mul, hqstar] using congrArg star hqb
  constructor
  · simp only [zeroCornerShift, mul_add, ← mul_assoc, hqa, hqb]
  · simp only [zeroCornerShift, add_mul, mul_assoc, hasq, hbsq]

include haa hbb hab in
lemma zeroCornerShift_mul (x y : E) (hy : q * y = y) :
    zeroCornerShift a b x * zeroCornerShift a b y = zeroCornerShift a b (x * y) := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  unfold zeroCornerShift
  calc
    _ = a * x * (star a * a) * y * star a +
        a * x * (star a * b) * y * star b +
        b * x * (star b * a) * y * star a +
        b * x * (star b * b) * y * star b := by noncomm_ring
    _ = a * x * q * y * star a + b * x * q * y * star b := by
      rw [haa, hbb, hab, hba]
      simp only [mul_zero, zero_mul, add_zero]
    _ = _ := by
      simp only [mul_assoc, hy]

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerShift_unit : zeroCornerShift a b q = q := by
  obtain ⟨_, haq, _, hbq⟩ := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  simpa only [zeroCornerShift, haq, hbq] using hsum

lemma zeroCornerParity_star : star (zeroCornerParity a b) = zeroCornerParity a b := by
  simp only [zeroCornerParity, star_sub, star_mul, star_star]

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerParity_sq : zeroCornerParity a b * zeroCornerParity a b = q := by
  obtain ⟨hqa, haq, hqb, hbq⟩ := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  unfold zeroCornerParity
  calc
    _ = a * (star a * a) * star a - a * (star a * b) * star b -
        b * (star b * a) * star a + b * (star b * b) * star b := by noncomm_ring
    _ = q := by rw [haa, hbb, hab, hba, haq, hbq]; simpa using hsum

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerParity_support : q * zeroCornerParity a b = zeroCornerParity a b ∧
    zeroCornerParity a b * q = zeroCornerParity a b := by
  obtain ⟨hqa, haq, hqb, hbq⟩ := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  have hasq : star a * q = star a := by
    simpa only [star_mul, hqstar] using congrArg star hqa
  have hbsq : star b * q = star b := by
    simpa only [star_mul, hqstar] using congrArg star hqb
  constructor
  · simp only [zeroCornerParity, mul_sub, ← mul_assoc, hqa, hqb]
  · simp only [zeroCornerParity, sub_mul, mul_assoc, hasq, hbsq]

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerShift_commute_seed (x : E) :
    Commute (a * star b) (zeroCornerShift a b x) := by
  obtain ⟨hqa, haq, hqb, hbq⟩ := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  have hqsb : q * star b = star b := by
    simpa only [star_mul, hqstar] using congrArg star hbq
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  change (a * star b) * zeroCornerShift a b x = zeroCornerShift a b x * (a * star b)
  unfold zeroCornerShift
  calc
    _ = a * (star b * a) * x * star a + a * (star b * b) * x * star b := by noncomm_ring
    _ = a * x * star b := by rw [hba, hbb, haq]; simp
    _ = a * x * (star a * a) * star b + b * x * (star b * a) * star b := by
      rw [haa, hba]
      simp only [mul_zero, zero_mul, add_zero, mul_assoc, hqsb]
    _ = _ := by noncomm_ring

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerShift_commute_parity (x : E) :
    Commute (zeroCornerParity a b) (zeroCornerShift a b x) := by
  obtain ⟨hqa, haq, hqb, hbq⟩ := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  have hqsa : q * star a = star a := by
    simpa only [star_mul, hqstar] using congrArg star haq
  have hqsb : q * star b = star b := by
    simpa only [star_mul, hqstar] using congrArg star hbq
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have haax (y : E) : star a * (a * y) = q * y := by rw [← mul_assoc, haa]
  have habx (y : E) : star a * (b * y) = 0 := by rw [← mul_assoc, hab, zero_mul]
  have hbax (y : E) : star b * (a * y) = 0 := by rw [← mul_assoc, hba, zero_mul]
  have hbbx (y : E) : star b * (b * y) = q * y := by rw [← mul_assoc, hbb]
  have haqx (y : E) : a * (q * y) = a * y := by rw [← mul_assoc, haq]
  have hbqx (y : E) : b * (q * y) = b * y := by rw [← mul_assoc, hbq]
  change zeroCornerParity a b * zeroCornerShift a b x =
    zeroCornerShift a b x * zeroCornerParity a b
  unfold zeroCornerParity zeroCornerShift
  noncomm_ring [haax, habx, hbax, hbbx, haqx, hbqx, hqsa, hqsb]

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerCAR_seed_relations :
    (a * star b) * (a * star b) = 0 ∧
      star (a * star b) * (a * star b) + (a * star b) * star (a * star b) = q ∧
      zeroCornerParity a b * (a * star b) = -(a * star b) * zeroCornerParity a b := by
  obtain ⟨hqa, haq, hqb, hbq⟩ := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have hqsb : q * star b = star b := by
    simpa only [star_mul, hqstar] using congrArg star hbq
  have haax (y : E) : star a * (a * y) = q * y := by rw [← mul_assoc, haa]
  have habx (y : E) : star a * (b * y) = 0 := by rw [← mul_assoc, hab, zero_mul]
  have hbax (y : E) : star b * (a * y) = 0 := by rw [← mul_assoc, hba, zero_mul]
  have hbbx (y : E) : star b * (b * y) = q * y := by rw [← mul_assoc, hbb]
  constructor
  · rw [mul_assoc, ← mul_assoc (star b), hba, zero_mul, mul_zero]
  constructor
  · rw [star_mul, star_star]
    calc
      _ = b * (star a * a) * star b + a * (star b * b) * star a := by noncomm_ring
      _ = q := by rw [haa, hbb, hbq, haq, add_comm, hsum]
  · unfold zeroCornerParity
    noncomm_ring [haax, habx, hbax, hbbx, hqsb]

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerCAR_support : ∀ n, q * zeroCornerCAR a b n = zeroCornerCAR a b n ∧
    zeroCornerCAR a b n * q = zeroCornerCAR a b n := by
  obtain ⟨hqa, haq, hqb, hbq⟩ := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  have hbsq : star b * q = star b := by
    simpa only [star_mul, hqstar] using congrArg star hqb
  have hp := zeroCornerParity_support q a b hqstar hqq haa hbb hab hsum
  intro n
  cases n with
  | zero => exact ⟨by change q * (a * star b) = a * star b; rw [← mul_assoc, hqa],
      by change (a * star b) * q = a * star b; rw [mul_assoc, hbsq]⟩
  | succ n =>
    have hs := zeroCornerShift_support q a b hqstar hqq haa hbb hab hsum (zeroCornerCAR a b n)
    constructor
    · change q * (zeroCornerParity a b * zeroCornerShift a b (zeroCornerCAR a b n)) =
        zeroCornerParity a b * zeroCornerShift a b (zeroCornerCAR a b n)
      rw [← mul_assoc, hp.1]
    · change (zeroCornerParity a b * zeroCornerShift a b (zeroCornerCAR a b n)) * q =
        zeroCornerParity a b * zeroCornerShift a b (zeroCornerCAR a b n)
      rw [mul_assoc, hs.2]

include hqstar hqq haa hbb hab hsum in
/-- The parity commutes with every positive-index generator. -/
lemma zeroCornerCAR_succ_commute_parity (n : ℕ) :
    Commute (zeroCornerParity a b) (zeroCornerCAR a b (n + 1)) := by
  change Commute (zeroCornerParity a b)
    (zeroCornerParity a b * zeroCornerShift a b (zeroCornerCAR a b n))
  exact (Commute.refl _).mul_right
    (zeroCornerShift_commute_parity q a b hqstar hqq haa hbb hab hsum _)


include hqstar hqq haa hbb hab hsum in
lemma zeroCornerShift_parity_mul (x y : E) (hy : q * y = y) :
    (zeroCornerParity a b * zeroCornerShift a b x) *
        (zeroCornerParity a b * zeroCornerShift a b y) = zeroCornerShift a b (x * y) := by
  have hc := zeroCornerShift_commute_parity q a b hqstar hqq haa hbb hab hsum x
  have hp := zeroCornerParity_sq q a b hqstar hqq haa hbb hab hsum
  have hs := zeroCornerShift_support q a b hqstar hqq haa hbb hab hsum x
  calc
    _ = zeroCornerShift a b x * (zeroCornerParity a b * zeroCornerParity a b) *
        zeroCornerShift a b y := by rw [hc.eq]; noncomm_ring
    _ = zeroCornerShift a b x * zeroCornerShift a b y := by rw [hp, hs.2]
    _ = _ := zeroCornerShift_mul q a b haa hbb hab x y hy

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerShift_parity_star_mul (x y : E) (hy : q * y = y) :
    star (zeroCornerParity a b * zeroCornerShift a b x) *
        (zeroCornerParity a b * zeroCornerShift a b y) = zeroCornerShift a b (star x * y) := by
  have hp := zeroCornerParity_sq q a b hqstar hqq haa hbb hab hsum
  have hs := zeroCornerShift_support q a b hqstar hqq haa hbb hab hsum (star x)
  rw [star_mul, zeroCornerParity_star, zeroCornerShift_star]
  calc
    _ = zeroCornerShift a b (star x) * (zeroCornerParity a b * zeroCornerParity a b) *
        zeroCornerShift a b y := by noncomm_ring
    _ = zeroCornerShift a b (star x) * zeroCornerShift a b y := by rw [hp, hs.2]
    _ = _ := zeroCornerShift_mul q a b haa hbb hab _ _ hy

include hqstar hqq haa hbb hab hsum in
/-- Shift covariance holds exactly for even products. -/
lemma zeroCornerCAR_shift_even (i j : ℕ) :
    zeroCornerShift a b (zeroCornerCAR a b i * star (zeroCornerCAR a b j)) =
      zeroCornerCAR a b (i + 1) * star (zeroCornerCAR a b (j + 1)) := by
  have hs := zeroCornerCAR_support q a b hqstar hqq haa hbb hab hsum j
  have hstar : q * star (zeroCornerCAR a b j) = star (zeroCornerCAR a b j) := by
    simpa only [star_mul, hqstar] using congrArg star hs.2
  have hci := zeroCornerShift_commute_parity q a b hqstar hqq haa hbb hab hsum
    (zeroCornerCAR a b i)
  have hcj := zeroCornerShift_commute_parity q a b hqstar hqq haa hbb hab hsum
    (star (zeroCornerCAR a b j))
  have hp := zeroCornerParity_sq q a b hqstar hqq haa hbb hab hsum
  have hsupport := zeroCornerShift_support q a b hqstar hqq haa hbb hab hsum
    (star (zeroCornerCAR a b j))
  rw [← zeroCornerShift_mul q a b haa hbb hab _ _ hstar]
  simp only [zeroCornerCAR, star_mul, zeroCornerParity_star, zeroCornerShift_star]
  symm
  calc
    _ = zeroCornerShift a b (zeroCornerCAR a b i) *
        (zeroCornerParity a b * zeroCornerShift a b (star (zeroCornerCAR a b j))) *
        zeroCornerParity a b := by rw [hci.eq]; noncomm_ring
    _ = zeroCornerShift a b (zeroCornerCAR a b i) *
        (zeroCornerShift a b (star (zeroCornerCAR a b j)) * zeroCornerParity a b) *
        zeroCornerParity a b := by rw [hcj.eq]
    _ = zeroCornerShift a b (zeroCornerCAR a b i) *
        (zeroCornerShift a b (star (zeroCornerCAR a b j)) *
          (zeroCornerParity a b * zeroCornerParity a b)) := by noncomm_ring
    _ = _ := by rw [hp, hsupport.2]

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerCAR_seed_anticommute (n : ℕ) :
    zeroCornerCAR a b 0 * zeroCornerCAR a b (n + 1) +
      zeroCornerCAR a b (n + 1) * zeroCornerCAR a b 0 = 0 := by
  have hc := zeroCornerShift_commute_seed q a b hqstar hqq haa hbb hab hsum
    (zeroCornerCAR a b n)
  have hz := (zeroCornerCAR_seed_relations q a b hqstar hqq haa hbb hab hsum).2.2
  change (a * star b) * (zeroCornerParity a b * zeroCornerShift a b _) +
      (zeroCornerParity a b * zeroCornerShift a b _) * (a * star b) = 0
  calc
    _ = ((a * star b) * zeroCornerParity a b) * zeroCornerShift a b (zeroCornerCAR a b n) +
        zeroCornerParity a b * (zeroCornerShift a b (zeroCornerCAR a b n) * (a * star b)) := by
      noncomm_ring
    _ = ((a * star b) * zeroCornerParity a b) * zeroCornerShift a b (zeroCornerCAR a b n) +
        zeroCornerParity a b * ((a * star b) * zeroCornerShift a b (zeroCornerCAR a b n)) := by
      rw [← hc.eq]
    _ = ((a * star b) * zeroCornerParity a b + zeroCornerParity a b * (a * star b)) *
        zeroCornerShift a b (zeroCornerCAR a b n) := by noncomm_ring
    _ = 0 := by rw [hz]; simp

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerCAR_anticommute : ∀ i j,
    zeroCornerCAR a b i * zeroCornerCAR a b j +
      zeroCornerCAR a b j * zeroCornerCAR a b i = 0 := by
  have hseed := zeroCornerCAR_seed_relations q a b hqstar hqq haa hbb hab hsum
  intro i
  induction i with
  | zero =>
    intro j
    cases j with
    | zero => change (a * star b) * (a * star b) + (a * star b) * (a * star b) = 0
              rw [hseed.1, zero_add]
    | succ j => exact zeroCornerCAR_seed_anticommute q a b hqstar hqq haa hbb hab hsum j
  | succ i ih =>
    intro j
    cases j with
    | zero =>
      rw [add_comm]
      exact zeroCornerCAR_seed_anticommute q a b hqstar hqq haa hbb hab hsum i
    | succ j =>
      have hi := zeroCornerCAR_support q a b hqstar hqq haa hbb hab hsum i
      have hj := zeroCornerCAR_support q a b hqstar hqq haa hbb hab hsum j
      simp only [zeroCornerCAR]
      rw [zeroCornerShift_parity_mul q a b hqstar hqq haa hbb hab hsum _ _ hj.1,
        zeroCornerShift_parity_mul q a b hqstar hqq haa hbb hab hsum _ _ hi.1,
        ← zeroCornerShift_add, ih j, zeroCornerShift_zero]

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerCAR_seed_star_anticommute (n : ℕ) :
    star (zeroCornerCAR a b 0) * zeroCornerCAR a b (n + 1) +
      zeroCornerCAR a b (n + 1) * star (zeroCornerCAR a b 0) = 0 := by
  have hc₀ := zeroCornerShift_commute_seed q a b hqstar hqq haa hbb hab hsum
    (star (zeroCornerCAR a b n))
  have hc : Commute (star (a * star b)) (zeroCornerShift a b (zeroCornerCAR a b n)) := by
    simpa only [zeroCornerShift_star, star_star] using hc₀.star_star
  have hz₀ := (zeroCornerCAR_seed_relations q a b hqstar hqq haa hbb hab hsum).2.2
  have hz : star (a * star b) * zeroCornerParity a b =
      -(zeroCornerParity a b * star (a * star b)) := by
    simpa only [star_mul, star_neg, zeroCornerParity_star, mul_neg] using congrArg star hz₀
  change star (a * star b) * (zeroCornerParity a b * zeroCornerShift a b _) +
      (zeroCornerParity a b * zeroCornerShift a b _) * star (a * star b) = 0
  calc
    _ = (star (a * star b) * zeroCornerParity a b) * zeroCornerShift a b (zeroCornerCAR a b n) +
        zeroCornerParity a b * (zeroCornerShift a b (zeroCornerCAR a b n) * star (a * star b)) := by
      noncomm_ring
    _ = (star (a * star b) * zeroCornerParity a b) * zeroCornerShift a b (zeroCornerCAR a b n) +
        zeroCornerParity a b * (star (a * star b) * zeroCornerShift a b (zeroCornerCAR a b n)) := by
      rw [← hc.eq]
    _ = (star (a * star b) * zeroCornerParity a b +
        zeroCornerParity a b * star (a * star b)) *
        zeroCornerShift a b (zeroCornerCAR a b n) := by noncomm_ring
    _ = 0 := by rw [hz]; simp

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerCAR_star_anticommute : ∀ i j,
    star (zeroCornerCAR a b i) * zeroCornerCAR a b j +
      zeroCornerCAR a b j * star (zeroCornerCAR a b i) = if i = j then q else 0 := by
  intro i
  induction i with
  | zero =>
    intro j
    cases j with
    | zero => simpa only [zeroCornerCAR, ite_true] using
                (zeroCornerCAR_seed_relations q a b hqstar hqq haa hbb hab hsum).2.1
    | succ j => simpa only [Nat.zero_ne_add_one, ite_false] using
                  zeroCornerCAR_seed_star_anticommute q a b hqstar hqq haa hbb hab hsum j
  | succ i ih =>
    intro j
    cases j with
    | zero =>
      have h := congrArg star (zeroCornerCAR_seed_star_anticommute q a b hqstar hqq haa hbb hab hsum i)
      simpa only [star_add, star_mul, star_star, star_zero, Nat.add_one_ne_zero, ite_false] using h
    | succ j =>
      have hi := zeroCornerCAR_support q a b hqstar hqq haa hbb hab hsum i
      have hj := zeroCornerCAR_support q a b hqstar hqq haa hbb hab hsum j
      have histar : q * star (zeroCornerCAR a b i) = star (zeroCornerCAR a b i) := by
        simpa only [star_mul, hqstar] using congrArg star hi.2
      have heven := zeroCornerCAR_shift_even q a b hqstar hqq haa hbb hab hsum j i
      change star (zeroCornerParity a b * zeroCornerShift a b (zeroCornerCAR a b i)) *
          (zeroCornerParity a b * zeroCornerShift a b (zeroCornerCAR a b j)) +
          zeroCornerCAR a b (j + 1) * star (zeroCornerCAR a b (i + 1)) = _
      rw [zeroCornerShift_parity_star_mul q a b hqstar hqq haa hbb hab hsum _ _ hj.1,
        ← heven, ← zeroCornerShift_add, ih j]
      by_cases hij : i = j
      · subst j
        simp only [ite_true, zeroCornerShift_unit q a b hqstar hqq haa hbb hab hsum]
      · have hsij : i + 1 ≠ j + 1 := by omega
        simp only [hij, hsij, ite_false, zeroCornerShift_zero]

end Pair

/-- The norm estimate for a finite CAR linear combination is algebraic:
square zero and its anticommutator determine the bound. -/
lemma squareZero_norm_sq_le (x q : E) (c : ℝ) (hc : 0 ≤ c)
    (hxx : x * x = 0) (hqx : q * x = x)
    (hgram : star x * x + x * star x = c • q) : ‖x‖ * ‖x‖ ≤ c := by
  have hpp : (star x * x) * (star x * x) = c • (star x * x) := by
    calc
      _ = star x * (star x * x + x * star x) * x := by noncomm_ring [hxx]
      _ = star x * (c • q) * x := by rw [hgram]
      _ = c • (star x * x) := by
        rw [mul_smul_comm, smul_mul_assoc, mul_assoc, hqx]
  have hpstar : star (star x * x) = star x * x := by simp only [star_mul, star_star]
  have hpnorm : ‖star x * x‖ * ‖star x * x‖ = c * ‖star x * x‖ := by
    calc
      _ = ‖star (star x * x) * (star x * x)‖ := CStarRing.norm_star_mul_self.symm
      _ = ‖c • (star x * x)‖ := by rw [hpstar, hpp]
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  have hple : ‖star x * x‖ ≤ c := by
    by_contra! hbad
    have hp : 0 < ‖star x * x‖ := hc.trans_lt hbad
    have hmul := mul_pos hp (sub_pos.mpr hbad)
    nlinarith
  simpa only [CStarRing.norm_star_mul_self] using hple

section PairNorm
variable (q a b : E) (hqstar : star q = q) (hqq : q * q = q)
  (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
  (hsum : a * star a + b * star b = q)

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerCAR_norm_le_one (n : ℕ) : ‖zeroCornerCAR a b n‖ ≤ 1 := by
  let x := zeroCornerCAR a b n
  have hanti : x * x + x * x = 0 :=
    zeroCornerCAR_anticommute q a b hqstar hqq haa hbb hab hsum n n
  have htwo : (2 : ℂ) • (x * x) = 0 := by rw [two_smul]; exact hanti
  have hxx : x * x = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hgram : star x * x + x * star x = (1 : ℝ) • q := by
    simpa only [ite_true, one_smul] using
      zeroCornerCAR_star_anticommute q a b hqstar hqq haa hbb hab hsum n n
  have hqx : q * x = x := (zeroCornerCAR_support q a b hqstar hqq haa hbb hab hsum n).1
  have hn := squareZero_norm_sq_le x q 1 zero_le_one hxx hqx hgram
  nlinarith [norm_nonneg x]

end PairNorm
end WeakPureInfiniteness

end

end OAI
