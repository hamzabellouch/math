import OAI.Analysis.OInfinity.JordanWigner

namespace OAI

/-! # Finite dyadic phase projections

The commuting two-level coordinates give exact finite partitions of the
corner unit. The phase conditions are the elementary dyadic root identities;
the shift estimates and cocycle construction are separate obligations.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def carSpinAxis (a : E) (ζ : ℂ) : E := ζ • a + star ζ • star a

def carSpinProjection (q a : E) (ζ : ℂ) : E := (2 : ℂ)⁻¹ • (q + carSpinAxis a ζ)

lemma carSpinAxis_star (a : E) (ζ : ℂ) : star (carSpinAxis a ζ) = carSpinAxis a ζ := by
  simp only [carSpinAxis, star_add, star_smul, star_star, add_comm]

lemma carSpinAxis_support (q a : E) (hqstar : star q = q)
    (hqa : q * a = a) (haq : a * q = a) (ζ : ℂ) :
    q * carSpinAxis a ζ = carSpinAxis a ζ ∧ carSpinAxis a ζ * q = carSpinAxis a ζ := by
  have hqa' : q * star a = star a := by
    simpa only [star_mul, hqstar] using congrArg star haq
  have haq' : star a * q = star a := by
    simpa only [star_mul, hqstar] using congrArg star hqa
  constructor <;>
    simp only [carSpinAxis, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      hqa, haq, hqa', haq']

lemma carSpinAxis_sq (q a : E) (haa : a * a = 0)
    (hgram : star a * a + a * star a = q) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    carSpinAxis a ζ * carSpinAxis a ζ = q := by
  have haa' : star a * star a = 0 := by
    simpa only [star_mul, star_zero] using congrArg star haa
  have hc : star ζ * ζ = (1 : ℂ) := by
    simpa [Complex.star_def, hζ] using Complex.conj_mul' ζ
  have hc' : ζ * star ζ = (1 : ℂ) := by rw [mul_comm, hc]
  simp only [carSpinAxis, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_smul, haa, haa', hc, hc', smul_zero, zero_add, add_zero, one_smul]
  simpa only [add_comm] using hgram

lemma carSpinProjection_support (q a : E) (hqstar : star q = q) (hqq : q * q = q)
    (hqa : q * a = a) (haq : a * q = a) (ζ : ℂ) :
    q * carSpinProjection q a ζ = carSpinProjection q a ζ ∧
      carSpinProjection q a ζ * q = carSpinProjection q a ζ := by
  have hs := carSpinAxis_support q a hqstar hqa haq ζ
  constructor <;>
    simp only [carSpinProjection, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
      hqq, hs.1, hs.2]

lemma carSpinProjection_isStarProjection (q a : E) (hqstar : star q = q)
    (hqq : q * q = q) (hqa : q * a = a) (haq : a * q = a)
    (haa : a * a = 0) (hgram : star a * a + a * star a = q)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) : IsStarProjection (carSpinProjection q a ζ) := by
  have hs := carSpinAxis_support q a hqstar hqa haq ζ
  have hx := carSpinAxis_sq q a haa hgram ζ hζ
  have hdouble : (q + carSpinAxis a ζ) * (q + carSpinAxis a ζ) =
      (2 : ℂ) • (q + carSpinAxis a ζ) := by
    rw [add_mul, mul_add, mul_add, hqq, hs.1, hs.2, hx, two_smul]
    abel
  refine ⟨?_, ?_⟩
  · change carSpinProjection q a ζ * carSpinProjection q a ζ = _
    simp only [carSpinProjection, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hdouble, smul_smul]
    norm_num
  · change star (carSpinProjection q a ζ) = _
    simp only [carSpinProjection, star_smul, star_add, carSpinAxis_star, hqstar]
    norm_num

lemma carSpinAxis_neg (a : E) (ζ : ℂ) : carSpinAxis a (-ζ) = -carSpinAxis a ζ := by
  simp only [carSpinAxis, neg_smul, star_neg, neg_add]

lemma carSpinProjection_neg (q a : E) (ζ : ℂ) :
    carSpinProjection q a (-ζ) = q - carSpinProjection q a ζ := by
  have hsum : carSpinProjection q a (-ζ) + carSpinProjection q a ζ = q := by
    rw [carSpinProjection, carSpinProjection, carSpinAxis_neg, ← smul_add]
    have he : (q + -carSpinAxis a ζ) + (q + carSpinAxis a ζ) = (2 : ℂ) • q := by
      rw [two_smul]
      abel
    rw [he, smul_smul]
    norm_num
  exact eq_sub_of_add_eq hsum

lemma carSpinProjection_opposite_mul (q a : E) (hqstar : star q = q)
    (hqq : q * q = q) (hqa : q * a = a) (haq : a * q = a)
    (haa : a * a = 0) (hgram : star a * a + a * star a = q)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    carSpinProjection q a ζ * carSpinProjection q a (-ζ) = 0 := by
  rw [carSpinProjection_neg, mul_sub,
    (carSpinProjection_support q a hqstar hqq hqa haq ζ).2,
    (carSpinProjection_isStarProjection q a hqstar hqq hqa haq haa hgram ζ hζ).isIdempotentElem.eq,
    sub_self]

lemma carSpinAxis_commute (a b : E) (hab : Commute a b)
    (hstar : Commute (star a) b) (ζ μ : ℂ) :
    Commute (carSpinAxis a ζ) (carSpinAxis b μ) := by
  have h : Commute (carSpinAxis a ζ) b :=
    (hab.smul_left ζ).add_left (hstar.smul_left (star ζ))
  have h' : Commute (carSpinAxis a ζ) (star b) := by
    simpa only [carSpinAxis_star] using h.star_star
  exact (h.smul_right μ).add_right (h'.smul_right (star μ))

lemma carSpinProjection_commute (q a b : E) (hqstar : star q = q)
    (hqa : q * a = a) (haq : a * q = a) (hqb : q * b = b) (hbq : b * q = b)
    (hab : Commute a b) (hstar : Commute (star a) b) (ζ μ : ℂ) :
    Commute (carSpinProjection q a ζ) (carSpinProjection q b μ) := by
  have ha := carSpinAxis_support q a hqstar hqa haq ζ
  have hb := carSpinAxis_support q b hqstar hqb hbq μ
  have hqa' : Commute q (carSpinAxis a ζ) := by
    change q * carSpinAxis a ζ = carSpinAxis a ζ * q
    rw [ha.1, ha.2]
  have hqb' : Commute q (carSpinAxis b μ) := by
    change q * carSpinAxis b μ = carSpinAxis b μ * q
    rw [hb.1, hb.2]
  have h := ((Commute.refl q).add_right hqb').add_left
    (hqa'.symm.add_right (carSpinAxis_commute a b hab hstar ζ μ))
  exact (h.smul_left (2 : ℂ)⁻¹).smul_right (2 : ℂ)⁻¹

/-- Ordered finite product, starting at the corner unit. -/
def dyadicSpinProjection (q : E) (a : ℕ → E) (ζ : ℕ → ℂ) : ℕ → ℕ → E
  | 0, _ => q
  | m + 1, k => dyadicSpinProjection q a ζ m k * carSpinProjection q (a m) (ζ m ^ k)

section Dyadic

variable (q : E) (a : ℕ → E) (ζ : ℕ → ℂ)
  (hqstar : star q = q) (hqq : q * q = q)
  (hleft : ∀ i, q * a i = a i) (hright : ∀ i, a i * q = a i)
  (hzero : ∀ i, a i * a i = 0)
  (hgram : ∀ i, star (a i) * a i + a i * star (a i) = q)
  (hcomm : ∀ i j, Commute (a i) (a j))
  (hstar : ∀ i j, i ≠ j → Commute (star (a i)) (a j))
  (hunit : ∀ i, ‖ζ i‖ = 1)
  (hhalf : ∀ i, ζ i ^ (2 ^ i) = -1)

include hqstar hqq hleft hright in
lemma dyadicSpinProjection_support (m k : ℕ) :
    q * dyadicSpinProjection q a ζ m k = dyadicSpinProjection q a ζ m k ∧
      dyadicSpinProjection q a ζ m k * q = dyadicSpinProjection q a ζ m k := by
  induction m with
  | zero => exact ⟨hqq, hqq⟩
  | succ m ih =>
    have hp := carSpinProjection_support q (a m) hqstar hqq (hleft m) (hright m) (ζ m ^ k)
    constructor
    · change q * (_ * _) = _
      rw [← mul_assoc, ih.1]
      rfl
    · change (_ * _) * q = _
      rw [mul_assoc, hp.2]
      rfl

include hqstar hqq hleft hright hcomm hstar in
lemma dyadicSpinProjection_commute_factor (m j k : ℕ) (hmj : m ≤ j) (μ : ℂ) :
    Commute (dyadicSpinProjection q a ζ m k) (carSpinProjection q (a j) μ) := by
  induction m with
  | zero =>
    have hp := carSpinProjection_support q (a j) hqstar hqq (hleft j) (hright j) μ
    change q * carSpinProjection q (a j) μ = carSpinProjection q (a j) μ * q
    rw [hp.1, hp.2]
  | succ m ih =>
    exact (ih (by omega)).mul_left
      (carSpinProjection_commute q (a m) (a j) hqstar (hleft m) (hright m)
        (hleft j) (hright j) (hcomm m j) (hstar m j (by omega)) _ _)

include hqstar hqq hleft hright hzero hgram hcomm hstar hunit in
lemma dyadicSpinProjection_isStarProjection (m k : ℕ) :
    IsStarProjection (dyadicSpinProjection q a ζ m k) := by
  induction m with
  | zero => exact ⟨hqq, hqstar⟩
  | succ m ih =>
    exact ih.mul
      (carSpinProjection_isStarProjection q (a m) hqstar hqq (hleft m) (hright m)
        (hzero m) (hgram m) _ (by rw [norm_pow, hunit, one_pow]))
      (dyadicSpinProjection_commute_factor q a ζ hqstar hqq hleft hright hcomm hstar
        m m k le_rfl _)

include hhalf in
lemma dyadic_phase_period (j m : ℕ) (hjm : j < m) : ζ j ^ (2 ^ m) = 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [pow_succ, pow_mul]
    by_cases hj : j = m
    · subst j
      rw [hhalf]
      norm_num
    · rw [ih (by omega)]
      norm_num

lemma dyadicSpinProjection_eq_of_phases (m k l : ℕ)
    (h : ∀ j, j < m → ζ j ^ k = ζ j ^ l) :
    dyadicSpinProjection q a ζ m k = dyadicSpinProjection q a ζ m l := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change dyadicSpinProjection q a ζ m k * carSpinProjection q (a m) (ζ m ^ k) = _
    rw [ih (fun j hj => h j (by omega)), h m (by omega)]
    rfl

include hhalf in
lemma dyadicSpinProjection_period (m k : ℕ) :
    dyadicSpinProjection q a ζ m (k + 2 ^ m) = dyadicSpinProjection q a ζ m k := by
  apply dyadicSpinProjection_eq_of_phases
  intro j hj
  rw [pow_add, dyadic_phase_period ζ hhalf j m hj, mul_one]

include hhalf in
lemma dyadicSpinProjection_upper_half (m k : ℕ) :
    dyadicSpinProjection q a ζ (m + 1) (k + 2 ^ m) =
      dyadicSpinProjection q a ζ m k * (q - carSpinProjection q (a m) (ζ m ^ k)) := by
  change dyadicSpinProjection q a ζ m (k + 2 ^ m) *
    carSpinProjection q (a m) (ζ m ^ (k + 2 ^ m)) = _
  rw [dyadicSpinProjection_period q a ζ hhalf, pow_add, hhalf, mul_neg_one,
    carSpinProjection_neg]

include hqstar hqq hleft hright hhalf in
lemma dyadicSpinProjection_split (m k : ℕ) :
    dyadicSpinProjection q a ζ (m + 1) k +
      dyadicSpinProjection q a ζ (m + 1) (k + 2 ^ m) = dyadicSpinProjection q a ζ m k := by
  rw [dyadicSpinProjection_upper_half q a ζ hhalf]
  change dyadicSpinProjection q a ζ m k * carSpinProjection q (a m) (ζ m ^ k) +
    dyadicSpinProjection q a ζ m k * (q - carSpinProjection q (a m) (ζ m ^ k)) = _
  rw [mul_sub]
  calc
    _ = dyadicSpinProjection q a ζ m k * q := by abel
    _ = _ := (dyadicSpinProjection_support q a ζ hqstar hqq hleft hright m k).2

include hqstar hqq hleft hright hhalf in
lemma dyadicSpinProjection_sum (m : ℕ) :
    ∑ k ∈ Finset.range (2 ^ m), dyadicSpinProjection q a ζ m k = q := by
  induction m with
  | zero => simp [dyadicSpinProjection]
  | succ m ih =>
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
    simp_rw [Nat.add_comm (2 ^ m), dyadicSpinProjection_split q a ζ hqstar hqq hleft hright hhalf]
    exact ih

include hqstar hqq hleft hright hcomm hstar in
lemma dyadicSpinProjection_next_mul_eq_zero (m k l : ℕ)
    (hparent : dyadicSpinProjection q a ζ m k * dyadicSpinProjection q a ζ m l = 0) :
    dyadicSpinProjection q a ζ (m + 1) k * dyadicSpinProjection q a ζ (m + 1) l = 0 := by
  have hc := dyadicSpinProjection_commute_factor q a ζ hqstar hqq hleft hright hcomm hstar
    m m l le_rfl (ζ m ^ k)
  change (dyadicSpinProjection q a ζ m k * carSpinProjection q (a m) (ζ m ^ k)) *
    (dyadicSpinProjection q a ζ m l * carSpinProjection q (a m) (ζ m ^ l)) = 0
  calc
    _ = dyadicSpinProjection q a ζ m k *
        (carSpinProjection q (a m) (ζ m ^ k) * dyadicSpinProjection q a ζ m l) *
          carSpinProjection q (a m) (ζ m ^ l) := by noncomm_ring
    _ = (dyadicSpinProjection q a ζ m k * dyadicSpinProjection q a ζ m l) *
        (carSpinProjection q (a m) (ζ m ^ k) * carSpinProjection q (a m) (ζ m ^ l)) := by
      rw [← hc.eq]
      noncomm_ring
    _ = 0 := by rw [hparent, zero_mul]

include hqstar hqq hleft hright hzero hgram hcomm hstar hunit hhalf in
lemma dyadicSpinProjection_opposite_children (m k : ℕ) :
    dyadicSpinProjection q a ζ (m + 1) k *
      dyadicSpinProjection q a ζ (m + 1) (k + 2 ^ m) = 0 := by
  rw [dyadicSpinProjection_upper_half q a ζ hhalf]
  have hc := dyadicSpinProjection_commute_factor q a ζ hqstar hqq hleft hright hcomm hstar
    m m k le_rfl (ζ m ^ k)
  have hp := carSpinProjection_isStarProjection q (a m) hqstar hqq (hleft m) (hright m)
    (hzero m) (hgram m) (ζ m ^ k) (by rw [norm_pow, hunit, one_pow])
  have hs := (carSpinProjection_support q (a m) hqstar hqq (hleft m) (hright m) (ζ m ^ k)).2
  change (dyadicSpinProjection q a ζ m k * carSpinProjection q (a m) (ζ m ^ k)) *
    (dyadicSpinProjection q a ζ m k * (q - carSpinProjection q (a m) (ζ m ^ k))) = 0
  calc
    _ = dyadicSpinProjection q a ζ m k *
        (carSpinProjection q (a m) (ζ m ^ k) * dyadicSpinProjection q a ζ m k) *
          (q - carSpinProjection q (a m) (ζ m ^ k)) := by noncomm_ring
    _ = (dyadicSpinProjection q a ζ m k * dyadicSpinProjection q a ζ m k) *
        (carSpinProjection q (a m) (ζ m ^ k) * (q - carSpinProjection q (a m) (ζ m ^ k))) := by
      rw [← hc.eq]
      noncomm_ring
    _ = 0 := by rw [mul_sub, hs, hp.isIdempotentElem.eq, sub_self, mul_zero]

include hqstar hqq hleft hright hzero hgram hcomm hstar hunit hhalf in
lemma dyadicSpinProjection_orthogonal : ∀ m k l : ℕ,
    k < 2 ^ m → l < 2 ^ m → k ≠ l →
      dyadicSpinProjection q a ζ m k * dyadicSpinProjection q a ζ m l = 0 := by
  intro m
  induction m with
  | zero => intro k l hk hl hne; norm_num at hk hl; omega
  | succ m ih =>
    intro k l hk hl hne
    have hk' : k < 2 ^ m + 2 ^ m := by simpa only [pow_succ, Nat.mul_two] using hk
    have hl' : l < 2 ^ m + 2 ^ m := by simpa only [pow_succ, Nat.mul_two] using hl
    by_cases hkm : k < 2 ^ m
    · by_cases hlm : l < 2 ^ m
      · exact dyadicSpinProjection_next_mul_eq_zero q a ζ hqstar hqq hleft hright hcomm hstar
          m k l (ih k l hkm hlm hne)
      · have hlower : l - 2 ^ m < 2 ^ m := by omega
        have hleq : l = (l - 2 ^ m) + 2 ^ m := by omega
        by_cases hkl : k = l - 2 ^ m
        · rw [hleq, ← hkl]
          exact dyadicSpinProjection_opposite_children q a ζ hqstar hqq hleft hright
            hzero hgram hcomm hstar hunit hhalf m k
        · apply dyadicSpinProjection_next_mul_eq_zero q a ζ hqstar hqq hleft hright hcomm hstar
          rw [hleq, dyadicSpinProjection_period q a ζ hhalf]
          exact ih k (l - 2 ^ m) hkm hlower hkl
    · have klower : k - 2 ^ m < 2 ^ m := by omega
      have hkeq : k = (k - 2 ^ m) + 2 ^ m := by omega
      by_cases hlm : l < 2 ^ m
      · by_cases hkl : l = k - 2 ^ m
        · have hz : dyadicSpinProjection q a ζ (m + 1) l *
              dyadicSpinProjection q a ζ (m + 1) k = 0 := by
            rw [hkeq, ← hkl]
            exact dyadicSpinProjection_opposite_children q a ζ hqstar hqq hleft hright
              hzero hgram hcomm hstar hunit hhalf m l
          have hp₁ := (dyadicSpinProjection_isStarProjection q a ζ hqstar hqq hleft hright
            hzero hgram hcomm hstar hunit (m + 1) k).isSelfAdjoint.star_eq
          have hp₂ := (dyadicSpinProjection_isStarProjection q a ζ hqstar hqq hleft hright
            hzero hgram hcomm hstar hunit (m + 1) l).isSelfAdjoint.star_eq
          simpa only [star_mul, hp₁, hp₂, star_zero] using congrArg star hz
        · apply dyadicSpinProjection_next_mul_eq_zero q a ζ hqstar hqq hleft hright hcomm hstar
          rw [hkeq, dyadicSpinProjection_period q a ζ hhalf]
          exact ih (k - 2 ^ m) l klower hlm (Ne.symm hkl)
      · have llower : l - 2 ^ m < 2 ^ m := by omega
        have hleq : l = (l - 2 ^ m) + 2 ^ m := by omega
        have hdiff : k - 2 ^ m ≠ l - 2 ^ m := by omega
        apply dyadicSpinProjection_next_mul_eq_zero q a ζ hqstar hqq hleft hright hcomm hstar
        rw [hkeq, hleq, dyadicSpinProjection_period q a ζ hhalf,
          dyadicSpinProjection_period q a ζ hhalf]
        exact ih (k - 2 ^ m) (l - 2 ^ m) klower llower hdiff

end Dyadic
end WeakPureInfiniteness

end

end OAI
