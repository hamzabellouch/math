import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.PCP.FinalConstants
import OAI.Computability.BinPacking.PCP.PoweringTableSemantics

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.PoweringNumeric

theorem min_density_ratio (ε C k t : ℝ)
    (hε : 0 < ε) (hC : 0 < C) (hk : 0 ≤ k)
    (ht : 0 < t) (hkt : k ≤ t) :
    min ε (1 / t) / (C + 1) ≤ ε / (C + k * ε) := by
  have hx : 0 ≤ min ε (1 / t) :=
    le_min hε.le (one_div_nonneg.mpr ht.le)
  have hxt : min ε (1 / t) * t ≤ 1 :=
    (le_div_iff₀ ht).mp (min_le_right ε (1 / t))
  have hkx : k * min ε (1 / t) ≤ 1 := by
    calc
      k * min ε (1 / t) ≤ t * min ε (1 / t) :=
        mul_le_mul_of_nonneg_right hkt hx
      _ ≤ 1 := by simpa only [mul_comm] using hxt
  have hC1 : 0 < C + 1 := by positivity
  have hden : 0 < C + k * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  apply (div_le_div_iff₀ hC1 hden).2
  calc
    min ε (1 / t) * (C + k * ε) =
        C * min ε (1 / t) + ε * (k * min ε (1 / t)) := by ring
    _ ≤ C * ε + ε * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (min_le_left ε (1 / t)) hC.le)
        (mul_le_mul_of_nonneg_left hkx hε.le)
    _ = ε * (C + 1) := by ring

theorem count_moment_ratio_lower (α ε C t : ℝ) (m : ℕ)
    (hm : 0 < m) (hε : 0 < ε) (hC : 0 < C) (ht : 0 < t)
    (hmt : (m : ℝ) - 1 ≤ t) :
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) ≤
      (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hk : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hm1
  have hden : 0 < C + ((m : ℝ) - 1) * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  have hαm : 0 ≤ α ^ 4 * (m : ℝ) := by positivity
  have hratio := min_density_ratio ε C ((m : ℝ) - 1) t hε hC hk ht hmt
  calc
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) =
        (α ^ 4 * (m : ℝ)) * (min ε (1 / t) / (C + 1)) := by ring
    _ ≤ (α ^ 4 * (m : ℝ)) * (ε / (C + ((m : ℝ) - 1) * ε)) :=
      mul_le_mul_of_nonneg_left hratio hαm
    _ = (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
      field_simp [ne_of_gt hm0, ne_of_gt hε, ne_of_gt hden]

end BinPackingGames.Foundations.PCP.PoweringNumeric

namespace BinPackingGames.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringWitness PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

def center (q M : Nat) : Nat := (4 * q * M) ^ 2

theorem le_center (q M : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M) : M ≤ center q M := by
  have hfour : 1 ≤ 4 * q := by omega
  have hx : M ≤ 4 * q * M := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right M hfour
  have hone : 1 ≤ 4 * q * M := hM.trans hx
  have hsquare : 4 * q * M ≤ (4 * q * M) * (4 * q * M) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * q * M) hone
  exact hx.trans (by simpa only [center, pow_two] using hsquare)

def gain (q M : Nat) (lambda : ℝ) : ℝ :=
  (1 / (2 * (q : ℝ))) ^ 4 * ((2 * M + 1 : Nat) : ℝ) /
    ((1 + 2 / (1 - lambda)) + 1)

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

def decodedError (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A) : ℝ :=
  edgeDensity (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))

def poweredRejection (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) : ℝ :=
  mean (fun d : Dart V D n => bit ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false))

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem witness_bit_eq (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    bit (witness G accepts n selectors labels fallback
      (decoded G (n + 1) N selectors labels fallback) w k) =
      vertexWitness G
        (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))
        (matchFn G (n + 1) N selectors labels fallback) n k w := by
  simp only [witness, vertexWitness, endpointWitness, matchFn,
    PoweringMoment.bit_mul, next, and_assoc]

omit [Nonempty V] in
theorem modal_witness_mean (G : PortGraph V D) (M : Nat) (hM : 1 ≤ M)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A) (k : Fin (2 * center (Fintype.card A) M + 1))
    (hlo : center (Fintype.card A) M - M ≤ k.val)
    (hhi : k.val ≤ center (Fintype.card A) M + M) :
    decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
      (center (Fintype.card A) M) selectors labels fallback / (4 * (Fintype.card A : ℝ) ^ 2) ≤
      mean (fun w => bit (witness (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors labels fallback (decoded (lazyGraph G) (2 * center (Fintype.card A) M + 1)
          (center (Fintype.card A) M) selectors labels fallback) w k)) := by
  have h := lazy_middle_witness_mean G (Fintype.card A) M Fintype.card_pos hM k hlo hhi
    (decodedBad (lazyGraph G) accepts
      (decoded (lazyGraph G) (2 * center (Fintype.card A) M + 1)
        (center (Fintype.card A) M) selectors labels fallback))
    (matchFn (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
    (matchFn_mem_Icc (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
    (decoded_modal_baseline (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
  simp_rw [witness_bit_eq]
  convert h using 1 <;> rfl

theorem rejection_lower_bound (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A)
    (hε : 0 < decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
      (center (Fintype.card A) M) selectors labels fallback) :
    gain (Fintype.card A) M lambda *
        min (decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
          (center (Fintype.card A) M) selectors labels fallback)
          (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ)) ≤
      poweredRejection (lazyGraph G) accepts (2 * center (Fintype.card A) M) selectors labels := by
  let q := Fintype.card A
  let N := center q M
  let n := 2 * N
  let m := 2 * M + 1
  let start := N - M
  let L := lazyGraph G
  let assignment := decoded L (n + 1) N selectors labels fallback
  let bad := decodedBad L accepts assignment
  let ε := edgeDensity bad
  let α : ℝ := 1 / (2 * (q : ℝ))
  let C : ℝ := 1 + 2 / (1 - lambda)
  have hNM : M ≤ N := le_center q M Fintype.card_pos hM
  have hw : start + m ≤ n + 1 := by dsimp [start, m, n]; omega
  let E := windowEvent L bad n start m hw
  let W : Fin m → Walk V (Bool × D) (n + 1) → Prop := fun i w =>
    witness L accepts n selectors labels fallback assignment w (windowIndex n start m hw i)
  let R : Walk V (Bool × D) (n + 1) → Prop := fun w =>
    pathAccepts L accepts n selectors w (labels w.1) (labels (endpoint L w)) = false
  have hWE : ∀ i w, W i w → E i w := by
    intro i w h
    exact h.1
  have hWR : ∀ i w, W i w → R w := by
    intro i w h
    exact witness_implies_path_rejection L accepts n selectors labels fallback assignment w
      (windowIndex n start m hw i) h
  have hpoint (i : Fin m) : ε / (4 * (q : ℝ) ^ 2) ≤ mean (fun w => bit (W i w)) := by
    have hlo : N - M ≤ (windowIndex n start m hw i).val := by
      dsimp [windowIndex, start]
      omega
    have hhi : (windowIndex n start m hw i).val ≤ N + M := by
      have hi := i.isLt
      dsimp [windowIndex, start]
      dsimp [m] at hi
      omega
    exact modal_witness_mean G M hM accepts selectors labels fallback
      (windowIndex n start m hw i) hlo hhi
  have hfirst : α ^ 2 * (m : ℝ) * ε ≤ mean (hits W) := by
    change α ^ 2 * (m : ℝ) * ε ≤ PoweringMoment.mean (hits W)
    rw [PoweringMoment.mean_hits]
    calc
      _ = ∑ _i : Fin m, ε / (4 * (q : ℝ) ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [α]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hpoint i)
  have hsecond : mean (fun w => hits E w ^ 2) ≤
      (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) :=
    window_second_moment_le L lambda certificate bad
      (decodedBad_rot L accepts reverse_accepts assignment) n start m hw
  have hε' : 0 < ε := hε
  have hm : 0 < m := by dsimp [m]; omega
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hqReal : (0 : ℝ) < q := Nat.cast_pos.mpr Fintype.card_pos
  have hden : 0 < 1 - lambda := sub_pos.mpr certificate.lt_one
  have hC : 0 < C := by dsimp [C]; positivity
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hα : 0 < α := by dsimp [α]; positivity
  have ha : 0 < α ^ 2 * (m : ℝ) * ε := by positivity
  have hb : 0 < (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) := by
    have hdiff : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hmOne
    positivity
  have hCS := PoweringMoment.rejection_lower_bound E W R hWE hWR
    (α ^ 2 * (m : ℝ) * ε) ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε))
    ha hb hfirst hsecond
  have ht : (0 : ℝ) < ((n + 1 : Nat) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hmn : m ≤ n + 1 := by dsimp [m, n]; omega
  have hmt : (m : ℝ) - 1 ≤ ((n + 1 : Nat) : ℝ) := by
    have hmnReal : (m : ℝ) ≤ ((n + 1 : Nat) : ℝ) := by exact_mod_cast hmn
    linarith
  have hratio := PoweringNumeric.count_moment_ratio_lower α ε C ((n + 1 : Nat) : ℝ)
    m hm hε' hC ht hmt
  change (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / ((n + 1 : Nat) : ℝ)) ≤ _
  change _ ≤ mean (fun d : Dart V (Bool × D) n =>
    bit ((poweredGraph L accepts n selectors).edgeSatisfied labels d = false))
  rw [rejection_mean_eq_path_mean]
  exact hratio.trans hCS

end BinPackingGames.Foundations.PCP.PoweringSoundness

namespace BinPackingGames.Foundations.PCP.PoweringGap

open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringSoundness PoweringCounting

variable {V D A : Type*}

theorem gain_nonneg (q M : Nat) (lambda : ℝ) (hlambda : lambda < 1) :
    0 ≤ gain q M lambda := by
  have hden : 0 < 1 - lambda := sub_pos.mpr hlambda
  unfold gain
  positivity

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

theorem uniform_count_gap (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G)
      (2 * center (Fintype.card A) M + 1) v)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V (Bool × D)) : ℝ) ≤
        ((baseGraph (lazyGraph G) accepts reverse_accepts).rejectionCount assignment : ℝ))
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A) :
    (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) (2 * center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors).rejectionCount labels : ℝ) := by
  classical
  let L := lazyGraph G
  let N := center (Fintype.card A) M
  let n := 2 * N
  let H := poweredGraph L accepts n selectors
  change (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((n + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) n) : ℝ) ≤
      (H.rejectionCount labels : ℝ)
  rcases eq_or_lt_of_le hepsilon with hzero | hpositive
  · rw [← hzero]
    have hcap : (0 : ℝ) ≤ 1 / ((n + 1 : Nat) : ℝ) := by positivity
    rw [min_eq_left hcap, mul_zero, zero_mul]
    exact Nat.cast_nonneg _
  · let fallback : A := Classical.choice (inferInstance : Nonempty A)
    let assignment := decoded L (n + 1) N selectors labels fallback
    have hdecoded : epsilon ≤ decodedError L accepts n N selectors labels fallback := by
      change epsilon ≤ edgeDensity (decodedBad L accepts assignment)
      exact base_count_lower_to_density L accepts reverse_accepts assignment
        Fintype.card_pos epsilon (hgap assignment)
    have herror : 0 < decodedError L accepts n N selectors labels fallback :=
      hpositive.trans_le hdecoded
    have hsound := PoweringSoundness.rejection_lower_bound G lambda certificate
      accepts reverse_accepts M hM selectors labels fallback herror
    have hgain : 0 ≤ gain (Fintype.card A) M lambda :=
      gain_nonneg (Fintype.card A) M lambda certificate.lt_one
    have hmin : min epsilon (1 / ((n + 1 : Nat) : ℝ)) ≤
        min (decodedError L accepts n N selectors labels fallback)
          (1 / ((n + 1 : Nat) : ℝ)) :=
      min_le_min hdecoded (le_refl _)
    have hlower : gain (Fintype.card A) M lambda *
        min epsilon (1 / ((n + 1 : Nat) : ℝ)) ≤
        poweredRejection L accepts n selectors labels :=
      (mul_le_mul_of_nonneg_left hmin hgain).trans hsound
    exact (constraint_rejection_lower_iff H labels Fintype.card_pos
      (gain (Fintype.card A) M lambda *
        min epsilon (1 / ((n + 1 : Nat) : ℝ)))).mp hlower

end BinPackingGames.Foundations.PCP.PoweringGap

namespace BinPackingGames.Foundations.PCP.PoweringPortReindex
open PoweringWalks PoweringLabels PoweringReach PoweringTest
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def wordEquiv (ports : D ≃ E) (n : Nat) : (Fin n → D) ≃ (Fin n → E) where
  toFun p := fun i => ports (p i)
  invFun p := fun i => ports.symm (p i)
  left_inv p := by funext i; exact ports.symm_apply_apply (p i)
  right_inv p := by funext i; exact ports.apply_symm_apply (p i)

def walkEquiv (ports : D ≃ E) (n : Nat) : Walk V D n ≃ Walk V E n :=
  Equiv.prodCongr (Equiv.refl V) (wordEquiv ports n)

def addressEquiv (ports : D ≃ E) (t : Nat) : PortWords D t ≃ PortWords E t where
  toFun w := ⟨w.1, wordEquiv ports w.1.val w.2⟩
  invFun w := ⟨w.1, (wordEquiv ports w.1.val).symm w.2⟩
  left_inv w := by rcases w with ⟨n,p⟩; simp
  right_inv w := by rcases w with ⟨n,p⟩; simp

def labelEquiv (ports : D ≃ E) (t : Nat) : PaddedLabel E t A ≃ PaddedLabel D t A where
  toFun a := fun w => a (addressEquiv ports t w)
  invFun a := fun w => a ((addressEquiv ports t).symm w)
  left_inv a := by funext w; simp
  right_inv a := by funext w; simp

variable (G : PortGraph V D) (H : PortGraph V E) (ports : D ≃ E)
variable (rotation : ∀ v d, H.rot (v, ports d) =
  ((G.rot (v,d)).1, ports (G.rot (v,d)).2))

include rotation

theorem wordEnd_map (n : Nat) (v : V) (p : Fin n → D) :
    wordEnd H n v (wordEquiv ports n p) = wordEnd G n v p := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [wordEnd, next, wordEquiv, Equiv.coe_fn_mk, rotation]
    exact ih _ _

theorem endpoint_map (n : Nat) (w : Walk V D n) :
    endpoint H (walkEquiv ports n w) = endpoint G w :=
  wordEnd_map G H ports rotation n w.1 w.2

theorem reach_iff (t : Nat) (v u : V) :
    (∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u) ↔
    (∃ n, n ≤ t ∧ ∃ p : Fin n → E, wordEnd H n v p = u) := by
  constructor
  · rintro ⟨n,hn,p,hp⟩
    exact ⟨n,hn,wordEquiv ports n p,(wordEnd_map G H ports rotation n v p).trans hp⟩
  · rintro ⟨n,hn,p,hp⟩
    refine ⟨n,hn,(wordEquiv ports n).symm p,?_⟩
    rw [← wordEnd_map G H ports rotation, Equiv.apply_symm_apply]
    exact hp

def ballEquiv (t : Nat) (v : V) : Ball G t v ≃ Ball H t v where
  toFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mp u.property⟩
  invFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mpr u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem wordToBall_map (t : Nat) (v : V) (w : PortWords D t) :
    wordToBall H t v (addressEquiv ports t w) =
      ballEquiv G H ports rotation t v (wordToBall G t v w) := by
  apply Subtype.ext
  exact wordEnd_map G H ports rotation w.1.val v w.2

def pullSelector {t : Nat} {v : V} (S : AddressSelector H t v) :
    AddressSelector G t v where
  address u := (addressEquiv ports t).symm
    (S.address (ballEquiv G H ports rotation t v u))
  correct u := by
    apply (ballEquiv G H ports rotation t v).injective
    rw [← wordToBall_map, Equiv.apply_symm_apply, S.correct]

theorem decode_pullSelector {t : Nat} {v : V} (S : AddressSelector H t v)
    (a : PaddedLabel E t A) (u : Ball G t v) :
    decode (pullSelector G H ports rotation S) (labelEquiv ports t a) u =
      decode S a (ballEquiv G H ports rotation t v u) := by
  simp [decode, pullSelector, labelEquiv]

theorem decode_transport {t : Nat} (selectors : ∀v, AddressSelector H t v)
    (a : PaddedLabel E t A) {v w : V} (hvw : v = w)
    (u : Ball G t v) (u' : Ball H t w) (hu : u.val = u'.val) :
    decode (pullSelector G H ports rotation (selectors v)) (labelEquiv ports t a) u =
      decode (selectors w) a u' := by
  subst w
  rw [decode_pullSelector]
  congr 1
  exact Subtype.ext hu

theorem opinionAt_pullSelector (t : Nat) (selectors : ∀v, AddressSelector H t v)
    (labels : V → PaddedLabel E t A) (fallback : A) (u v : V) :
    PoweringOpinions.opinionAt G t (fun v => pullSelector G H ports rotation (selectors v))
      (fun v => labelEquiv ports t (labels v)) fallback u v =
    PoweringOpinions.opinionAt H t selectors labels fallback u v := by
  classical
  unfold PoweringOpinions.opinionAt
  split_ifs with hG hH hH
  · exact decode_pullSelector G H ports rotation (selectors v) (labels v) ⟨u,hG⟩
  · exact False.elim (hH ((reach_iff G H ports rotation t v u).mp hG))
  · exact False.elim (hG ((reach_iff G H ports rotation t v u).mpr hH))
  · rfl

theorem advanceTail_map (n : Nat) (w : Walk V D (n+1)) :
    advanceTail H (walkEquiv ports (n+1) w) =
      walkEquiv ports n (advanceTail G w) := by
  apply Prod.ext
  · change (H.rot (w.1, ports (w.2 0))).1 = (G.rot (w.1,w.2 0)).1
    rw [rotation]
  · rfl

theorem edgeAt_map (n : Nat) (w : Walk V D (n+1)) (k : Fin (n+1)) :
    edgeAt H n (walkEquiv ports (n+1) w) k =
      ((edgeAt G n w k).1, ports (edgeAt G n w k).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction k using Fin.cases with
    | zero => rfl
    | succ k =>
      simp only [edgeAt, Fin.cases_succ]
      rw [advanceTail_map G H ports rotation]
      exact ih _ _

variable (accepts : Edge V E → A → A → Bool)

def pullAccepts : Edge V D → A → A → Bool :=
  fun e => accepts (e.1, ports e.2)

theorem pathAccepts_map (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (w : Walk V D (n+1)) (a b : PaddedLabel E (n+1) A) :
    pathAccepts G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v)) w
      (labelEquiv ports (n+1) a) (labelEquiv ports (n+1) b) =
    pathAccepts H accepts n selectors (walkEquiv ports (n+1) w) a b := by
  classical
  unfold pathAccepts
  congr 1
  apply propext
  apply forall_congr'
  intro k
  have ht := decode_transport G H ports rotation selectors a rfl
    (tailFromStart G n w k) (tailFromStart H n (walkEquiv ports (n+1) w) k)
    (congrArg Prod.fst (edgeAt_map G H ports rotation n w k)).symm
  have hh := decode_transport G H ports rotation selectors b
    (endpoint_map G H ports rotation (n+1) w).symm
    (headFromEnd G n w k) (headFromEnd H n (walkEquiv ports (n+1) w) k)
    (by
      change (G.rot (edgeAt G n w k)).1 =
        (H.rot (edgeAt H n (walkEquiv ports (n+1) w) k)).1
      rw [edgeAt_map G H ports rotation, rotation])
  rw [ht, hh]
  simp only [pullAccepts, edgeAt_map G H ports rotation]
  rfl

def dartEquiv (n : Nat) : Dart V D n ≃ Dart V E n :=
  Equiv.prodCongr (Equiv.refl Bool) (walkEquiv ports (n+1))

theorem edgeSatisfied_map (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (labels : V → PaddedLabel E (n+1) A) (e : Dart V D n) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).edgeSatisfied
        (fun v => labelEquiv ports (n+1) (labels v)) e =
    (poweredGraph H accepts n selectors).edgeSatisfied labels (dartEquiv ports n e) := by
  rcases e with ⟨direction,w⟩
  rw [poweredGraph_edgeSatisfied]
  change _ = (poweredGraph H accepts n selectors).edgeSatisfied labels
    (direction, walkEquiv ports (n+1) w)
  rw [poweredGraph_edgeSatisfied, endpoint_map G H ports rotation]
  exact pathAccepts_map G H ports rotation accepts n selectors w _ _

theorem rejectionCount_map [Fintype V] [Fintype D] [Fintype E]
    (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (labels : V → PaddedLabel E (n+1) A) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).rejectionCount
        (fun v => labelEquiv ports (n+1) (labels v)) =
    (poweredGraph H accepts n selectors).rejectionCount labels := by
  classical
  unfold ConstraintGraph.rejectionCount
  apply Finset.card_bij (fun e _ => dartEquiv ports n e)
  · intro e he
    rw [ConstraintGraph.mem_rejectedDarts, ← edgeSatisfied_map G H ports rotation]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp he
  · intro e _ f _ h
    exact (dartEquiv ports n).injective h
  · intro e he
    refine ⟨(dartEquiv ports n).symm e, ?_, (dartEquiv ports n).apply_symm_apply e⟩
    rw [ConstraintGraph.mem_rejectedDarts, edgeSatisfied_map G H ports rotation,
      Equiv.apply_symm_apply]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp he

theorem satisfiable_iff (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).Satisfiable ↔
    (poweredGraph H accepts n selectors).Satisfiable := by
  constructor
  · rintro ⟨labels,hlabels⟩
    refine ⟨fun v => (labelEquiv ports (n+1)).symm (labels v), ?_⟩
    intro e
    obtain ⟨e,rfl⟩ := (dartEquiv ports n).surjective e
    rw [← edgeSatisfied_map G H ports rotation]
    simpa only [Equiv.apply_symm_apply] using hlabels e
  · rintro ⟨labels,hlabels⟩
    refine ⟨fun v => labelEquiv ports (n+1) (labels v), ?_⟩
    intro e
    rw [edgeSatisfied_map G H ports rotation]
    exact hlabels _

theorem pullReverse
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (e : Edge V D) (a b : A) :
    pullAccepts ports accepts (G.rot e) b a = pullAccepts ports accepts e a b := by
  simpa only [pullAccepts, rotation] using reverse_accepts (e.1,ports e.2) a b

theorem base_edgeSatisfied_map
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    (baseGraph G (pullAccepts ports accepts)
      (pullReverse G H ports rotation accepts reverse_accepts)).edgeSatisfied assignment e =
    (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (e.1,ports e.2) := by
  change accepts (e.1,ports e.2) (assignment e.1) (assignment (G.rot e).1) =
    accepts (e.1,ports e.2) (assignment e.1) (assignment (H.rot (e.1,ports e.2)).1)
  rw [rotation]

theorem base_rejectionCount_map [Fintype V] [Fintype D] [Fintype E]
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (assignment : V → A) :
    (baseGraph G (pullAccepts ports accepts)
      (pullReverse G H ports rotation accepts reverse_accepts)).rejectionCount assignment =
    (baseGraph H accepts reverse_accepts).rejectionCount assignment := by
  classical
  let e : Edge V D ≃ Edge V E := Equiv.prodCongr (Equiv.refl V) ports
  have edgeEq (x : Edge V D) :=
    base_edgeSatisfied_map G H ports rotation accepts reverse_accepts assignment x
  unfold ConstraintGraph.rejectionCount
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    rw [ConstraintGraph.mem_rejectedDarts]
    change (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (x.1,ports x.2) = false
    rw [← edgeEq]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp hx
  · intro x _ y _ h
    exact e.injective h
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [ConstraintGraph.mem_rejectedDarts, edgeEq]
    change (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (e (e.symm y)) = false
    rw [e.apply_symm_apply]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp hy

omit rotation in

theorem uniform_count_gap
    [Fintype V] [Fintype D] [Fintype E] [Nonempty V] [Nonempty D]
    [Fintype A] [Nonempty A]
    (G : PortGraph V D) (H : PortGraph V E) (ports : (Bool × D) ≃ E)
    (rotation : ∀ v d, H.rot (v, ports d) =
      (((lazyGraph G).rot (v,d)).1, ports ((lazyGraph G).rot (v,d)).2))
    (lambda : ℝ) (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V E → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀v, AddressSelector H (2*center (Fintype.card A) M+1) v)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V E) : ℝ) ≤
        ((baseGraph H accepts reverse_accepts).rejectionCount assignment : ℝ))
    (labels : V → PaddedLabel E (2*center (Fintype.card A) M+1) A) :
    (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((2*center (Fintype.card A) M+1 : Nat) : ℝ))) *
        (Fintype.card (Dart V E (2*center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph H accepts (2*center (Fintype.card A) M) selectors).rejectionCount labels : ℝ) := by
  have hbase : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V (Bool × D)) : ℝ) ≤
      ((baseGraph (lazyGraph G) (pullAccepts ports accepts)
        (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts)).rejectionCount assignment : ℝ) := by
    intro assignment
    rw [base_rejectionCount_map (lazyGraph G) H ports rotation,
      Fintype.card_congr (Equiv.prodCongr (Equiv.refl V) ports)]
    exact hgap assignment
  have bound := PoweringGap.uniform_count_gap G lambda certificate
    (pullAccepts ports accepts)
    (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts) M hM
    (fun v => pullSelector (lazyGraph G) H ports rotation (selectors v))
    epsilon hepsilon hbase (fun v => labelEquiv ports _ (labels v))
  rw [rejectionCount_map (lazyGraph G) H ports rotation,
    Fintype.card_congr (dartEquiv (V := V) ports (2*center (Fintype.card A) M))] at bound
  exact bound

omit rotation in

theorem lazy_table_uniform_count_gap {vertices d : Nat}
    (input : PortTables.Table vertices d) (hv : 0 < vertices) (hd : 0 < d)
    (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph (PortTables.portGraph input)) lambda)
    (M : Nat) (hM : 1 ≤ M) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : Fin vertices → Fin 64,
      epsilon * (Fintype.card (Fin vertices × Fin (2*d)) : ℝ) ≤
        ((PortTables.baseGraph (PreprocessingOverlayTables.lazy input)).rejectionCount assignment : ℝ)) :
    ∀ labels : PoweringTableSemantics.EncodedLabeling vertices (2*d) (2*center 64 M),
    (gain 64 M lambda * min epsilon (1 / ((2*center 64 M+1 : Nat) : ℝ))) *
      ((PoweringTables.table (PreprocessingOverlayTables.lazy input) (2*center 64 M)).darts : ℝ) ≤
      ((GenericGraphTables.semantics
        (PoweringTables.table (PreprocessingOverlayTables.lazy input) (2*center 64 M))).rejectionCount labels : ℝ) := by
  let : Nonempty (Fin vertices) := ⟨⟨0,hv⟩⟩
  let : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  apply PoweringTableSemantics.uniform_count_gap
  intro labels
  have hrot : ∀ v p,
      (PortTables.portGraph (PreprocessingOverlayTables.lazy input)).rot
          (v, PreprocessingOverlayTables.lazyPorts d p) =
        (((lazyGraph (PortTables.portGraph input)).rot (v,p)).1,
          PreprocessingOverlayTables.lazyPorts d
            ((lazyGraph (PortTables.portGraph input)).rot (v,p)).2) := by
    intro v p
    rw [PreprocessingTableSpectral.lazy_portGraph]
    exact GraphTransport.reindex_rot _ (Equiv.refl _) _ v p
  have bound := uniform_count_gap (PortTables.portGraph input)
      (PortTables.portGraph (PreprocessingOverlayTables.lazy input))
      (PreprocessingOverlayTables.lazyPorts d) hrot lambda certificate
      (PortTables.accepts (PreprocessingOverlayTables.lazy input))
      (PortTables.accepts_rotation (PreprocessingOverlayTables.lazy input)) M hM
      (PoweringAddresses.finitePortSelector
        (PortTables.portGraph (PreprocessingOverlayTables.lazy input)) _) epsilon hepsilon
      hgap
  simp only [PortTables.Label, GraphTables.Label, Fintype.card_fin] at bound
  exact bound labels

omit rotation in

theorem lazy_table_uniform_count_gap_at {vertices d : Nat}
    (input : PortTables.Table vertices d) (hv : 0 < vertices) (hd : 0 < d)
    (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph (PortTables.portGraph input)) lambda)
    (M : Nat) (hM : 1 ≤ M) (n : Nat) (hn : n = 2*center 64 M)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : Fin vertices → Fin 64,
      epsilon * (Fintype.card (Fin vertices × Fin (2*d)) : ℝ) ≤
        ((PortTables.baseGraph (PreprocessingOverlayTables.lazy input)).rejectionCount
          assignment : ℝ)) :
    ∀ labels : PoweringTableSemantics.EncodedLabeling vertices (2*d) n,
    (gain 64 M lambda * min epsilon (1 / ((n+1 : Nat) : ℝ))) *
      ((PoweringTables.table (PreprocessingOverlayTables.lazy input) n).darts : ℝ) ≤
      ((GenericGraphTables.semantics
        (PoweringTables.table (PreprocessingOverlayTables.lazy input) n)).rejectionCount
          labels : ℝ) := by
  subst n
  exact lazy_table_uniform_count_gap input hv hd lambda certificate M hM
    epsilon hepsilon hgap

end BinPackingGames.Foundations.PCP.PoweringPortReindex

namespace BinPackingGames.Foundations.PCP.PoweringFinalConstants

abbrev Alphabet := Fin 6 → Bool

@[simp] theorem card_alphabet : Fintype.card Alphabet = 64 := by
  norm_num [Alphabet, Fintype.card_fun]

theorem card_alphabet_eq_final : Fintype.card Alphabet = FinalConstants.alphabet := by
  exact card_alphabet

theorem center_eq :
    PoweringSoundness.center (Fintype.card Alphabet) FinalConstants.windowHalf =
      FinalConstants.endpointLength := by
  rw [card_alphabet]
  rfl

theorem walkLength_eq :
    2 * PoweringSoundness.center (Fintype.card Alphabet) FinalConstants.windowHalf + 1 =
      FinalConstants.walkLength := by
  rw [center_eq]
  rfl

theorem spectral_denominator_eq :
    (1 + 2 / (1 - (31 / 32 : ℝ))) + 1 = 66 := by
  norm_num

theorem gain_eq :
    PoweringSoundness.gain 64 FinalConstants.windowHalf (31 / 32) / 12288 =
      FinalConstants.gain := by
  change
    (1 / (2 * (FinalConstants.alphabet : ℝ))) ^ 4 *
        (FinalConstants.windowSize : ℝ) /
        ((1 + 2 / (1 - (31 / 32 : ℝ))) + 1) /
        (FinalConstants.compositionLoss : ℝ) =
      (FinalConstants.windowSize : ℝ) / (FinalConstants.denominator : ℝ)
  rw [spectral_denominator_eq]
  have hden : (FinalConstants.denominator : ℝ) =
      16 * (FinalConstants.alphabet : ℝ) ^ 4 * 66 *
        (FinalConstants.compositionLoss : ℝ) := by
    simp only [FinalConstants.denominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hden]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem gain_card_eq :
    PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) /
        12288 = FinalConstants.gain := by
  rw [card_alphabet]
  exact gain_eq

theorem scaled_bound_eq (ε : ℝ) :
    (PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) *
        min ε
          (1 / ((2 * PoweringSoundness.center (Fintype.card Alphabet)
            FinalConstants.windowHalf + 1 : Nat) : ℝ))) / 12288 =
      FinalConstants.gain * min ε FinalConstants.cap := by
  rw [walkLength_eq]
  rw [mul_div_right_comm, gain_card_eq]
  rfl

theorem composed_scaled_gap (ε : ℝ) (hε : 0 ≤ ε) :
    min (2 * ε) FinalConstants.cap ≤
      (PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) *
        min (ε / (Preprocessing.sizeFactor : ℝ))
          (1 / ((2 * PoweringSoundness.center (Fintype.card Alphabet)
            FinalConstants.windowHalf + 1 : Nat) : ℝ))) / 12288 := by
  rw [scaled_bound_eq]
  exact FinalConstants.composed_gap ε hε

end BinPackingGames.Foundations.PCP.PoweringFinalConstants

end

end OAI
