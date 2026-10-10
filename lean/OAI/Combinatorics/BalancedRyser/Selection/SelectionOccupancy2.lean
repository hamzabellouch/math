import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence

namespace OAI

open scoped BigOperators

namespace Balanced.SelectionOccupancy

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P V I : Type*}

def hits (Q : Finset V) (T : Finset P) (R : P → V → Prop) : Finset V :=
  Q.filter (fun v => ∃ p ∈ T, R p v)

theorem card_hits_le (Q : Finset V) (T : Finset P) (R : P → V → Prop)
    (hunique : ∀ p ∈ T, ∀ v ∈ Q, ∀ w ∈ Q, R p v → R p w → v = w) :
    (hits Q T R).card ≤ T.card := by
  classical
  have hsub : hits Q T R ⊆ T.biUnion (fun p => Q.filter (R p)) := by
    intro v hv
    obtain ⟨hvQ, p, hpT, hpv⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_biUnion.mpr ⟨p, hpT, Finset.mem_filter.mpr ⟨hvQ, hpv⟩⟩
  have hcard : ∀ p ∈ T, (Q.filter (R p)).card ≤ 1 := by
    intro p hp
    apply Finset.card_le_one.mpr
    intro v hv w hw
    exact hunique p hp v (Finset.mem_filter.mp hv).1 w (Finset.mem_filter.mp hw).1
      (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2
  simpa using (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le_card_mul T (fun p => Q.filter (R p)) 1 hcard)

def average (slots : Finset I) (Q : I → Finset V) (f : I → V → ℝ) : ℝ :=
  (∑ i ∈ slots, (∑ v ∈ Q i, f i v) / (Q i).card) / slots.card

def hitProbability (slots : Finset I) (Q : I → Finset V)
    (T : Finset P) (R : I → P → V → Prop) : ℝ :=
  (∑ i ∈ slots, ((hits (Q i) T (R i)).card : ℝ) / (Q i).card) / slots.card

theorem average_hit_indicator (slots : Finset I) (Q : I → Finset V)
    (T : Finset P) (R : I → P → V → Prop) :
    average slots Q (fun i v => if ∃ p ∈ T, R i p v then 1 else 0) =
      hitProbability slots Q T R := by
  unfold average hitProbability hits
  simp only [Finset.sum_boole]

theorem hitProbability_le (slots : Finset I) (hslots : slots.Nonempty)
    (Q : I → Finset V) (T : Finset P) (R : I → P → V → Prop)
    (L : ℝ) (hL : 0 < L)
    (hsize : ∀ i ∈ slots, L ≤ ((Q i).card : ℝ))
    (hunique : ∀ i ∈ slots, ∀ p ∈ T, ∀ v ∈ Q i, ∀ w ∈ Q i,
      R i p v → R i p w → v = w) :
    hitProbability slots Q T R ≤ (T.card : ℝ) / L := by
  have hcard : (0 : ℝ) < slots.card := by
    exact_mod_cast Finset.card_pos.mpr hslots
  unfold hitProbability
  apply (div_le_iff₀ hcard).2
  calc
    (∑ i ∈ slots, ((hits (Q i) T (R i)).card : ℝ) / (Q i).card) ≤
        ∑ _i ∈ slots, (T.card : ℝ) / L := by
      apply Finset.sum_le_sum
      intro i hi
      exact div_le_div₀ (Nat.cast_nonneg T.card)
        (by exact_mod_cast card_hits_le (Q i) T (R i) (hunique i hi)) hL (hsize i hi)
    _ = (T.card : ℝ) / L * slots.card := by simp [mul_comm]

theorem average_const (slots : Finset I) (hslots : slots.Nonempty)
    (Q : I → Finset V) (hQ : ∀ i ∈ slots, (Q i).Nonempty) (c : ℝ) :
    average slots Q (fun _ _ => c) = c := by
  have hI : (slots.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hslots).ne'
  unfold average
  have hinner : ∀ i ∈ slots, (∑ _v ∈ Q i, c) / ((Q i).card : ℝ) = c := by
    intro i hi
    have hiQ : ((Q i).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr (hQ i hi)).ne'
    simp [hiQ]
  rw [Finset.sum_congr rfl hinner]
  simp [hI]

theorem average_sub (slots : Finset I) (Q : I → Finset V) (f g : I → V → ℝ) :
    average slots Q (fun i v => f i v - g i v) =
      average slots Q f - average slots Q g := by
  simp only [average, Finset.sum_sub_distrib, sub_div]

theorem remaining_card (T : Finset P) (R : P → V → Prop) (v : V)
    (hsmall : (T.filter (fun p => R p v)).card ≤ 1) :
    ((T.filter (fun p => ¬ R p v)).card : ℝ) =
      (T.card : ℝ) - if ∃ p ∈ T, R p v then 1 else 0 := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := T) (fun p => R p v)
  by_cases hhit : ∃ p ∈ T, R p v
  · have hpos : 0 < (T.filter (fun p => R p v)).card := by
      apply Finset.card_pos.mpr
      obtain ⟨p, hp, hpv⟩ := hhit
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpv⟩⟩
    have hone : (T.filter (fun p => R p v)).card = 1 := by omega
    have hsumR : (1 : ℝ) + ((T.filter (fun p => ¬ R p v)).card : ℝ) = T.card := by
      exact_mod_cast (hone ▸ hsum)
    simp only [ite_eq_left hhit]
    linarith
  · have hzero : (T.filter (fun p => R p v)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hhit ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
    have heq : (T.filter (fun p => ¬ R p v)).card = T.card := by omega
    simp [hhit, heq]

theorem average_remaining_eq (slots : Finset I) (hslots : slots.Nonempty)
    (Q : I → Finset V) (hQ : ∀ i ∈ slots, (Q i).Nonempty)
    (T : Finset P) (R : I → P → V → Prop)
    (hsmall : ∀ i ∈ slots, ∀ v ∈ Q i, (T.filter (fun p => R i p v)).card ≤ 1) :
    average slots Q (fun i v => ((T.filter (fun p => ¬ R i p v)).card : ℝ)) =
      (T.card : ℝ) - hitProbability slots Q T R := by
  have heq : average slots Q (fun i v => ((T.filter (fun p => ¬ R i p v)).card : ℝ)) =
      average slots Q (fun i v => (T.card : ℝ) - if ∃ p ∈ T, R i p v then 1 else 0) := by
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    exact remaining_card T (R i) v (hsmall i hi v hv)
  rw [heq, average_sub, average_const slots hslots Q hQ, average_hit_indicator]

theorem average_remaining_ge (slots : Finset I) (hslots : slots.Nonempty)
    (Q : I → Finset V) (T : Finset P) (R : I → P → V → Prop)
    (L : ℝ) (hL : 0 < L)
    (hsize : ∀ i ∈ slots, L ≤ ((Q i).card : ℝ))
    (hunique : ∀ i ∈ slots, ∀ p ∈ T, ∀ v ∈ Q i, ∀ w ∈ Q i,
      R i p v → R i p w → v = w)
    (hsmall : ∀ i ∈ slots, ∀ v ∈ Q i, (T.filter (fun p => R i p v)).card ≤ 1) :
    (1 - L⁻¹) * (T.card : ℝ) ≤
      average slots Q (fun i v => ((T.filter (fun p => ¬ R i p v)).card : ℝ)) := by
  have hQ : ∀ i ∈ slots, (Q i).Nonempty := by
    intro i hi
    apply Finset.card_pos.mp
    have : (0 : ℝ) < (Q i).card := hL.trans_le (hsize i hi)
    exact_mod_cast this
  rw [average_remaining_eq slots hslots Q hQ T R hsmall]
  have hhit := hitProbability_le slots hslots Q T R L hL hsize hunique
  rw [div_eq_mul_inv] at hhit
  nlinarith

theorem average_remaining_ge_ratio (slots : Finset I) (hslots : slots.Nonempty)
    (Q : I → Finset V) (T : Finset P) (R : I → P → V → Prop)
    (q B : ℝ) (hq : 0 < q) (hB : 0 < B)
    (hsize : ∀ i ∈ slots, q / B ≤ ((Q i).card : ℝ))
    (hunique : ∀ i ∈ slots, ∀ p ∈ T, ∀ v ∈ Q i, ∀ w ∈ Q i,
      R i p v → R i p w → v = w)
    (hsmall : ∀ i ∈ slots, ∀ v ∈ Q i, (T.filter (fun p => R i p v)).card ≤ 1) :
    (1 - B / q) * (T.card : ℝ) ≤
      average slots Q (fun i v => ((T.filter (fun p => ¬ R i p v)).card : ℝ)) := by
  simpa only [inv_div] using
    average_remaining_ge slots hslots Q T R (q / B) (div_pos hq hB) hsize hunique hsmall

theorem average_div (slots : Finset I) (Q : I → Finset V)
    (f : I → V → ℝ) (d : ℝ) :
    average slots Q (fun i v => f i v / d) = average slots Q f / d := by
  unfold average
  simp only [div_eq_mul_inv]
  have h : ∀ i, (∑ v ∈ Q i, f i v * d⁻¹) * ((Q i).card : ℝ)⁻¹ =
      ((∑ v ∈ Q i, f i v) * ((Q i).card : ℝ)⁻¹) * d⁻¹ := by
    intro i
    rw [← Finset.sum_mul]
    ring
  simp_rw [h]
  rw [← Finset.sum_mul]
  ring

theorem rescaled_average_ge (slots : Finset I) (Q : I → Finset V)
    (f : I → V → ℝ) (t c : ℝ) (n : ℕ) (hc : 0 < c)
    (hmean : c * t ≤ average slots Q f) :
    t / c ^ n ≤ average slots Q (fun i v => f i v / c ^ (n + 1)) := by
  rw [average_div]
  apply (le_div_iff₀ (pow_pos hc _)).2
  have heq : t / c ^ n * c ^ (n + 1) = c * t := by
    rw [pow_succ]
    field_simp
  simpa only [heq] using hmean

theorem rescaled_increment_abs_le {t t' c a b d L M : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (ha : 0 < a) (hb : b = c * a)
    (hd : 0 < d) (hdb : d ≤ b) (ht : 0 ≤ t) (htM : t ≤ M)
    (hL : 0 ≤ L) (hjump : |t' - t| ≤ L) :
    |t' / b - t / a| ≤ (L + (1 - c) * M) / d := by
  have hbpos : 0 < b := by rw [hb]; positivity
  have hscale : 0 ≤ (1 - c) * t := mul_nonneg (sub_nonneg.mpr hc1) ht
  have hscaleM : (1 - c) * t ≤ (1 - c) * M :=
    mul_le_mul_of_nonneg_left htM (sub_nonneg.mpr hc1)
  have heq : t' / b - t / a = (t' - t + (1 - c) * t) / b := by
    rw [hb]
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hbpos]
  apply div_le_div₀ (add_nonneg hL (mul_nonneg (sub_nonneg.mpr hc1) (ht.trans htM)))
    ?_ hd hdb
  calc
    |t' - t + (1 - c) * t| ≤ |t' - t| + |(1 - c) * t| := abs_add_le _ _
    _ = |t' - t| + (1 - c) * t := by rw [abs_of_nonneg hscale]
    _ ≤ L + (1 - c) * M := add_le_add hjump hscaleM

section Affine

variable {F : Type*} [Field F]

theorem line_eq_of_direction_eq_of_incident {l m : Line F} {p : Point F}
    (hd : l.1 = m.1) (hl : OnLine p l) (hm : OnLine p m) : l = m := by
  apply Prod.ext hd
  exact hl.symm.trans ((congrArg (fun d => lineEval d p) hd).trans hm)

theorem card_affine_hits_le (Q : Finset V) (T : Finset (Point F))
    (lineOf : V → Line F) (d : Direction F)
    (hinj : Set.InjOn lineOf (↑Q : Set V))
    (hdir : ∀ v ∈ Q, (lineOf v).1 = d)
    (eligible : V → Prop) :
    (hits Q T (fun p v => eligible v ∧ OnLine p (lineOf v))).card ≤ T.card := by
  apply card_hits_le
  intro p hp v hv w hw hpv hpw
  exact hinj hv hw (line_eq_of_direction_eq_of_incident
    ((hdir v hv).trans (hdir w hw).symm) hpv.2 hpw.2)

def afterLine (T : Finset (Point F)) (tracked chosen : Line F) : Finset (Point F) :=
  T.filter (fun p => ¬ (chosen ≠ tracked ∧ OnLine p chosen))

@[simp] theorem afterLine_self (T : Finset (Point F)) (l : Line F) :
    afterLine T l l = T := by simp [afterLine]

theorem afterLine_of_ne (T : Finset (Point F)) {l m : Line F} (hne : m ≠ l) :
    afterLine T l m = T.filter (fun p => ¬ OnLine p m) := by simp [afterLine, hne]

theorem affine_deletion_card_le_one (T : Finset (Point F)) (l m : Line F)
    (hT : ∀ p ∈ T, OnLine p l) :
    (T.filter (fun p => m ≠ l ∧ OnLine p m)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp r hr
  obtain ⟨hpT, hne, hpm⟩ := Finset.mem_filter.mp hp
  obtain ⟨hrT, _, hrm⟩ := Finset.mem_filter.mp hr
  exact Balanced.common_point_eq_of_lines_ne l m hne.symm p r
    (hT p hpT) hpm (hT r hrT) hrm

theorem affine_occupancy_drift (slots : Finset I) (hslots : slots.Nonempty)
    (Q : I → Finset V) (lineOf : I → V → Line F) (direction : I → Direction F)
    (hinj : ∀ i ∈ slots, Set.InjOn (lineOf i) (↑(Q i) : Set V))
    (hdir : ∀ i ∈ slots, ∀ v ∈ Q i, (lineOf i v).1 = direction i)
    (l : Line F) (T : Finset (Point F)) (hT : ∀ p ∈ T, OnLine p l)
    (q B : ℝ) (hq : 0 < q) (hB : 0 < B)
    (hsize : ∀ i ∈ slots, q / B ≤ ((Q i).card : ℝ)) :
    (1 - B / q) * (T.card : ℝ) ≤
      average slots Q (fun i v => ((afterLine T l (lineOf i v)).card : ℝ)) := by
  classical
  have hu : ∀ i ∈ slots, ∀ p ∈ T, ∀ v ∈ Q i, ∀ w ∈ Q i,
      lineOf i v ≠ l ∧ OnLine p (lineOf i v) →
      lineOf i w ≠ l ∧ OnLine p (lineOf i w) → v = w := by
    intro i hi p hp v hv w hw hpv hpw
    exact hinj i hi hv hw (line_eq_of_direction_eq_of_incident
      ((hdir i hi v hv).trans (hdir i hi w hw).symm) hpv.2 hpw.2)
  have hs : ∀ i ∈ slots, ∀ v ∈ Q i,
      (T.filter (fun p => lineOf i v ≠ l ∧ OnLine p (lineOf i v))).card ≤ 1 := by
    intro i hi v hv
    exact affine_deletion_card_le_one T l (lineOf i v) hT
  have h := average_remaining_ge_ratio slots hslots Q T
    (fun i p v => lineOf i v ≠ l ∧ OnLine p (lineOf i v)) q B hq hB hsize hu (by
      intro i hi v hv
      convert hs i hi v hv using 1
      congr 1
      ext p
      simp)
  convert h using 1
  congr 1
  funext i v
  congr 1
  apply congrArg Finset.card
  ext p
  simp [afterLine]

end Affine
end
end Balanced.SelectionOccupancy

end OAI
