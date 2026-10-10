import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import OAI.NumberTheory.Jacobsthal.Estimates.InverseWeightGrowth
import OAI.NumberTheory.Jacobsthal.Primes.HighPrimeRemoval

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeTiltGeometry

open _root_.Erdos970.Set _root_.Erdos970.Finset
open FinitePathGeometry ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def childRatio (w r : ℝ) (p : ℕ) : ℝ := r / primeExponent w p - 1

noncomputable def capGuard (closed : Bool) (cap x : ℝ) : Prop :=
  if closed then x ≤ cap else x < cap

noncomputable def children (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) : Finset ℕ := by
  classical
  exact (Nat.primesLE ⌊w^cap⌋₊).filter (fun p => ell < primeExponent w p ∧
    capGuard closed cap (primeExponent w p) ∧ minRatio i s ≤ childRatio w r p ∧ childRatio w r p ≤ S)

theorem mem_children_iff {w ell S s r cap : ℝ} (hw : 1 < w) (i : Side) (closed : Bool) (p : ℕ) :
    p ∈ children w ell S i s r cap closed ↔ p.Prime ∧ ell < primeExponent w p ∧
      capGuard closed cap (primeExponent w p) ∧ minRatio i s ≤ childRatio w r p ∧ childRatio w r p ≤ S := by
  classical
  unfold children
  simp only [Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_,hp⟩,hx,hcap,ht,hS⟩
    exact ⟨hp,hx,hcap,ht,hS⟩
  · rintro ⟨hp,hx,hcap,ht,hS⟩
    refine ⟨⟨?_,hp⟩,hx,hcap,ht,hS⟩
    have hc : primeExponent w p ≤ cap := by
      cases closed with
      | false => exact (show primeExponent w p < cap from hcap).le
      | true => exact hcap
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hreal : (p : ℝ) ≤ w^cap := (exponent_le_iff hw hp0).mp hc
    exact (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) cap).le).mpr hreal

theorem child_valid {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {p : ℕ}
    (hs : Valid i s) (hp : p ∈ children w ell S i s r cap closed) : Valid i.flip (childRatio w r p) := by
  classical
  have ht := (Finset.mem_filter.mp hp).2.2.2.1
  exact valid_next hs ht

theorem child_exponent_positive {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {p : ℕ}
    (hell : 0 ≤ ell) (hp : p ∈ children w ell S i s r cap closed) : 0 < primeExponent w p := by
  classical
  exact lt_of_le_of_lt hell (Finset.mem_filter.mp hp).2.1

theorem nextExponent_childRatio {w r : ℝ} {p : ℕ} (hr : 0 < r) (hp : 0 < primeExponent w p) :
    nextExponent r (childRatio w r p) = primeExponent w p := by
  unfold nextExponent childRatio
  simp only [sub_add_cancel]
  field_simp

theorem nextGap_childRatio {w r : ℝ} {p : ℕ} (hr : 0 < r) (hp : 0 < primeExponent w p)
    (ht : 0 < childRatio w r p) : nextGap r (childRatio w r p) = r - primeExponent w p := by
  have h := gap_exponent_conservation (r := r) ht
  rw [nextExponent_childRatio hr hp] at h
  linarith

theorem child_gap_positive {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {p : ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s) (hp : p ∈ children w ell S i s r cap closed) :
    0 < r - primeExponent w p := by
  have ht := valid_pos (child_valid hs hp)
  rw [← nextGap_childRatio hr (child_exponent_positive hell hp) ht]
  exact nextGap_pos hr ht

noncomputable def primeTilt (w r : ℝ) (i : Side) (s : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ)⁻¹ * ((childRatio w r p + 1) / childRatio w r p)^2 *
    weight i.flip (childRatio w r p) / weight i s

theorem primeTilt_nonneg {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {p : ℕ}
    (hs : Valid i s) (hp : p ∈ children w ell S i s r cap closed) : 0 ≤ primeTilt w r i s p := by
  unfold primeTilt
  exact div_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) (sq_nonneg _))
    (weight_pos (child_valid hs hp)).le) (weight_pos hs).le

theorem prime_tilt_step_identity {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {p : ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s) (hp : p ∈ children w ell S i s r cap closed) :
    (p : ℝ)⁻¹ = primeTilt w r i s p * ((r - primeExponent w p)/r)^2 *
      (weight i s / weight i.flip (childRatio w r p)) := by
  have ht := valid_pos (child_valid hs hp)
  have hw := weight_pos hs
  have hw' := weight_pos (child_valid hs hp)
  rw [← nextGap_childRatio hr (child_exponent_positive hell hp) ht]
  unfold primeTilt nextGap
  field_simp [hr.ne', ht.ne', hw.ne', hw'.ne']

end NumberTheoryLean.PrimeTiltGeometry

end

section

namespace NumberTheoryLean.PrimeTiltPrefixes

open _root_.Erdos970.Set _root_.Erdos970.Finset
open FinitePathGeometry PrimeTiltGeometry ErdosPrimeInputs.HarmonicPrimeMeasure
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def PrimeAdmissible (w ell S : ℝ) : Side → ℝ → ℝ → ℝ → Bool → List ℕ → Prop
  | _, _, _, _, _, [] => True
  | i, s, r, cap, closed, p::ps => p ∈ children w ell S i s r cap closed ∧
      PrimeAdmissible w ell S i.flip (childRatio w r p) (r-primeExponent w p) (primeExponent w p) false ps

noncomputable def primeRatios (w : ℝ) : ℝ → List ℕ → List ℝ
  | _, [] => []
  | r, p::ps => childRatio w r p :: primeRatios w (r-primeExponent w p) ps

noncomputable def primeFinalGap (w : ℝ) : ℝ → List ℕ → ℝ
  | r, [] => r
  | r, p::ps => primeFinalGap w (r-primeExponent w p) ps

noncomputable def tiltProduct (w : ℝ) : Side → ℝ → ℝ → List ℕ → ℝ
  | _, _, _, [] => 1
  | i, s, r, p::ps => primeTilt w r i s p * tiltProduct w i.flip (childRatio w r p) (r-primeExponent w p) ps

noncomputable def normalizedTiltProduct (e w : ℝ) : Side → ℝ → ℝ → List ℕ → ℝ
  | _, _, _, [] => 1
  | i, s, r, p::ps => (primeTilt w r i s p / (1+e)) *
      normalizedTiltProduct e w i.flip (childRatio w r p) (r-primeExponent w p) ps

theorem ratios_admissible {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) : Admissible i s (primeRatios w r ps) := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => trivial
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    exact ⟨(Finset.mem_filter.mp hp).2.2.2.1, ih hps⟩

theorem primeFinalGap_eq {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    primeFinalGap w r ps = finalGap r (primeRatios w r ps) := by
  induction ps generalizing i s r cap closed with
  | nil => rfl
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    simp only [primeFinalGap, primeRatios, finalGap]
    rw [nextGap_childRatio hr (child_exponent_positive hell hp) (valid_pos (child_valid hs hp))]
    exact ih (child_gap_positive hell hr hs hp) (child_valid hs hp) hps

theorem primeFinalGap_pos {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) : 0 < primeFinalGap w r ps := by
  induction ps generalizing i s r cap closed with
  | nil => exact hr
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    exact ih (child_gap_positive hell hr hs hp) (child_valid hs hp) hps

theorem prime_prefix_weight_identity {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    prefixWeight ps = tiltProduct w i s r ps * (primeFinalGap w r ps / r)^2 *
      (weight i s / weight (finalSide i (primeRatios w r ps)) (finalRatio s (primeRatios w r ps))) := by
  induction ps generalizing i s r cap closed with
  | nil =>
    simp only [prefixWeight, List.map_nil, List.prod_nil, tiltProduct, primeFinalGap, primeRatios, finalSide, finalRatio]
    rw [div_self hr.ne', div_self (weight_pos hs).ne']
    norm_num
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    have hr' := child_gap_positive hell hr hs hp
    have hs' := child_valid hs hp
    have hi := ih hr' hs' hps
    have hf := weight_pos (valid_final hs' (ratios_admissible hps))
    have hstep := prime_tilt_step_identity hell hr hs hp
    simp only [prefixWeight, List.map_cons, List.prod_cons] at ⊢
    change (p : ℝ)⁻¹ * prefixWeight ps = _
    rw [hi, hstep]
    simp only [tiltProduct, primeFinalGap, primeRatios, finalSide, finalRatio]
    field_simp [hr.ne', hr'.ne', (weight_pos hs').ne', hf.ne']

theorem normalized_product_correction {e : ℝ} (he : 0 ≤ e) (w : ℝ) (i : Side) (s r : ℝ) (ps : List ℕ) :
    normalizedTiltProduct e w i s r ps * (1+e)^ps.length = tiltProduct w i s r ps := by
  induction ps generalizing i s r with
  | nil => simp [normalizedTiltProduct, tiltProduct]
  | cons p ps ih =>
    simp only [normalizedTiltProduct, tiltProduct, List.length_cons, pow_succ]
    rw [show (primeTilt w r i s p / (1+e)) * normalizedTiltProduct e w i.flip (childRatio w r p) (r-primeExponent w p) ps *
      ((1+e)^ps.length * (1+e)) = primeTilt w r i s p *
        (normalizedTiltProduct e w i.flip (childRatio w r p) (r-primeExponent w p) ps * (1+e)^ps.length) by
          field_simp [show 1+e ≠ 0 by linarith]]
    rw [ih]

theorem normalized_prime_prefix_weight_identity {w ell S s r cap e : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (he : 0 ≤ e) (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    prefixWeight ps = normalizedTiltProduct e w i s r ps * (1+e)^ps.length * (primeFinalGap w r ps / r)^2 *
      (weight i s / weight (finalSide i (primeRatios w r ps)) (finalRatio s (primeRatios w r ps))) := by
  rw [normalized_product_correction he]
  exact prime_prefix_weight_identity hell hr hs hpath

end NumberTheoryLean.PrimeTiltPrefixes

end

section

namespace NumberTheoryLean.PrimeTiltBounds

open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry WeightGlobalBounds DerivativeWeights

noncomputable def multiplier (i : Side) (s t : ℝ) : ℝ :=
  ((t+1)/t)^2 * weight i.flip t / weight i s

theorem primeTilt_eq_multiplier (w r : ℝ) (i : Side) (s : ℝ) (p : ℕ) :
    primeTilt w r i s p = (p : ℝ)⁻¹ * multiplier i s (childRatio w r p) := by
  unfold primeTilt multiplier
  ring

theorem multiplier_pos {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i.flip t) :
    0 < multiplier i s t := by
  have ht0 := valid_pos ht
  exact div_pos (mul_pos (sq_pos_of_pos (div_pos (by linarith) ht0)) (weight_pos ht)) (weight_pos hs)

theorem valid_ge_half {i : Side} {t : ℝ} (ht : Valid i t) : (1/2 : ℝ) ≤ t := by
  cases i <;> dsimp [Valid] at ht <;> linarith

theorem multiplier_envelope : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, ∀ i : Side, ∀ s t : ℝ,
    Valid i s → s ≤ S → minRatio i s ≤ t → multiplier i s t ≤ C * (1+S)^2 := by
  obtain ⟨C,hC,he,ho⟩ := weights_global_ratio_bound
  refine ⟨9*C, by positivity, ?_⟩
  intro S i s t hs hsS hst
  have ht := valid_next hs hst
  have ht0 := valid_pos ht
  have hhalf := valid_ge_half ht
  have hrat : weight i.flip t / weight i s ≤ C * (1+s)^2 := by
    cases i with
    | even =>
      have hm : phiOdd t ≤ phiOdd (s-1) := phiOdd_antitone hst
      exact (div_le_div_of_nonneg_right hm (weight_pos hs).le).trans (he s hs)
    | odd =>
      change max 2 (s-1) ≤ t at hst
      have hm2 : 2 ≤ max 2 (s-1) := le_max_left _ _
      have hm : phiEven t ≤ phiEven (max 2 (s-1)) :=
        phiEven_strictAntiOn.antitoneOn (by change 1 < max 2 (s-1); linarith)
          (by change 1 < t; linarith) hst
      exact (div_le_div_of_nonneg_right hm (weight_pos hs).le).trans (ho s hs)
  have hq : (t+1)/t ≤ 3 := (div_le_iff₀ ht0).mpr (by linarith)
  have hq0 : 0 ≤ (t+1)/t := (div_pos (by linarith) ht0).le
  have hsq : ((t+1)/t)^2 ≤ 9 := by nlinarith
  have hs0 := valid_pos hs
  calc
    _ = ((t+1)/t)^2 * (weight i.flip t / weight i s) := by unfold multiplier; ring
    _ ≤ 9 * (C * (1+s)^2) := mul_le_mul hsq hrat (div_pos (weight_pos ht) (weight_pos hs)).le (by norm_num)
    _ ≤ (9*C) * (1+S)^2 := by
      have hp : (1+s)^2 ≤ (1+S)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 9*C by positivity)]

theorem log_lipschitz_half {u v : ℝ} (hu : (1/2 : ℝ) ≤ u) (hv : (1/2 : ℝ) ≤ v) :
    |Real.log u - Real.log v| ≤ 2 * |u-v| := by
  have ordered : ∀ a b : ℝ, (1/2 : ℝ) ≤ a → a ≤ b →
      |Real.log b - Real.log a| ≤ 2*(b-a) := by
    intro a b ha hab
    apply interval_abs_bound hab
    · exact Real.continuousOn_log.mono (by intro t ht; exact ne_of_gt (by linarith [ht.1] : 0 < t))
    · intro t ht
      exact Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)
    · intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      rw [abs_of_nonneg (inv_nonneg.mpr ht0.le)]
      exact (inv_le_comm₀ ht0 (by norm_num : (0 : ℝ) < 2)).mpr (by linarith [ht.1])
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm (Real.log u), abs_sub_comm u, abs_of_nonneg (sub_nonneg.mpr huv)]
    exact ordered u v hu huv
  · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact ordered v u hv hvu

theorem log_multiplier {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i.flip t) :
    Real.log (multiplier i s t) = 2*(Real.log (t+1)-Real.log t) + Real.log (weight i.flip t) - Real.log (weight i s) := by
  have ht0 := valid_pos ht
  have hq : (t+1)/t ≠ 0 := (div_pos (by linarith) ht0).ne'
  unfold multiplier
  rw [Real.log_div (mul_ne_zero (pow_ne_zero _ hq) (weight_pos ht).ne') (weight_pos hs).ne',
    Real.log_mul (pow_ne_zero _ hq) (weight_pos ht).ne', Real.log_pow,
    Real.log_div (by linarith : t+1 ≠ 0) ht0.ne']
  norm_num

theorem multiplier_log_lipschitz : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 3 ≤ S →
    ∀ i : Side, ∀ s u v : ℝ, Valid i s → Valid i.flip u → Valid i.flip v → u ≤ S → v ≤ S →
      |Real.log (multiplier i s u) - Real.log (multiplier i s v)| ≤ C * (1+S)^3 * |u-v| := by
  obtain ⟨C,hC,hbound⟩ := weights_log_lipschitz
  refine ⟨C+8, by linarith, ?_⟩
  intro S hS i s u v hs hu hv huS hvS
  have hw : |Real.log (weight i.flip u) - Real.log (weight i.flip v)| ≤ C*(1+S)^3*|u-v| := by
    cases i with
    | even => exact (hbound S hS).2 u v hu hv huS hvS
    | odd => exact (hbound S hS).1 u v hu hv huS hvS
  have hbase := log_lipschitz_half (valid_ge_half hu) (valid_ge_half hv)
  have hshift : |Real.log (u+1)-Real.log (v+1)| ≤ 2*|u-v| := by
    have h := log_lipschitz_half (u := u+1) (v := v+1)
      (by linarith [valid_ge_half hu]) (by linarith [valid_ge_half hv])
    simpa only [add_sub_add_right_eq_sub] using h
  have hp : (1 : ℝ) ≤ (1+S)^3 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1+S)
  rw [log_multiplier hs hu, log_multiplier hs hv]
  calc
    _ = |2*(Real.log (u+1)-Real.log (v+1)) - 2*(Real.log u-Real.log v) +
        (Real.log (weight i.flip u)-Real.log (weight i.flip v))| := by congr 1; ring
    _ ≤ 2*|Real.log (u+1)-Real.log (v+1)| + 2*|Real.log u-Real.log v| +
        |Real.log (weight i.flip u)-Real.log (weight i.flip v)| := by
      rw [abs_le]
      constructor <;> nlinarith [
        le_abs_self (Real.log (u+1)-Real.log (v+1)), neg_abs_le (Real.log (u+1)-Real.log (v+1)),
        le_abs_self (Real.log u-Real.log v), neg_abs_le (Real.log u-Real.log v),
        le_abs_self (Real.log (weight i.flip u)-Real.log (weight i.flip v)),
        neg_abs_le (Real.log (weight i.flip u)-Real.log (weight i.flip v))]
    _ ≤ (C+8)*(1+S)^3*|u-v| := by
      have hmul := mul_le_mul_of_nonneg_right hp (show 0 ≤ 8*|u-v| by positivity)
      nlinarith

theorem multiplier_relative_bound : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 3 ≤ S →
    ∀ i : Side, ∀ s u v : ℝ, Valid i s → Valid i.flip u → Valid i.flip v → u ≤ S → v ≤ S →
      multiplier i s u ≤ Real.exp (C*(1+S)^3*|u-v|) * multiplier i s v := by
  obtain ⟨C,hC,hbound⟩ := multiplier_log_lipschitz
  refine ⟨C,hC,?_⟩
  intro S hS i s u v hs hu hv huS hvS
  have h := (abs_le.mp (hbound S hS i s u v hs hu hv huS hvS)).2
  have hl : Real.log (multiplier i s u) ≤ C*(1+S)^3*|u-v| + Real.log (multiplier i s v) := by linarith
  have he := Real.exp_le_exp.mpr hl
  rwa [Real.exp_add, Real.exp_log (multiplier_pos hs hu), Real.exp_log (multiplier_pos hs hv)] at he

end NumberTheoryLean.PrimeTiltBounds

end

section

namespace NumberTheoryLean.PrimeHistories

open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure

structure Node where
  side : Side
  ratio : ℝ
  gap : ℝ
  cutoff : ℝ
  closed : Bool

noncomputable def nodeChildren (w ell S : ℝ) (z : Node) : Finset ℕ :=
  children w ell S z.side z.ratio z.gap z.cutoff z.closed

noncomputable def step (w : ℝ) (z : Node) (p : ℕ) : Node where
  side := z.side.flip
  ratio := childRatio w z.gap p
  gap := z.gap - primeExponent w p
  cutoff := primeExponent w p
  closed := false

noncomputable def terminal (w : ℝ) (z : Node) (ps : List ℕ) : Node := ps.foldl (step w) z

noncomputable def allowed (w ell S : ℝ) (z : Node) (ps : List ℕ) : Prop :=
  PrimeAdmissible w ell S z.side z.ratio z.gap z.cutoff z.closed ps

@[simp] theorem terminal_nil (w : ℝ) (z : Node) : terminal w z [] = z := rfl
@[simp] theorem terminal_cons (w : ℝ) (z : Node) (p : ℕ) (ps : List ℕ) :
    terminal w z (p::ps) = terminal w (step w z p) ps := rfl

theorem terminal_append (w : ℝ) (z : Node) (ps qs : List ℕ) :
    terminal w z (ps++qs) = terminal w (terminal w z ps) qs := by
  exact List.foldl_append

theorem allowed_nil (w ell S : ℝ) (z : Node) : allowed w ell S z [] := trivial

theorem allowed_cons (w ell S : ℝ) (z : Node) (p : ℕ) (ps : List ℕ) :
    allowed w ell S z (p::ps) ↔ p ∈ nodeChildren w ell S z ∧ allowed w ell S (step w z p) ps := Iff.rfl

theorem allowed_append (w ell S : ℝ) (z : Node) (ps qs : List ℕ) :
    allowed w ell S z (ps++qs) ↔ allowed w ell S z ps ∧ allowed w ell S (terminal w z ps) qs := by
  induction ps generalizing z with
  | nil => simp only [List.nil_append, terminal_nil, iff_true_intro (allowed_nil w ell S z), true_and]
  | cons p ps ih =>
    rw [List.cons_append, allowed_cons, ih, allowed_cons, terminal_cons]
    tauto

theorem terminal_valid {w ell S : ℝ} {z : Node} {ps : List ℕ} (hs : Valid z.side z.ratio)
    (hp : allowed w ell S z ps) : Valid (terminal w z ps).side (terminal w z ps).ratio := by
  induction ps generalizing z with
  | nil => exact hs
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hpath⟩
    exact ih (child_valid hs hchild) hpath

theorem terminal_gap_positive {w ell S : ℝ} {z : Node} {ps : List ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hp : allowed w ell S z ps) :
    0 < (terminal w z ps).gap := by
  induction ps generalizing z with
  | nil => exact hr
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hpath⟩
    exact ih (child_gap_positive hell hr hs hchild) (child_valid hs hchild) hpath

theorem terminal_ratio_le {w ell S : ℝ} {z : Node} {ps : List ℕ} (hs : z.ratio ≤ S)
    (hp : allowed w ell S z ps) : (terminal w z ps).ratio ≤ S := by
  classical
  induction ps generalizing z with
  | nil => exact hs
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hpath⟩
    exact ih (Finset.mem_filter.mp hchild).2.2.2.2 hpath

theorem terminal_gap_eq (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).gap = primeFinalGap w z.gap ps := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => simpa only [terminal_cons, primeFinalGap, step] using ih (step w z p)

theorem terminal_ratio_eq (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).ratio = finalRatio z.ratio (primeRatios w z.gap ps) := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => simpa only [terminal_cons, primeRatios, finalRatio, step] using ih (step w z p)

theorem terminal_side_eq (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).side = finalSide z.side (primeRatios w z.gap ps) := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => simpa only [terminal_cons, primeRatios, finalSide, step] using ih (step w z p)

structure History (w ell S : ℝ) (start : Node) where
  primes : List ℕ
  admissible : allowed w ell S start primes

namespace History

variable {w ell S : ℝ} {start : Node}

@[ext] theorem ext {h k : History w ell S start} (heq : h.primes = k.primes) : h = k := by
  cases h
  cases k
  cases heq
  rfl

instance : Countable (History w ell S start) := (show Function.Injective (History.primes : History w ell S start → List ℕ) from fun _ _ h => ext h).countable
instance : MeasurableSpace (History w ell S start) := ⊤
instance : MeasurableSingletonClass (History w ell S start) := ⟨fun _ => trivial⟩

def empty : History w ell S start := ⟨[],allowed_nil w ell S start⟩
noncomputable def node (h : History w ell S start) : Node := terminal w start h.primes

noncomputable def append (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) : History w ell S start where
  primes := h.primes ++ [p]
  admissible := (allowed_append w ell S start h.primes [p]).mpr ⟨h.admissible,
    (allowed_cons w ell S h.node p []).mpr ⟨hp,allowed_nil w ell S _⟩⟩

@[simp] theorem append_primes (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    (h.append p hp).primes = h.primes ++ [p] := rfl

theorem append_node (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    (h.append p hp).node = step w h.node p := by
  change terminal w start (h.primes ++ [p]) = _
  rw [terminal_append, terminal_cons, terminal_nil]
  rfl

end History
end NumberTheoryLean.PrimeHistories

end

section

namespace NumberTheoryLean.PrimeRatioBins

open _root_.Erdos970.Finset _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

noncomputable def ratioBin (w r a b : ℝ) : Finset ℕ := by
  classical
  exact (Nat.primesLE ⌊w ^ (r/(a+1))⌋₊).filter
    (fun p => a ≤ childRatio w r p ∧ childRatio w r p < b)

noncomputable def ratioBinMass (w r a b : ℝ) : ℝ :=
  ∑ p ∈ ratioBin w r a b, (p : ℝ)⁻¹

theorem ratio_interval_iff {r a b x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : 0 < x) :
    (a ≤ r/x-1 ∧ r/x-1 < b) ↔ r/(b+1) < x ∧ x ≤ r/(a+1) := by
  have ha1 : 0 < a+1 := by linarith
  have hb1 : 0 < b+1 := by linarith
  constructor
  · rintro ⟨hlo,hhi⟩
    constructor
    · apply (div_lt_iff₀ hb1).mpr
      have h := (div_lt_iff₀ hx).mp (show r/x < b+1 by linarith)
      nlinarith
    · apply (le_div_iff₀ ha1).mpr
      have h := (le_div_iff₀ hx).mp (show a+1 ≤ r/x by linarith)
      nlinarith
  · rintro ⟨hlo,hhi⟩
    constructor
    · have h := (le_div_iff₀ ha1).mp hhi
      have hh : a+1 ≤ r/x := (le_div_iff₀ hx).mpr (by nlinarith)
      linarith
    · have h := (div_lt_iff₀ hb1).mp hlo
      have hh : r/x < b+1 := (div_lt_iff₀ hx).mpr (by nlinarith)
      linarith

theorem primeExponent_pos {w : ℝ} (hw : 1 < w) {p : ℕ} (hp : p.Prime) : 0 < primeExponent w p := by
  apply div_pos
  · apply Real.log_pos
    exact_mod_cast hp.one_lt
  · exact Real.log_pos hw

theorem ratioBinMass_eq_harmonic {w r a b : ℝ} (hw : 1 < w) (ha : 0 < a) (hab : a ≤ b) :
    ratioBinMass w r a b = harmonicMass w false true (r/(b+1)) (r/(a+1)) := by
  classical
  unfold ratioBinMass ratioBin harmonicMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have heq := ratio_interval_iff (r := r) ha hab (primeExponent_pos hw (Nat.mem_primesLE.mp hp).2)
  simp only [childRatio, intervalGuard, Bool.false_eq_true, ite_false, ite_true, heq]

theorem bin_log_width {r a b : ℝ} (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b) :
    Real.log (r/(a+1)) - Real.log (r/(b+1)) = Real.log (b+1)-Real.log (a+1) := by
  rw [Real.log_div hr.ne' (by linarith : a+1 ≠ 0), Real.log_div hr.ne' (by linarith : b+1 ≠ 0)]
  ring

theorem bin_log_width_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b-a)/(b+1) ≤ Real.log (b+1)-Real.log (a+1) ∧
      Real.log (b+1)-Real.log (a+1) ≤ (b-a)/(a+1) := by
  have ha1 : 0 < a+1 := by linarith
  have hb1 : 0 < b+1 := by linarith
  have hq := div_pos hb1 ha1
  have hl := Real.one_sub_inv_le_log_of_pos hq
  have hu := Real.log_le_sub_one_of_pos hq
  rw [Real.log_div hb1.ne' ha1.ne'] at hl hu
  have heL : 1-((b+1)/(a+1))⁻¹ = (b-a)/(b+1) := by field_simp; ring
  have heU : (b+1)/(a+1)-1 = (b-a)/(a+1) := by field_simp; ring
  rw [heL] at hl
  rw [heU] at hu
  exact ⟨hl,hu⟩

theorem prime_ratio_bin_error : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ r a b : ℝ, 0 < r → 0 < a → a ≤ b → 1/2 ≤ r/(b+1) →
      |ratioBinMass w r a b - (Real.log (b+1)-Real.log (a+1))| ≤
        C * Real.exp (-c * Real.sqrt ((1/2 : ℝ) * Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := harmonic_prime_measure
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw r a b hr ha hab hlow
  have hw1 := hw₀.trans_le hw
  have hend : r/(b+1) ≤ r/(a+1) := div_le_div_of_nonneg_left hr.le (by linarith : 0 < a+1) (by linarith)
  have h := hbound w hw (r/(b+1)) (r/(a+1)) hlow hend false true
  rw [← ratioBinMass_eq_harmonic hw1 ha hab, bin_log_width hr ha hab] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hlow (Real.log_pos hw1).le)) (by linarith)

end NumberTheoryLean.PrimeRatioBins

end

end Erdos970

end OAI
