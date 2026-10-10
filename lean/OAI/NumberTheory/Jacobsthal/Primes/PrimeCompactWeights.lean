import OAI.NumberTheory.Jacobsthal.Partitions.CompletedParentInterval

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.WeightedPrimeBins

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone
open PrimeRatioBins ContinuousRatioBins

noncomputable def weightedPrimeBin (w r : ℝ) (i : Side) (s a b : ℝ) : ℝ :=
  ∑ p ∈ ratioBin w r a b, primeTilt w r i s p

theorem weightedPrimeBin_sandwich {w r s a b : ℝ} {i : Side} (hs : Valid i s)
    (hma : minRatio i s ≤ a) (hab : a ≤ b) :
    multiplier i s b * ratioBinMass w r a b ≤ weightedPrimeBin w r i s a b ∧
      weightedPrimeBin w r i s a b ≤ multiplier i s a * ratioBinMass w r a b := by
  classical
  have hlo : ∀ p ∈ ratioBin w r a b, multiplier i s b ≤ multiplier i s (childRatio w r p) := by
    intro p hp
    have ht := (Finset.mem_filter.mp hp).2
    exact multiplier_antitone hs (Set.mem_Ici.mpr (hma.trans ht.1))
      (Set.mem_Ici.mpr (hma.trans hab)) ht.2.le
  have hup : ∀ p ∈ ratioBin w r a b, multiplier i s (childRatio w r p) ≤ multiplier i s a := by
    intro p hp
    have ht := (Finset.mem_filter.mp hp).2
    exact multiplier_antitone hs (Set.mem_Ici.mpr hma) (Set.mem_Ici.mpr (hma.trans ht.1)) ht.1
  constructor
  · rw [ratioBinMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [primeTilt_eq_multiplier, mul_comm (multiplier i s b)]
    exact mul_le_mul_of_nonneg_left (hlo p hp) (inv_nonneg.mpr (Nat.cast_nonneg p))
  · rw [ratioBinMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [primeTilt_eq_multiplier, mul_comm (multiplier i s a)]
    exact mul_le_mul_of_nonneg_left (hup p hp) (inv_nonneg.mpr (Nat.cast_nonneg p))

theorem sandwich_difference {ma mb R H D C E : ℝ} (hma : 0 ≤ ma) (hmb : 0 ≤ mb)
    (hm : mb ≤ ma) (hE : 0 ≤ E) (hraw : |R-H| ≤ E)
    (hD : mb*R ≤ D ∧ D ≤ ma*R) (hC : mb*H ≤ C ∧ C ≤ ma*H) :
    |D-C| ≤ ma*E + (ma-mb)*H := by
  rw [abs_le]
  constructor
  · have h := mul_le_mul_of_nonneg_left (show H-R ≤ E by linarith [(abs_le.mp hraw).1]) hmb
    have h' := mul_le_mul_of_nonneg_right hm hE
    nlinarith [hD.1,hC.2]
  · have h := mul_le_mul_of_nonneg_left (abs_le.mp hraw).2 hma
    nlinarith [hD.2,hC.1]

theorem sub_le_mul_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a-b ≤ a*(Real.log a-Real.log b) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h ha.le
  have he : a*(b/a-1) = b-a := by field_simp
  rw [he] at hm
  nlinarith

theorem multiplier_drop : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 3 ≤ S →
    ∀ i : Side, ∀ s a b : ℝ, Valid i s → minRatio i s ≤ a → a ≤ b → b ≤ S →
      multiplier i s a-multiplier i s b ≤ multiplier i s a*(C*(1+S)^3*(b-a)) := by
  obtain ⟨C,hC,hbound⟩ := multiplier_log_lipschitz
  refine ⟨C,hC,?_⟩
  intro S hS i s a b hs hma hab hbS
  have ha := valid_next hs hma
  have hb := valid_next hs (hma.trans hab)
  have h := hbound S hS i s a b hs ha hb (hab.trans hbS) hbS
  rw [abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact (sub_le_mul_log_sub (multiplier_pos hs ha) (multiplier_pos hs hb)).trans
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans h) (multiplier_pos hs ha).le)

theorem weighted_bin_error : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ r : ℝ, 0 < r → ∀ i : Side, ∀ s a b : ℝ,
      Valid i s → minRatio i s ≤ a → a ≤ b → 1/2 ≤ r/(b+1) →
      |weightedPrimeBin w r i s a b-continuousBin i s a b| ≤
        multiplier i s a * (C*Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w))) +
          (multiplier i s a-multiplier i s b)*(Real.log (b+1)-Real.log (a+1)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hraw⟩ := prime_ratio_bin_error
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw r hr i s a b hs hma hab hlow
  have ha := (minRatio_pos hs).trans_le hma
  apply sandwich_difference (multiplier_pos hs (valid_next hs hma)).le
    (multiplier_pos hs (valid_next hs (hma.trans hab))).le
    (multiplier_antitone hs (Set.mem_Ici.mpr hma) (Set.mem_Ici.mpr (hma.trans hab)) hab)
    (by positivity) (hraw w hw r a b hr ha hab hlow)
    (weightedPrimeBin_sandwich hs hma hab) (continuousBin_sandwich hs hma hab)

theorem weighted_bin_polynomial_error : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ r S : ℝ, 0 < r → 3 ≤ S → ∀ i : Side, ∀ s a b : ℝ,
      Valid i s → s ≤ S → minRatio i s ≤ a → a ≤ b → b ≤ S → 1/2 ≤ r/(b+1) →
      |weightedPrimeBin w r i s a b-continuousBin i s a b| ≤
        C*(1+S)^5*((b-a)^2+Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w))) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,herr⟩ := weighted_bin_error
  obtain ⟨D,hD,henv⟩ := multiplier_envelope
  obtain ⟨L,hL,hdrop⟩ := multiplier_drop
  let M := D*C+D*L
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨c,M,w₀,hc,hM,hw₀,?_⟩
  intro w hw r S hr hS i s a b hs hsS hma hab hbS hlow
  let P := 1+S
  let e := Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w))
  let H := Real.log (b+1)-Real.log (a+1)
  let delta := multiplier i s a-multiplier i s b
  have hP : 1 ≤ P := by dsimp [P]; linarith
  have hP0 : 0 ≤ P := by linarith
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hh : 0 ≤ b-a := sub_nonneg.mpr hab
  have ha := (minRatio_pos hs).trans_le hma
  have hH0 : 0 ≤ H := sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  have hH : H ≤ b-a := ((bin_log_width_bounds ha hab).2).trans (div_le_self hh (by linarith))
  have hd0 : 0 ≤ delta := sub_nonneg.mpr
    (multiplier_antitone hs (Set.mem_Ici.mpr hma) (Set.mem_Ici.mpr (hma.trans hab)) hab)
  have hm := henv S i s a hs hsS hma
  have hd : delta ≤ D*L*P^5*(b-a) := by
    calc
      _ ≤ multiplier i s a*(L*P^3*(b-a)) := hdrop S hS i s a b hs hma hab hbS
      _ ≤ (D*P^2)*(L*P^3*(b-a)) := mul_le_mul_of_nonneg_right hm (by positivity)
      _ = _ := by ring
  have hp25 : P^2 ≤ P^5 := by
    have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hP : (1 : ℝ) ≤ P^3) (sq_nonneg P)
    nlinarith
  have hfirst : multiplier i s a*(C*e) ≤ D*C*P^5*e := by
    calc
      _ ≤ (D*P^2)*(C*e) := mul_le_mul_of_nonneg_right hm (mul_nonneg hC.le he)
      _ = (D*C*e)*P^2 := by ring
      _ ≤ (D*C*e)*P^5 := mul_le_mul_of_nonneg_left hp25 (by positivity)
      _ = _ := by ring
  have hsecond : delta*H ≤ D*L*P^5*(b-a)^2 := by
    calc
      _ ≤ (D*L*P^5*(b-a))*H := mul_le_mul_of_nonneg_right hd hH0
      _ ≤ (D*L*P^5*(b-a))*(b-a) := mul_le_mul_of_nonneg_left hH (by positivity)
      _ = _ := by ring
  have hDC : D*C ≤ M := le_add_of_nonneg_right (mul_nonneg hD.le hL.le)
  have hDL : D*L ≤ M := le_add_of_nonneg_left (mul_nonneg hD.le hC.le)
  calc
    _ ≤ multiplier i s a*(C*e)+delta*H := herr w hw r hr i s a b hs hma hab hlow
    _ ≤ D*C*P^5*e + D*L*P^5*(b-a)^2 := add_le_add hfirst hsecond
    _ ≤ M*P^5*e + M*P^5*(b-a)^2 := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC (pow_nonneg hP0 _)) he)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDL (pow_nonneg hP0 _)) (sq_nonneg _))
    _ = _ := by dsimp [P,e]; ring

end NumberTheoryLean.WeightedPrimeBins

end

section

namespace NumberTheoryLean.NormalizedPrimeBins

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeRatioBins PrimeTiltBounds
open WeightedPrimeBins ContinuousRatioBins PrimeKilledChain

theorem division_error {D C e : ℝ} (hC : 0 ≤ C) (he : 0 ≤ e) :
    |D/(1+e)-C| ≤ |D-C|+e*C := by
  let A := |D-C|
  have hA : 0 ≤ A := abs_nonneg _
  have hlo : C-A ≤ D := by dsimp [A]; linarith [neg_abs_le (D-C)]
  have hup : D ≤ C+A := by dsimp [A]; linarith [le_abs_self (D-C)]
  have hZ : 0 < 1+e := by linarith
  have hu : D/(1+e) ≤ C+A := (div_le_iff₀ hZ).mpr (by
    nlinarith [mul_nonneg (add_nonneg hC hA) he])
  have hl : C-A-e*C ≤ D/(1+e) := (le_div_iff₀ hZ).mpr (by
    nlinarith [mul_nonneg hA he, mul_nonneg hC (sq_nonneg e)])
  rw [abs_le]
  constructor <;> dsimp [A] at hu hl <;> nlinarith [mul_nonneg he hC]

noncomputable def normalizedPrimeBin (w r : ℝ) (i : Side) (s a b : ℝ) : ℝ :=
  ∑ p ∈ ratioBin w r a b, primeTilt w r i s p/(1+epsilon w)

theorem normalizedPrimeBin_eq (w r : ℝ) (i : Side) (s a b : ℝ) :
    normalizedPrimeBin w r i s a b = weightedPrimeBin w r i s a b/(1+epsilon w) := by
  exact (Finset.sum_div _ _ _).symm

theorem normalized_bin_error : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ r S : ℝ, 0 < r → 3 ≤ S → ∀ i : Side, ∀ s a b : ℝ,
      Valid i s → s ≤ S → minRatio i s ≤ a → a ≤ b → b ≤ S → 1/2 ≤ r/(b+1) →
      |normalizedPrimeBin w r i s a b-continuousBin i s a b| ≤
        C*(1+S)^5*((b-a)^2+Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w))) +
          epsilon w*continuousBin i s a b := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := weighted_bin_polynomial_error
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw r S hr hS i s a b hs hsS hma hab hbS hlow
  rw [normalizedPrimeBin_eq]
  exact (division_error (show 0 ≤ continuousBin i s a b from ENNReal.toReal_nonneg) (epsilon_pos w).le).trans
    (add_le_add (hbound w hw r S hr hS i s a b hs hsS hma hab hbS hlow) le_rfl)

end NumberTheoryLean.NormalizedPrimeBins

end

section

namespace NumberTheoryLean.PrimeBinMembership

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open PrimeRatioBins NormalizedPrimeBins PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure

def Consistent (z : Node) : Prop := z.cutoff = z.gap/z.ratio

theorem step_consistent {w ell S : ℝ} {z : Node} {p : ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hp : p ∈ nodeChildren w ell S z) :
    Consistent (step w z p) := by
  have hx := child_exponent_positive hell hp
  have ht := valid_pos (child_valid hs hp)
  change primeExponent w p = (z.gap-primeExponent w p)/childRatio w z.gap p
  rw [← nextGap_childRatio hr hx ht, nextGap_div_ratio ht, nextExponent_childRatio hr hx]

theorem terminal_consistent {w ell S : ℝ} {z : Node} {ps : List ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hz : Consistent z) (hp : allowed w ell S z ps) :
    Consistent (terminal w z ps) := by
  induction ps generalizing z with
  | nil => exact hz
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hc,ht⟩
    exact ih (child_gap_positive hell hr hs hc) (child_valid hs hc) (step_consistent hell hr hs hc) ht

theorem history_consistent {w ell S : ℝ} {start : Node} (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hc : Consistent start)
    (h : History w ell S start) : Consistent h.node :=
  terminal_consistent hell hr hs hc h.admissible

theorem children_full_bin {w ell S s r cap a b : ℝ} {i : Side} (hw : 1 < w)
    (hell : 0 < ell) (_hr : 0 < r) (hs : Valid i s) (hcap : cap = r/s)
    (hma : minRatio i s < a) (hab : a ≤ b) (hbS : b ≤ S) (harr : b ≤ r/ell-1) (closed : Bool) :
    (children w ell S i s r cap closed).filter (fun p => a ≤ childRatio w r p ∧ childRatio w r p < b) =
      ratioBin w r a b := by
  classical
  have ha : 0 < a := (PrimeTiltMonotone.minRatio_pos hs).trans hma
  have hb : 0 < b := ha.trans_le hab
  have hs0 := valid_pos hs
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hchild,hbin⟩
    have hprime := ((mem_children_iff hw i closed p).mp hchild).1
    have hxp := PrimeRatioBins.primeExponent_pos hw hprime
    have hinterval := (ratio_interval_iff (r := r) ha hab hxp).mp hbin
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hreal : (p : ℝ) ≤ w^(r/(a+1)) := (exponent_le_iff hw hp0).mp hinterval.2
    apply Finset.mem_filter.mpr
    exact ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) _).le).mpr hreal,hprime⟩,hbin⟩
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpprime,hbin⟩
    have hprime := (Nat.mem_primesLE.mp hpprime).2
    have hxp := PrimeRatioBins.primeExponent_pos hw hprime
    have hinterval := (ratio_interval_iff (r := r) ha hab hxp).mp hbin
    have hlow : ell ≤ r/(b+1) := by
      apply (le_div_iff₀ (by linarith : 0 < b+1)).mpr
      have h := (le_div_iff₀ hell).mp (show b+1 ≤ r/ell by linarith)
      nlinarith
    have hbelow : primeExponent w p < cap := by
      rw [hcap]
      apply (lt_div_iff₀ hs0).mpr
      have hrat : s < r/primeExponent w p := by
        have hmin := minRatio_ge_sub_one i s
        have hlo : a ≤ r/primeExponent w p-1 := hbin.1
        linarith
      have h := (lt_div_iff₀ hxp).mp hrat
      nlinarith
    have hguard : capGuard closed cap (primeExponent w p) := by
      cases closed with
      | false => exact hbelow
      | true => exact hbelow.le
    apply Finset.mem_filter.mpr
    refine ⟨(mem_children_iff hw i closed p).mpr ⟨hprime,hlow.trans_lt hinterval.1,hguard,?_,?_⟩,hbin⟩
    · exact hma.le.trans hbin.1
    · exact hbin.2.le.trans hbS

theorem normalized_children_full_bin {w ell S s r cap a b : ℝ} {i : Side} (hw : 1 < w)
    (hell : 0 < ell) (hr : 0 < r) (hs : Valid i s) (hcap : cap = r/s)
    (hma : minRatio i s < a) (hab : a ≤ b) (hbS : b ≤ S) (harr : b ≤ r/ell-1) (closed : Bool) :
    (∑ p ∈ children w ell S i s r cap closed,
      if a ≤ childRatio w r p ∧ childRatio w r p < b then primeTilt w r i s p/(1+epsilon w) else 0) =
      normalizedPrimeBin w r i s a b := by
  classical
  rw [← Finset.sum_filter, children_full_bin hw hell hr hs hcap hma hab hbS harr closed]
  rfl

end NumberTheoryLean.PrimeBinMembership

end

section

namespace NumberTheoryLean.ActualPrimeBins

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeHistories PrimeKilledChain
open PrimeBinMembership NormalizedPrimeBins PrimeRatioBins

variable {w ell S : ℝ} {start : Node}

def liveBin (a b : ℝ) : Set (ChainState w ell S start) :=
  fun z => match z with
    | none => False
    | some h => a ≤ h.node.ratio ∧ h.node.ratio < b

theorem mem_liveBin_some (h : History w ell S start) (a b : ℝ) :
    some h ∈ liveBin a b ↔ a ≤ h.node.ratio ∧ h.node.ratio < b := Iff.rfl

theorem not_mem_liveBin_none (a b : ℝ) :
    (none : ChainState w ell S start) ∉ liveBin a b := by
  change ¬False
  exact not_false

theorem liveBin_measurable (a b : ℝ) : MeasurableSet (liveBin (w := w) (ell := ell) (S := S) (start := start) a b) := trivial

theorem chain_live_bin_formula (h : History w ell S start) (a b : ℝ) :
    chain w ell S start (some h) (liveBin a b) =
      ∑ p ∈ nodeChildren w ell S h.node,
        if a ≤ childRatio w h.node.gap p ∧ childRatio w h.node.gap p < b then childProbability w ell S start h p else 0 := by
  classical
  simp only [chain_some, completedLaw, Measure.add_apply, liveLaw, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator, mem_liveBin_some, not_mem_liveBin_none, History.append_node, step,
    Pi.one_apply, mul_ite, mul_one, mul_zero, ite_false, add_zero]
  exact Finset.sum_attach _ (fun p : ℕ =>
    if a ≤ childRatio w h.node.gap p ∧ childRatio w h.node.gap p < b then childProbability w ell S start h p else 0)

theorem chain_full_bin (h : History w ell S start) {a b : ℝ} (hw : 1 < w)
    (hell : 0 < ell) (hr : 0 < h.node.gap) (hs : Valid h.node.side h.node.ratio) (hc : Consistent h.node)
    (hma : minRatio h.node.side h.node.ratio < a) (hab : a ≤ b) (hbS : b ≤ S)
    (harr : b ≤ h.node.gap/ell-1) :
    chain w ell S start (some h) (liveBin a b) =
      ENNReal.ofReal (normalizedPrimeBin w h.node.gap h.node.side h.node.ratio a b) := by
  classical
  rw [chain_live_bin_formula]
  have hnonneg : ∀ p ∈ nodeChildren w ell S h.node,
      0 ≤ if a ≤ childRatio w h.node.gap p ∧ childRatio w h.node.gap p < b
        then primeTilt w h.node.gap h.node.side h.node.ratio p/(1+epsilon w) else 0 := by
    intro p hp
    split_ifs
    · exact div_nonneg (primeTilt_nonneg (w := w) (r := h.node.gap) (i := h.node.side) (s := h.node.ratio) hs hp) (normalizer_pos w).le
    · exact le_rfl
  calc
    _ = ENNReal.ofReal (∑ p ∈ nodeChildren w ell S h.node,
        if a ≤ childRatio w h.node.gap p ∧ childRatio w h.node.gap p < b
          then primeTilt w h.node.gap h.node.side h.node.ratio p/(1+epsilon w) else 0) := by
      rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp only [childProbability, ENNReal.ofReal_zero]
    _ = _ := congrArg ENNReal.ofReal (normalized_children_full_bin hw hell hr hs hc hma hab hbS harr h.node.closed)

theorem chain_full_bin_real (h : History w ell S start) {a b : ℝ} (hw : 1 < w)
    (hell : 0 < ell) (hr : 0 < h.node.gap) (hs : Valid h.node.side h.node.ratio) (hc : Consistent h.node)
    (hma : minRatio h.node.side h.node.ratio < a) (hab : a ≤ b) (hbS : b ≤ S)
    (harr : b ≤ h.node.gap/ell-1) :
    (chain w ell S start (some h) (liveBin a b)).toReal =
      normalizedPrimeBin w h.node.gap h.node.side h.node.ratio a b := by
  rw [chain_full_bin h hw hell hr hs hc hma hab hbS harr]
  apply ENNReal.toReal_ofReal
  unfold normalizedPrimeBin
  apply Finset.sum_nonneg
  intro p hp
  have ht := (Finset.mem_filter.mp hp).2
  rw [primeTilt_eq_multiplier]
  exact div_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
    (multiplier_pos hs (valid_next hs (hma.le.trans ht.1))).le) (normalizer_pos w).le

end NumberTheoryLean.ActualPrimeBins

end

section

namespace NumberTheoryLean.ActualPrimeHigh
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.HighPrimeGeometry

theorem allowed_prime_bounds {w ell U : ℝ} (hw : 1 < w) {z : Node} {ps : List ℕ}
    (hpath : allowed w ell U z ps) : ∀ p ∈ ps,
      p.Prime ∧ ell < primeExponent w p ∧ capGuard z.closed z.cutoff (primeExponent w p) := by
  induction ps generalizing z with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := (allowed_cons w ell U z p ps).mp hpath
    have hdata := (mem_children_iff hw z.side z.closed p).mp hc
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨hdata.1,hdata.2.1,hdata.2.2.1⟩
    · have htail := ih ht q hq
      have hqp : primeExponent w q < primeExponent w p := htail.2.2
      refine ⟨htail.1,htail.2.1,?_⟩
      have hpcap := hdata.2.2.1
      cases he : z.closed <;> simp only [capGuard,he,Bool.false_eq_true,ite_false,ite_true] at hpcap ⊢
      · exact hqp.trans hpcap
      · exact hqp.le.trans hpcap

theorem allowed_decreasing {w ell U : ℝ} (hw : 1 < w) {z : Node} {ps : List ℕ}
    (hpath : allowed w ell U z ps) : ps.Pairwise (· > ·) := by
  induction ps generalizing z with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := (allowed_cons w ell U z p ps).mp hpath
    refine List.pairwise_cons.mpr ⟨?_,ih ht⟩
    intro q hq
    have hqp : primeExponent w q < primeExponent w p := (allowed_prime_bounds hw ht q hq).2.2
    exact lt_of_not_ge (fun hpq => (not_lt_of_ge (exponent_monotone hw hpq)) hqp)

theorem allowed_mem_decreasing {w ell U : ℝ} (hw : 1 < w) {z : Node} {ps : List ℕ}
    (hpath : allowed w ell U z ps) :
    ps ∈ decreasingPrefixes (primesBetween (w^ell) (w^z.cutoff)) := by
  apply mem_decreasingPrefixes.mpr
  refine ⟨allowed_decreasing hw hpath,?_⟩
  intro p hp
  obtain ⟨hprime,hlo,hcap⟩ := allowed_prime_bounds hw hpath p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hup : primeExponent w p ≤ z.cutoff := by
    cases he : z.closed <;> simp only [capGuard,he,Bool.false_eq_true,ite_false,ite_true] at hcap
    · exact hcap.le
    · exact hcap
  have hlow : w^ell < (p : ℝ) := (lt_exponent_iff hw hp0).mp hlo
  have hhigh : (p : ℝ) ≤ w^z.cutoff := (exponent_le_iff hw hp0).mp hup
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_,hprime⟩,hlow⟩
  exact (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) _).le).mpr hhigh

theorem terminal_gap_remaining (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).gap = remainingGap z.gap w ps := by
  induction ps generalizing z with
  | nil => simp [remainingGap]
  | cons p ps ih =>
    rw [terminal_cons,ih]
    simp only [remainingGap,step,List.map_cons,List.sum_cons]
    ring

theorem terminal_cutoff (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).cutoff = primeCutoff w z.cutoff ps := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih => exact ih (step w z p)

theorem terminal_ratio_remaining {w ell U : ℝ} {z : Node} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hz : Consistent z) (hp : allowed w ell U z ps) :
    (terminal w z ps).ratio = remainingGap z.gap w ps / primeCutoff w z.cutoff ps := by
  have hc := terminal_consistent hell hr hs hz hp
  have hg := terminal_gap_positive hell hr hs hp
  have hv := valid_pos (terminal_valid hs hp)
  rw [← terminal_gap_remaining w z ps,← terminal_cutoff w z ps]
  change (terminal w z ps).cutoff = (terminal w z ps).gap/(terminal w z ps).ratio at hc
  rw [hc]
  field_simp

noncomputable def actualHasHigh (w T : ℝ) (z : Node) (ps : List ℕ) : Prop :=
  ∃ pre suf : List ℕ, ps = pre ++ suf ∧ T < (terminal w z pre).ratio

theorem actual_has_high_iff {w ell U T : ℝ} {z : Node} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hz : Consistent z) (hp : allowed w ell U z ps) :
    actualHasHigh w T z ps ↔ hasHighState z.gap w z.cutoff T ps := by
  constructor <;> rintro ⟨pre,suf,he,hh⟩
  · have hpre : allowed w ell U z pre := (allowed_append w ell U z pre suf).mp (he ▸ hp) |>.1
    rw [terminal_ratio_remaining hell hr hs hz hpre] at hh
    exact ⟨pre,suf,he,hh⟩
  · have hpre : allowed w ell U z pre := (allowed_append w ell U z pre suf).mp (he ▸ hp) |>.1
    rw [← terminal_ratio_remaining hell hr hs hz hpre] at hh
    exact ⟨pre,suf,he,hh⟩

end NumberTheoryLean.ActualPrimeHigh

end

section

namespace NumberTheoryLean.ActualPrimeHigh
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ErdosPrimeInputs.HighPrimeGeometry

noncomputable def uncappedChildren (w ell : ℝ) (z : Node) : Finset ℕ := by
  classical
  exact (Nat.primesLE ⌊w^z.cutoff⌋₊).filter (fun p => ell < primeExponent w p ∧
    capGuard z.closed z.cutoff (primeExponent w p) ∧
      minRatio z.side z.ratio ≤ childRatio w z.gap p)

noncomputable def uncappedAllowed (w ell : ℝ) : Node → List ℕ → Prop
  | _, [] => True
  | z, p::ps => p ∈ uncappedChildren w ell z ∧ uncappedAllowed w ell (step w z p) ps

theorem allowed_mono {w ell U V : ℝ} (hUV : U ≤ V) {z : Node} {ps : List ℕ}
    (hp : allowed w ell U z ps) : allowed w ell V z ps := by
  classical
  induction ps generalizing z with
  | nil => trivial
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := (allowed_cons w ell U z p ps).mp hp
    obtain ⟨hprime,hlo,hcap,hmin,hmax⟩ := Finset.mem_filter.mp hc
    apply (allowed_cons w ell V z p ps).mpr
    exact ⟨Finset.mem_filter.mpr ⟨hprime,hlo,hcap,hmin,hmax.trans hUV⟩,ih ht⟩

theorem uncapped_iff_exists_ceiling (w ell : ℝ) (z : Node) (ps : List ℕ) :
    uncappedAllowed w ell z ps ↔ ∃ U : ℝ, z.ratio ≤ U ∧ allowed w ell U z ps := by
  classical
  induction ps generalizing z with
  | nil => exact ⟨fun _ => ⟨z.ratio,le_rfl,trivial⟩,fun _ => trivial⟩
  | cons p ps ih =>
    constructor
    · rintro ⟨hc,ht⟩
      obtain ⟨U,hchildU,hrest⟩ := (ih (step w z p)).mp ht
      let V := max U z.ratio
      refine ⟨V,le_max_right _ _,?_⟩
      obtain ⟨hprime,hlo,hcap,hmin⟩ := Finset.mem_filter.mp hc
      apply (allowed_cons w ell V z p ps).mpr
      refine ⟨Finset.mem_filter.mpr ⟨hprime,hlo,hcap,hmin,?_⟩,
        allowed_mono (le_max_left _ _) hrest⟩
      exact hchildU.trans (le_max_left _ _)
    · rintro ⟨U,_hstart,hpath⟩
      obtain ⟨hc,ht⟩ := (allowed_cons w ell U z p ps).mp hpath
      obtain ⟨hprime,hlo,hcap,hmin,hmax⟩ := Finset.mem_filter.mp hc
      refine ⟨Finset.mem_filter.mpr ⟨hprime,hlo,hcap,hmin⟩,?_⟩
      exact (ih (step w z p)).mpr ⟨U,hmax,ht⟩

theorem uncapped_mem_decreasing {w ell : ℝ} (hw : 1 < w) {z : Node} {ps : List ℕ}
    (hp : uncappedAllowed w ell z ps) :
    ps ∈ decreasingPrefixes (primesBetween (w^ell) (w^z.cutoff)) := by
  obtain ⟨U,_,hU⟩ := (uncapped_iff_exists_ceiling w ell z ps).mp hp
  exact allowed_mem_decreasing hw hU

noncomputable def uncappedPrefixes (w ell : ℝ) (z : Node) : Finset (List ℕ) := by
  classical
  exact (decreasingPrefixes (primesBetween (w^ell) (w^z.cutoff))).filter (uncappedAllowed w ell z)

theorem mem_uncappedPrefixes {w ell : ℝ} (hw : 1 < w) (z : Node) (ps : List ℕ) :
    ps ∈ uncappedPrefixes w ell z ↔ uncappedAllowed w ell z ps := by
  classical
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨uncapped_mem_decreasing hw h,h⟩⟩

theorem uncapped_gap_positive {w ell : ℝ} {z : Node} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hp : uncappedAllowed w ell z ps) : 0 < (terminal w z ps).gap := by
  obtain ⟨U,_,hU⟩ := (uncapped_iff_exists_ceiling w ell z ps).mp hp
  exact terminal_gap_positive hell hr hs hU

theorem uncapped_has_high_iff {w ell T : ℝ} {z : Node} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hp : uncappedAllowed w ell z ps) :
    actualHasHigh w T z ps ↔ hasHighState z.gap w z.cutoff T ps := by
  obtain ⟨U,_,hU⟩ := (uncapped_iff_exists_ceiling w ell z ps).mp hp
  exact actual_has_high_iff hell hr hs hz hU

end NumberTheoryLean.ActualPrimeHigh

end

section

open scoped BigOperators
namespace NumberTheoryLean.ActualPrimeHigh
attribute [local instance] Classical.propDecidable
open FinitePathGeometry PrimeHistories PrimeBinMembership
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail ErdosPrimeInputs.HighPrimeGeometry

noncomputable def uncappedLowGapHighMass (w ell : ℝ) (z : Node) (T K : ℝ) : ℝ := by
  classical
  exact ∑ ps ∈ (uncappedPrefixes w ell z).filter
    (fun ps => (terminal w z ps).gap ≤ K ∧ actualHasHigh w T z ps), prefixWeight ps

noncomputable def uncappedRewardedHighMass (w ell : ℝ) (z : Node) (T c : ℝ) : ℝ := by
  classical
  exact ∑ ps ∈ (uncappedPrefixes w ell z).filter (actualHasHigh w T z),
    prefixWeight ps * Real.exp (-c*(terminal w z ps).gap)

theorem uncapped_reward_filter {w ell T : ℝ} (hw : 1 < w) {z : Node}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio) :
    (uncappedPrefixes w ell z).filter (actualHasHigh w T z) =
      (uncappedPrefixes w ell z).filter
        (fun ps => actualHasHigh w T z ps ∧ 0 ≤ (terminal w z ps).gap) := by
  classical
  ext ps
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp,hh⟩
    exact ⟨hp,hh,(uncapped_gap_positive hell hr hs ((mem_uncappedPrefixes hw z ps).mp hp)).le⟩
  · rintro ⟨hp,hh,_⟩
    exact ⟨hp,hh⟩

theorem uncapped_low_mass_le {w ell : ℝ} (_hw : 1 < w) {z : Node}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hz : Consistent z) (T K : ℝ) :
    uncappedLowGapHighMass w ell z T K ≤
      ErdosPrimeInputs.HighPrimeMass.lowGapHighMass z.gap w z.cutoff ell T K := by
  classical
  unfold uncappedLowGapHighMass ErdosPrimeInputs.HighPrimeMass.lowGapHighMass
  simp only [terminal_gap_remaining]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ps hp
    obtain ⟨hfamily,hgap,hhigh⟩ := Finset.mem_filter.mp hp
    obtain ⟨hdec,hactual⟩ := Finset.mem_filter.mp hfamily
    exact Finset.mem_filter.mpr ⟨hdec,hgap,
      (uncapped_has_high_iff hell hr hs hz hactual).mp hhigh⟩
  · intro ps _ _
    exact prefixWeight_nonneg ps

theorem uncapped_rewarded_mass_le {w ell : ℝ} (_hw : 1 < w) {z : Node}
    (hell : 0 ≤ ell) (hr : 0 < z.gap) (hs : Valid z.side z.ratio)
    (hz : Consistent z) (T c : ℝ) :
    uncappedRewardedHighMass w ell z T c ≤
      ErdosPrimeInputs.HighPrimeMass.rewardedHighMass z.gap w z.cutoff ell T c := by
  classical
  unfold uncappedRewardedHighMass ErdosPrimeInputs.HighPrimeMass.rewardedHighMass
  simp only [terminal_gap_remaining]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ps hp
    obtain ⟨hfamily,hhigh⟩ := Finset.mem_filter.mp hp
    obtain ⟨hdec,hactual⟩ := Finset.mem_filter.mp hfamily
    have hgap := (uncapped_gap_positive hell hr hs hactual).le
    rw [terminal_gap_remaining] at hgap
    exact Finset.mem_filter.mpr ⟨hdec,
      (uncapped_has_high_iff hell hr hs hz hactual).mp hhigh,hgap⟩
  · intro ps _ _
    exact mul_nonneg (prefixWeight_nonneg ps) (Real.exp_pos _).le

end NumberTheoryLean.ActualPrimeHigh

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open FinitePathGeometry PrimeHistories PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass
open ActualPrimeHigh

noncomputable def retainedPrefixes (w ell S : ℝ) (start : Node) : Finset (List ℕ) := by
  classical
  exact (uncappedPrefixes w ell start).filter (allowed w ell S start)

theorem mem_retainedPrefixes {w ell S : ℝ} (hw : 1 < w) (start : Node) (ps : List ℕ) :
    ps ∈ retainedPrefixes w ell S start ↔ allowed w ell S start ps := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨(mem_uncappedPrefixes hw start ps).mpr ?_,h⟩
    apply (uncapped_iff_exists_ceiling w ell start ps).mpr
    exact ⟨max S start.ratio,le_max_right _ _,allowed_mono (le_max_left _ _) h⟩

noncomputable def retainedHistoryEquiv {w ell S : ℝ} (hw : 1 < w) (start : Node) :
    {ps // ps ∈ retainedPrefixes w ell S start} ≃ History w ell S start where
  toFun ps := ⟨ps.val,(mem_retainedPrefixes hw start ps.val).mp ps.property⟩
  invFun h := ⟨h.primes,(mem_retainedPrefixes hw start h.primes).mpr h.admissible⟩
  left_inv ps := by cases ps; rfl
  right_inv h := by cases h; rfl

noncomputable abbrev historyFintype {w ell S : ℝ} (hw : 1 < w) (start : Node) :
    Fintype (History w ell S start) :=
  Fintype.ofEquiv {ps // ps ∈ retainedPrefixes w ell S start} (retainedHistoryEquiv hw start)

theorem sum_histories {w ell S : ℝ} (hw : 1 < w) (start : Node) (F : List ℕ → ℝ) :
    letI := historyFintype (ell := ell) (S := S) hw start
    (∑ h : History w ell S start,F h.primes) =
      ∑ ps ∈ retainedPrefixes w ell S start,F ps := by
  classical
  let := historyFintype (ell := ell) (S := S) hw start
  calc
    _ = ∑ ps : {ps // ps ∈ retainedPrefixes w ell S start},F ps.val :=
      (Equiv.sum_comp (retainedHistoryEquiv hw start) (fun h => F h.primes)).symm
    _ = _ := Finset.sum_attach _ F

theorem retained_history_horizon {w ell S B : ℝ} (hw : 1 < w)
    (hell : 1 ≤ ell) (hS0 : 0 ≤ S) {start : Node}
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B)
    {ps : List ℕ} (hps : ps ∈ retainedPrefixes w ell S start) :
    ps.length < LowStateHorizon.sourceHorizon S B := by
  exact PrimeHistoryHorizon.history_length_lt hell hS0 hr hs hB hsize
    ⟨ps,(mem_retainedPrefixes hw start ps).mp hps⟩

end NumberTheoryLean.PrimeFamilyOccupation

end

section

namespace NumberTheoryLean.PrimeCompactWeights

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactVisits
open PrimeCorrectionFactor PrimeBinMembership PrimeTiltGeometry DerivativeWeights

noncomputable def inverseBound (K : ℝ) : ℝ := max (1/weight .even K) (1/weight .odd K)

theorem valid_compact_end {K : ℝ} (hK : 3 ≤ K) (i : Side) : Valid i K := by
  cases i <;> change _ ≤ K <;> linarith

theorem inverseBound_pos {K : ℝ} (hK : 3 ≤ K) : 0 < inverseBound K :=
  (one_div_pos.mpr (weight_pos (valid_compact_end hK .even))).trans_le (le_max_left _ _)

theorem compact_inverse_weight {K s : ℝ} {i : Side} (hK : 3 ≤ K) (hs : Valid i s) (hsK : s ≤ K) :
    1/weight i s ≤ inverseBound K := by
  have hpos := weight_pos (valid_compact_end hK i)
  have hmono := TwoStepDensityBounds.weight_antitone hs (valid_compact_end hK i) hsK
  have h := one_div_le_one_div_of_le hpos hmono
  cases i with
  | even => exact h.trans (le_max_left _ _)
  | odd => exact h.trans (le_max_right _ _)

theorem terminal_cutoff_lower {w ell S : ℝ} {start : Node} {ps : List ℕ}
    (hc : ell ≤ start.cutoff) (hp : allowed w ell S start ps) : ell ≤ (terminal w start ps).cutoff := by
  classical
  induction ps generalizing start with
  | nil => exact hc
  | cons p ps ih =>
    obtain ⟨hchild,htail⟩ := (allowed_cons w ell S start p ps).mp hp
    have hlo : ell < ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p :=
      (Finset.mem_filter.mp hchild).2.1
    exact ih hlo.le htail

theorem history_ratio_le_gap {w ell S : ℝ} {start : Node}
    (hell : 1 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hc : Consistent start) (hcut : ell ≤ start.cutoff) (h : History w ell S start) :
    h.node.ratio ≤ h.node.gap := by
  have hv : 0 < h.node.ratio := valid_pos (terminal_valid hs h.admissible)
  have hn : Consistent h.node := history_consistent (by linarith) hr hs hc h
  have hlow : ell ≤ h.node.cutoff := terminal_cutoff_lower hcut h.admissible
  change h.node.cutoff = h.node.gap/h.node.ratio at hn
  have he := (eq_div_iff hv.ne').mp hn
  nlinarith

noncomputable def compactConstant (K : ℝ) : ℝ :=
  2*K^2*weight .even (199/100)*inverseBound K

theorem compactConstant_pos {K : ℝ} (hK : 3 ≤ K) : 0 < compactConstant K := by
  have hφ : 0 < weight .even (199/100) := weight_pos (by norm_num [Valid])
  have hI := inverseBound_pos hK
  unfold compactConstant
  positivity

noncomputable def scaledWeight (w B : ℝ) {ell S : ℝ} (start : Node) : ChainState w ell S start → ℝ
  | none => 0
  | some h => B^2*(1+epsilon w)^h.primes.length*(h.node.gap/start.gap)^2*
      (weight start.side start.ratio/weight h.node.side h.node.ratio)

theorem scaledWeight_nonneg {w B ell S : ℝ} {start : Node}
    (hs : Valid start.side start.ratio) (z : ChainState w ell S start) : 0 ≤ scaledWeight w B start z := by
  cases z with
  | none => exact le_rfl
  | some h =>
    have hφ := (weight_pos hs).le
    have hφ' := (weight_pos (terminal_valid hs h.admissible)).le
    have he := (normalizer_pos w).le
    unfold scaledWeight
    positivity

theorem scaled_compact_bound {d w ell B K : ℝ} {start : Node}
    (hK : 3 ≤ K) (hB : 0 < B) (hell : 1 ≤ ell) (hellB : ell ≤ B)
    (hlogB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w)
    (hbudget : correctionBudget d w ≤ 1)
    (hi : start.side = .even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hc : Consistent start) (hcut : start.cutoff = B)
    (h : History w ell ((Real.log B)^2) start) (hgK : h.node.gap ≤ K) :
    scaledWeight w B start (some h) ≤ compactConstant K := by
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hs0 := valid_pos hs
  have he : start.gap = B*start.ratio := by
    have hh : start.cutoff = start.gap/start.ratio := hc
    rw [hcut] at hh
    exact ((eq_div_iff hs0.ne').mp hh).symm
  have hr : 0 < start.gap := by rw [he]; positivity
  have hBr : B ≤ start.gap := by rw [he]; nlinarith
  have hsize : start.gap ≤ (23/10:ℝ)*B := by rw [he]; nlinarith
  have hrat : h.node.ratio ≤ K := (history_ratio_le_gap hell hr hs hc (by rwa [hcut]) h).trans hgK
  have hgv : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
  have hgp : 0 < h.node.gap := terminal_gap_positive (by linarith) hr hs h.admissible
  have hinv := compact_inverse_weight hK hgv hrat
  have hinit : weight start.side start.ratio ≤ weight .even (199/100) := by
    rw [hi]
    exact TwoStepDensityBounds.weight_antitone (by norm_num [Valid]) (hi ▸ hs) h199
  have hcorr : (1+epsilon w)^h.primes.length ≤ 2 := by
    have hh := (history_correction hlogB hcomp hell hr hs hB hsize h).2
    linarith
  have hgap : B^2*(h.node.gap/start.gap)^2 ≤ K^2 := by
    have hratio : B/start.gap ≤ 1 := (div_le_one hr).mpr hBr
    have hpos : 0 ≤ B/start.gap := div_nonneg hB.le hr.le
    have heq : B^2*(h.node.gap/start.gap)^2 = (B/start.gap)^2*h.node.gap^2 := by ring
    rw [heq]
    have h1 : (B/start.gap)^2 ≤ 1 := by nlinarith
    have h2 : h.node.gap^2 ≤ K^2 := by nlinarith
    nlinarith [sq_nonneg (B/start.gap),mul_nonneg (sub_nonneg.mpr h1) (sq_nonneg h.node.gap)]
  have hC : 0 ≤ (1+epsilon w)^h.primes.length := pow_nonneg (normalizer_pos w).le _
  have hI : 0 ≤ inverseBound K := (inverseBound_pos hK).le
  have hφ : 0 ≤ weight .even (199/100) := (weight_pos (by norm_num [Valid])).le
  have hpφ : 0 ≤ weight start.side start.ratio := (weight_pos hs).le
  have hφg : 0 < weight h.node.side h.node.ratio := weight_pos hgv
  calc
    _ = ((1+epsilon w)^h.primes.length*(B^2*(h.node.gap/start.gap)^2))*
        (weight start.side start.ratio*(1/weight h.node.side h.node.ratio)) := by unfold scaledWeight; ring
    _ ≤ (2*K^2)*(weight .even (199/100)*inverseBound K) := by
      exact mul_le_mul (mul_le_mul hcorr hgap (by positivity) (by norm_num))
        (mul_le_mul hinit hinv (by positivity) hφ) (by positivity) (by positivity)
    _ = _ := by unfold compactConstant; ring

end NumberTheoryLean.PrimeCompactWeights

end

end Erdos970

end OAI
