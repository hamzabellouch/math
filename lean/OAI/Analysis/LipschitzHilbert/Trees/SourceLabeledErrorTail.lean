import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledErrorFamily
import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularErrorTail

namespace OAI

/-! The bounded active-label overlap gives the same logarithmic dyadic
source budget and exponential error tail, with no total-label count. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

namespace LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

/-- Every actual packet is short, even if the original index horizon
contains empty longer scales. -/
theorem error_le_restricted_majorant (P : LabeledAngularErrorFamily N Λ κ ι) (H : ℝ)
    (hshort : ∀ j b (_u : ι j b), P.length j ≤ H) (y x : ℝ) :
    P.error y x ≤ ((P.sources y).restrictLength H).majorant x := by
  apply Finset.sum_le_sum
  intro j _
  rw [LineErrorSources.restrictLength_term_eq]
  change P.scaleError j y x ≤ if P.length j ≤ H then (P.sources y).term j x else 0
  by_cases h : P.length j ≤ H
  · rw [ite_eq_left h]
    exact P.scaleError_le j y x
  · rw [ite_eq_right h]
    have heq : P.scaleError j y x = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      apply Finset.sum_eq_zero
      intro u _
      exact False.elim (h (hshort j b u))
    exact le_of_eq heq

/-- The exact dyadic source branching gives polynomial error-source
budgets without any dependence on the wide carrier constant. -/
theorem eventually_source_error_budgets (p : ℝ) (J₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (Λ : Fin N → Type) (κ : Type) (ι : ∀ j, Λ j → Type)
      [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)] (P : LabeledAngularErrorFamily N Λ κ ι),
      P.sourceAmplitude ≤ L^p → P.wideExponent ≤ J₀ →
      P.exponent = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      ∀ y, (P.sources y).sourceBound ≤ L^(p+3) ∧ (P.sources y).sumBound ≤ L^(p+3) := by
  let c : ℝ := (J₀+1:ℕ)+4+4/Real.log 2
  have hc : 0 < c := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [c]
    positivity
  filter_upwards [SourceParameters.eventually_branching_separation,
    eventually_ge_atTop (max 1 (max (2*Real.pi) (c*Real.pi)))] with L hsep hlarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hpi : 2*Real.pi ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hcpi : c*Real.pi ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hlogB : Real.log (SourceParameters.branching L) ≤ L := by
    have h := Real.log_le_log (pow_pos (SourceParameters.branching_pos L) 100) hsep
    rw [Real.log_pow,Real.log_exp] at h
    have hpow : L^(9/10:ℝ) ≤ L := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
        (by norm_num : (9/10:ℝ) ≤ 1)
    norm_num only [Nat.cast_ofNat] at h
    linarith
  intro N Λ κ ι _ _ _ P hP hJ hE y
  have hAmp := P.sourceAmplitude_nonneg
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : (P.sources y).sourceBound ≤ 2*Real.pi*L^p := by
    change (P.sourceAmplitude*(1+P.smallRatio))*Real.pi ≤ _
    have h := mul_le_mul hP (add_le_add_left P.smallRatio_le 1)
      (by linarith [P.smallRatio_pos]) (Real.rpow_nonneg hL0.le p)
    calc
      _ = (P.sourceAmplitude*(P.smallRatio+1))*Real.pi := by ring
      _ ≤ (L^p*(1+1))*Real.pi := mul_le_mul_of_nonneg_right h Real.pi_pos.le
      _ = _ := by ring
  have hwide : ((P.wideExponent+1:ℕ):ℝ)+4*P.smallRatio+
      (4/Real.log 2)*Real.log ((2:ℝ)^P.exponent) ≤ c*L := by
    have hJ' : ((P.wideExponent+1:ℕ):ℝ) ≤ (J₀+1:ℕ) := by exact_mod_cast Nat.add_le_add_right hJ 1
    have hlog : Real.log ((2:ℝ)^P.exponent) ≤ L := by
      rw [hE,← source_branching_eq_two_pow]
      exact hlogB
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4/Real.log 2)
    have hsmall := P.smallRatio_le
    have hconstant := mul_le_mul_of_nonneg_left hL
      (show 0 ≤ ((J₀+1:ℕ):ℝ)+4 by positivity)
    dsimp [c]
    nlinarith
  have hsmall0 := P.smallRatio_pos.le
  have hlog0 : 0 ≤ Real.log ((2:ℝ)^P.exponent) :=
    Real.log_nonneg (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hsum : (P.sources y).sumBound ≤ c*Real.pi*L^(p+1) := by
    rw [P.sources_log_budget]
    calc
      _ ≤ (L^p*(c*L))*Real.pi := by gcongr
      _ = _ := by rw [Real.rpow_add hL0,Real.rpow_one]; ring
  have hpow : L^(p+2) ≤ L^(p+3) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  constructor
  · apply hs.trans
    calc
      _ ≤ L*L^p := mul_le_mul_of_nonneg_right hpi (Real.rpow_nonneg hL0.le _)
      _ = L^(p+1) := by rw [Real.rpow_add hL0,Real.rpow_one]; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  · apply hsum.trans
    calc
      _ ≤ L*L^(p+1) := mul_le_mul_of_nonneg_right hcpi (Real.rpow_nonneg hL0.le _)
      _ = L^((p+1)+1) := by
        conv_rhs => rw [Real.rpow_add hL0,Real.rpow_one]
        ring
      _ = L^(p+2) := by congr 1; ring
      _ ≤ _ := hpow

/-- The actual angular error has a polynomial threshold and arbitrary
exponential tail on every binary reference interval of retained lengths. -/
theorem eventually_source_error_tail (p J : ℝ) (hp : 0 ≤ p) (hJ : 0 ≤ J) (J₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (Λ : Fin N → Type) (κ : Type) (ι : ∀ j, Λ j → Type)
      [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)] (P : LabeledAngularErrorFamily N Λ κ ι),
      P.sourceAmplitude ≤ L^p → P.wideExponent ≤ J₀ →
      P.exponent = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      ∀ (y : ℝ) (grid : FiniteLineGrid), grid.branching = 2 →
      (∀ j b (_u : ι j b), P.length j ≤ grid.width) →
      grid.lineMeasure {x | L^(p+7) ≤ P.error y x} ≤
        ENNReal.ofReal (Real.exp (-J*L))*grid.lineMeasure univ := by
  filter_upwards [eventually_source_error_budgets p J₀,
    LineErrorSources.eventually_error_polynomial_tail (p+3) J (by linarith) hJ]
    with L hbudget htail
  intro N Λ κ ι _ _ _ P hP hJ₀ hE y grid hb hshort
  have hbud := hbudget N Λ κ ι P hP hJ₀ hE y
  let Q := (P.sources y).restrictLength grid.width
  have ht := htail N Q grid hb
    ((P.sources y).restrictLength_source_zero grid.width) hbud.1 hbud.2
  have hsub : {x | L^(p+7) ≤ P.error y x} ⊆ {x | L^((p+3)+4) ≤ Q.majorant x} := by
    intro x hx
    rw [show (p+3)+4 = p+7 by ring]
    exact hx.trans (P.error_le_restricted_majorant grid.width hshort y x)
  exact (measure_mono hsub).trans ht

/-- The labeled error tail on every original physical interval. -/
theorem eventually_source_error_physical_tail (p J : ℝ) (hp : 0 ≤ p) (hJ : 0 ≤ J)
    (J₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (Λ : Fin N → Type) (κ : Type) (ι : ∀ j, Λ j → Type)
      [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]
      (P : LabeledAngularErrorFamily N Λ κ ι),
      P.sourceAmplitude ≤ L^p → P.wideExponent ≤ J₀ →
      P.exponent = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      ∀ (y u H : ℝ), 0 < H → (∀ j b (_i : ι j b), P.length j ≤ H) →
      (volume.restrict (Ico u (u+H))) {x | L^(p+7) ≤ P.error y x} ≤
        ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [eventually_source_error_tail p J hp hJ J₀] with L htail
  intro N Λ κ ι _ _ _ P hP hJ₀ hE y u H hH hshort
  let grid : FiniteLineGrid :=
    { branching := 2, branching_pos := by decide, origin := u,
      width := H, width_pos := hH, depth := 0 }
  have ht := htail N Λ κ ι P hP hJ₀ hE y grid rfl hshort
  have hm : grid.lineMeasure univ = ENNReal.ofReal H := by
    change (volume.restrict (Ico u (u+H))) univ = _
    rw [Measure.restrict_apply_univ,Real.volume_Ico]
    congr 1
    ring
  rwa [hm] at ht

end LabeledAngularErrorFamily
end LipschitzHilbert

end

end OAI
