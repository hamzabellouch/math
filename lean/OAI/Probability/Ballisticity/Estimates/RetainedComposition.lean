import Mathlib
import OAI.Probability.Ballisticity.Estimates.RawPair
import OAI.Probability.Ballisticity.Estimates.ProtectionLoss

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma rawTupleMixture_mono {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) {μ ν : Measure (Fin k → Lattice d)} (h : μ≤ν) :
    rawTupleMixture ℓ H μ ω≤rawTupleMixture ℓ H ν ω := by
  apply Measure.le_iff.mpr
  intro U hU
  rw [rawTupleMixture_apply,rawTupleMixture_apply]
  exact lintegral_mono' h le_rfl

lemma rawTupleMixture_smul {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (c : ℝ≥0∞) (μ : Measure (Fin k → Lattice d)) :
    rawTupleMixture ℓ H (c•μ) ω=c•rawTupleMixture ℓ H μ ω :=
  Measure.bind_smul c μ (measurable_of_countable _).aemeasurable

lemma rawTupleMixture_comp_le {d k : ℕ} (e : Direction d) (h m : ℕ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    rawTupleMixture (realPosition (step e)) m
      (rawTupleMixture (realPosition (step e)) h π ω) ω≤
        rawTupleMixture (realPosition (step e)) (h+m) π ω := by
  unfold rawTupleMixture
  rw [Measure.bind_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  apply Measure.le_iff.mpr
  intro U hU
  rw [Measure.bind_apply hU (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hU (measurable_of_countable _).aemeasurable]
  apply lintegral_mono
  intro x
  exact rawTupleEndpointLaw_comp_le e h m ω x U

lemma rawTupleEndpointLaw_zero {d k : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Fin k → Lattice d) : rawTupleEndpointLaw ℓ 0 ω x=Measure.dirac x := by
  apply Measure.ext_of_singleton
  intro y
  rw [rawTupleEndpointLaw_singleton]
  have hz (j : Fin k) : variableHitKernel ℓ 0 (ω,x j)=Measure.dirac (x j) := by
    simpa only [variableHitKernel, Kernel.coe_mk, Nat.cast_zero] using hitKernel_height_zero ℓ (x j) ω
  simp_rw [hz]
  by_cases h : x=y
  · subst y
    simp
  · obtain ⟨j,hj⟩ : ∃ j, x j ≠ y j := by
      by_contra! hn
      exact h (funext hn)
    simp only [Measure.dirac_apply', measurableSet_singleton, Set.indicator_apply,
      Pi.one_apply, Set.mem_singleton_iff, h, ↓reduceIte]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

lemma rawTupleMixture_zero {d k : ℕ} (ℓ : Vector d) (π : Measure (Fin k → Lattice d))
    (ω : Environment d) : rawTupleMixture ℓ 0 π ω=π := by
  unfold rawTupleMixture
  have hz : rawTupleEndpointLaw (k:=k) ℓ 0 ω=Measure.dirac := funext (rawTupleEndpointLaw_zero ℓ ω)
  rw [hz,Measure.bind_dirac]

lemma budgetEndpointMixture_le_raw {d k : ℕ} (e f : Direction d) (H : ℕ) (r : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    budgetEndpointMixture e f H r π ω≤rawTupleMixture (realPosition (step e)) H π ω := by
  apply Measure.le_iff.mpr
  intro U hU
  rw [budgetEndpointMixture_apply,rawTupleMixture_apply]
  exact lintegral_mono fun x => relativeBudgetEndpointLaw_le e f H r ω x U

lemma protectionMass_ennreal {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0≤r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) (n : ℕ) (ω : Environment d) :
    ENNReal.ofReal (protectionMass e f base G H r hr π n ω)=
      relativeBudgetMassENN e f (H n) (r n) (protectionProfile e f base G H r hr π n ω).val ω := by
  rw [protectionMass,←relativeBudgetMassENN_toReal]
  exact ENNReal.ofReal_toReal (lt_of_le_of_lt (relativeBudgetMassENN_le_one e f _ _ _ _) ENNReal.one_lt_top).ne

lemma protection_retained_succ {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0≤r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) (n : ℕ) (ω : Environment d) :
    ENNReal.ofReal (protectionMass e f base G H r hr π n ω) •
      (protectionProfile e f base G H r hr π (n+1) ω).val≤
        rawTupleMixture (realPosition (step e)) (H n)
          (protectionProfile e f base G H r hr π n ω).val ω := by
  rw [protectionMass_ennreal]
  change relativeBudgetMassENN e f (H n) (r n) _ ω •
    (nextBudgetProfile e f (H n) _ _ (r n) (hr n) _ ω).val≤_
  rw [nextBudgetProfile_mass]
  exact budgetEndpointMixture_le_raw e f _ _ _ ω

theorem protection_retained_le_raw {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0≤r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) (n : ℕ) (ω : Environment d) :
    (∏ i∈Finset.range n, ENNReal.ofReal (protectionMass e f base G H r hr π i ω)) •
      (protectionProfile e f base G H r hr π n ω).val≤
        rawTupleMixture (realPosition (step e)) (∑ i∈Finset.range n, H i) (π ω).val ω := by
  induction n with
  | zero => simp [protectionProfile,rawTupleMixture_zero]
  | succ n ih =>
    rw [Finset.prod_range_succ,Finset.sum_range_succ,mul_smul]
    let c := ∏ i∈Finset.range n, ENNReal.ofReal (protectionMass e f base G H r hr π i ω)
    let p := (protectionProfile e f base G H r hr π n ω).val
    have hs : c • (ENNReal.ofReal (protectionMass e f base G H r hr π n ω) •
        (protectionProfile e f base G H r hr π (n+1) ω).val)≤
        c • rawTupleMixture (realPosition (step e)) (H n) p ω :=
      smul_le_smul_left c (protection_retained_succ e f base G H r hr π n ω)
    have hc := rawTupleMixture_smul (realPosition (step e)) (H n) ω c p
    have hm := rawTupleMixture_mono (realPosition (step e)) (H n) ω ih
    exact hs.trans ((le_of_eq hc.symm).trans
      (hm.trans (rawTupleMixture_comp_le e _ _ _ ω)))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma upwardEndpoint_atom {d : ℕ} (e : Direction d) (ω : Environment d) (x : Lattice d) :
    ((ω x).val e : ℝ≥0∞) ≤ variableHitKernel (realPosition (step e)) 1 (ω,x) {x+step e} := by
  rw [←rawWordLaw_endpoint (realPosition (step e)) 1 ω x,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hm := measure_mono (μ:=rawWordLaw (realPosition (step e)) 1 ω x)
    (show {[e]} ⊆ (fun w => wordPath x w w.length) ⁻¹' {x+step e} by
      intro w hw; rcases Set.mem_singleton_iff.mp hw with rfl; simp [wordPath])
  rw [rawWordLaw_singleton,ite_eq_left (upwardWord_successful e x)] at hm
  simpa only [wordWeight,mul_one,ENNReal.ofReal_coe_nnreal] using hm

lemma tupleUpwardEndpoint_atom {d k : ℕ} (e : Direction d) (ω : Environment d)
    (x : Fin k → Lattice d) (κ : ℝ≥0) (hκ : ∀ y, κ≤(ω y).val e) :
    (κ : ℝ≥0∞)^k ≤ rawTupleEndpointLaw (realPosition (step e)) 1 ω x {tupleShiftUp e 1 x} := by
  rw [rawTupleEndpointLaw_singleton]
  calc
    (κ : ℝ≥0∞)^k = ∏ _j : Fin k, (κ : ℝ≥0∞) := by simp
    _ ≤ _ := Finset.prod_le_prod fun j _ =>
      (ENNReal.coe_le_coe.mpr (hκ (x j))).trans (by simpa only [tupleShiftUp,one_nsmul] using upwardEndpoint_atom e ω (x j))

lemma tupleUpwardEndpoint_le {d k : ℕ} (e : Direction d) (ω : Environment d)
    (x : Fin k → Lattice d) (κ : ℝ≥0) (hκ : ∀ y, κ≤(ω y).val e) :
    (κ : ℝ≥0∞)^k • Measure.dirac (tupleShiftUp e 1 x) ≤ rawTupleEndpointLaw (realPosition (step e)) 1 ω x := by
  have h : (κ : ℝ≥0∞)^k • Measure.dirac (tupleShiftUp e 1 x) ≤
      rawTupleEndpointLaw (realPosition (step e)) 1 ω x {tupleShiftUp e 1 x} • Measure.dirac (tupleShiftUp e 1 x) := by
    intro U
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul_left (tupleUpwardEndpoint_atom e ω x κ hκ) _
  rw [←Measure.restrict_singleton] at h
  exact h.trans Measure.restrict_le_self

lemma tupleUpwardMixture_le {d k : ℕ} (e : Direction d) (ω : Environment d)
    (μ : Measure (Fin k → Lattice d)) (κ : ℝ≥0) (hκ : ∀ y, κ≤(ω y).val e) :
    (κ : ℝ≥0∞)^k • μ.map (tupleShiftUp e 1) ≤ rawTupleMixture (realPosition (step e)) 1 μ ω := by
  rw [←Measure.bind_dirac_eq_map μ (measurable_of_countable _),
    ←Measure.bind_smul _ _ (measurable_of_countable _).aemeasurable]
  apply Measure.le_iff.mpr
  intro U hU
  rw [Measure.bind_apply hU (measurable_of_countable _).aemeasurable,rawTupleMixture_apply,
    lintegral_smul_measure,smul_eq_mul]
  rw [←lintegral_const_mul _ (measurable_of_countable _)]
  apply lintegral_mono
  intro x
  exact tupleUpwardEndpoint_le e ω x κ hκ U

lemma stage_separated_mass_upward {d k : ℕ} (e f : Direction d) (H : ℕ) (G : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d)
    (κ : ℝ≥0) (hκ : ∀ y, κ≤(ω y).val e) :
    (κ : ℝ≥0∞)^k * rawTupleMixture (realPosition (step e)) H π ω {y | TupleSeparated f G y} ≤
      rawTupleMixture (realPosition (step e)) (H+1) π ω {y | TupleSeparated f G y} := by
  let μ := (rawTupleMixture (realPosition (step e)) H π ω).restrict {y | TupleSeparated f G y}
  have hm := (tupleUpwardMixture_le e ω μ κ hκ).trans
    ((rawTupleMixture_mono (realPosition (step e)) 1 ω (show μ≤rawTupleMixture (realPosition (step e)) H π ω from Measure.restrict_le_self)).trans
      (rawTupleMixture_comp_le e H 1 π ω))
  have he : μ.map (tupleShiftUp e 1) {y | TupleSeparated f G y}=μ Set.univ := by
    rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    apply measure_congr
    have hs : ∀ᵐ x ∂μ,TupleSeparated f G x := ae_restrict_mem (Set.to_countable _).measurableSet
    filter_upwards [hs] with x hx
    apply propext
    apply iff_true_intro
    intro i j hij
    change G≤|signedCoordinate f (x i+1 • step e)-signedCoordinate f (x j+1 • step e)|
    simp only [one_nsmul,signedCoordinate_add,add_sub_add_right_eq_sub]
    exact hx i j hij
  have hb := hm {y | TupleSeparated f G y}
  rw [Measure.smul_apply,smul_eq_mul,he] at hb
  simpa only [μ,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] using hb

end DirectionalTransience

end

end OAI
