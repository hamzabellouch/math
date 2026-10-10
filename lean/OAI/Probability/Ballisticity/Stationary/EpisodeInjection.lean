import Mathlib
import OAI.Probability.Ballisticity.Estimates.StageInjection
import OAI.Probability.Ballisticity.Stationary.EpisodeRetention
import OAI.Probability.Ballisticity.Estimates.GlobalTuple

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience.BoundedInjection

noncomputable def injectionMultiplier (R : ℝ) : ℕ := ⌈2*R⌉₊+1

lemma injectionMultiplier_lt (R : ℝ) : 2*R < (injectionMultiplier R : ℝ) := by
  have h := Nat.le_ceil (2*R)
  dsimp [injectionMultiplier]
  push_cast
  linarith

noncomputable def injectionChoice {d k : ℕ} (f : Direction d) (R : ℝ) (hR : 0 ≤ R)
    (x : Fin k → Lattice d) : Fin k → Fin k :=
  (finite_injection_choice k R (injectionMultiplier R) hR (injectionMultiplier_lt R)
    (fun j => signedCoordinate f (x j))).choose

noncomputable def injectionOffset {d k : ℕ} (f : Direction d) (R : ℝ) (hR : 0 ≤ R)
    (x : Fin k → Lattice d) (j : Fin k) : ℕ :=
  injectionMultiplier R * ((injectionChoice f R hR x j : ℕ)+1)

noncomputable def injectTuple {d k : ℕ} (e f : Direction d) (R : ℝ) (hR : 0 ≤ R)
    (x : Fin k → Lattice d) : Fin k → Lattice d :=
  fun j => x j+injectionOffset f R hR x j • step f+step e

lemma injectionOffset_le {d k : ℕ} (f : Direction d) (R : ℝ) (hR : 0 ≤ R)
    (x : Fin k → Lattice d) (j : Fin k) : injectionOffset f R hR x j ≤ injectionMultiplier R*k := by
  exact Nat.mul_le_mul_left _ (injectionChoice f R hR x j).isLt

lemma injectTuple_separated {d k : ℕ} (e f : Direction d) (R : ℝ) (hR : 0 ≤ R)
    (x : Fin k → Lattice d) : TupleSeparated f R (injectTuple e f R hR x) := by
  intro i j hij
  have h := (finite_injection_choice k R (injectionMultiplier R) hR (injectionMultiplier_lt R)
    (fun j => signedCoordinate f (x j))).choose_spec i j hij
  simpa only [injectTuple,injectionOffset,signedCoordinate_add,signedCoordinate_nsmul,
    signedCoordinate_step_self,mul_one,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    add_sub_add_right_eq_sub,injectionChoice] using h

lemma injectTuple_height {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R : ℝ) (hR : 0 ≤ R) (a : ℝ) (x : Fin k → Lattice d)
    (hx : x ∈ TupleAtHeight (realPosition (step e)) a) :
    injectTuple e f R hR x ∈ TupleAtHeight (realPosition (step e)) (a+1) := by
  intro j
  have hh := hx j
  simp only [signedHeight_projection] at hh
  change dot (realPosition (x j+injectionOffset f R hR x j • step f+step e)) (realPosition (step e))=a+1
  simp only [signedHeight_projection,signedHeight_add_step_self,
    signedHeight_add_nsmul_other e f hef,Int.cast_add,Int.cast_one,hh]

lemma injectTuple_kernel_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R : ℝ) (hR : 0 ≤ R) (ω : Environment d) (x : Fin k → Lattice d)
    (κ : ℝ≥0) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (κ : ℝ≥0∞)^(k*(injectionMultiplier R*k+1)) • Measure.dirac (injectTuple e f R hR x) ≤
      rawTupleEndpointLaw (realPosition (step e)) 1 ω x := by
  apply TupleKernel.measure_le_of_singletons
  intro y
  by_cases hy : y=injectTuple e f R hR x
  · subst y
    simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply_of_mem (Set.mem_singleton _),mul_one,
      rawTupleEndpointLaw_singleton]
    have hc : (κ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hκ1
    calc
      _ = ∏ _j : Fin k, (κ : ℝ≥0∞)^(injectionMultiplier R*k+1) := by
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul,Nat.mul_comm]
      _ ≤ ∏ j, variableHitKernel (realPosition (step e)) 1 (ω,x j) {injectTuple e f R hR x j} := by
        apply Finset.prod_le_prod
        intro j _
        have hp := elliptic_lateral_script ω e f hef (x j) (injectionOffset f R hR x j) hκ
        have hb : (κ : ℝ≥0∞)^(injectionMultiplier R*k+1) ≤
            (κ : ℝ≥0∞)^(injectionOffset f R hR x j+1) :=
          pow_le_pow_of_le_one bot_le hc (Nat.add_le_add_right (injectionOffset_le f R hR x j) 1)
        apply hb.trans
        simp only [variableHitKernel, Kernel.coe_mk, Nat.cast_one]
        change (κ : ℝ≥0∞)^(injectionOffset f R hR x j+1) ≤
          hitKernel (Strip (realPosition (step e)) (x j) 1) (Upper (realPosition (step e)) (x j) 1) (ω,x j) {injectTuple e f R hR x j}
        simpa only [Measure.smul_apply,smul_eq_mul,injectTuple,
          Measure.dirac_apply_of_mem (Set.mem_singleton _),mul_one] using hp {injectTuple e f R hR x j}
  · simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply',measurableSet_singleton,
      Set.indicator_apply,Set.mem_singleton_iff]
    simp [Ne.symm hy]

noncomputable def injectionProfile {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R : ℝ) (hR : 0 ≤ R) (a : ℝ) (π : LayerTupleProfile (k:=k) e a) :
    BudgetProfile (k:=k) e f (a+1) R := by
  let ρ := π.val.map (injectTuple e f R hR)
  refine ⟨ρ,inferInstance,?_⟩
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
  exact π.property.2.mono fun x hx => ⟨injectTuple_height e f hef R hR a x hx,
    injectTuple_separated e f R hR x⟩

lemma injectionProfile_measurable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R : ℝ) (hR : 0 ≤ R) (a : ℝ) : Measurable (injectionProfile (k:=k) e f hef R hR a) := by
  exact ((Measure.measurable_map _ (measurable_of_countable _)).comp measurable_subtype_coe).subtype_mk

lemma injectionProfile_retained {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R : ℝ) (hR : 0 ≤ R) (a : ℝ) (π : LayerTupleProfile (k:=k) e a)
    (ω : Environment d) (κ : ℝ≥0) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (κ : ℝ≥0∞)^(k*(injectionMultiplier R*k+1)) • (injectionProfile e f hef R hR a π).val ≤
      rawTupleMixture (realPosition (step e)) 1 π.val ω := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  change (κ : ℝ≥0∞)^(k*(injectionMultiplier R*k+1))*(π.val.map (injectTuple e f R hR)) U ≤ _
  rw [Measure.map_apply (measurable_of_countable _) hU,rawTupleMixture_apply]
  calc
    _ = ∫⁻ x, ((κ : ℝ≥0∞)^(k*(injectionMultiplier R*k+1)) • Measure.dirac (injectTuple e f R hR x)) U ∂π.val := by
      simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ hU]
      rw [lintegral_const_mul _ (measurable_of_countable _)]
      congr 1
      rw [←lintegral_indicator_one ((measurable_of_countable _) hU)]
      apply lintegral_congr
      intro x
      by_cases hx : injectTuple e f R hR x ∈ U <;> simp [hx]
    _ ≤ _ := lintegral_mono fun x => (injectTuple_kernel_le e f hef R hR ω x κ hκ1 hκ) U

end DirectionalTransience.BoundedInjection

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

noncomputable def episodeInitial {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (sfloor : ℝ) (hR : 0 ≤ r sfloor) (t : ℕ) (ω : Environment d) :
    EpisodeState (k:=k) e f r := by
  let p := BoundedInjection.injectionProfile e f hef (r sfloor) hR t
    (globalTupleProfile (k:=k) e t ω)
  refine ⟨t+1,sfloor,p.val,p.property.1,?_⟩
  simpa only [Nat.cast_add,Nat.cast_one] using p.property.2

lemma episodeInitial_retained {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (sfloor : ℝ) (hR : 0 ≤ r sfloor) (t : ℕ) (ω : Environment d)
    (κ : ℝ≥0) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (crossingQuenched (realPosition (step e)) 0 t ω)^k •
      (κ : ℝ≥0∞)^(k*(BoundedInjection.injectionMultiplier (r sfloor)*k+1)) •
      episodeMeasure (episodeInitial (k:=k) e f hef r sfloor hR t ω) ≤
      rawTupleEndpointLaw (realPosition (step e)) (t+1) ω (fun _ : Fin k => 0) := by
  have hi := BoundedInjection.injectionProfile_retained e f hef (r sfloor) hR t
    (globalTupleProfile (k:=k) e t ω) ω κ hκ1 hκ
  have hi := smul_le_smul_left ((crossingQuenched (realPosition (step e)) 0 t ω)^k) hi
  rw [←rawTupleMixture_smul,globalTupleProfile_mass] at hi
  exact hi.trans (rawTupleEndpointLaw_comp_le e t 1 ω (fun _ : Fin k => 0))

noncomputable def episodeFinal {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (ω : Environment d) : EpisodeState (k:=k) e f r :=
  episodeRun e f hef r fexp g χ b sfloor N
    (episodeInitial e f hef r sfloor hR t ω) ω N

lemma episodeFinal_gt {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (ω : Environment d) : t < (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height := by
  have hh := episodeRun_height_mono e f hef r fexp g χ b sfloor N
    (episodeInitial (k:=k) e f hef r sfloor hR t ω) ω N
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self t) hh

lemma episodeFinal_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (ω : Environment d) (ht : t<N) :
    (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ≤ N :=
  episodeRun_le e f hef r fexp g χ b sfloor N _ ω (Nat.succ_le_of_lt ht) N

noncomputable def episodeBoundary {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) : ℕ → ℕ
  | 0 => 0
  | i+1 => let t := episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    if t<N then (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height else t

lemma episodeBoundary_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) (i : ℕ) : episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i ≤ N := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    rw [episodeBoundary]
    split
    · exact episodeFinal_le e f hef r fexp g χ b sfloor hR N _ ω ‹_›
    · exact ih

lemma episodeBoundary_progress {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) (i : ℕ) :
    min i N ≤ episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    rw [episodeBoundary]
    split
    · have hh := episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N
        (episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i) ω
      omega
    · omega

theorem episodeBoundary_complete {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) : episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω N=N := by
  have hu := episodeBoundary_le (k:=k) e f hef r fexp g χ b sfloor hR N ω N
  have hl := episodeBoundary_progress (k:=k) e f hef r fexp g χ b sfloor hR N ω N
  omega

end DirectionalTransience

end

end OAI
