import OAI.MathematicalPhysics.Boltzmann.Branching.ControlledParameterPath
import OAI.MathematicalPhysics.Boltzmann.Branching.FiveGainPullback
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedThermalChain
import OAI.MathematicalPhysics.Boltzmann.Jets.ThermalParameterChain

namespace OAI

section

/-! # Identification of the five actual thermal transitions with the analytic path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

def cycleFive {A : Type*} (f : Fin 5 → A) (k : ℕ) : A := f ⟨k%5,Nat.mod_lt _ (by decide)⟩

theorem cycleFive_apply {A : Type*} (f : Fin 5 → A) (i : Fin 5) : cycleFive f i.val = f i := by
  unfold cycleFive
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

def controlBlocks (q : ThermalControls) : Fin 5 → StageControls :=
  fun i => ((q.1.1 i,q.1.2 i),q.2 i)

theorem controlBlocks_eq (q : ThermalControls) : controlBlocks q = packControls.symm q := rfl

def actualNext (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment) :
    ℕ → State → StageControls → State :=
  fun k => coreNext α γ (cycleFive env.1 k) (cycleFive env.2.1 k) (cycleFive colors k)

theorem actualNext_controlBlock (colors : Fin 5 → Bool) (α γ : ℝ)
    (env : ThermalEnvironment) {q : ThermalControls} (hq : q ∈ controlDomain)
    (i : Fin 5) (z : State) :
    actualNext colors α γ env i.val z (cycleFive (controlBlocks q) i.val) =
      thermalStep (JetPrototype.sign (colors i)) α γ (env.1 i) (env.2.1 i)
        (q.1.1 i) (q.1.2 i) (q.2 i) z := by
  simp only [actualNext,cycleFive_apply,controlBlocks]
  exact coreNext_eq_thermalStep (colors i) z _ (hq i).le

attribute [local irreducible] thermalPath actualNext

theorem actualPath_eq_thermalPath (colors : Fin 5 → Bool) (α γ : ℝ)
    (env : ThermalEnvironment) {q : ThermalControls} (hq : q ∈ controlDomain)
    {n : ℕ} (hn : n ≤ 5) :
    controlledPath (actualNext colors α γ env) (cycleFive (controlBlocks q)) 0 env.2.2 n =
      thermalPath (fun i => JetPrototype.sign (colors i)) α γ env q n := by
  induction n with
  | zero => simp only [controlledPath,thermalPath]
  | succ n ih =>
    have hnlt : n < 5 := by omega
    have hprev := ih (by omega)
    rw [controlledPath,hprev]
    simp only [Nat.zero_add,thermalPath,dite_eq_left hnlt]
    let i : Fin 5 := ⟨n,hnlt⟩
    exact actualNext_controlBlock colors α γ env hq i _

def stageValidity (colors : Fin 5 → Bool) (α γ a : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) : ℝ≥0∞ :=
  (validStage a).indicator (fun _ => 1)
    (stagePrevious colors α γ env q i,controlBlocks q i)

theorem stageValidity_le_one (colors : Fin 5 → Bool) (α γ a : ℝ)
    (env : ThermalEnvironment) (q : ThermalControls) (i : Fin 5) :
    stageValidity colors α γ a env q i ≤ 1 := by
  unfold stageValidity
  exact indicator_le_self' (fun _ _ => zero_le) _

theorem coreDensity_eq_stage {r η K α γ qexp a : ℝ} (colors : Fin 5 → Bool)
    (env : ThermalEnvironment) {q : ThermalControls} (hq : q ∈ controlDomain) (i : Fin 5) :
    coreDensity r η K α γ (env.1 i) (env.2.1 i) qexp a (colors i)
      (stagePrevious colors α γ env q i) (controlBlocks q i) =
        stageValidity colors α γ a env q i * stageDensity colors r η K α γ qexp env q i := by
  unfold coreDensity stageValidity
  by_cases hv : (stagePrevious colors α γ env q i,controlBlocks q i) ∈ validStage a
  · rw [indicator_of_mem hv,indicator_of_mem hv,one_mul]
    simp only [controlBlocks,stageArguments,max_eq_right (hq i).le]
    rfl
  · rw [indicator_of_notMem hv,indicator_of_notMem hv,zero_mul]

def pathValidity (colors : Fin 5 → Bool) (α γ a : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) : ℝ≥0∞ := ∏ i : Fin 5, stageValidity colors α γ a env q i

theorem pathValidity_le_one (colors : Fin 5 → Bool) (α γ a : ℝ)
    (env : ThermalEnvironment) (q : ThermalControls) : pathValidity colors α γ a env q ≤ 1 := by
  unfold pathValidity
  calc
    _ ≤ ∏ _i : Fin 5, (1 : ℝ≥0∞) := Finset.prod_le_prod (fun i _ =>
      stageValidity_le_one colors α γ a env q i)
    _ = _ := by simp

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The actual five-collision integrand is the bounded thermal path density -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

def actualDensity (colors : Fin 5 → Bool) (r η K α γ qexp a : ℝ) (env : ThermalEnvironment) :
    ℕ → State → StageControls → ℝ≥0∞ :=
  fun k => coreDensity r η K α γ (cycleFive env.1 k) (cycleFive env.2.1 k) qexp a
    (cycleFive colors k)

def actualFiveIntegrand (colors : Fin 5 → Bool) (r η K α γ qexp a : ℝ)
    (env : ThermalEnvironment) (f : Published.KineticPhase → ℝ≥0∞) (q : ThermalControls) : ℝ≥0∞ :=
  chainIntegrand (actualNext colors α γ env) (actualDensity colors r η K α γ qexp a env)
    (fun z => f (toKinetic z)) 0 5 env.2.2 (controlBlocks q)

attribute [local irreducible] thermalPath actualNext actualDensity coreDensity stageDensity

theorem actualFiveIntegrand_eq (colors : Fin 5 → Bool) (r η K α γ qexp a : ℝ)
    (env : ThermalEnvironment) (f : Published.KineticPhase → ℝ≥0∞)
    {q : ThermalControls} (hq : q ∈ controlDomain) :
    actualFiveIntegrand colors r η K α γ qexp a env f q =
      (pathValidity colors α γ a env q * pathDensity colors r η K α γ qexp env q) *
        f (toKinetic (thermalMap (fun i => JetPrototype.sign (colors i)) α γ (env,q))) := by
  let next := actualNext colors α γ env
  let density := actualDensity colors r η K α γ qexp a env
  let controls := cycleFive (controlBlocks q)
  have he := chainIntegrand_eq_pathProduct next density (fun z => f (toKinetic z))
    controls 0 5 env.2.2
  simp only [Nat.zero_add] at he
  have hcontrols : (fun j : Fin 5 => controls j.val) = controlBlocks q := by
    funext j
    exact cycleFive_apply (controlBlocks q) j
  rw [hcontrols] at he
  have hp (n : ℕ) (hn : n ≤ 5) : controlledPath next controls 0 env.2.2 n =
      thermalPath (fun i => JetPrototype.sign (colors i)) α γ env q n :=
    actualPath_eq_thermalPath colors α γ env hq hn
  have hfactor (i : Fin 5) : density i.val (controlledPath next controls 0 env.2.2 i.val)
      (controls i.val) = stageValidity colors α γ a env q i *
        stageDensity colors r η K α γ qexp env q i := by
    rw [hp i.val i.isLt.le]
    simp only [density,actualDensity,controls,cycleFive_apply]
    exact coreDensity_eq_stage colors env hq i
  have hprod : (∏ i : Fin 5, density i.val (controlledPath next controls 0 env.2.2 i.val)
      (controls i.val)) = ∏ i : Fin 5, stageValidity colors α γ a env q i *
        stageDensity colors r η K α γ qexp env q i :=
    Finset.prod_congr rfl (fun i _ => hfactor i)
  calc
    _ = (∏ i : Fin 5, density i.val (controlledPath next controls 0 env.2.2 i.val)
        (controls i.val)) * f (toKinetic (controlledPath next controls 0 env.2.2 5)) := he
    _ = (∏ i : Fin 5, stageValidity colors α γ a env q i *
        stageDensity colors r η K α γ qexp env q i) *
          f (toKinetic (thermalMap (fun i => JetPrototype.sign (colors i)) α γ (env,q))) := by
      rw [hprod,hp 5 le_rfl]
      rfl
    _ = _ := by rw [Finset.prod_mul_distrib]; rfl

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The physical five-core chain as one thermal parameter integral -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

attribute [local irreducible] actualNext actualDensity actualFiveIntegrand

theorem actualFiveIntegrand_measurable {r α γ : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (colors : Fin 5 → Bool) (η K qexp a : ℝ)
    (env : PositiveEnvironment) {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    Measurable (actualFiveIntegrand colors r η K α γ qexp a env.val f) := by
  have hnext (i : ℕ) : Measurable (fun p : State × StageControls =>
      actualNext colors α γ env.val i p.1 p.2) := by
    unfold actualNext
    exact coreNext_measurable hα hγ (env.property _) _ _
  have hdensity (i : ℕ) : Measurable (fun p : State × StageControls =>
      actualDensity colors r η K α γ qexp a env.val i p.1 p.2) := by
    unfold actualDensity
    exact coreDensity_measurable hr hα hγ (env.property _) η K _ qexp a _
  have hinput : Measurable (fun q : ThermalControls => (env.val.2.2,packControls.symm q)) :=
    measurable_const.prodMk packControls.symm.measurable
  have hm := (chainIntegrand_measurable _ _ hnext hdensity
    (hf.comp toKinetic.measurable) 0 5).comp
      hinput
  unfold actualFiveIntegrand
  simpa only [controlBlocks_eq,Function.comp_def] using hm

theorem actual_five_core_integral {r α γ a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 ≤ a) (colors : Fin 5 → Bool)
    (η K qexp : ℝ) (env : PositiveEnvironment) (hd : ∀ i, 0 < env.val.2.1 i)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    actualCoreChain r η K α γ qexp a (cycleFive env.val.1) (cycleFive env.val.2.1)
      (cycleFive colors) f 0 5 (toKinetic env.val.2.2) =
        ∫⁻ q, actualFiveIntegrand colors r η K α γ qexp a env.val f q := by
  have hμ' (i : ℕ) : 0 < cycleFive env.val.1 i := env.property _
  have hd' (i : ℕ) : 0 < cycleFive env.val.2.1 i := hd _
  have hm := actualFiveIntegrand_measurable hr hα hγ colors η K qexp a env hf
  have he := packControls_measurePreserving.lintegral_comp hm
  calc
    _ = ∫⁻ p : Fin 5 → StageControls,
        chainIntegrand (actualNext colors α γ env.val)
          (actualDensity colors r η K α γ qexp a env.val) (fun z => f (toKinetic z))
          0 5 env.val.2.2 p := by
      unfold actualNext actualDensity
      exact actualCoreChain_product_integral hr hα hγ ha η K qexp (cycleFive env.val.1)
          (cycleFive env.val.2.1) (cycleFive colors) hμ' hd' hf 0 5 env.val.2.2
    _ = _ := by
      convert he using 1
      apply lintegral_congr
      intro p
      unfold actualFiveIntegrand
      rw [controlBlocks_eq,packControls.symm_apply_apply]

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Physical five-collision integrals have only positive collision times -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

attribute [local irreducible] actualNext actualDensity coreDensity thermalPath

theorem actualFiveIntegrand_zero_outside {a : ℝ} (ha : 0 ≤ a)
    (colors : Fin 5 → Bool) (r η K α γ qexp : ℝ) (env : ThermalEnvironment)
    (f : Published.KineticPhase → ℝ≥0∞) {q : ThermalControls} (hq : q ∉ controlDomain) :
    actualFiveIntegrand colors r η K α γ qexp a env f q = 0 := by
  classical
  have hbad : ∃ i : Fin 5, q.1.1 i ≤ 0 := by
    change ¬ (∀ i : Fin 5, 0 < q.1.1 i) at hq
    push Not at hq
    exact hq
  obtain ⟨i,hi⟩ := hbad
  let next := actualNext colors α γ env
  let density := actualDensity colors r η K α γ qexp a env
  let controls := cycleFive (controlBlocks q)
  have he := chainIntegrand_eq_pathProduct next density (fun z => f (toKinetic z))
    controls 0 5 env.2.2
  simp only [Nat.zero_add] at he
  have hcontrols : (fun j : Fin 5 => controls j.val) = controlBlocks q := by
    funext j
    exact cycleFive_apply (controlBlocks q) j
  rw [hcontrols] at he
  have hzero : density i.val (controlledPath next controls 0 env.2.2 i.val) (controls i.val) = 0 := by
    unfold density actualDensity controls
    rw [cycleFive_apply,cycleFive_apply,cycleFive_apply,cycleFive_apply]
    unfold coreDensity
    apply indicator_of_notMem
    intro h
    exact (not_lt_of_ge (hi.trans ha)) h.1
  have hp : (∏ j : Fin 5, density j.val (controlledPath next controls 0 env.2.2 j.val)
      (controls j.val)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hzero
  rw [hp,zero_mul] at he
  exact he

theorem actualFiveIntegrand_eq_indicator {a : ℝ} (ha : 0 ≤ a)
    (colors : Fin 5 → Bool) (r η K α γ qexp : ℝ) (env : ThermalEnvironment)
    (f : Published.KineticPhase → ℝ≥0∞) :
    actualFiveIntegrand colors r η K α γ qexp a env f =
      controlDomain.indicator (fun q =>
        (pathValidity colors α γ a env q*pathDensity colors r η K α γ qexp env q)*
          f (toKinetic (thermalMap (fun i => JetPrototype.sign (colors i)) α γ (env,q)))) := by
  classical
  funext q
  by_cases hq : q ∈ controlDomain
  · rw [indicator_of_mem hq]
    exact actualFiveIntegrand_eq colors r η K α γ qexp a env f hq
  · rw [indicator_of_notMem hq]
    exact actualFiveIntegrand_zero_outside ha colors r η K α γ qexp env f hq

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Compact retained physical five-core integrals vanish by the published scalar input -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.FiveGainMap

theorem actual_five_core_masked_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a b Vmax : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η : ℝ) {μ : Fin 5 → ℝ} (hμ : ∀ i, 0 < μ i)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    {D : Set ThermalControls} (hD : IsCompact D) (hDT : D ⊆ controlDomain)
    (mask : ℕ → ThermalControls → ℝ≥0∞)
    (hm : ∀ n q, q ∈ controlDomain → mask n q ≤ 1)
    (hgood : ∀ n q, q ∈ controlDomain → mask n q ≠ 0 →
      pathValidity colors α γ a (env n).val q ≠ 0 →
      ∀ i, stageGood colors α γ a b Vmax (env n).val q i)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q in D, mask n q*
      actualFiveIntegrand colors (r n) η K α γ qexp a (env n).val (g n) q)
      atTop (𝓝 0) := by
  let retained : ℕ → ThermalControls → ℝ≥0∞ :=
    fun n q => mask n q*pathValidity colors α γ a (env n).val q
  have hretained : ∀ n q, q ∈ controlDomain → retained n q ≤ 1 := by
    intro n q hqt
    simpa only [one_mul] using mul_le_mul' (hm n q hqt)
      (pathValidity_le_one colors α γ a (env n).val q)
  have hrGood : ∀ n q, q ∈ controlDomain → retained n q ≠ 0 →
      ∀ i, stageGood colors α γ a b Vmax (env n).val q i := by
    intro n q hqt hne
    have hn := mul_ne_zero_iff.mp hne
    exact hgood n q hqt hn.1 hn.2
  have hlim := five_gain_parameter_tendsto hMityagin hK hα hγ hq ha hb hV colors η hμ
    t₀ x v hv henv r hr hD hDT retained hretained hrGood hM hg hgM hL
  have he : (fun n => ∫⁻ q in D, mask n q*
        actualFiveIntegrand colors (r n) η K α γ qexp a (env n).val (g n) q) =
      (fun n => ∫⁻ q in D,
        (retained n q*pathDensity colors (r n) η K α γ qexp (env n).val q)*
          g n (toKinetic (thermalMap (fun i => JetPrototype.sign (colors i)) α γ ((env n).val,q)))) := by
    funext n
    apply setLIntegral_congr_fun hD.measurableSet
    intro q hqd
    dsimp only
    rw [actualFiveIntegrand_eq colors (r n) η K α γ qexp a (env n).val (g n) (hDT hqd)]
    dsimp only [retained]
    ring
  rw [he]
  exact hlim

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Exact physical five-core integrals with all state restrictions retained -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

def actualPathWeight (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (weight : Fin 5 → Published.KineticPhase → ℝ≥0∞) (q : ThermalControls) : ℝ≥0∞ :=
  statePathWeight (actualNext colors α γ env)
    (fun i z => cycleFive weight i (toKinetic z)) (cycleFive (controlBlocks q)) 0 5 env.2.2

theorem actualPathWeight_le_one (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (weight : Fin 5 → Published.KineticPhase → ℝ≥0∞) (hw : ∀ i z, weight i z ≤ 1)
    (q : ThermalControls) : actualPathWeight colors α γ env weight q ≤ 1 :=
  statePathWeight_le_one _ _ (fun _i z => hw _ (toKinetic z)) _ _ _ _

attribute [local irreducible] actualNext actualDensity actualFiveIntegrand controlledPath

theorem weighted_five_integrand (colors : Fin 5 → Bool) (r η K α γ qexp a : ℝ)
    (env : ThermalEnvironment) (weight : Fin 5 → Published.KineticPhase → ℝ≥0∞)
    (f : Published.KineticPhase → ℝ≥0∞) (q : ThermalControls) :
    chainIntegrand (actualNext colors α γ env)
      (fun i z p => actualDensity colors r η K α γ qexp a env i z p *
        cycleFive weight i (toKinetic (actualNext colors α γ env i z p)))
      (fun z => f (toKinetic z)) 0 5 env.2.2 (controlBlocks q) =
        actualPathWeight colors α γ env weight q *
          actualFiveIntegrand colors r η K α γ qexp a env f q := by
  have h := chainIntegrand_weighted (actualNext colors α γ env)
    (actualDensity colors r η K α γ qexp a env)
    (fun i z => cycleFive weight i (toKinetic z)) (fun z => f (toKinetic z))
    (cycleFive (controlBlocks q)) 0 5 env.2.2
  have hc : (fun j : Fin 5 => cycleFive (controlBlocks q) (0+j.val)) = controlBlocks q := by
    funext j
    simpa only [Nat.zero_add] using cycleFive_apply (controlBlocks q) j
  rw [hc] at h
  simpa only [actualPathWeight,actualFiveIntegrand] using h

theorem actual_weighted_five_integral {r α γ a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 ≤ a) (colors : Fin 5 → Bool)
    (η K qexp : ℝ) (env : PositiveEnvironment) (hd : ∀ i, 0 < env.val.2.1 i)
    (weight : Fin 5 → Published.KineticPhase → ℝ≥0∞)
    (hw : ∀ i, Measurable (weight i)) (hwfin : ∀ i z, weight i z ≠ ∞)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    weightedCoreChain r η K α γ qexp a (cycleFive env.val.1) (cycleFive env.val.2.1)
      (cycleFive colors) (cycleFive weight) f 0 5 (toKinetic env.val.2.2) =
        ∫⁻ q, actualPathWeight colors α γ env.val weight q *
          actualFiveIntegrand colors r η K α γ qexp a env.val f q := by
  let F : ThermalControls → ℝ≥0∞ := fun q =>
    chainIntegrand (actualNext colors α γ env.val)
      (fun i z p => actualDensity colors r η K α γ qexp a env.val i z p *
        cycleFive weight i (toKinetic (actualNext colors α γ env.val i z p)))
      (fun z => f (toKinetic z)) 0 5 env.val.2.2 (controlBlocks q)
  have hnext (i : ℕ) : Measurable (fun p : State × StageControls =>
      actualNext colors α γ env.val i p.1 p.2) := by
    unfold actualNext
    exact coreNext_measurable hα hγ (env.property _) _ _
  have hdensity (i : ℕ) : Measurable (fun p : State × StageControls =>
      actualDensity colors r η K α γ qexp a env.val i p.1 p.2 *
        cycleFive weight i (toKinetic (actualNext colors α γ env.val i p.1 p.2))) := by
    apply Measurable.mul
    · unfold actualDensity
      exact coreDensity_measurable hr hα hγ (env.property _) η K _ qexp a _
    · exact (hw _).comp (toKinetic.measurable.comp (hnext i))
  have hinput : Measurable (fun q : ThermalControls => (env.val.2.2,packControls.symm q)) :=
    measurable_const.prodMk packControls.symm.measurable
  have hF : Measurable F := by
    have hh := (chainIntegrand_measurable (actualNext colors α γ env.val)
      (fun i z p => actualDensity colors r η K α γ qexp a env.val i z p *
        cycleFive weight i (toKinetic (actualNext colors α γ env.val i z p))) hnext hdensity
      (hf.comp toKinetic.measurable) 0 5).comp hinput
    simpa only [F,controlBlocks_eq,Function.comp_def] using hh
  have he := packControls_measurePreserving.lintegral_comp hF
  calc
    _ = ∫⁻ p : Fin 5 → StageControls,
        chainIntegrand (actualNext colors α γ env.val)
          (fun i z p => actualDensity colors r η K α γ qexp a env.val i z p *
            cycleFive weight i (toKinetic (actualNext colors α γ env.val i z p)))
          (fun z => f (toKinetic z)) 0 5 env.val.2.2 p := by
      unfold actualNext actualDensity
      exact weightedCoreChain_product_integral hr hα hγ ha η K qexp _ _ _
        (fun _ => env.property _) (fun _ => hd _) (fun _ => hw _) (fun _ z => hwfin _ z)
        hf 0 5 env.val.2.2
    _ = ∫⁻ q, F q := by
      convert he using 1
      apply lintegral_congr
      intro p
      dsimp only [F]
      rw [controlBlocks_eq,packControls.symm_apply_apply]
    _ = _ := by
      apply lintegral_congr
      intro q
      exact weighted_five_integrand colors r η K α γ qexp a env.val weight f q

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Uniform compact support of a retained physical five-collision path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.FiveGainMap

def retainedPath (colors : Fin 5 → Bool) (α γ a T b Vmax : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) : Prop := ∀ i : Fin 5,
  q.1.1 i ∈ Icc a T ∧
    ‖WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2‖ ≤ Vmax ∧
    b ≤ ‖transverse (WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2)‖ ∧
    ‖stagePoint colors α γ env q i‖ ≤ Vmax ∧ b ≤ ‖transverse (stagePoint colors α γ env q i)‖

theorem retainedPath_stageGood {colors : Fin 5 → Bool} {α γ a T b Vmax : ℝ}
    {env : ThermalEnvironment} {q : ThermalControls}
    (h : retainedPath colors α γ a T b Vmax env q) (i : Fin 5) :
    stageGood colors α γ a b Vmax env q i :=
  ⟨(h i).1.1,(h i).2.1,(h i).2.2.2.2⟩

theorem retainedPath_density_support {r α γ a T b Vmax : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η K qexp : ℝ) (env : PositiveEnvironment)
    (hd : ∀ i, 0 < env.val.2.1 i) (hdmax : ∀ i, env.val.2.1 i ≤ 1)
    (hthin : ∀ i, env.val.2.1 i ≤ b/2) {q : ThermalControls}
    (hpath : retainedPath colors α γ a T b Vmax env.val q)
    (hpositive : pathDensity colors r η K α γ qexp env.val q ≠ 0) :
    q ∈ parameterBox a T (retainedPlaneBound α b Vmax) := by
  apply (mem_parameterBox a T _ q).mpr
  intro i
  have hfactor : stageDensity colors r η K α γ qexp env.val q i ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hpositive) i (Finset.mem_univ i)
  have hs := rescaledParameterDensity_support hr hα hγ (env.property i)
    (ha.le.trans (hpath i).1.1) (hd i) (hdmax i) hb (hthin i) hV η K qexp (colors i)
    (jetPosition (stagePosition colors α γ env.val q i))
    (WithLp.toLp 2 (stagePrevious colors α γ env.val q i).2.2) (q.2 i) (q.1.2 i)
    (hpath i).2.1 (hpath i).2.2.1 (hpath i).2.2.2.1 hfactor
  exact ⟨(hpath i).1,hs.2,hs.1.le⟩

theorem retained_integrand_zero_outside {r α γ a T b Vmax : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η K qexp : ℝ) (env : PositiveEnvironment)
    (hd : ∀ i, 0 < env.val.2.1 i) (hdmax : ∀ i, env.val.2.1 i ≤ 1)
    (hthin : ∀ i, env.val.2.1 i ≤ b/2) (mask : ThermalControls → ℝ≥0∞)
    (hpath : ∀ q, mask q ≠ 0 → q ∈ controlDomain →
      pathValidity colors α γ a env.val q ≠ 0 →
      retainedPath colors α γ a T b Vmax env.val q)
    (f : Published.KineticPhase → ℝ≥0∞) {q : ThermalControls}
    (hq : q ∉ parameterBox a T (retainedPlaneBound α b Vmax)) :
    mask q*actualFiveIntegrand colors r η K α γ qexp a env.val f q = 0 := by
  by_cases hm : mask q = 0
  · rw [hm,zero_mul]
  by_cases hqt : q ∈ controlDomain
  · rw [actualFiveIntegrand_eq colors r η K α γ qexp a env.val f hqt]
    by_cases hv : pathValidity colors α γ a env.val q = 0
    · rw [hv,zero_mul,zero_mul,mul_zero]
    have hz : pathDensity colors r η K α γ qexp env.val q = 0 := by
      by_contra hn
      exact hq (retainedPath_density_support hr hα hγ ha hb hV colors η K qexp env hd hdmax
        hthin (hpath q hm hqt hv) hn)
    rw [hz,mul_zero,zero_mul,mul_zero]
  · rw [actualFiveIntegrand_zero_outside ha.le colors r η K α γ qexp env.val f hqt,mul_zero]

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Full retained five-core integrals vanish on their actual compact support -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

theorem retained_integral_eq_box {r α γ a T b Vmax : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η K qexp : ℝ) (env : PositiveEnvironment)
    (hd : ∀ i, 0 < env.val.2.1 i) (hdmax : ∀ i, env.val.2.1 i ≤ 1)
    (hthin : ∀ i, env.val.2.1 i ≤ b/2) (mask : ThermalControls → ℝ≥0∞)
    (hpath : ∀ q, mask q ≠ 0 → q ∈ controlDomain →
      pathValidity colors α γ a env.val q ≠ 0 →
      retainedPath colors α γ a T b Vmax env.val q)
    (f : Published.KineticPhase → ℝ≥0∞) :
    (∫⁻ q, mask q*actualFiveIntegrand colors r η K α γ qexp a env.val f q) =
      ∫⁻ q in parameterBox a T (retainedPlaneBound α b Vmax),
        mask q*actualFiveIntegrand colors r η K α γ qexp a env.val f q := by
  symm
  apply setLIntegral_eq_of_support_subset
  intro q hq
  by_contra hout
  exact hq (retained_integrand_zero_outside hr hα hγ ha hb hV colors η K qexp env
    hd hdmax hthin mask hpath f hout)

theorem actual_five_retained_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a T b Vmax : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η : ℝ) {μ : Fin 5 → ℝ} (hμ : ∀ i, 0 < μ i)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hd : ∀ᶠ n in atTop, ∀ i, 0 < (env n).val.2.1 i ∧
      (env n).val.2.1 i ≤ 1 ∧ (env n).val.2.1 i ≤ b/2)
    (mask : ℕ → ThermalControls → ℝ≥0∞)
    (hm : ∀ n q, q ∈ controlDomain → mask n q ≤ 1)
    (hpath : ∀ n q, mask n q ≠ 0 → q ∈ controlDomain →
      pathValidity colors α γ a (env n).val q ≠ 0 →
      retainedPath colors α γ a T b Vmax (env n).val q)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q, mask n q*
      actualFiveIntegrand colors (r n) η K α γ qexp a (env n).val (g n) q)
      atTop (𝓝 0) := by
  have hlim := actual_five_core_masked_tendsto hMityagin hK hα hγ hq ha hb hV
    colors η hμ t₀ x v hv henv r hr (parameterBox_compact a T (retainedPlaneBound α b Vmax))
    (parameterBox_subset_domain ha T (retainedPlaneBound α b Vmax)) mask hm
    (fun n q hqt hm hv i => retainedPath_stageGood (hpath n q hm hqt hv) i) hM hg hgM hL
  apply (tendsto_congr' ?_).mpr hlim
  filter_upwards [hd] with n hn
  exact retained_integral_eq_box (hr n) hα.le hγ.le ha hb hV colors η K qexp (env n)
    (fun i => (hn i).1) (fun i => (hn i).2.1) (fun i => (hn i).2.2)
    (mask n) (hpath n) (g n)

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # State restrictions give the bounds of the retained five-collision path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.FiveGainMap

attribute [local irreducible] thermalPath actualNext controlledPath

theorem thermalPath_succ (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) :
    thermalPath (fun j => JetPrototype.sign (colors j)) α γ env q (i.val+1) =
      thermalStep (JetPrototype.sign (colors i)) α γ (env.1 i) (env.2.1 i)
        (q.1.1 i) (q.1.2 i) (q.2 i) (stagePrevious colors α γ env q i) := by
  rw [thermalPath,dite_eq_left i.isLt]
  rfl

theorem thermalPath_succ_time (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) :
    (thermalPath (fun j => JetPrototype.sign (colors j)) α γ env q (i.val+1)).1 = q.1.1 i := by
  rw [thermalPath_succ]
  rfl

theorem thermalPath_succ_velocity (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) :
    WithLp.toLp 2
      (thermalPath (fun j => JetPrototype.sign (colors j)) α γ env q (i.val+1)).2.2 =
        stagePoint colors α γ env q i := by
  rw [thermalPath_succ,thermalStep_eq_parameterPoint]
  rfl

theorem actualPathWeight_factor_ne_zero (colors : Fin 5 → Bool) (α γ : ℝ)
    (env : ThermalEnvironment) (weight : Fin 5 → Published.KineticPhase → ℝ≥0∞)
    {q : ThermalControls} (hqt : q ∈ controlDomain)
    (hw : actualPathWeight colors α γ env weight q ≠ 0) (i : Fin 5) :
    weight i (toKinetic
      (thermalPath (fun j => JetPrototype.sign (colors j)) α γ env q (i.val+1))) ≠ 0 := by
  unfold actualPathWeight statePathWeight at hw
  have hi := (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
  change cycleFive weight (0+i.val)
    (toKinetic (controlledPath (actualNext colors α γ env) (cycleFive (controlBlocks q))
      0 env.2.2 (i.val+1))) ≠ 0 at hi
  rw [Nat.zero_add,cycleFive_apply,
    actualPath_eq_thermalPath colors α γ env hqt (by omega)] at hi
  exact hi

/-- Any additional spatial masks are permitted: only their nonzero support matters. -/
theorem actualPathWeight_retained (colors : Fin 5 → Bool) (α γ a T b Vmax : ℝ)
    (env : ThermalEnvironment) (weight : Fin 5 → Published.KineticPhase → ℝ≥0∞)
    (hweight : ∀ i z, weight i z ≠ 0 →
      z.1.1 ∈ Icc a T ∧ ‖z.2‖ ≤ Vmax ∧ b ≤ ‖transverse z.2‖)
    (hinit : ‖WithLp.toLp 2 env.2.2.2.2‖ ≤ Vmax ∧
      b ≤ ‖transverse (WithLp.toLp 2 env.2.2.2.2)‖)
    {q : ThermalControls} (hqt : q ∈ controlDomain)
    (hw : actualPathWeight colors α γ env weight q ≠ 0) :
    retainedPath colors α γ a T b Vmax env q := by
  have hnext (i : Fin 5) := hweight i _
    (actualPathWeight_factor_ne_zero colors α γ env weight hqt hw i)
  have hnext' (i : Fin 5) : q.1.1 i ∈ Icc a T ∧
      ‖stagePoint colors α γ env q i‖ ≤ Vmax ∧
      b ≤ ‖transverse (stagePoint colors α γ env q i)‖ := by
    simpa only [toKinetic_apply,thermalPath_succ_time,thermalPath_succ_velocity] using hnext i
  intro i
  have hprev : ‖WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2‖ ≤ Vmax ∧
      b ≤ ‖transverse (WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2)‖ := by
    by_cases hi : i.val = 0
    · simpa only [stagePrevious,hi,thermalPath] using hinit
    · let j : Fin 5 := ⟨i.val-1,by omega⟩
      have hj : j.val+1 = i.val := by dsimp [j]; omega
      have he := (hnext j).2
      simpa only [toKinetic_apply,hj,stagePrevious] using he
  exact ⟨(hnext' i).1,hprev.1,hprev.2,(hnext' i).2⟩

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Vanishing of the actual restricted five-core chain -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.FiveGainMap

theorem thermal_widths_eventually_small {μ : Fin 5 → ℝ} (hμ : ∀ i, 0 < μ i)
    (t₀ : ℝ) (x v : V) {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    {b : ℝ} (hb : 0 < b) :
    ∀ᶠ n in atTop, ∀ i, (env n).val.2.1 i ≤ 1 ∧ (env n).val.2.1 i ≤ b/2 := by
  have hi (i : Fin 5) : ∀ᶠ n in atTop,
      (env n).val.2.1 i ≤ 1 ∧ (env n).val.2.1 i ≤ b/2 := by
    have hcont : Continuous (fun e : PositiveEnvironment => e.val.2.1 i) := by fun_prop
    have hlim : Tendsto (fun n => (env n).val.2.1 i) atTop (𝓝 0) := by
      simpa only [Pi.zero_apply,Function.comp_def] using (hcont.tendsto _).comp henv
    filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      hlim.eventually (gt_mem_nhds (half_pos hb))] with n h1 h2
    exact ⟨h1.le,h2.le⟩
  filter_upwards [(Finset.eventually_all (Finset.univ : Finset (Fin 5))).mpr
    (fun i _ => hi i)] with n hn i
  exact hn i (Finset.mem_univ i)

theorem actual_weighted_five_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a T b Vmax : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η : ℝ) {μ : Fin 5 → ℝ} (hμ : ∀ i, 0 < μ i)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hd : ∀ n i, 0 < (env n).val.2.1 i)
    (hinit : ∀ n, ‖WithLp.toLp 2 (env n).val.2.2.2.2‖ ≤ Vmax ∧
      b ≤ ‖transverse (WithLp.toLp 2 (env n).val.2.2.2.2)‖)
    (weight : ℕ → Fin 5 → Published.KineticPhase → ℝ≥0∞)
    (hwm : ∀ n i, Measurable (weight n i)) (hw : ∀ n i z, weight n i z ≤ 1)
    (hweight : ∀ n i z, weight n i z ≠ 0 →
      z.1.1 ∈ Icc a T ∧ ‖z.2‖ ≤ Vmax ∧ b ≤ ‖transverse z.2‖)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => weightedCoreChain (r n) η K α γ qexp a
      (cycleFive (env n).val.1) (cycleFive (env n).val.2.1) (cycleFive colors)
      (cycleFive (weight n)) (g n) 0 5 (toKinetic (env n).val.2.2)) atTop (𝓝 0) := by
  have hsmall : ∀ᶠ n in atTop, ∀ i, 0 < (env n).val.2.1 i ∧
      (env n).val.2.1 i ≤ 1 ∧ (env n).val.2.1 i ≤ b/2 := by
    filter_upwards [thermal_widths_eventually_small hμ t₀ x v henv hb] with n hn i
    exact ⟨hd n i,hn i⟩
  have hlim := actual_five_retained_tendsto hMityagin hK hα hγ hq ha hb hV colors η
    hμ t₀ x v hv henv r hr hsmall
    (fun n => actualPathWeight colors α γ (env n).val (weight n))
    (fun n q _ => actualPathWeight_le_one colors α γ (env n).val (weight n) (hw n) q)
    (fun n q hm hqt _ => actualPathWeight_retained colors α γ a T b Vmax (env n).val
      (weight n) (hweight n) (hinit n) hqt hm) hM hg hgM hL
  apply hlim.congr'
  exact Eventually.of_forall (fun n => (actual_weighted_five_integral (hr n) hα.le hγ.le ha.le
    colors η K qexp (env n) (hd n) (weight n) (hwm n)
    (fun i z => ne_top_of_le_ne_top (by norm_num) (hw n i z)) (hg n)).symm)

end BoltzmannNonuniqueness.FiveGainMap

end

end

end OAI
