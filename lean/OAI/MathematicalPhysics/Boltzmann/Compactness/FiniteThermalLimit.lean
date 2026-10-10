import OAI.MathematicalPhysics.Boltzmann.Branching.FiveGainConvergence

namespace OAI

section

/-! # Expansion of a finite selected gain into its collision-label tuples -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

theorem step_finset_sum {I : Type*} (s : Finset I) (a : ℝ)
    (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    (f : I → KineticPhase → ℝ≥0∞) (hf : ∀ i ∈ s, Measurable (f i)) :
    step a K (fun z => ∑ i ∈ s, f i z) = fun z => ∑ i ∈ s, step a K (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext z
    simp only [Finset.sum_empty]
    unfold step
    simp only [lintegral_zero]
  | @insert i s hi ih =>
    have hm := hf i (Finset.mem_insert_self i s)
    have ht := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hi]
    have he := step_add a K (g := fun z => ∑ j ∈ s, f j z) hm
    rw [show (fun z => f i z+∑ j ∈ s, f j z) = f i+(fun z => ∑ j ∈ s, f j z) from rfl,
      he,ht]
    rfl

def chosenGainChain {I : Type*} (a : ℝ) (K : ℕ → I → Kernel KineticPhase Velocity)
    (weight : ℕ → I → KineticPhase → ℝ≥0∞) (f : KineticPhase → ℝ≥0∞) (i : ℕ) :
    (n : ℕ) → (Fin n → I) → KineticPhase → ℝ≥0∞
  | 0, _ => f
  | n+1, labels => step a (K i (labels 0)) (fun z => weight i (labels 0) z *
      chosenGainChain a K weight f (i+1) n (Fin.tail labels) z)

def finiteGainChain {I : Type*} [Fintype I] (a : ℝ)
    (K : ℕ → I → Kernel KineticPhase Velocity)
    (weight : ℕ → I → KineticPhase → ℝ≥0∞) (f : KineticPhase → ℝ≥0∞)
    (i : ℕ) : ℕ → KineticPhase → ℝ≥0∞
  | 0 => f
  | n+1 => fun z => ∑ j : I, step a (K i j) (fun y => weight i j y *
      finiteGainChain a K weight f (i+1) n y) z

theorem chosenGainChain_measurable {I : Type*} (a : ℝ)
    (K : ℕ → I → Kernel KineticPhase Velocity) [∀ i j, IsSFiniteKernel (K i j)]
    {weight : ℕ → I → KineticPhase → ℝ≥0∞} (hw : ∀ i j, Measurable (weight i j))
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) (labels : Fin n → I) :
    Measurable (chosenGainChain a K weight f i n labels) := by
  induction n generalizing i with
  | zero => exact hf
  | succ n ih => exact step_measurable a _ ((hw i (labels 0)).mul (ih (i+1) (Fin.tail labels)))

theorem finiteGainChain_eq_sum {I : Type*} [Fintype I] (a : ℝ)
    (K : ℕ → I → Kernel KineticPhase Velocity) [∀ i j, IsSFiniteKernel (K i j)]
    {weight : ℕ → I → KineticPhase → ℝ≥0∞} (hw : ∀ i j, Measurable (weight i j))
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) (z : KineticPhase) :
    finiteGainChain a K weight f i n z = ∑ labels : Fin n → I,
      chosenGainChain a K weight f i n labels z := by
  classical
  induction n generalizing i z with
  | zero => simp only [finiteGainChain,chosenGainChain,Finset.sum_const,Finset.card_univ,
      Fintype.card_fun,Fintype.card_fin,pow_zero,one_smul]
  | succ n ih =>
    have ht : (∑ labels : Fin (n+1) → I, chosenGainChain a K weight f i (n+1) labels z) =
        ∑ j : I, ∑ labels : Fin n → I, step a (K i j) (fun y => weight i j y *
          chosenGainChain a K weight f (i+1) n labels y) z := by
      rw [← (Fin.consEquiv (fun _ : Fin (n+1) => I)).sum_comp,Fintype.sum_prod_type]
      change (∑ j : I, ∑ labels : Fin n → I,
        chosenGainChain a K weight f i (n+1) (Fin.cons j labels) z) = _
      simp only [chosenGainChain,Fin.cons_zero,Fin.tail_cons]
    rw [ht]
    apply Finset.sum_congr rfl
    intro j _
    have hfuns : (fun y => weight i j y * finiteGainChain a K weight f (i+1) n y) =
        fun y => ∑ labels : Fin n → I, weight i j y * chosenGainChain a K weight f (i+1) n labels y := by
      funext y
      rw [ih,Finset.mul_sum]
    change step a (K i j) _ z = _
    rw [hfuns]
    exact congrFun (step_finset_sum Finset.univ a (K i j)
      (fun labels y => weight i j y * chosenGainChain a K weight f (i+1) n labels y)
      (fun labels _ => (hw i j).mul
        (chosenGainChain_measurable a K hw hf (i+1) n labels))) z

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # A finite chain depends only on its actual collision-stage weights -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

theorem finiteGainChain_congr_weights {I : Type*} [Fintype I] (a : ℝ)
    (K : ℕ → I → Kernel Published.KineticPhase Velocity)
    (w w' : ℕ → I → Published.KineticPhase → ℝ≥0∞)
    (f : Published.KineticPhase → ℝ≥0∞) (i n : ℕ) :
    (∀ k, i ≤ k → k < i+n → w k = w' k) → ∀ z,
      finiteGainChain a K w f i n z = finiteGainChain a K w' f i n z := by
  induction n generalizing i with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro h z
    have hi : w i = w' i := h i le_rfl (by omega)
    have ht : ∀ k, i+1 ≤ k → k < (i+1)+n → w k = w' k := by
      intro k hk hkn
      exact h k (by omega) (by omega)
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (fun g => step a (K i j) g z)
    funext y
    rw [hi,ih (i+1) ht y]

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Finite physical thermal families expand into the actual weighted chains -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCoreSheet

def thermalKernelFamily {I : Type*} (r η K α γ q : ℝ)
    (μ d : ℕ → I → ℝ) (colors : ℕ → I → Bool) : ℕ → I → Kernel Published.KineticPhase Velocity :=
  fun i j => dilatedFreeKernel r η K α γ (r*μ i j) (d i j) q (colors i j)

instance thermalKernelFamily_sFinite {I : Type*} (r η K α γ q : ℝ)
    (μ d : ℕ → I → ℝ) (colors : ℕ → I → Bool) (i : ℕ) (j : I) :
    IsSFiniteKernel (thermalKernelFamily r η K α γ q μ d colors i j) := by
  unfold thermalKernelFamily
  infer_instance

theorem chosenThermalChain_eq_weighted {I : Type*} (r η K α γ q a : ℝ)
    (μ d : ℕ → I → ℝ) (colors : ℕ → I → Bool)
    (weight : ℕ → I → Published.KineticPhase → ℝ≥0∞)
    (f : Published.KineticPhase → ℝ≥0∞) (labels : ℕ → I) (i n : ℕ) :
    chosenGainChain a (thermalKernelFamily r η K α γ q μ d colors) weight f i n
      (fun j => labels (i+j.val)) =
      weightedCoreChain r η K α γ q a (fun i => μ i (labels i)) (fun i => d i (labels i))
        (fun i => colors i (labels i)) (fun i => weight i (labels i)) f i n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [chosenGainChain,weightedCoreChain]
    have htail : Fin.tail (fun j : Fin (n+1) => labels (i+j.val)) =
        (fun j : Fin n => labels ((i+1)+j.val)) := by
      funext j
      change labels (i+(j.val+1)) = labels ((i+1)+j.val)
      congr 1
      omega
    rw [htail,ih]
    rfl

theorem chosenThermalFive_eq_weighted {I : Type*} (r η K α γ q a : ℝ)
    (μ d : Fin 5 → I → ℝ) (colors : Fin 5 → I → Bool)
    (weight : Fin 5 → I → Published.KineticPhase → ℝ≥0∞)
    (f : Published.KineticPhase → ℝ≥0∞) (labels : Fin 5 → I) :
    chosenGainChain a
      (thermalKernelFamily r η K α γ q (cycleFive μ) (cycleFive d) (cycleFive colors))
      (cycleFive weight) f 0 5 labels =
      weightedCoreChain r η K α γ q a (cycleFive (fun i => μ i (labels i)))
        (cycleFive (fun i => d i (labels i))) (cycleFive (fun i => colors i (labels i)))
        (cycleFive (fun i => weight i (labels i))) f 0 5 := by
  have h := chosenThermalChain_eq_weighted r η K α γ q a
    (cycleFive μ) (cycleFive d) (cycleFive colors) (cycleFive weight) f (cycleFive labels) 0 5
  have he : (fun j : Fin 5 => cycleFive labels (0+j.val)) = labels := by
    funext j
    simpa only [Nat.zero_add] using cycleFive_apply labels j
  rw [he] at h
  exact h

theorem finiteThermalFive_eq_sum {I : Type*} [Fintype I] (r η K α γ q a : ℝ)
    (μ d : Fin 5 → I → ℝ) (colors : Fin 5 → I → Bool)
    (weight : Fin 5 → I → Published.KineticPhase → ℝ≥0∞)
    (hw : ∀ i j, Measurable (weight i j))
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (z : Published.KineticPhase) :
    finiteGainChain a
      (thermalKernelFamily r η K α γ q (cycleFive μ) (cycleFive d) (cycleFive colors))
      (cycleFive weight) f 0 5 z =
      ∑ labels : Fin 5 → I,
        weightedCoreChain r η K α γ q a (cycleFive (fun i => μ i (labels i)))
          (cycleFive (fun i => d i (labels i))) (cycleFive (fun i => colors i (labels i)))
          (cycleFive (fun i => weight i (labels i))) f 0 5 z := by
  rw [finiteGainChain_eq_sum (weight := cycleFive weight) a _ (fun _ j => hw _ j) hf]
  apply Finset.sum_congr rfl
  intro labels _
  exact congrFun (chosenThermalFive_eq_weighted r η K α γ q a μ d colors weight f labels) z

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Every fixed finite retained physical thermal family has vanishing fifth gain -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem finite_thermal_five_tendsto {I : Type*} [Fintype I]
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a T b Vmax : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → I → Bool) (η : ℝ) (μ : Fin 5 → I → ℝ) (hμ : ∀ i j, 0 < μ i j)
    (μn dn : ℕ → Fin 5 → I → ℝ) (hμn : ∀ n i j, 0 < μn n i j)
    (hdn : ∀ n i j, 0 < dn n i j)
    (hμlim : ∀ i j, Tendsto (fun n => μn n i j) atTop (𝓝 (μ i j)))
    (hdlim : ∀ i j, Tendsto (fun n => dn n i j) atTop (𝓝 0))
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hinit : ∀ n, ‖WithLp.toLp 2 (states n).2.2‖ ≤ Vmax ∧
      b ≤ ‖transverse (WithLp.toLp 2 (states n).2.2)‖)
    (weight : ℕ → Fin 5 → I → Published.KineticPhase → ℝ≥0∞)
    (hwm : ∀ n i j, Measurable (weight n i j)) (hw : ∀ n i j z, weight n i j z ≤ 1)
    (hweight : ∀ n i j z, weight n i j z ≠ 0 →
      z.1.1 ∈ Icc a T ∧ ‖z.2‖ ≤ Vmax ∧ b ≤ ‖transverse z.2‖)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => finiteGainChain a
      (thermalKernelFamily (r n) η K α γ qexp (cycleFive (μn n)) (cycleFive (dn n))
        (cycleFive colors)) (cycleFive (weight n)) (g n) 0 5 (toKinetic (states n)))
      atTop (𝓝 0) := by
  classical
  have htuple (labels : Fin 5 → I) : Tendsto (fun n =>
      weightedCoreChain (r n) η K α γ qexp a (cycleFive (fun i => μn n i (labels i)))
        (cycleFive (fun i => dn n i (labels i))) (cycleFive (fun i => colors i (labels i)))
        (cycleFive (fun i => weight n i (labels i))) (g n) 0 5 (toKinetic (states n)))
      atTop (𝓝 0) := by
    let env : ℕ → PositiveEnvironment := fun n =>
      ⟨((fun i => μn n i (labels i)),(fun i => dn n i (labels i)),states n),
        fun i => hμn n i (labels i)⟩
    have henv : Tendsto env atTop
        (𝓝 (⟨((fun i => μ i (labels i)),0,(t₀,x,v)),fun i => hμ i (labels i)⟩ :
          PositiveEnvironment)) := by
      apply tendsto_subtype_rng.mpr
      exact (tendsto_pi_nhds.mpr (fun i => hμlim i (labels i))).prodMk_nhds
        ((tendsto_pi_nhds.mpr (fun i => hdlim i (labels i))).prodMk_nhds hstates)
    exact actual_weighted_five_tendsto hMityagin hK hα hγ hq ha hb hV
      (fun i => colors i (labels i)) η (fun i => hμ i (labels i)) t₀ x v hv henv r hr
      (fun n i => hdn n i (labels i)) hinit (fun n i => weight n i (labels i))
      (fun n i => hwm n i (labels i)) (fun n i => hw n i (labels i))
      (fun n i => hweight n i (labels i)) hM hg hgM hL
  have hs := tendsto_finsetSum (Finset.univ : Finset (Fin 5 → I)) (fun labels _ => htuple labels)
  simp only [Finset.sum_const_zero] at hs
  apply hs.congr'
  exact Eventually.of_forall (fun n => (finiteThermalFive_eq_sum (r n) η K α γ qexp a
    (μn n) (dn n) colors (weight n) (hwm n) (hg n) (toKinetic (states n))).symm)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
