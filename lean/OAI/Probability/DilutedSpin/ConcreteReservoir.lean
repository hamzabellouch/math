import OAI.Probability.DilutedSpin.CompoundSuperposition
import OAI.Probability.DilutedSpin.FullSelectedRegularity
import OAI.Probability.DilutedSpin.ParameterRate

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot
open scoped NNReal BigOperators Topology

abbrev Site (N : ℕ) := Fin (max N 1)
instance siteNeZero (N : ℕ) : NeZero (max N 1) := ⟨by omega⟩

/-- N=0 is an irrelevant harmless extension; for every positive N this reads
exactly the spin at the uniformly sampled original site. -/
def readSpin {N : ℕ} (σ : Fin N → Spin) (i : Site N) : Spin :=
  if h : i.val < N then σ ⟨i.val,h⟩ else false

lemma readSpin_eq {N : ℕ} (hN : 0 < N) (σ : Fin N → Spin) (i : Site N) :
    readSpin σ i = σ ⟨i.val,by have := i.isLt; simp only [max_eq_left (Nat.succ_le_iff.mpr hN)] at this; exact this⟩ := by
  unfold readSpin
  split_ifs with h
  · rfl
  · have := i.isLt
    simp only [max_eq_left (Nat.succ_le_iff.mpr hN)] at this
    exact (h this).elim

noncomputable def siteLaw (N : ℕ) : Measure (Site N) := (PMF.uniformOfFintype (Site N)).toMeasure
instance siteLaw_probability (N : ℕ) : IsProbabilityMeasure (siteLaw N) := by unfold siteLaw; infer_instance

abbrev Bond (p N : ℕ) := InteractionSample p × (Fin p → Site N)
noncomputable def bondLaw {p : ℕ} (M : Model p) (N : ℕ) : Measure (Bond p N) :=
  M.disorder.toMeasure.prod (PMF.uniformOfFintype (Fin p → Site N)).toMeasure
instance bondLaw_probability {p : ℕ} (M : Model p) (N : ℕ) : IsProbabilityMeasure (bondLaw M N) := by
  unfold bondLaw; infer_instance

noncomputable def boundedPotential {p N : ℕ} (C : ℝ) (z : Bond p N) (σ : Fin N → Spin) : ℝ :=
  clipReal C (z.1.1 (fun l => readSpin σ (z.2 l)))

lemma boundedPotential_bound {p N : ℕ} {C : ℝ} (hC : 0 ≤ C) (z : Bond p N) (σ) :
    |boundedPotential C z σ| ≤ C := clipReal_bound hC _

lemma measurable_boundedPotential {p N : ℕ} (C : ℝ) (σ : Fin N → Spin) :
    Measurable (fun z : Bond p N => boundedPotential C z σ) := by
  apply (measurable_clipReal C).comp
  apply measurable_from_prod_countable_left
  intro indices
  exact (measurable_pi_apply (fun l => readSpin σ (indices l))).comp measurable_fst

variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

noncomputable def markLaw (N : ℕ) : Measure ((K×ℕ)×Site N) := ν.prod (siteLaw N)
instance markLaw_probability (N : ℕ) : IsProbabilityMeasure (markLaw ν N) := by unfold markLaw; infer_instance

noncomputable def siteObservable
    (D : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ) (N : ℕ)
    (i : (K×ℕ)×Site N) (x : FinitePath (Fin N → Spin) (L+1)) (y : FinitePath (A i.1.1) (L+1)) : ℝ :=
  D i.1.1 (readSpin (KernelTower.terminalState L x) i.2) y

/-- Literal full-root globally centered score for the physical iid-uniform
Poisson reservoir, with bounded representatives equal to the original bounded
physical variables almost surely. Every old dictionary term remains present. -/
noncomputable def scoreError (M : Model p) (C H : ℝ) (j : K×ℕ) (N : ℕ) (u : K×ℕ → ℝ) : ℝ :=
  normalizedParameterError (bondLaw M) (markLaw ν) M.field.toMeasure (fun N => M.alpha*N)
    (fun _ => boundedPotential C) (clipReal H) (fun _ i => Q i.1.1) m (fun _ => Prod.fst)
    (fun i => probeLow i.2) (fun i => probeHigh i.2) (fun i => extractionProbe i.2)
    (fun i => ν.real {i}) (siteObservable D) (siteObservable E) j N u

omit [Countable K] [MeasurableSingletonClass K] [IsProbabilityMeasure ν] in
lemma scoreError_nonneg (M : Model p) (C H : ℝ) (hc : ∀ j, 0 < ν.real {j})
    (j : K×ℕ) (N : ℕ) (u : K×ℕ → ℝ) : 0 ≤ scoreError ν Q m D E M C H j N u :=
  normalizedParameterError_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc j N u

/-- Concentration for these concrete model laws (not an assumed concentration
interface) under the manuscript's bounded-stage hypotheses. -/
theorem scoreError_tendsto (M : Model p) {C H c : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hc : 0 < c)
    (hm : ∀ l, c ≤ m l) (hw : ∀ j, 0 < ν.real {j})
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1) (j : K×ℕ) :
    Filter.Tendsto (fun N => ∫ u, scoreError ν Q m D E M C H j N u
      ∂Measure.infinitePi (fun i : K×ℕ => intervalParameterLaw (probeLow i.2) (probeHigh i.2)))
      Filter.atTop (𝓝 0) := by
  apply normalizedParameterError_tendsto _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun N σ => measurable_boundedPotential C σ) (measurable_clipReal H)
    hC hc (NNReal.coe_nonneg M.alpha)
    (fun N => by simp only [NNReal.coe_mul,NNReal.coe_natCast]; rfl)
    (fun N => boundedPotential_bound hC) (clipReal_bound hH) hm
    (fun i => probeLow_lt_high i.2) (fun i => by have := probeLow_pos i.2; linarith)
    (fun i => probeHigh_lt_quarter i.2) (fun i => extractionProbe_abs_le_quarter i.2) hw
    (fun N i x y => hD _ _ _) (fun N i x y => hE _ _ _) j

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
