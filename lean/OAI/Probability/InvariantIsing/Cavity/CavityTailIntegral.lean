import OAI.Probability.InvariantIsing.Cavity.CavityTiltedTail
import OAI.Probability.InvariantIsing.Cavity.CavityFullCutoff

namespace OAI

/-! Tail probabilities as measurable disorder averages and as the
one-coordinate marginal of the physical two-replica Gibbs test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical
open Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_random_tilted_tail_integrable {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (s : Ω → Set X) (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1}) :
    Integrable (fun ω => ((ν ω).tilted (fun x => H (ω,x))).real (s ω)) P := by
  classical
  let Z := fun ω => ∫ x, (s ω).indicator (fun _ => (1 : ℝ)) x
    ∂(ν ω).tilted (fun x => H (ω,x))
  have hZ ω : Z ω = ((ν ω).tilted (fun x => H (ω,x))).real (s ω) :=
    integral_indicator_one (hs.preimage measurable_prodMk_left)
  have hm : Measurable Z := measurable_random_tilted_integral hν hH
    (Measurable.ite hs measurable_const measurable_const)
  have hi : Integrable Z P := Integrable.of_bound hm.aestronglyMeasurable 1 (by
    apply ae_of_all
    intro ω
    rw [hZ, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one)
  exact hi.congr (ae_of_all _ hZ)

lemma cavity_random_tilted_tail_antitone {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H R : Ω × X → ℝ) (hH : Measurable H) (hR : Measurable R) :
    Antitone (fun A => ∫ ω, ((ν ω).tilted (fun x => H (ω,x))).real
      {x | A < |R (ω,x)|} ∂P) := by
  intro A B hAB
  have hi A := cavity_random_tilted_tail_integrable P ν hν H hH
    (fun ω => {x | A < |R (ω,x)|}) (measurableSet_lt measurable_const hR.abs)
  apply integral_mono (hi B) (hi A)
  intro ω
  exact measureReal_mono (μ := (ν ω).tilted (fun x => H (ω,x)))
    (fun x hx => lt_of_le_of_lt hAB hx)

lemma cavity_reference_replica_tail {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (he : Integrable (fun x => Real.exp (H x)) ν)
    {r : ℕ} (i : Fin r) (s : Set X) (hs : MeasurableSet s) :
    referenceReplicaMean ν H (fun σ : Fin r → X => if σ i ∈ s then 1 else 0) =
      (ν.tilted H).real s := by
  classical
  let := isProbabilityMeasure_tilted he
  rw [referenceReplicaMean_eq_tilted ν H he]
  change (∫ σ, s.indicator (fun _ => (1 : ℝ)) (σ i)
    ∂Measure.pi (fun _ : Fin r => ν.tilted H)) = _
  exact ((measurePreserving_eval (fun _ : Fin r => ν.tilted H) i).hasLaw.integral_comp
    ((measurable_const.indicator hs).aestronglyMeasurable)).trans (integral_indicator_one hs)

theorem cavity_full_tail_integral {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (s : SpecialOrthogonal N → Set (Spin N × LabeledLeaf depth))
    (hs : MeasurableSet {p : SpecialOrthogonal N × (Spin N × LabeledLeaf depth) |
      p.2 ∈ s p.1}) :
    (∫ p, ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted
      (cavityFullHamiltonian eig I u p)).real (s p.1) ∂μ.prod gaussianCoordinates) =
      cavityFullDisorderTest μ T eig I u
        (fun U σ => if σ 0 ∈ s U then 1 else 0) := by
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  have hi := cavity_random_tilted_tail_integrable (μ.prod gaussianCoordinates)
    (fun _ => ν) measurable_const (Function.uncurry (cavityFullHamiltonian eig I u))
    (measurable_cavityFullHamiltonian eig I u) (fun p => s p.1)
    (hs.preimage (measurable_fst.fst.prodMk measurable_snd))
  change (∫ p, (ν.tilted (fun x => Function.uncurry
      (cavityFullHamiltonian eig I u) (p,x))).real (s p.1) ∂μ.prod gaussianCoordinates) = _
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod (cavity_full_exp_integrable_ae μ T eig I u hu)] with U hU
  apply integral_congr_ae
  filter_upwards [hU] with z hz
  exact (cavity_reference_replica_tail ν (cavityFullHamiltonian eig I u (U,z)) hz
    (0 : Fin 2) (s U) (hs.preimage measurable_prodMk_left)).symm

theorem cavity_full_gibbs_special_tightness {n m d depth : ℕ}
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k + n)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k + n)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (T : ℕ → LabeledTree depth) (eig : (k : ℕ) → Fin (N k + n) → ℝ)
    (g : (k : ℕ) → Fin (N k + n) → Fin m)
    (u : ℕ → ℕ → ℝ) (hu : ∀ k j, |u k j| ≤ 2)
    (B : (k : ℕ) → SpecialOrthogonal (N k + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hmB : ∀ k, Measurable (B k)) (hB : ∀ k U, (B k U).transpose * B k U = 1)
    (good : (k : ℕ) → Set (SpecialOrthogonal (N k + n)))
    (hgood : ∀ k, MeasurableSet (good k))
    (hp : Tendsto (fun k => (μ k).real (good k)) atTop (𝓝 1))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ k U, U ∈ good k → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g k) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L) :
    ∀ ε > 0, ∃ A > 0, ∀ᶠ k in atTop,
      (∫ p, ((labeledSpinReference depth (uniformSpinPrior (N k + n) : Measure (Spin (N k + n)))
        (T k)).tilted (cavityFullHamiltonian (eig k) (cavitySpectralGroup (g k)) (u k) p)).real
        {x | A < ‖cavityFullSpecialCoordinates (g k) (B k p.1) p.1 x.1‖}
        ∂(μ k).prod gaussianCoordinates) < ε := by
  intro ε hε
  obtain ⟨A, hA, ht⟩ := cavity_full_special_tightness N hN μ T eig g u hu B hmB hB
    good hgood hp hL hbound ε hε
  refine ⟨A, hA, ht.mono fun k hk => ?_⟩
  have hmy : Measurable (fun z : SpecialOrthogonal (N k + n) ×
      (Spin (N k + n) × LabeledLeaf depth) =>
      cavityFullSpecialCoordinates (g k) (B k z.1) z.1 z.2.1) := by
    apply measurable_from_prod_countable_left
    intro x
    exact measurable_cavityFullSpecialCoordinates (g k) (B k) (hmB k) x.1
  have he := cavity_full_tail_integral (μ k) (T k) (eig k) (cavitySpectralGroup (g k))
    (u k) (hu k) (fun U => {x | A < ‖cavityFullSpecialCoordinates (g k) (B k U) U x.1‖})
    (measurableSet_lt measurable_const hmy.norm)
  simpa only [he, Set.mem_ofPred_eq] using hk

end InvariantIsing

end

end OAI
