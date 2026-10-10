import OAI.Probability.RadialTransition.PerturbationMoments

namespace OAI

universe uX

noncomputable section


open Filter MeasureTheory Set

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

section Fock
variable {X : Type uX} [MeasurableSpace X]
variable (F : ∀ (ι : Type) [Fintype ι], (ι → X) → ℝ≥0∞)
variable (heq : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → X),
  F ι (x ∘ e) = F κ x)
include heq

lemma functional_integral_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (μ : κ → Measure X) [∀ i, SigmaFinite (μ i)] :
    (∫⁻ x, F ι x ∂Measure.pi (fun i => μ (e i))) = ∫⁻ x, F κ x ∂Measure.pi μ := by
  have hp := measurePreserving_piCongrLeft μ e
  have hh := MeasurePreserving.lintegral_map_equiv (F κ)
    (MeasurableEquiv.piCongrLeft (fun _ => X) e) hp
  rw [hh]
  apply lintegral_congr
  intro x
  have h := heq ι κ e (MeasurableEquiv.piCongrLeft (fun _ => X) e x)
  simpa [MeasurableEquiv.piCongrLeft, Function.comp_def] using h

lemma functional_sector {ι : Type} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (hF : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] :
    (∫⁻ x : ι → X, F ι x ∂Measure.pi (fun i => if p i then μ else ν)) =
      ∫⁻ x : Subtype p → X, ∫⁻ y : {i // ¬p i} → X,
        F (Subtype p ⊕ {i // ¬p i}) (Sum.elim x y)
          ∂Measure.pi (fun _ => ν) ∂Measure.pi (fun _ => μ) := by
  have hs : ∀ i : ι, SigmaFinite (if p i then μ else ν) := by
    intro i
    split_ifs <;> infer_instance
  let e := Equiv.sumCompl p
  have hh := functional_integral_equiv F heq e (fun i => if p i then μ else ν)
  rw [← hh]
  have hm : (fun i : Subtype p ⊕ {i // ¬p i} => if p (e i) then μ else ν) = Sum.elim (fun _ => μ) (fun _ => ν) := by
    funext i
    cases i with
    | inl i => exact ite_eq_left i.property
    | inr i => exact ite_eq_right i.property
  rw [hm]
  have hs' : ∀ i : Subtype p ⊕ {i // ¬p i}, SigmaFinite (Sum.elim (fun _ => μ) (fun _ => ν) i) := by
    intro i
    cases i
    · change SigmaFinite μ; infer_instance
    · change SigmaFinite ν; infer_instance
  let e' := MeasurableEquiv.sumPiEquivProdPi (fun _ : Subtype p ⊕ {i // ¬p i} => X)
  have hp := measurePreserving_sumPiEquivProdPi_symm (Sum.elim (fun _ : Subtype p => μ) (fun _ : {i // ¬p i} => ν))
  have hh := hp.lintegral_comp (hF _)
  rw [← hh]
  exact lintegral_prod _ ((hF _).comp e'.symm.measurable).aemeasurable

lemma functional_sector_card (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    {N : ℕ} (T : Finset (Fin N)) :
    (∫⁻ x : Fin N → X, F (Fin N) x ∂Measure.pi (fun i => if i ∈ T then μ else ν)) =
      ∫⁻ x : Fin T.card ⊕ Fin (N-T.card) → X, F _ x
        ∂Measure.pi (Sum.elim (fun _ => μ) (fun _ => ν)) := by
  classical
  have hcardA : Fintype.card {i : Fin N // i ∈ T} = T.card := Fintype.card_coe T
  have hcardB : Fintype.card {i : Fin N // i ∉ T} = N - T.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardA]
  let eA := (Fintype.equivFinOfCardEq hcardA).symm
  let eB := (Fintype.equivFinOfCardEq hcardB).symm
  let e := (Equiv.sumCongr eA eB).trans (Equiv.sumCompl (fun i => i ∈ T))
  have hs : ∀ i : Fin N, SigmaFinite (if i ∈ T then μ else ν) := by
    intro i
    split_ifs <;> infer_instance
  have hh := (functional_integral_equiv F heq e (fun i => if i ∈ T then μ else ν)).symm
  have hm : (fun i => if e i ∈ T then μ else ν) = Sum.elim (fun _ : Fin T.card => μ) (fun _ : Fin (N-T.card) => ν) := by
    funext i
    cases i with
    | inl i => exact ite_eq_left (eA i).property
    | inr i => exact ite_eq_right (eB i).property
  rwa [hm] at hh

end Fock

def fockCoeff (z : ℝ) (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (z*n)/n.factorial)

lemma fockCoeff_choose (z : ℝ) {N m : ℕ} (hm : m ≤ N) :
    fockCoeff z N * N.choose m = fockCoeff z m * fockCoeff z (N-m) := by
  have hz : z*(N:ℝ) = z*m + z*(N-m : ℕ) := by rw [Nat.cast_sub hm]; ring
  have hr : Real.exp (z*N)/(N.factorial:ℝ) * (N.choose m:ℝ) =
      (Real.exp (z*m)/m.factorial) * (Real.exp (z*(N-m : ℕ))/(N-m).factorial) := by
    calc
      _ = Real.exp (z*N) * ((N.factorial:ℝ)⁻¹ * (N.choose m:ℝ)) := by ring
      _ = Real.exp (z*N) * ((m.factorial:ℝ)⁻¹ * ((N-m).factorial:ℝ)⁻¹) := by rw [factorial_choose_cancel hm]
      _ = _ := by rw [hz, Real.exp_add]; ring
  have hh := congrArg ENNReal.ofReal hr
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (z*N)/(N.factorial:ℝ)),
    ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (z*m)/(m.factorial:ℝ)),
    ENNReal.ofReal_natCast, fockCoeff] using hh

lemma ennreal_subsets_card (N : ℕ) (f : ℕ → ℝ≥0∞) :
    (∑ T : Finset (Fin N), f T.card) = ∑ m ∈ Finset.range (N+1), (N.choose m:ℝ≥0∞)*f m := by
  have hh := Finset.sum_powerset (Finset.univ : Finset (Fin N)) (fun T => f T.card)
  simpa only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin,
    Finset.sum_powersetCard, nsmul_eq_mul] using hh

lemma ennreal_tsum_triangle (g : ℕ → ℕ → ℝ≥0∞) :
    (∑' N, ∑ m ∈ Finset.range (N+1), g m (N-m)) = ∑' m, ∑' n, g m n := by
  rw [← ENNReal.tsum_prod,
    ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq (fun p : ℕ × ℕ => g p.1 p.2),
    ENNReal.tsum_sigma']
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  change (∑ m ∈ Finset.range (n+1), g m (n-m)) =
    ∑ b : {p : ℕ × ℕ // p ∈ Finset.HasAntidiagonal.antidiagonal n}, g b.1.1 b.1.2
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => g k l) n).symm.trans
    (Finset.sum_finset_coe (fun p : ℕ × ℕ => g p.1 p.2) (Finset.HasAntidiagonal.antidiagonal n)).symm

section FockAdd
variable {X : Type uX} [MeasurableSpace X]
variable (F : ∀ (ι : Type) [Fintype ι], (ι → X) → ℝ≥0∞)
variable (heq : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → X),
  F ι (x ∘ e) = F κ x)

def fockIntegral (μ : Measure X) (z : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, fockCoeff z n * ∫⁻ x : Fin n → X, F _ x ∂Measure.pi (fun _ => μ)

include heq in
lemma fockIntegral_add (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] (z : ℝ) :
    fockIntegral F (μ+ν) z = ∑' m : ℕ, ∑' n : ℕ,
      fockCoeff z m * fockCoeff z n *
        ∫⁻ x : Fin m ⊕ Fin n → X, F _ x ∂Measure.pi (Sum.elim (fun _ => μ) (fun _ => ν)) := by
  classical
  unfold fockIntegral
  calc
    _ = ∑' N : ℕ, ∑ m ∈ Finset.range (N+1),
        fockCoeff z m * fockCoeff z (N-m) *
          ∫⁻ x : Fin m ⊕ Fin (N-m) → X, F _ x ∂Measure.pi (Sum.elim (fun _ => μ) (fun _ => ν)) := by
      apply tsum_congr
      intro N
      rw [measure_pi_add, lintegral_finsetSum_measure]
      simp_rw [functional_sector_card F heq μ ν]
      rw [ennreal_subsets_card N (fun m =>
        ∫⁻ x : Fin m ⊕ Fin (N-m) → X, F _ x ∂Measure.pi (Sum.elim (fun _ => μ) (fun _ => ν))),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [← mul_assoc, fockCoeff_choose z (Nat.le_of_lt_succ (Finset.mem_range.mp hm))]
    _ = _ := ennreal_tsum_triangle (fun m n => fockCoeff z m * fockCoeff z n *
      ∫⁻ x : Fin m ⊕ Fin n → X, F _ x ∂Measure.pi (Sum.elim (fun _ => μ) (fun _ => ν)))

end FockAdd
section MultisetFock
variable {X : Type uX}

def configurationMultiset {ι : Type} [Fintype ι] (x : ι → X) : Multiset X := ∑ i, {x i}

def particleMultiset (x : ParticleState X) : Multiset X := configurationMultiset x.2

lemma configurationMultiset_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → X) : configurationMultiset (x ∘ e) = configurationMultiset x :=
  e.sum_comp (fun i => {x i})

lemma configurationMultiset_sum {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → X) (y : κ → X) :
    configurationMultiset (Sum.elim x y) = configurationMultiset x + configurationMultiset y := by
  exact Fintype.sum_sum_type _

variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (F : Multiset X → ℝ≥0∞)

def ContinuousConfiguration : Prop :=
  ∀ (s : Multiset X) (ι : Type) [Fintype ι], Continuous (fun x : ι → X => F (s+configurationMultiset x))

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma continuous_particleObservable (hF : ContinuousConfiguration F) (s : Multiset X) :
    Continuous (fun x : ParticleState X => F (s+particleMultiset x)) := by
  apply continuous_sigma
  intro n
  exact hF s (Fin n)

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma continuous_particlePairObservable (hF : ContinuousConfiguration F) (s : Multiset X) :
    Continuous (fun p : ParticleState X × ParticleState X => F (s+particleMultiset p.1+particleMultiset p.2)) := by
  apply continuous_particle_prod (f := fun x y => F (s+particleMultiset x+particleMultiset y))
  intro m n
  have hh := (hF s (Fin m ⊕ Fin n)).comp
    (show Continuous (fun p : (Fin m → X) × (Fin n → X) => Sum.elim p.1 p.2) from by
      apply continuous_pi
      intro i
      cases i with
      | inl i => exact (continuous_apply i).comp continuous_fst
      | inr i => exact (continuous_apply i).comp continuous_snd)
  change Continuous (fun p : (Fin m → X) × (Fin n → X) => F (s+configurationMultiset (Sum.elim p.1 p.2))) at hh
  simpa only [configurationMultiset_sum, add_assoc, particleMultiset] using hh

lemma fockIntegral_eq_lintegral (hF : ContinuousConfiguration F) (μ : Measure X) (z : ℝ) (s : Multiset X) :
    fockIntegral (fun _ι _ x => F (s+configurationMultiset x)) μ z =
      ∫⁻ x, F (s+particleMultiset x) ∂particleBase μ z := by
  rw [lintegral_particleBase μ z (continuous_particleObservable F hF s).measurable]
  rfl

lemma particleBase_add_observable (hF : ContinuousConfiguration F)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (z : ℝ) (s : Multiset X) :
    (∫⁻ x, F (s+particleMultiset x) ∂particleBase (μ+ν) z) =
      ∫⁻ x, ∫⁻ y, F (s+particleMultiset x+particleMultiset y) ∂particleBase ν z ∂particleBase μ z := by
  let G (ι : Type) [Fintype ι] (x : ι → X) := F (s+configurationMultiset x)
  have hG : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → X), G ι (x ∘ e) = G κ x := by
    intros
    dsimp [G]
    rw [configurationMultiset_equiv]
  rw [← fockIntegral_eq_lintegral F hF, fockIntegral_add G hG μ ν z]
  have hpair := (continuous_particlePairObservable F hF s).measurable
  rw [lintegral_particleBase μ z hpair.lintegral_prod_right]
  apply tsum_congr
  intro m
  simp only [particleMultiset]
  have hinner (x : Fin m → X) :
      (∫⁻ y : ParticleState X, F (s+configurationMultiset x+configurationMultiset y.2) ∂particleBase ν z) =
      ∑' n : ℕ, fockCoeff z n * ∫⁻ y : Fin n → X, F (s+configurationMultiset x+configurationMultiset y)
        ∂Measure.pi (fun _ => ν) :=
    lintegral_particleBase ν z ((continuous_particleObservable F hF (s+configurationMultiset x)).measurable)
  simp_rw [hinner]
  rw [lintegral_tsum]
  · rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro n
    rw [lintegral_const_mul' _ _ (by exact ENNReal.ofReal_ne_top)]
    rw [← mul_assoc]
    congr 1
    let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => X)
    have hs : ∀ i : Fin m ⊕ Fin n, SigmaFinite (Sum.elim (fun _ => μ) (fun _ => ν) i) := by
      intro i
      cases i
      · change SigmaFinite μ; infer_instance
      · change SigmaFinite ν; infer_instance
    have hp := measurePreserving_sumPiEquivProdPi_symm (Sum.elim (fun _ : Fin m => μ) (fun _ : Fin n => ν))
    rw [← hp.lintegral_comp (hF s (Fin m ⊕ Fin n)).measurable]
    change (∫⁻ p : (Fin m → X) × (Fin n → X), F (s+configurationMultiset (Sum.elim p.1 p.2))
      ∂(Measure.pi (fun _ => μ)).prod (Measure.pi (fun _ => ν))) = _
    have hmeas : Measurable (fun p : (Fin m → X) × (Fin n → X) => F (s+configurationMultiset (Sum.elim p.1 p.2))) :=
      (hF s (Fin m ⊕ Fin n)).measurable.comp e.symm.measurable
    rw [lintegral_prod _ hmeas.aemeasurable]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro y
    dsimp [G]
    rw [configurationMultiset_sum, add_assoc]
  · intro n
    apply Measurable.aemeasurable
    apply Measurable.const_mul
    have hh := (hF s (Fin m ⊕ Fin n)).measurable.comp
      (show Measurable (fun p : (Fin m → X) × (Fin n → X) => Sum.elim p.1 p.2) from by
        apply measurable_pi_iff.mpr
        intro i
        cases i with
        | inl i => exact (measurable_pi_apply i).comp measurable_fst
        | inr i => exact (measurable_pi_apply i).comp measurable_snd)
    change Measurable (fun p : (Fin m → X) × (Fin n → X) => F (s+configurationMultiset (Sum.elim p.1 p.2))) at hh
    simp only [configurationMultiset_sum, ← add_assoc] at hh
    exact hh.lintegral_prod_right

end MultisetFock
end RadialTransition

end

end OAI
