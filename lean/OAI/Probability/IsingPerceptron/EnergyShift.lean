import Mathlib
import OAI.Probability.IsingPerceptron.VarianceOfConditionalCenterBound

namespace OAI

/-! Energy Shift. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma energyRecursion_add_const (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    (hb : ∀ i < n, 0 < b i) (H : I → ℝ) (c : ℝ) :
    energyRecursion n b μ ν (fun x => c+H x) = c+energyRecursion n b μ ν H := by
  induction n generalizing b μ H with
  | zero => exact finiteLogIntegral_add_const ν H c
  | succ n ih =>
    change logMean (b 0) (μ 0 : Measure (I → ℝ))
      (fun a => energyRecursion n (fun i => b (i+1)) (fun i => μ (i+1)) ν
        ((fun x => c+H x)+a)) = c+logMean (b 0) (μ 0 : Measure (I → ℝ))
      (fun a => energyRecursion n (fun i => b (i+1)) (fun i => μ (i+1)) ν (H+a))
    have he (a : I → ℝ) : ((fun x => c+H x)+a) = fun x => c+(H+a) x := by
      ext x; simp only [Pi.add_apply]; ring
    simp_rw [he,ih (fun i => b (i+1)) (fun i => μ (i+1))
      (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega))]
    apply logMean_const_add _ (hb 0 (by omega)).ne'
    exact integrable_exp_of_linearGrowth _ (hμ 0 (by omega))
      ((measurable_energyRecursion n _ _ ν).comp (measurable_const.add measurable_id))
      ((energyRecursion_linearGrowth n _ _ ν (fun i hi => hμ (i+1) (by omega))
        (fun i hi => hb (i+1) (by omega))).add_left H) _

 
def scalarShiftLaw (μ : ProbabilityMeasure (I → ℝ)) (v : ℝ≥0) : ProbabilityMeasure (I → ℝ) :=
  ⟨((μ : Measure (I → ℝ)).prod (gaussianReal 0 v)).map
    (fun p : (I → ℝ) × ℝ => fun x => p.1 x+p.2),
    inferInstance⟩

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma scalarShiftLaw_exponentialNormMoments (μ : ProbabilityMeasure (I → ℝ))
    (hμ : ExponentialNormMoments (μ : Measure (I → ℝ))) (v : ℝ≥0) :
    ExponentialNormMoments (scalarShiftLaw μ v : Measure (I → ℝ)) := by
  intro a
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  have hi := (hμ |a|).mul_prod (gaussianReal_exponentialNormMoments 0 v |a|)
  have hm : Measurable (fun p : (I → ℝ) × ℝ => fun x => p.1 x+p.2) := by fun_prop
  apply hi.mono' ((hm.norm.const_mul a).exp.aestronglyMeasurable)
  apply ae_of_all
  rintro ⟨H,g⟩
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    a*‖fun x => H x+g‖ ≤ |a| *‖fun x => H x+g‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |a| *(‖H‖+‖g‖) := by
      gcongr
      exact (norm_add_le H (fun _ : I => g)).trans (add_le_add le_rfl ((pi_norm_le_iff_of_nonneg (norm_nonneg g)).mpr (fun _ => le_rfl)))
    _ = _ := by rw [Real.norm_eq_abs]; ring

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma logMean_scalarShift (μ : ProbabilityMeasure (I → ℝ)) (v : ℝ≥0)
    (r : ℝ) {F : (I → ℝ) → ℝ} (hFm : Measurable F)
    (hFi : Integrable (fun H => Real.exp (r*F H)) (μ : Measure (I → ℝ)))
    (hFc : ∀ H c, F (fun x => c+H x) = c+F H) (hr : r ≠ 0) :
    logMean r (scalarShiftLaw μ v : Measure (I → ℝ)) F =
      (v:ℝ)*r/2+logMean r (μ : Measure (I → ℝ)) F := by
  change Real.log (∫ p, Real.exp (r*F p) ∂((μ : Measure (I → ℝ)).prod (gaussianReal 0 v)).map
    (fun p : (I → ℝ) × ℝ => fun x => p.1 x+p.2))/r = _
  unfold logMean
  rw [integral_map (by fun_prop) ((hFm.const_mul r).exp).aestronglyMeasurable]
  have he (p : (I → ℝ) × ℝ) : Real.exp (r*F (fun x => p.1 x+p.2)) =
      Real.exp (r*F p.1)*Real.exp (r*p.2) := by
    rw [show (fun x => p.1 x+p.2) = (fun x => p.2+p.1 x) by ext x; ring,hFc]
    rw [mul_add,Real.exp_add,mul_comm]
  simp_rw [he]
  rw [integral_prod_mul (fun H : I → ℝ => Real.exp (r*F H)) (fun g : ℝ => Real.exp (r*g))]
  have hg : (∫ g : ℝ, Real.exp (r*g) ∂gaussianReal 0 v) = Real.exp ((v:ℝ)*r^2/2) := by
    simpa [mgf] using (congrFun (mgf_fun_id_gaussianReal (μ := (0:ℝ)) (v := v)) r)
  rw [hg,Real.log_mul (integral_exp_pos (μ : Measure (I → ℝ)) F (b := r) hFi).ne' (Real.exp_ne_zero _),Real.log_exp]
  field_simp [hr]
  ring

 

theorem energyRecursion_scalarShift (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    (hb : ∀ i < n, 0 < b i) (v : ℕ → ℝ≥0) (H : I → ℝ) :
    energyRecursion n b (fun i => scalarShiftLaw (μ i) (v i)) ν H =
      (∑ i ∈ Finset.range n, b i*(v i:ℝ))/2+energyRecursion n b μ ν H := by
  induction n generalizing b μ v H with
  | zero => simp [energyRecursion,cascadeRecursion]
  | succ n ih =>
    let F : (I → ℝ) → ℝ := fun a => energyRecursion n (fun i => b (i+1))
      (fun i => μ (i+1)) ν (H+a)
    have hFm : Measurable F := (measurable_energyRecursion n _ _ ν).comp
      (measurable_const.add measurable_id)
    have hFg : HasLinearGrowth F := (energyRecursion_linearGrowth n _ _ ν
      (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega))).add_left H
    have hFi : Integrable (fun a => Real.exp (b 0*F a)) (μ 0 : Measure (I → ℝ)) :=
      integrable_exp_of_linearGrowth _ (hμ 0 (by omega)) hFm hFg _
    have hFsi : Integrable (fun a => Real.exp (b 0*F a))
        (scalarShiftLaw (μ 0) (v 0) : Measure (I → ℝ)) :=
      integrable_exp_of_linearGrowth _ (scalarShiftLaw_exponentialNormMoments _ (hμ 0 (by omega)) _)
        hFm hFg _
    have hFc (a : I → ℝ) (c : ℝ) : F (fun x => c+a x) = c+F a := by
      dsimp [F]
      rw [show H+(fun x => c+a x) = (fun x => c+(H+a) x) by ext x; simp [Pi.add_apply]; ring]
      exact energyRecursion_add_const _ _ _ ν (fun i hi => hμ (i+1) (by omega))
        (fun i hi => hb (i+1) (by omega)) _ _
    change logMean (b 0) (scalarShiftLaw (μ 0) (v 0) : Measure (I → ℝ))
      (fun a => energyRecursion n (fun i => b (i+1))
        (fun i => scalarShiftLaw (μ (i+1)) (v (i+1))) ν (H+a)) = _
    simp_rw [ih (fun i => b (i+1)) (fun i => μ (i+1))
      (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega))]
    change logMean (b 0) (scalarShiftLaw (μ 0) (v 0) : Measure (I → ℝ))
      (fun a => (∑ i ∈ Finset.range n, b (i+1)*(v (i+1):ℝ))/2+F a) = _
    rw [logMean_const_add _ (hb 0 (by omega)).ne' hFsi,
      logMean_scalarShift _ _ _ hFm hFi hFc (hb 0 (by omega)).ne']
    change _ = (∑ i ∈ Finset.range (n+1), b i*(v i:ℝ))/2+
      logMean (b 0) (μ 0 : Measure (I → ℝ)) F
    rw [Finset.sum_range_succ']
    ring

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

abbrev EnrichedLabeledData (N n : ℕ) (A : Type*) :=
  EnrichedPoissonRoot N A × (LabeledTree n × (ForestVertex n → Fin (EnrichedRootSize N) → ℝ))

 
def enrichedCoordinateLaw {A : Type*} [MeasurableSpace A] (P : Measure A)
    (r : ℝ≥0) (N n : ℕ) (b : ℕ → ℝ) : Measure (EnrichedLabeledData N n A) :=
  ((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
    (Measure.infinitePi (fun _ : ℕ => P)))).prod
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (enrichedForestCoordinates N n))

instance enrichedCoordinateLaw_probability {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (N n : ℕ) (b : ℕ → ℝ) :
    IsProbabilityMeasure (enrichedCoordinateLaw P r N n b) := by
  unfold enrichedCoordinateLaw
  infer_instance

 

def enrichedCoordinatePressure {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (p : EnrichedLabeledData N n A) : ℝ :=
  (labeledEnergyLog n ν (enrichedPoissonBase n h u φ p.1)
    (p.2.1,enrichedForest N n h u p.2.2) - N*h n/2) / N

 

def enrichedToNoise {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (p : EnrichedLabeledData N n A) : EnrichedPoissonRoot N A × NoiseTree (Spin N → ℝ) n :=
  (p.1,labeledNoiseJoin (Spin N → ℝ) n (p.2.1,enrichedForest N n h u p.2.2))

lemma enrichedToNoise_preserving {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) :
    MeasurePreserving (enrichedToNoise (A := A) n h u) (enrichedCoordinateLaw P r N n b)
      (((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
        (Measure.infinitePi (fun _ : ℕ => P)))).prod
          (noiseCascadeLaw (Spin N → ℝ) n b (fun i => enrichedIncrementLaw N n h u (i+1)))) := by
  have hf : Measurable (fun p : LabeledTree n × (ForestVertex n → Fin (EnrichedRootSize N) → ℝ) =>
      (p.1,enrichedForest N n h u p.2)) :=
    measurable_fst.prodMk ((measurable_enrichedForest N n h u).comp measurable_snd)
  have hp : MeasurePreserving
      (fun p : LabeledTree n × (ForestVertex n → Fin (EnrichedRootSize N) → ℝ) =>
        labeledNoiseJoin (Spin N → ℝ) n (p.1,enrichedForest N n h u p.2))
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (enrichedForestCoordinates N n))
      (noiseCascadeLaw (Spin N → ℝ) n b (fun i => enrichedIncrementLaw N n h u (i+1))) :=
    ⟨(measurable_labeledNoiseJoin (Spin N → ℝ) n).comp hf,
      labeledEnrichedCoordinates_law N n b h u⟩
  exact (MeasurePreserving.id _).prod hp

 

theorem enrichedCoordinatePressure_eq_noise {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (hb : CascadeExponents n b) (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    enrichedCoordinatePressure n h u ν φ =ᵐ[enrichedCoordinateLaw P r N n b]
      (fun p => enrichedPoissonLog n b h u ν φ (enrichedToNoise n h u p) / N) := by
  let Q := (poissonMeasure r).prod
    ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))
  let μ := fun i => enrichedIncrementLaw N n h u (i+1)
  have hpF : MeasurePreserving (enrichedForest N n h u) (enrichedForestCoordinates N n)
      (markForestLaw (Spin N → ℝ) n μ) :=
    ⟨measurable_enrichedForest N n h u,enrichedForest_law N n h u⟩
  have hpT := (MeasurePreserving.id (labeledCascadeLaw n b : Measure (LabeledTree n))).prod hpF
  have hp := (MeasurePreserving.id Q).prod hpT
  have he := labeledEnergyLog_eq_cascade_random Q n b hb μ ν (measurable_enrichedPoissonBase n h u hm)
  have he' : ∀ᵐ p ∂enrichedCoordinateLaw P r N n b,
      labeledEnergyLog n ν (enrichedPoissonBase n h u φ p.1)
        (p.2.1,enrichedForest N n h u p.2.2) =
      cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1)
        (labeledNoiseJoin (Spin N → ℝ) n (p.2.1,enrichedForest N n h u p.2.2)) := by
    apply ae_of_ae_map (p := fun p : EnrichedPoissonRoot N A ×
        (LabeledTree n × MarkForest (Spin N → ℝ) n) =>
      labeledEnergyLog n ν (enrichedPoissonBase n h u φ p.1) p.2 =
        cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1)
          (labeledNoiseJoin (Spin N → ℝ) n p.2)) hp.measurable.aemeasurable
    rw [show enrichedCoordinateLaw P r N n b = Q.prod
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (enrichedForestCoordinates N n)) from rfl,
      hp.map_eq]
    exact he
  filter_upwards [he'] with p he
  unfold enrichedCoordinatePressure enrichedPoissonLog enrichedToNoise
  dsimp only
  rw [he]

 

theorem enrichedCoordinatePressure_field_cap {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N) :
    let Q := enrichedCoordinateLaw P r N n b
    let C := 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
    let X := enrichedCoordinatePressure n h u ν φ
    MemLp X 2 Q ∧ Var[X;Q] ≤ (C+H+4+5*K^2*α)/N := by
  have hv := enriched_field_cap_variance hN n b hb hh h0 hH u hu ν P hm hK hφ r hr
  have hp := enrichedToNoise_preserving P r n b h u
  have he := enrichedCoordinatePressure_eq_noise P r n b h hb u ν hm
  have hL := hv.1.comp_measurePreserving hp
  refine ⟨MemLp.ae_eq he.symm hL, ?_⟩
  have ht := variance_map (X := fun p => enrichedPoissonLog n b h u ν φ p / N)
    (hp.map_eq.symm ▸ hv.1.aemeasurable) hp.measurable.aemeasurable
  rw [hp.map_eq] at ht
  simp only [Function.comp_def] at ht
  rw [variance_congr he, ← ht]
  exact hv.2

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 
def nodeAddress : (n : ℕ) → Option (ForestVertex n) → List ChildLabel
  | _, none => []
  | 0, some v => v.elim
  | n+1, some (m,i,v) => (m,i) :: nodeAddress n v

lemma nodeAddress_injective (n : ℕ) : Function.Injective (nodeAddress n) := by
  induction n with
  | zero =>
    intro v w _
    cases v with
    | none => cases w with
      | none => rfl
      | some w => exact w.elim
    | some v => exact v.elim
  | succ n ih =>
    intro v w h
    cases v with
    | none => cases w with
      | none => rfl
      | some w => simp [nodeAddress] at h
    | some v => cases w with
      | none => simp [nodeAddress] at h
      | some w =>
        rcases v with ⟨m,i,v⟩
        rcases w with ⟨m',i',w⟩
        simp only [nodeAddress,List.cons.injEq,Prod.mk.injEq] at h
        rcases h with ⟨⟨rfl,rfl⟩,h⟩
        rw [ih h]

 
def nodeAt : (n : ℕ) → LabeledLeaf n → Fin (n+1) → Option (ForestVertex n)
  | 0, _, _ => none
  | n+1, γ, i => Fin.cases none (fun j => some (γ.1.1,γ.1.2,nodeAt n γ.2 j)) i

lemma nodeAddress_nodeAt (n : ℕ) (γ : LabeledLeaf n) (i : Fin (n+1)) :
    nodeAddress n (nodeAt n γ i) = (labeledAddress n γ).take i := by
  induction n with
  | zero => simp [nodeAt,nodeAddress,labeledAddress]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [nodeAt,nodeAddress]
    · simp [nodeAt,nodeAddress,labeledAddress,ih]

lemma nodeAddress_length_some (n : ℕ) (v : ForestVertex n) :
    (nodeAddress n (some v)).length = forestVertexDepth n v+1 := by
  induction n with
  | zero => exact v.elim
  | succ n ih =>
    rcases v with ⟨m,i,_ | v⟩
    · simp [nodeAddress,forestVertexDepth]
    · simp only [nodeAddress,List.length_cons,ih,forestVertexDepth,Nat.add_assoc]

lemma nodeAddress_nodeAt_length (n : ℕ) (γ : LabeledLeaf n) (i : Fin (n+1)) :
    (nodeAddress n (nodeAt n γ i)).length = i := by
  rw [nodeAddress_nodeAt,List.length_take,labeledAddress_length]
  exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)

 
def enrichedNodeTag {N n : ℕ} (v : Option (ForestVertex n)) : EnrichedBlock N → ℕ
  | .inl a => Nat.pair 0 (Encodable.encode ((nodeAddress n v).length,nodeAddress n v,a))
  | .inr ⟨j,t⟩ => Nat.pair (j+1) (Encodable.encode ((nodeAddress n v).length,nodeAddress n v,t))

lemma enrichedNodeTag_injective (N n : ℕ) :
    Function.Injective (fun p : Option (ForestVertex n) × EnrichedBlock N => enrichedNodeTag p.1 p.2) := by
  rintro ⟨v,a⟩ ⟨w,b⟩ h
  cases a with
  | inl a => cases b with
    | inl b =>
      have he := Encodable.encode_inj.mp (Nat.pair_eq_pair.mp h).2
      have hv : v = w := nodeAddress_injective n (congrArg (fun p => p.2.1) he)
      have hab : a = b := congrArg (fun p => p.2.2) he
      subst w; subst b; rfl
    | inr b =>
      have h' := (Nat.pair_eq_pair.mp h).1
      omega
  | inr a => cases b with
    | inl b =>
      have h' := (Nat.pair_eq_pair.mp h).1
      omega
    | inr b =>
      rcases a with ⟨j,t⟩
      rcases b with ⟨k,s⟩
      have hj : j = k := Fin.ext (by have h' := (Nat.pair_eq_pair.mp h).1; exact Nat.add_right_cancel h')
      subst k
      have he := Encodable.encode_inj.mp (Nat.pair_eq_pair.mp h).2
      have hv : v = w := nodeAddress_injective n (congrArg (fun p => p.2.1) he)
      have hts : t = s := congrArg (fun p => p.2.2) he
      subst w; subst s; rfl

 

def enrichedGaussianNodes (N n : ℕ) (g : ℕ → ℝ)
    (v : Option (ForestVertex n)) (j : Fin (EnrichedRootSize N)) : ℝ :=
  g (enrichedNodeTag v ((Fintype.equivFin (EnrichedBlock N)).symm j))

lemma measurable_enrichedGaussianNodes (N n : ℕ) :
    Measurable (enrichedGaussianNodes N n) := by
  unfold enrichedGaussianNodes
  fun_prop

theorem enrichedGaussianNodes_law (N n : ℕ) :
    gaussianCoordinates.map (enrichedGaussianNodes N n) =
      Measure.infinitePi (fun _ : Option (ForestVertex n) =>
        Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)) := by
  let t : Option (ForestVertex n) × Fin (EnrichedRootSize N) → ℕ :=
    fun p => enrichedNodeTag p.1 ((Fintype.equivFin (EnrichedBlock N)).symm p.2)
  have ht : Function.Injective t := by
    intro p q h
    have he := @enrichedNodeTag_injective N n
      (p.1,(Fintype.equivFin (EnrichedBlock N)).symm p.2)
      (q.1,(Fintype.equivFin (EnrichedBlock N)).symm q.2) h
    have he' := Prod.mk.inj he
    exact Prod.ext he'.1 ((Fintype.equivFin (EnrichedBlock N)).symm.injective he'.2)
  have hp := gaussian_pullback_measurePreserving t ht
  change gaussianCoordinates.map
    ((MeasurableEquiv.curry (Option (ForestVertex n)) (Fin (EnrichedRootSize N)) ℝ) ∘
      (fun g => fun p => g (t p))) = _
  rw [← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable hp.measurable,hp.map_eq,
    Measure.infinitePi_map_curry (fun (_ : Option (ForestVertex n)) (_ : Fin (EnrichedRootSize N)) => gaussianReal 0 1)]
  simp only [Measure.infinitePi_eq_pi]

 
theorem enrichedGaussianRootForest_law (N n : ℕ) :
    gaussianCoordinates.map (fun g =>
      (enrichedGaussianNodes N n g none, fun v => enrichedGaussianNodes N n g (some v))) =
      (Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
        (enrichedForestCoordinates N n) := by
  change gaussianCoordinates.map
    ((fun q : Option (ForestVertex n) → Fin (EnrichedRootSize N) → ℝ =>
      (q none,fun v => q (some v))) ∘ enrichedGaussianNodes N n) = _
  rw [← Measure.map_map (by fun_prop) (measurable_enrichedGaussianNodes N n),enrichedGaussianNodes_law]
  have he := infinitePi_option_split
    (Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))
    (fun _ : ForestVertex n => Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))
  have hc : (fun i : Option (ForestVertex n) => i.elim
      (Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))
      (fun _ => Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))) =
      (fun _ => Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)) := by
    funext i; cases i <;> rfl
  simpa only [hc,enrichedForestCoordinates] using he

lemma cylinderField_tag (j : ℕ) (a : ℕ →₀ ℝ) (g : ℕ → ℝ) :
    cylinderField (tagCoefficients j a) g = cylinderField a (fun i => g (Nat.pair j i)) := by
  unfold cylinderField tagCoefficients
  rw [Finsupp.sum_mapDomain_index_inj (pair_left_injective j)]

lemma cylinderField_feature {J : Type*} [Fintype J] (t : J → ℕ) (a : J → ℝ) (g : ℕ → ℝ) :
    cylinderField (featureCoefficients t a) g = ∑ j, a j*g (t j) := by
  classical
  rw [featureCoefficients,cylinderField_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact Finsupp.sum_single_index (by simp)

def edgeAt : (n : ℕ) → LabeledLeaf n → Fin n → ForestVertex n
  | 0, _, i => i.elim0
  | n+1, γ, i => (γ.1.1,γ.1.2,nodeAt n γ.2 i)

lemma nodeAt_zero (n : ℕ) (γ : LabeledLeaf n) : nodeAt n γ 0 = none := by
  cases n <;> simp [nodeAt]

lemma nodeAt_succ (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    nodeAt n γ i.succ = some (edgeAt n γ i) := by
  cases n with
  | zero => exact i.elim0
  | succ n => simp [nodeAt,edgeAt]

lemma labeledEnergy_edge_sum {I : Type} (n : ℕ) (g : ForestVertex n → I → ℝ)
    (γ : LabeledLeaf n) (H : I → ℝ) (x : I) :
    labeledEnergy n (markForestOfCoords (I → ℝ) n g) γ H x =
      H x + ∑ i : Fin n, g (edgeAt n γ i) x := by
  induction n generalizing H with
  | zero => simp [labeledEnergy]
  | succ n ih =>
    rw [labeledEnergy,markForestOfCoords,ih,Fin.sum_univ_succ]
    simp only [edgeAt,nodeAt_zero,nodeAt_succ,Pi.add_apply]
    ring

lemma labeledEnergy_node_sum {I : Type} (n : ℕ) (g : Option (ForestVertex n) → I → ℝ)
    (γ : LabeledLeaf n) (H : I → ℝ) (x : I) :
    labeledEnergy n (markForestOfCoords (I → ℝ) n (fun v => g (some v))) γ (H+g none) x =
      H x + ∑ i : Fin (n+1), g (nodeAt n γ i) x := by
  rw [labeledEnergy_edge_sum,Fin.sum_univ_succ]
  simp only [nodeAt_zero,nodeAt_succ,Pi.add_apply]
  ring

lemma enrichedIncrement_nodes (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ)
    (g : ℕ → ℝ) (v : Option (ForestVertex n)) (x : Spin N) :
    enrichedIncrement N n h u i (enrichedGaussianNodes N n g v) x =
      ∑ a : EnrichedBlock N, enrichedLevelCoefficient n h u i x a * g (enrichedNodeTag v a) := by
  unfold enrichedIncrement enrichedCoefficientsFin enrichedGaussianNodes
  exact (Fintype.equivFin (EnrichedBlock N)).symm.sum_comp
    (fun a => enrichedLevelCoefficient n h u i x a * g (enrichedNodeTag v a))

lemma cylinderField_external_nodes {N : ℕ} (n : ℕ) (h : ℕ → ℝ)
    (x : Spin N) (γ : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (tagCoefficients 0 (externalFieldCoefficients n h (x,γ))) g =
      ∑ i : Fin (n+1), ∑ a : Fin N,
        pathAmplitude h i * spinValue (x a) * g (enrichedNodeTag (nodeAt n γ i) (.inl a)) := by
  rw [cylinderField_tag,externalFieldCoefficients,treeFieldCoefficients,cylinderField_feature,
    Fintype.sum_prod_type]
  simp only [enrichedNodeTag]
  simp_rw [nodeAddress_nodeAt_length,nodeAddress_nodeAt]
  simp only [treeFeatureTag]

lemma cylinderField_monomial_nodes {N : ℕ} (n : ℕ) (j : Fin N) (c : ℝ)
    (x : Spin N) (γ : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (tagCoefficients (j+1) (c • monomialCoefficients n (monomialIndex j).1
      (monomialIndex j).2 (x,γ))) g =
      ∑ i : Fin (n+1), ∑ a : Fin (monomialIndex j).1 → Fin N,
        (c * pathAmplitude (monomialPath n (monomialIndex j).2) i *
          tensorFeature (monomialIndex j).1 (spinCoordinate x) a) *
            g (enrichedNodeTag (nodeAt n γ i) (.inr ⟨j,a⟩)) := by
  rw [cylinderField_tag,cylinderField_smul,monomialCoefficients,treeFieldCoefficients,
    cylinderField_feature,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [enrichedNodeTag]
  simp_rw [nodeAddress_nodeAt_length,nodeAddress_nodeAt]
  simp only [treeFeatureTag]
  ring

lemma cylinderField_enriched_nodes {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (x : Spin N) (γ : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (enrichedCoefficients n h u (x,γ)) g =
      ∑ i : Fin (n+1), ∑ a : EnrichedBlock N,
        enrichedLevelCoefficient n h u i x a * g (enrichedNodeTag (nodeAt n γ i) a) := by
  classical
  rw [enrichedCoefficients,cylinderField_finset_sum,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Fin.val_zero,Fin.val_succ,
    cylinderField_external_nodes,cylinderField_monomial_nodes]
  simp only [Fintype.sum_sum_type,Fintype.sum_sigma,enrichedLevelCoefficient,
    Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

 

theorem enrichedEnergy_eq_cylinder {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (g : ℕ → ℝ) (H : Spin N → ℝ) (x : Spin N) (γ : LabeledLeaf n) :
    labeledEnergy n (enrichedForest N n h u
      (fun v => enrichedGaussianNodes N n g (some v))) γ
      (H+enrichedIncrement N n h u 0 (enrichedGaussianNodes N n g none)) x =
      H x + cylinderField (enrichedCoefficients n h u (x,γ)) g := by
  let F : Option (ForestVertex n) → Spin N → ℝ := fun v =>
    enrichedIncrement N n h u (nodeAddress n v).length (enrichedGaussianNodes N n g v)
  have he := labeledEnergy_node_sum n F γ H x
  have hf : (fun v => F (some v)) =
      (fun v => enrichedIncrement N n h u (forestVertexDepth n v+1)
        (enrichedGaussianNodes N n g (some v))) := by
    funext v
    simp only [F,nodeAddress_length_some]
  have h0 : F none = enrichedIncrement N n h u 0 (enrichedGaussianNodes N n g none) := by
    simp only [F,nodeAddress,List.length_nil]
  rw [hf,h0] at he
  rw [cylinderField_enriched_nodes]
  simpa only [F,nodeAddress_nodeAt_length,enrichedIncrement_nodes,enrichedForest] using he

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

private lemma preserving_three_rotate {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (fun p : (A × B) × C => (p.1.1,(p.2,p.1.2)))
      ((μ.prod ν).prod ρ) (μ.prod (ρ.prod ν)) :=
  ((MeasurePreserving.id μ).prod Measure.measurePreserving_swap).comp
    (measurePreserving_prodAssoc μ ν ρ)

private lemma preserving_four_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (τ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ] :
    MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μ.prod ν).prod (ρ.prod τ)) ((μ.prod ρ).prod (ν.prod τ)) := by
  have h1 := (measurePreserving_prodAssoc (μ.prod ν) ρ τ).symm MeasurableEquiv.prodAssoc
  have h2 := ((measurePreserving_prodAssoc μ ρ ν).symm MeasurableEquiv.prodAssoc).comp
    (preserving_three_rotate μ ν ρ)
  exact (measurePreserving_prodAssoc (μ.prod ρ) ν τ).comp
    ((h2.prod (MeasurePreserving.id τ)).comp h1)

abbrev EnrichedCylinderBase (n : ℕ) (A : Type*) := (ℕ × (ℕ → A)) × LabeledTree n
abbrev EnrichedCylinderData (n : ℕ) (A : Type*) := EnrichedCylinderBase n A × (ℕ → ℝ)

def enrichedCylinderBaseLaw {A : Type*} [MeasurableSpace A] (P : Measure A)
    (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ) : Measure (EnrichedCylinderBase n A) :=
  ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => P))).prod (labeledCascadeLaw n b)

def enrichedCylinderLaw {A : Type*} [MeasurableSpace A] (P : Measure A)
    (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ) : Measure (EnrichedCylinderData n A) :=
  (enrichedCylinderBaseLaw P r n b).prod gaussianCoordinates

instance enrichedCylinderBaseLaw_probability {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ) :
    IsProbabilityMeasure (enrichedCylinderBaseLaw P r n b) := by
  unfold enrichedCylinderBaseLaw
  infer_instance

instance enrichedCylinderLaw_probability {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ) :
    IsProbabilityMeasure (enrichedCylinderLaw P r n b) := by
  unfold enrichedCylinderLaw
  infer_instance

def enrichedCylinderToCoordinates (N n : ℕ) {A : Type*}
    (p : EnrichedCylinderData n A) : EnrichedLabeledData N n A :=
  ((p.1.1.1,(enrichedGaussianNodes N n p.2 none,p.1.1.2)),
    (p.1.2,fun v => enrichedGaussianNodes N n p.2 (some v)))

theorem enrichedCylinderToCoordinates_preserving {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (N n : ℕ) (b : ℕ → ℝ) :
    MeasurePreserving (enrichedCylinderToCoordinates (A := A) N n)
      (enrichedCylinderLaw P r n b) (enrichedCoordinateLaw P r N n b) := by
  let μ := poissonMeasure r
  let ν := Measure.infinitePi (fun _ : ℕ => P)
  let ρ := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let γ := Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)
  let τ := enrichedForestCoordinates N n
  have hn : MeasurePreserving (fun g =>
      (enrichedGaussianNodes N n g none,fun v => enrichedGaussianNodes N n g (some v)))
      gaussianCoordinates (γ.prod τ) :=
    ⟨(by unfold enrichedGaussianNodes; fun_prop),enrichedGaussianRootForest_law N n⟩
  have h1 := (MeasurePreserving.id ((μ.prod ν).prod ρ)).prod hn
  have h2 := preserving_four_shuffle (μ.prod ν) ρ γ τ
  have h3 := (preserving_three_rotate μ ν γ).prod (MeasurePreserving.id (ρ.prod τ))
  exact h3.comp (h2.comp h1)

 

def enrichedCylinderPressure {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (p : EnrichedCylinderData n A) : ℝ :=
  (Real.log (∫ s, Real.exp (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i) s.1 +
      cylinderField (enrichedCoefficients n h u s) p.2) ∂labeledSpinReference n ν p.1.2) - N*h n/2)/N

theorem enrichedCylinderPressure_eq_coordinates {N : ℕ} {A : Type*}
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (ν : Measure (Spin N))
    (φ : A → Spin N → ℝ) (p : EnrichedCylinderData n A) :
    enrichedCylinderPressure n h u ν φ p =
      enrichedCoordinatePressure n h u ν φ (enrichedCylinderToCoordinates N n p) := by
  unfold enrichedCylinderPressure enrichedCoordinatePressure enrichedCylinderToCoordinates
    labeledEnergyLog enrichedPoissonBase enrichedBaseEnergy rootPrefix
  dsimp only
  congr 3
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  exact (enrichedEnergy_eq_cylinder n h u p.2
    (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i)) s.1 s.2).symm

 

theorem enrichedCylinderPressure_field_cap {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N) :
    let Q := enrichedCylinderLaw P r n b
    let C := 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
    let X := enrichedCylinderPressure n h u ν φ
    MemLp X 2 Q ∧ Var[X;Q] ≤ (C+H+4+5*K^2*α)/N := by
  have hv := enrichedCoordinatePressure_field_cap hN n b hb hh h0 hH u hu ν P hm hK hφ r hr
  have hp := enrichedCylinderToCoordinates_preserving P r N n b
  have he : enrichedCylinderPressure n h u ν φ =
      (enrichedCoordinatePressure n h u ν φ) ∘ enrichedCylinderToCoordinates N n := by
    funext p
    exact enrichedCylinderPressure_eq_coordinates n h u ν φ p
  have hL := hv.1.comp_measurePreserving hp
  refine ⟨he ▸ hL, ?_⟩
  have ht := variance_map (X := enrichedCoordinatePressure n h u ν φ)
    (hp.map_eq.symm ▸ hv.1.aemeasurable) hp.measurable.aemeasurable
  rw [hp.map_eq] at ht
  rw [he, ← ht]
  exact hv.2

end IsingPerceptron

end

end OAI
