import Mathlib
import OAI.Probability.ThreeStateClauses.Degradation
import OAI.Probability.ThreeStateClauses.RegularLaw
import OAI.Probability.ThreeStateClauses.Projection

namespace OAI

/-! Compact Limits. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

def quadraticGap (z : Message × Message) : ℝ := avg (fun i ↦ (z.1.1 i-z.2.1 i)^2)/2

lemma continuous_quadraticGap : Continuous quadraticGap := by
  unfold quadraticGap
  exact (continuous_avg.comp (continuous_pi (fun i ↦
    ((continuous_coordinate i).comp continuous_fst |>.sub ((continuous_coordinate i).comp continuous_snd)).pow 2))).div_const 2

lemma quadraticGap_nonneg (z : Message × Message) : 0 ≤ quadraticGap z := by
  dsimp [quadraticGap, avg]; positivity

lemma quadraticGap_zero_iff (z : Message × Message) : quadraticGap z = 0 ↔ z.1 = z.2 := by
  constructor
  · intro h
    apply Subtype.ext
    funext i
    have h₀ := sq_nonneg (z.1.1 0-z.2.1 0)
    have h₁ := sq_nonneg (z.1.1 1-z.2.1 1)
    have h₂ := sq_nonneg (z.1.1 2-z.2.1 2)
    dsimp [quadraticGap, avg] at h
    fin_cases i <;> dsimp <;> nlinarith
  · intro h; simp [quadraticGap, h, avg]

lemma quadraticGap_expand (z : Message × Message) :
    quadraticGap z = xMoment z.1-xMoment z.2-
      avg (fun i ↦ (z.1.1 i-z.2.1 i)*(z.2.1 i-1)) := by
  dsimp [quadraticGap, xMoment, momentX, avg, centered]; ring

lemma continuous_centeredProduct (i : Fin 3) :
    Continuous (fun z : Message × Message ↦ (z.1.1 i-z.2.1 i)*(z.2.1 i-1)) :=
  (((continuous_coordinate i).comp continuous_fst).sub ((continuous_coordinate i).comp continuous_snd)).mul
    (((continuous_coordinate i).comp continuous_snd).sub continuous_const)

section Discrete
variable {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

def degradationCoupling (p : Fin 3 → PMF α) (K : α → PMF β) : ProbabilityMeasure (Message × Message) :=
  ⟨((kernelJoint (discreteMarginal p) K).map (fun z ↦
    (discreteMessage p z.1, discreteMessage (fun i ↦ (p i).bind K) z.2))).toMeasure, inferInstance⟩

lemma integral_degradationCoupling (p : Fin 3 → PMF α) (K : α → PMF β)
    {f : Message × Message → ℝ} (hf : Measurable f) :
    (∫ z, f z ∂(degradationCoupling p K).toMeasure) =
      ∫ z, f (discreteMessage p z.1, discreteMessage (fun i ↦ (p i).bind K) z.2)
        ∂(kernelJoint (discreteMarginal p) K).toMeasure := by
  change (∫ z, f z ∂(PMF.map _ _).toMeasure) = _
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  exact integral_map (measurable_of_countable _).aemeasurable hf.aestronglyMeasurable

omit [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma degradationCoupling_fst (p : Fin 3 → PMF α) (K : α → PMF β) :
    (degradationCoupling p K).map Prod.fst = discreteProbability p := by
  apply Subtype.ext
  change Measure.map Prod.fst (PMF.map _ _).toMeasure = Measure.map _ (discreteMarginal p).toMeasure
  rw [PMF.toMeasure_map _ _ measurable_fst, PMF.map_comp]
  change (PMF.map ((discreteMessage p) ∘ Prod.fst) _).toMeasure = _
  rw [← PMF.map_comp, kernelJoint_fst, PMF.toMeasure_map _ _ (measurable_of_countable _)]

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma degradationCoupling_snd (p : Fin 3 → PMF α) (K : α → PMF β) :
    (degradationCoupling p K).map Prod.snd =
      discreteProbability (fun i ↦ (p i).bind K) := by
  apply Subtype.ext
  change Measure.map Prod.snd (PMF.map _ _).toMeasure = Measure.map _ (discreteMarginal _).toMeasure
  rw [PMF.toMeasure_map _ _ measurable_snd, PMF.map_comp]
  change (PMF.map ((discreteMessage (fun i ↦ (p i).bind K)) ∘ Prod.snd) _).toMeasure = _
  rw [← PMF.map_comp, kernelJoint_snd, ← discreteMarginal_bind,
    PMF.toMeasure_map _ _ (measurable_of_countable _)]

lemma degradationCoupling_centered (p : Fin 3 → PMF α) (K : α → PMF β) (i : Fin 3) :
    (∫ z, (z.1.1 i-z.2.1 i)*(z.2.1 i-1) ∂(degradationCoupling p K).toMeasure) = 0 := by
  rw [integral_degradationCoupling _ _ (continuous_centeredProduct i).measurable]
  exact discrete_degradation_centered p K i
    (g := fun b ↦ (discreteMessage (fun j ↦ (p j).bind K) b).1 i-1) (C := 2) (fun b ↦ by
    apply abs_le.mpr
    constructor <;> linarith [coordinate_nonneg (discreteMessage (fun j ↦ (p j).bind K) b) i,
      coordinate_le_three (discreteMessage (fun j ↦ (p j).bind K) b) i])

lemma degradationCoupling_loss (p : Fin 3 → PMF α) (K : α → PMF β) :
    (∫ z, quadraticGap z ∂(degradationCoupling p K).toMeasure) =
      (∫ m, xMoment m ∂(discreteProbability p).toMeasure)-
      ∫ m, xMoment m ∂(discreteProbability (fun i ↦ (p i).bind K)).toMeasure := by
  let C := degradationCoupling p K
  have hx : Integrable (fun z : Message × Message ↦ xMoment z.1) C.toMeasure :=
    compact_integrable (continuous_xMoment.comp continuous_fst)
  have hy : Integrable (fun z : Message × Message ↦ xMoment z.2) C.toMeasure :=
    compact_integrable (continuous_xMoment.comp continuous_snd)
  have hc (i : Fin 3) : Integrable (fun z : Message × Message ↦ (z.1.1 i-z.2.1 i)*(z.2.1 i-1)) C.toMeasure :=
    compact_integrable (continuous_centeredProduct i)
  have hz : (∫ z, avg (fun i ↦ (z.1.1 i-z.2.1 i)*(z.2.1 i-1)) ∂C.toMeasure) = 0 := by
    rw [integral_avg_measure hc]
    simp only [C, degradationCoupling_centered, avg]
    norm_num
  simp_rw [quadraticGap_expand]
  rw [integral_sub (f := fun z : Message × Message ↦ xMoment z.1-xMoment z.2)
    (g := fun z : Message × Message ↦ avg (fun i ↦ (z.1.1 i-z.2.1 i)*(z.2.1 i-1)))
    (hx.sub hy) (integrable_avg hc),
    integral_sub (f := fun z : Message × Message ↦ xMoment z.1)
    (g := fun z : Message × Message ↦ xMoment z.2) hx hy, hz, sub_zero]
  congr 1
  · rw [← degradationCoupling_fst p K]
    exact (integral_map measurable_fst.aemeasurable continuous_xMoment.measurable.aestronglyMeasurable).symm
  · rw [← degradationCoupling_snd p K]
    exact (integral_map measurable_snd.aemeasurable continuous_xMoment.measurable.aestronglyMeasurable).symm

lemma discrete_degradation_mu (p : Fin 3 → PMF α) (K : α → PMF β) :
    (∫ m, xMoment m ∂(discreteProbability (fun i ↦ (p i).bind K)).toMeasure) ≤
      ∫ m, xMoment m ∂(discreteProbability p).toMeasure := by
  have h := MeasureTheory.integral_nonneg (μ := (degradationCoupling p K).toMeasure)
    (f := quadraticGap) quadraticGap_nonneg
  rw [degradationCoupling_loss] at h
  linarith

end Discrete
end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

def vertex (i : Spin) : Message :=
  ⟨fun j ↦ if i = j then 3 else 0, fun j ↦ by dsimp; split_ifs <;> norm_num, by
    fin_cases i <;> norm_num [avg, Fin.ext_iff]⟩

lemma discreteMessage_pure (i : Spin) : discreteMessage (fun j : Spin ↦ PMF.pure j) i = vertex i := by
  apply Subtype.ext
  funext j
  fin_cases i <;> fin_cases j <;> norm_num [discreteMessage, discreteWeight, avg, PMF.pure_apply, vertex, Fin.ext_iff]

lemma vertex_permute (σ : Equiv.Perm Spin) (i : Spin) : permute σ (vertex i) = vertex (σ.symm i) := by
  apply Subtype.ext
  funext j
  change (if i = σ j then (3:ℝ) else 0) = if σ.symm i = j then 3 else 0
  simp only [σ.symm_apply_eq]

lemma pureMarginal : discreteMarginal (fun i : Spin ↦ PMF.pure i) = uniformSpin := PMF.bind_pure _

lemma integral_rootProbability {f : Message → ℝ} (hf : Measurable f) :
    (∫ m, f m ∂(discreteProbability (fun i : Spin ↦ PMF.pure i)).toMeasure) =
      (∑ i : Spin, f (vertex i))/3 := by
  rw [integral_discreteProbability _ hf, pureMarginal, PMF.integral_eq_sum]
  simp only [discreteMessage_pure, smul_eq_mul, uniformSpin_apply, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat]
  rw [← Finset.mul_sum]
  ring

lemma rootProbability_symmetric (σ : Equiv.Perm Spin) :
    MeasurePreserving (permute σ) (discreteProbability (fun i : Spin ↦ PMF.pure i)).toMeasure
      (discreteProbability (fun i : Spin ↦ PMF.pure i)).toMeasure := by
  refine ⟨(continuous_permute σ).measurable, ?_⟩
  have h : (discreteProbability (fun i : Spin ↦ PMF.pure i)).map
      (permute σ) = discreteProbability (fun i : Spin ↦ PMF.pure i) := by
    apply probability_ext_continuous
    intro f hf
    change (∫ m, f m ∂Measure.map (permute σ) _) = _
    rw [integral_map (continuous_permute σ).measurable.aemeasurable hf.measurable.aestronglyMeasurable,
      integral_rootProbability (f := fun m ↦ f (permute σ m)) (hf.comp (continuous_permute σ)).measurable,
      integral_rootProbability hf.measurable]
    simp only [vertex_permute]
    exact congrArg (fun x : ℝ ↦ x/3) (Equiv.sum_comp σ.symm (fun i ↦ f (vertex i)))
  exact congrArg ProbabilityMeasure.toMeasure h

def rootLaw : Law where
  probability := discreteProbability (fun i : Spin ↦ PMF.pure i)
  balanced := discreteProbability_balanced _
  symmetric := rootProbability_symmetric

def regularPosteriorLaw (b : ℕ) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) : ℕ → Law
  | 0 => rootLaw
  | ℓ+1 => finiteLaw (regularPosteriorLaw b hl₀ hl₁ ℓ) hl₀ hl₁ b

lemma regularPosteriorLaw_probability (b : ℕ) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (hlam : Admissible lam) (ℓ : ℕ) :
    (regularPosteriorLaw b hl₀ hl₁ ℓ).probability = discreteProbability (regularLaw b lam hlam ℓ) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    exact (discreteBranchLaw_probability (regularLaw b lam hlam ℓ)
      (regularPosteriorLaw b hl₀ hl₁ ℓ) ih hl₀ hl₁ hlam b).symm

lemma regularPosteriorLaw_antitone (b : ℕ) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (hlam : Admissible lam) : Antitone (fun ℓ ↦ (regularPosteriorLaw b hl₀ hl₁ ℓ).mu) := by
  apply antitone_nat_of_succ_le
  intro ℓ
  unfold Law.mu
  rw [regularPosteriorLaw_probability b hl₀ hl₁ hlam ℓ,
    regularPosteriorLaw_probability b hl₀ hl₁ hlam (ℓ+1)]
  have h := discrete_degradation_mu (regularLaw b lam hlam ℓ) (regularExpansion b lam hlam ℓ)
  simpa only [regularLaw_degrades] using h

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

lemma probability_continuous_integral {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {f : X → ℝ} (hf : Continuous f) :
    Continuous (fun P : ProbabilityMeasure X ↦ ∫ x, f x ∂P.toMeasure) :=
  ProbabilityMeasure.continuous_integral_continuousMap (⟨f, hf⟩ : C(X, ℝ))

section Limits
variable {ι : Type*} {F : Filter ι} [F.NeBot] {Q : ι → Law} {P : ProbabilityMeasure Message}

lemma limit_balanced (hP : Tendsto (fun i ↦ (Q i).probability) F (𝓝 P)) (j : Fin 3) :
    (∫ m, m.1 j ∂P.toMeasure) = 1 := by
  have h := (probability_continuous_integral (continuous_coordinate j)).tendsto P |>.comp hP
  simp only [Function.comp_def, Law.balanced] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

lemma limit_symmetric (hP : Tendsto (fun i ↦ (Q i).probability) F (𝓝 P))
    (σ : Equiv.Perm (Fin 3)) : MeasurePreserving (permute σ) P.toMeasure P.toMeasure := by
  refine ⟨(continuous_permute σ).measurable, ?_⟩
  have hm := (ProbabilityMeasure.continuous_map (continuous_permute σ)).tendsto P |>.comp hP
  have he (i : ι) : (Q i).probability.map (permute σ) =
      (Q i).probability := Subtype.ext ((Q i).symmetric σ).map_eq
  simp only [Function.comp_def, he] at hm
  exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hm hP)

def limitLaw (hP : Tendsto (fun i ↦ (Q i).probability) F (𝓝 P)) : Law where
  probability := P
  balanced := limit_balanced hP
  symmetric := limit_symmetric hP

end Limits

lemma finiteProbability_tendsto {ι : Type*} {F : Filter ι} {Q : ι → Law} {R : Law}
    (hQ : Tendsto (fun i ↦ (Q i).probability) F (𝓝 R.probability))
    {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    Tendsto (fun i ↦ finiteProbability (Q i) hl₀ hl₁ n) F (𝓝 (finiteProbability R hl₀ hl₁ n)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hp : Tendsto (fun i ↦ ProbabilityMeasure.pi (fun _ : Fin n ↦ (Q i).probability)) F
      (𝓝 (ProbabilityMeasure.pi (fun _ : Fin n ↦ R.probability))) :=
    ProbabilityMeasure.continuous_pi.tendsto _ |>.comp (tendsto_pi_nhds.mpr (fun _ ↦ hQ))
  have hfun : Continuous (fun m : Fin n → Message ↦ normalizer (branchEdges lam m)*f (branchOutput hl₀ hl₁ m)) :=
    (continuous_normalizer n lam).mul (f.continuous.comp (continuous_branchOutput hl₀ hl₁ n))
  have h := (probability_continuous_integral hfun).tendsto _ |>.comp hp
  simpa only [Function.comp_def, ProbabilityMeasure.toMeasure_pi,
    integral_finiteProbability _ hl₀ hl₁ n f.continuous.measurable] using h

lemma coupling_diagonal_of_loss_zero (C : ProbabilityMeasure (Message × Message))
    (h : (∫ z, quadraticGap z ∂C.toMeasure) = 0) :
    C.map Prod.fst = C.map Prod.snd := by
  have he := (integral_eq_zero_iff_of_nonneg quadraticGap_nonneg
    (compact_integrable continuous_quadraticGap)).mp h
  apply Subtype.ext
  exact Measure.map_congr (he.mono (fun z hz ↦ (quadraticGap_zero_iff z).mp hz))

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

lemma degrading_finite_fixed_point (Q : ℕ → Law) (C : ℕ → ProbabilityMeasure (Message × Message))
    (hfst : ∀ ℓ, (C ℓ).map Prod.fst = (Q ℓ).probability)
    (hsnd : ∀ ℓ, (C ℓ).map Prod.snd = (Q (ℓ+1)).probability)
    (hloss : ∀ ℓ, (∫ z, quadraticGap z ∂(C ℓ).toMeasure) = (Q ℓ).mu-(Q (ℓ+1)).mu)
    {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ)
    (hrec : ∀ ℓ, (Q (ℓ+1)).probability = finiteProbability (Q ℓ) hl₀ hl₁ n) :
    ∃ R : Law, R.probability = finiteProbability R hl₀ hl₁ n ∧
      Tendsto (fun ℓ ↦ (Q ℓ).mu) atTop (𝓝 R.mu) := by
  have hanti : Antitone (fun ℓ ↦ (Q ℓ).mu) := by
    apply antitone_nat_of_succ_le
    intro ℓ
    have h := MeasureTheory.integral_nonneg (μ := (C ℓ).toMeasure) (f := quadraticGap) quadraticGap_nonneg
    rw [hloss] at h
    linarith
  let a := ⨅ ℓ, (Q ℓ).mu
  have hlim : Tendsto (fun ℓ ↦ (Q ℓ).mu) atTop (𝓝 a) :=
    tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨ℓ,rfl⟩; exact (Q ℓ).mu_nonneg⟩
  have hdiff : Tendsto (fun ℓ ↦ (Q ℓ).mu-(Q (ℓ+1)).mu) atTop (𝓝 0) := by
    simpa using hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))
  obtain ⟨D, hD⟩ := exists_clusterPt_of_compactSpace (Filter.map C atTop)
  let F : Filter ℕ := Filter.comap C (𝓝 D) ⊓ atTop
  have : F.NeBot := neBot_inf_comap_iff_map'.mpr hD
  have hF : F ≤ atTop := inf_le_right
  have hC : Tendsto C F (𝓝 D) := tendsto_comap.mono_left inf_le_left
  have hgap : (∫ z, quadraticGap z ∂D.toMeasure) = 0 := by
    have hg := (probability_continuous_integral continuous_quadraticGap).tendsto D |>.comp hC
    simp only [Function.comp_def, hloss] at hg
    exact tendsto_nhds_unique hg (hdiff.mono_left hF)
  have hdiag := coupling_diagonal_of_loss_zero D hgap
  have hP := (ProbabilityMeasure.continuous_map (continuous_fst : Continuous (Prod.fst : Message × Message → Message))).tendsto D |>.comp hC
  simp only [Function.comp_def, hfst] at hP
  let R : Law := limitLaw hP
  have hS := (ProbabilityMeasure.continuous_map (continuous_snd : Continuous (Prod.snd : Message × Message → Message))).tendsto D |>.comp hC
  simp only [Function.comp_def, hsnd] at hS
  rw [← hdiag] at hS
  have hR : R.probability = finiteProbability R hl₀ hl₁ n := by
    have hr := finiteProbability_tendsto (R := R) hP hl₀ hl₁ n
    simp only [← hrec] at hr
    exact tendsto_nhds_unique hS hr
  have hm : a = R.mu := by
    have hp := (probability_continuous_integral continuous_xMoment).tendsto R.probability |>.comp hP
    exact tendsto_nhds_unique (hlim.mono_left hF) hp
  exact ⟨R, hR, hm ▸ hlim⟩

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

def tvMessage (m : Message) : ℝ := avg (fun i ↦ |m.1 i-1|)/2

lemma continuous_tvMessage : Continuous tvMessage :=
  (continuous_avg.comp (continuous_pi (fun i ↦ ((continuous_coordinate i).sub continuous_const).abs))).div_const 2

lemma tvMessage_nonneg (m : Message) : 0 ≤ tvMessage m := by
  dsimp [tvMessage, avg]; positivity

lemma tvMessage_formula (m : Message) :
    tvMessage m = (∑ i : Spin, |m.1 i/3-(1/3:ℝ)|)/2 := by
  simp only [tvMessage, avg, ← sub_div, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 3), Fin.sum_univ_three]
  ring

lemma tvMessage_sq_bound (m : Message) : tvMessage m^2 ≤ xMoment m/2 := by
  have h₀ := sq_nonneg (|m.1 0-1|-|m.1 1-1|)
  have h₁ := sq_nonneg (|m.1 1-1|-|m.1 2-1|)
  have h₂ := sq_nonneg (|m.1 2-1|-|m.1 0-1|)
  dsimp [tvMessage, xMoment, momentX, centered, avg]
  nlinarith only [h₀,h₁,h₂, sq_abs (m.1 0-1), sq_abs (m.1 1-1), sq_abs (m.1 2-1)]

lemma integral_tvMessage_sq_bound (P : ProbabilityMeasure Message) :
    (∫ m, tvMessage m ∂P.toMeasure)^2 ≤ (∫ m, xMoment m ∂P.toMeasure)/2 := by
  let t := ∫ m, tvMessage m ∂P.toMeasure
  have hi := compact_integrable continuous_tvMessage (μ := P.toMeasure)
  have hi₂ := compact_integrable (continuous_tvMessage.pow 2) (μ := P.toMeasure)
  have h := MeasureTheory.integral_nonneg (μ := P.toMeasure) (f := fun m ↦ (tvMessage m-t)^2)
    (fun m ↦ sq_nonneg (tvMessage m-t))
  have he : (fun m : Message ↦ (tvMessage m-t)^2) = fun m ↦ tvMessage m^2-2*t*tvMessage m+t^2 := by
    funext m; ring
  rw [he, integral_add (f := fun m ↦ tvMessage m^2-2*t*tvMessage m) (g := fun _ ↦ t^2)
    (hi₂.sub (hi.const_mul _)) (integrable_const _),
    integral_sub (f := fun m ↦ tvMessage m^2) (g := fun m ↦ 2*t*tvMessage m) hi₂ (hi.const_mul _),
    integral_const_mul] at h
  simp only [integral_const, measure_univ, Measure.real, ENNReal.toReal_one, smul_eq_mul, one_mul] at h
  have hb := integral_mono (μ := P.toMeasure) hi₂ (compact_integrable (continuous_xMoment.div_const 2)) tvMessage_sq_bound
  rw [integral_div] at hb
  change (∫ m, tvMessage m^2 ∂P.toMeasure) ≤ (∫ m, xMoment m ∂P.toMeasure)/2 at hb
  change 0 ≤ (∫ m, tvMessage m^2 ∂P.toMeasure)-2*t*t+t^2 at h
  change t^2 ≤ _
  nlinarith

lemma main_marginal_eq (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (o : Observation ℓ) :
    marginalWeight lam hlam offspring ℓ o = discreteMarginal (observationLaw lam hlam offspring ℓ) o := by
  simp only [marginalWeight, jointWeight, discreteMarginal, PMF.bind_apply, tsum_fintype, uniformSpin_apply]

lemma main_posterior_eq (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (o : Observation ℓ) (ho : discreteWeight (observationLaw lam hlam offspring ℓ) o ≠ 0) (i : Spin) :
    posterior lam hlam offspring ℓ o i = (discreteMessage (observationLaw lam hlam offspring ℓ) o).1 i/3 := by
  rw [posterior, ENNReal.toReal_div, main_marginal_eq, discreteMarginal_real, jointWeight,
    ENNReal.toReal_mul, discrete_coord ho]
  norm_num
  ring

lemma tvMessage_le_one (m : Message) : tvMessage m ≤ 1 := by
  have hb (i : Spin) : |m.1 i-1| ≤ 2 := abs_le.mpr ⟨by linarith [coordinate_nonneg m i],
    by linarith [coordinate_le_three m i]⟩
  dsimp [tvMessage, avg]
  linarith [hb 0, hb 1, hb 2]

lemma integrable_tv_discrete {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : Spin → PMF α) :
    Integrable (fun o ↦ tvMessage (discreteMessage p o)) (discreteMarginal p).toMeasure := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun a ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (tvMessage_nonneg _)]
    exact tvMessage_le_one _)

lemma advantage_eq_integral (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) (ℓ : ℕ) :
    advantage lam hlam offspring ℓ =
      ∫ m, tvMessage m ∂(discreteProbability (observationLaw lam hlam offspring ℓ)).toMeasure := by
  have hi : Integrable (fun o ↦ tvMessage (discreteMessage (observationLaw lam hlam offspring ℓ) o))
      (discreteMarginal (observationLaw lam hlam offspring ℓ)).toMeasure :=
    integrable_tv_discrete (observationLaw lam hlam offspring ℓ)
  rw [integral_discreteProbability _ continuous_tvMessage.measurable, PMF.integral_eq_tsum _ _ hi]
  unfold advantage
  apply tsum_congr
  intro o
  rw [main_marginal_eq, discreteMarginal_real]
  simp only [smul_eq_mul]
  by_cases ho : discreteWeight (observationLaw lam hlam offspring ℓ) o = 0
  · simp only [ho, zero_mul]
  · simp only [main_posterior_eq lam hlam offspring ℓ o ho, tvMessage_formula]

lemma advantage_nonneg (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) (ℓ : ℕ) :
    0 ≤ advantage lam hlam offspring ℓ := by
  rw [advantage_eq_integral]
  exact MeasureTheory.integral_nonneg tvMessage_nonneg

lemma advantage_sq_bound (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) (ℓ : ℕ) :
    (advantage lam hlam offspring ℓ)^2 ≤
      (∫ m, xMoment m ∂(discreteProbability (observationLaw lam hlam offspring ℓ)).toMeasure)/2 := by
  rw [advantage_eq_integral]
  exact integral_tvMessage_sq_bound _

end ThreeState.TreeClauses.Experiment

end

end OAI
