import Mathlib
import OAI.Probability.ThreeStateClauses.RegularCritical
import OAI.Probability.ThreeStateClauses.ObservedMixtures

namespace OAI

/-! Offspring Laws. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

@[reducible] def OrderedObservation : ℕ → Type
  | 0 => Spin
  | ℓ+1 => Σ n : ℕ, Fin n → OrderedObservation ℓ

instance orderedObservationCountable : (ℓ : ℕ) → Countable (OrderedObservation ℓ)
  | 0 => inferInstanceAs (Countable Spin)
  | ℓ+1 => letI := orderedObservationCountable ℓ
           inferInstanceAs (Countable (Σ n : ℕ, Fin n → OrderedObservation ℓ))

instance orderedObservationMeasurable : (ℓ : ℕ) → MeasurableSpace (OrderedObservation ℓ)
  | 0 => inferInstanceAs (MeasurableSpace Spin)
  | ℓ+1 => letI := orderedObservationMeasurable ℓ
           inferInstanceAs (MeasurableSpace (Σ n : ℕ, Fin n → OrderedObservation ℓ))

instance orderedObservationSingleton : (ℓ : ℕ) → MeasurableSingletonClass (OrderedObservation ℓ)
  | 0 => inferInstanceAs (MeasurableSingletonClass Spin)
  | ℓ+1 => letI := orderedObservationSingleton ℓ
           inferInstanceAs (MeasurableSingletonClass (Σ n : ℕ, Fin n → OrderedObservation ℓ))

def orderedLaw (ρ : PMF ℕ) (lam : ℝ) (hlam : Admissible lam) :
    (ℓ : ℕ) → Spin → PMF (OrderedObservation ℓ)
  | 0, i => PMF.pure i
  | ℓ+1, i => sigmaPMF ρ (fun n ↦ productPMF (fun _ : Fin n ↦
      (channel lam hlam i).bind (orderedLaw ρ lam hlam ℓ)))

def forgetOrdered : (ℓ : ℕ) → OrderedObservation ℓ → Observation ℓ
  | 0, i => i
  | ℓ+1, ⟨_,v⟩ => (List.ofFn (fun j ↦ forgetOrdered ℓ (v j)) : Multiset (Observation ℓ))

lemma orderedLaw_forget (ρ : PMF ℕ) (lam : ℝ) (hlam : Admissible lam) (ℓ : ℕ) (i : Spin) :
    (orderedLaw ρ lam hlam ℓ i).map (forgetOrdered ℓ) = observationLaw lam hlam ρ ℓ i := by
  induction ℓ generalizing i with
  | zero => exact PMF.map_id _
  | succ ℓ ih =>
    rw [orderedLaw, sigmaPMF_map]
    change ρ.bind _ = ρ.bind _
    congr 1
    funext n
    change (productPMF (fun _ : Fin n ↦ (channel lam hlam i).bind (orderedLaw ρ lam hlam ℓ))).map
      ((fun xs : List (Observation ℓ) ↦ (xs : Multiset (Observation ℓ))) ∘
        List.ofFn ∘ (fun v j ↦ forgetOrdered ℓ (v j))) = _
    rw [← PMF.map_comp, ← PMF.map_comp, productPMF_map]
    simp_rw [PMF.map_bind, ih]
    rw [productPMF_list]
    exact (PMF.map_id ((iidList ((channel lam hlam i).bind
      (observationLaw lam hlam ρ ℓ)) n).map (fun xs : List (Observation ℓ) ↦ (xs : Multiset (Observation ℓ))))).symm

def orderedExpansion (ρ : PMF ℕ) (lam : ℝ) (hlam : Admissible lam) :
    (ℓ : ℕ) → OrderedObservation ℓ → PMF (OrderedObservation (ℓ+1))
  | 0, i => sigmaPMF ρ (fun n ↦ productPMF (fun _ : Fin n ↦ channel lam hlam i))
  | ℓ+1, ⟨n,v⟩ => (productPMF (fun j ↦ orderedExpansion ρ lam hlam ℓ (v j))).map (Sigma.mk n)

lemma orderedLaw_degrades (ρ : PMF ℕ) (lam : ℝ) (hlam : Admissible lam) (ℓ : ℕ) (i : Spin) :
    (orderedLaw ρ lam hlam ℓ i).bind (orderedExpansion ρ lam hlam ℓ) =
      orderedLaw ρ lam hlam (ℓ+1) i := by
  induction ℓ generalizing i with
  | zero =>
    change (PMF.pure i).bind _ = sigmaPMF ρ (fun n ↦
      productPMF (fun _ : Fin n ↦ (channel lam hlam i).bind PMF.pure))
    rw [PMF.pure_bind]
    simp only [PMF.bind_pure]
    rfl
  | succ ℓ ih =>
    change (sigmaPMF ρ (fun n ↦ productPMF (fun _ : Fin n ↦
      (channel lam hlam i).bind (orderedLaw ρ lam hlam ℓ)))).bind
      (fun z ↦ (productPMF (fun j ↦ orderedExpansion ρ lam hlam ℓ (z.2 j))).map (Sigma.mk (β := fun n ↦ Fin n → OrderedObservation (ℓ+1)) z.1)) = _
    rw [sigmaPMF_bind_components ρ _ (fun n (v : Fin n → OrderedObservation ℓ) ↦
      productPMF (fun j ↦ orderedExpansion ρ lam hlam ℓ (v j)))]
    simp only [productPMF_bind, PMF.bind_bind]
    simp_rw [ih]
    rfl

def offspringPosteriorLaw (ρ : PMF ℕ) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) : ℕ → Law
  | 0 => rootLaw
  | ℓ+1 => offspringLaw ρ (offspringPosteriorLaw ρ hl₀ hl₁ ℓ) hl₀ hl₁

lemma offspringPosteriorLaw_probability (ρ : PMF ℕ) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (hlam : Admissible lam) (ℓ : ℕ) :
    (offspringPosteriorLaw ρ hl₀ hl₁ ℓ).probability = discreteProbability (orderedLaw ρ lam hlam ℓ) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    change mixtureProbability ρ (fun n ↦ finiteProbability (offspringPosteriorLaw ρ hl₀ hl₁ ℓ) hl₀ hl₁ n) =
      discreteProbability (fun i ↦ sigmaPMF ρ (fun n ↦ discreteBranchLaw (orderedLaw ρ lam hlam ℓ) lam hlam n i))
    rw [discreteSigma_probability]
    congr 1
    funext n
    exact (discreteBranchLaw_probability _ _ ih hl₀ hl₁ hlam n).symm

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

lemma sigmaPMF_map_components {α β : ℕ → Type*} (ρ : PMF ℕ) (p : ∀ n, PMF (α n))
    (f : ∀ n, α n → β n) :
    (sigmaPMF ρ p).map (fun z ↦ ⟨z.1,f z.1 z.2⟩) = sigmaPMF ρ (fun n ↦ (p n).map (f n)) := by
  rw [sigmaPMF_map, sigmaPMF_eq_bind]
  congr 1
  funext n
  rw [PMF.map_comp]
  rfl

def relabelOrdered (σ : Equiv.Perm Spin) : (ℓ : ℕ) → OrderedObservation ℓ → OrderedObservation ℓ
  | 0, i => σ i
  | ℓ+1, ⟨n,v⟩ => ⟨n,fun j ↦ relabelOrdered σ ℓ (v j)⟩

lemma orderedLaw_permute (ρ : PMF ℕ) (lam : ℝ) (hlam : Admissible lam) (σ : Equiv.Perm Spin)
    (ℓ : ℕ) (i : Spin) :
    (orderedLaw ρ lam hlam ℓ i).map (relabelOrdered σ ℓ) = orderedLaw ρ lam hlam ℓ (σ i) := by
  induction ℓ generalizing i with
  | zero => exact PMF.pure_bind _ _
  | succ ℓ ih =>
    change (sigmaPMF ρ (fun n ↦ productPMF (fun _ : Fin n ↦
      (channel lam hlam i).bind (orderedLaw ρ lam hlam ℓ)))).map
      (fun z ↦ Sigma.mk (β := fun n ↦ Fin n → OrderedObservation ℓ) z.1
        (fun j ↦ relabelOrdered σ ℓ (z.2 j))) = _
    rw [sigmaPMF_map_components ρ _ (fun n (v : Fin n → OrderedObservation ℓ) j ↦ relabelOrdered σ ℓ (v j))]
    simp_rw [productPMF_map, PMF.map_bind, ih]
    have he : (channel lam hlam i).bind (fun j ↦ orderedLaw ρ lam hlam ℓ (σ j)) =
        (channel lam hlam (σ i)).bind (orderedLaw ρ lam hlam ℓ) := by
      rw [← channel_permute hlam σ i, PMF.bind_map]
      rfl
    simp_rw [he]
    rfl

def orderedNoise (c : ℝ) (hc : Admissible c) :
    (ℓ : ℕ) → OrderedObservation ℓ → PMF (OrderedObservation ℓ)
  | 0, i => PMF.pure i
  | ℓ+1, ⟨n,v⟩ => (productPMF (fun j ↦
      (channel c hc 0).bind (fun s ↦ (orderedNoise c hc ℓ (v j)).map
        (relabelOrdered (Equiv.addRight s) ℓ)))).map (Sigma.mk n)

lemma orderedLaw_noise (ρ : PMF ℕ) (lam c : ℝ) (hlam : Admissible lam) (hc : Admissible c)
    (hprod : Admissible (lam*c)) (ℓ : ℕ) (i : Spin) :
    (orderedLaw ρ lam hlam ℓ i).bind (orderedNoise c hc ℓ) = orderedLaw ρ (lam*c) hprod ℓ i := by
  induction ℓ generalizing i with
  | zero => exact PMF.pure_bind _ _
  | succ ℓ ih =>
    change (sigmaPMF ρ (fun n ↦ productPMF (fun _ : Fin n ↦
      (channel lam hlam i).bind (orderedLaw ρ lam hlam ℓ)))).bind
      (fun z ↦ (productPMF (fun j ↦ (channel c hc 0).bind (fun s ↦
        (orderedNoise c hc ℓ (z.2 j)).map (relabelOrdered (Equiv.addRight s) ℓ)) )).map (Sigma.mk (β := fun n ↦ Fin n → OrderedObservation ℓ) z.1)) = _
    rw [sigmaPMF_bind_components ρ _ (fun n (v : Fin n → OrderedObservation ℓ) ↦
      productPMF (fun j ↦ (channel c hc 0).bind (fun s ↦
        (orderedNoise c hc ℓ (v j)).map (relabelOrdered (Equiv.addRight s) ℓ))))]
    change sigmaPMF ρ _ = sigmaPMF ρ _
    congr 1
    funext n
    rw [productPMF_bind (fun _ : Fin n ↦ (channel lam hlam i).bind (orderedLaw ρ lam hlam ℓ))
      (fun _ a ↦ (channel c hc 0).bind (fun s ↦
        (orderedNoise c hc ℓ a).map (relabelOrdered (Equiv.addRight s) ℓ)))]
    congr 1
    funext j
    rw [PMF.bind_bind]
    have he (k : Spin) : (orderedLaw ρ lam hlam ℓ k).bind (fun a ↦ (channel c hc 0).bind
        (fun s ↦ (orderedNoise c hc ℓ a).map (relabelOrdered (Equiv.addRight s) ℓ))) =
        (channel c hc k).bind (orderedLaw ρ (lam*c) hprod ℓ) := by
      rw [PMF.bind_comm]
      simp_rw [← PMF.map_bind, ih, orderedLaw_permute]
      change (channel c hc 0).bind (fun s ↦ orderedLaw ρ (lam*c) hprod ℓ (k+s)) = _
      have hm := channel_permute hc (Equiv.addLeft k) 0
      simp only [Equiv.coe_addLeft, add_zero] at hm
      rw [← hm, PMF.bind_map]
      rfl
    simp_rw [he, ← PMF.bind_bind, channel_compose hlam hc hprod]

lemma ordered_channel_mu_le (ρ : PMF ℕ) (lam c : ℝ) (hlam : Admissible lam) (hc : Admissible c)
    (hprod : Admissible (lam*c)) (ℓ : ℕ) :
    (∫ m, xMoment m ∂(discreteProbability (orderedLaw ρ (lam*c) hprod ℓ)).toMeasure) ≤
      ∫ m, xMoment m ∂(discreteProbability (orderedLaw ρ lam hlam ℓ)).toMeasure := by
  have h := discrete_degradation_mu (orderedLaw ρ lam hlam ℓ) (orderedNoise c hc ℓ)
  change (∫ m, xMoment m ∂(discreteProbability (fun i ↦
    (orderedLaw ρ lam hlam ℓ i).bind (orderedNoise c hc ℓ))).toMeasure) ≤ _ at h
  simpa only [orderedLaw_noise ρ lam c hlam hc hprod] using h

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

lemma degrading_offspring_fixed_point (Q : ℕ → Law) (C : ℕ → ProbabilityMeasure (Message × Message))
    (hfst : ∀ ℓ, (C ℓ).map Prod.fst = (Q ℓ).probability)
    (hsnd : ∀ ℓ, (C ℓ).map Prod.snd = (Q (ℓ+1)).probability)
    (hloss : ∀ ℓ, (∫ z, quadraticGap z ∂(C ℓ).toMeasure) = (Q ℓ).mu-(Q (ℓ+1)).mu)
    {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (ρ : PMF ℕ)
    (hrec : ∀ ℓ, (Q (ℓ+1)).probability = (offspringLaw ρ (Q ℓ) hl₀ hl₁).probability) :
    ∃ R : Law, R.probability = (offspringLaw ρ R hl₀ hl₁).probability ∧
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
  have hR : R.probability = (offspringLaw ρ R hl₀ hl₁).probability := by
    have hr := offspringLaw_tendsto (R := R) ρ hl₀ hl₁ hP
    simp only [← hrec] at hr
    exact tendsto_nhds_unique hS hr
  have hm : a = R.mu := by
    have hp := (probability_continuous_integral continuous_xMoment).tendsto R.probability |>.comp hP
    exact tendsto_nhds_unique (hlim.mono_left hF) hp
  exact ⟨R, hR, hm ▸ hlim⟩

end ThreeState.TreeClauses.Experiment

end

end OAI
