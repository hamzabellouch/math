import Mathlib
import OAI.Probability.ThreeStateClauses.CompactLimits
import OAI.Probability.ThreeStateClauses.PositiveFixed

namespace OAI

/-! Regular Critical. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

lemma regular_positive_critical_mu (b : ℕ) (hb : 2 ≤ b) {lam : ℝ}
    (hl₀ : 0 < lam) (hl₁ : lam < 1) (hlam : Admissible lam) (hcrit : (b:ℝ)*lam^2 = 1) :
    Tendsto (fun ℓ ↦ (regularPosteriorLaw b hl₀.le hl₁ ℓ).mu) atTop (𝓝 0) := by
  let Q := regularPosteriorLaw b hl₀.le hl₁
  let C := fun ℓ ↦ degradationCoupling (regularLaw b lam hlam ℓ) (regularExpansion b lam hlam ℓ)
  have hf (ℓ : ℕ) : (C ℓ).map Prod.fst = (Q ℓ).probability := by
    rw [degradationCoupling_fst, regularPosteriorLaw_probability b hl₀.le hl₁ hlam ℓ]
  have hs (ℓ : ℕ) : (C ℓ).map Prod.snd = (Q (ℓ+1)).probability := by
    rw [degradationCoupling_snd]
    simp only [regularLaw_degrades]
    exact (regularPosteriorLaw_probability b hl₀.le hl₁ hlam (ℓ+1)).symm
  have hl (ℓ : ℕ) : (∫ z, quadraticGap z ∂(C ℓ).toMeasure) = (Q ℓ).mu-(Q (ℓ+1)).mu := by
    rw [degradationCoupling_loss]
    simp only [regularLaw_degrades]
    simp only [Q, Law.mu, regularPosteriorLaw_probability b hl₀.le hl₁ hlam]
  obtain ⟨R,hR,hlim⟩ := degrading_finite_fixed_point Q C hf hs hl hl₀.le hl₁ b (fun _ ↦ rfl)
  rw [regular_fixed_mu_zero R hl₀ hl₁ b hb hcrit hR] at hlim
  exact hlim

lemma regular_advantage_sq_bound (b : ℕ) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (hlam : Admissible lam) (ℓ : ℕ) :
    (advantage lam hlam (PMF.pure b) ℓ)^2 ≤ (regularPosteriorLaw b hl₀ hl₁ ℓ).mu/2 := by
  have h := discrete_degradation_mu (regularLaw b lam hlam ℓ) (fun v ↦ PMF.pure (forgetRegular b ℓ v))
  change (∫ m, xMoment m ∂(discreteProbability (fun i ↦ (regularLaw b lam hlam ℓ i).map (forgetRegular b ℓ))).toMeasure) ≤ _ at h
  simp only [regularLaw_forget] at h
  have ha := advantage_sq_bound lam hlam (PMF.pure b) ℓ
  unfold Law.mu
  rw [regularPosteriorLaw_probability b hl₀ hl₁ hlam ℓ]
  linarith

theorem regular_positive_critical_nonreconstruction (b : ℕ) (hb : 2 ≤ b)
    (lam : ℝ) (hlam : Admissible lam) (hl₀ : 0 < lam) (hcrit : (b:ℝ)*lam^2 = 1) :
    Tendsto (advantage lam hlam (PMF.pure b)) atTop (𝓝 0) := by
  have hb' : (2:ℝ) ≤ b := by exact_mod_cast hb
  have hl₁ : lam < 1 := by
    have h := mul_le_mul_of_nonneg_right hb' (sq_nonneg lam)
    nlinarith
  have hm := regular_positive_critical_mu b hb hl₀ hl₁ hlam hcrit
  have hu : Tendsto (fun ℓ ↦ Real.sqrt (regularPosteriorLaw b hl₀.le hl₁ ℓ).mu) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hm
  apply squeeze_zero (fun ℓ ↦ advantage_nonneg lam hlam (PMF.pure b) ℓ) _ hu
  intro ℓ
  apply (sq_le_sq₀ (advantage_nonneg lam hlam (PMF.pure b) ℓ) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (regularPosteriorLaw b hl₀.le hl₁ ℓ).mu_nonneg]
  have h := regular_advantage_sq_bound b hl₀.le hl₁ hlam ℓ
  linarith [(regularPosteriorLaw b hl₀.le hl₁ ℓ).mu_nonneg]

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

lemma channelWeight_alt (lam : ℝ) (i j : Spin) :
    channelWeight lam i j = lam*(if i = j then 1 else 0)+(1-lam)/3 := by
  unfold channelWeight
  split_ifs <;> ring

lemma channelWeight_compose (lam c : ℝ) (i j : Spin) :
    (∑ k : Spin, channelWeight lam i k*channelWeight c k j) = channelWeight (lam*c) i j := by
  classical
  simp only [channelWeight_alt, add_mul, mul_add, Finset.sum_add_distrib,
    ← Finset.mul_sum, mul_assoc]
  by_cases h : i = j
  · subst j
    simp
    ring
  · simp [h]
    ring

lemma channel_compose {lam c : ℝ} (hlam : Admissible lam) (hc : Admissible c)
    (hprod : Admissible (lam*c)) (i : Spin) :
    (channel lam hlam i).bind (channel c hc) = channel (lam*c) hprod i := by
  apply PMF.ext
  intro j
  apply (ENNReal.toReal_eq_toReal_iff' ((channel lam hlam i).bind (channel c hc) |>.apply_ne_top j)
    ((channel (lam*c) hprod i).apply_ne_top j)).mp
  rw [PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum (fun k _ ↦ ENNReal.mul_ne_top ((channel lam hlam i).apply_ne_top k)
      ((channel c hc k).apply_ne_top j))]
  simp only [ENNReal.toReal_mul, channel_real]
  exact channelWeight_compose lam c i j

lemma channel_permute {lam : ℝ} (hlam : Admissible lam) (σ : Equiv.Perm Spin) (i : Spin) :
    (channel lam hlam i).map σ = channel lam hlam (σ i) := by
  classical
  apply PMF.ext
  intro j
  rw [PMF.map_apply, tsum_eq_single (σ.symm j)]
  · simp only [σ.apply_symm_apply, ↓reduceIte]
    change ENNReal.ofReal (channelWeight lam i (σ.symm j)) =
      ENNReal.ofReal (channelWeight lam (σ i) j)
    congr 1
    unfold channelWeight
    simp only [Equiv.eq_symm_apply]
  · intro a ha
    have hne : j ≠ σ a := by
      intro h
      exact ha (σ.injective (h.symm.trans (σ.apply_symm_apply j).symm))
    simp only [hne, ↓reduceIte]

def relabelRegular (b : ℕ) (σ : Equiv.Perm Spin) : (ℓ : ℕ) → RegularObservation b ℓ → RegularObservation b ℓ
  | 0, i => σ i
  | ℓ+1, v => fun j ↦ relabelRegular b σ ℓ (v j)

lemma regularLaw_permute (b : ℕ) (lam : ℝ) (hlam : Admissible lam) (σ : Equiv.Perm Spin)
    (ℓ : ℕ) (i : Spin) :
    (regularLaw b lam hlam ℓ i).map (relabelRegular b σ ℓ) = regularLaw b lam hlam ℓ (σ i) := by
  induction ℓ generalizing i with
  | zero => exact PMF.pure_bind _ _
  | succ ℓ ih =>
    change (productPMF (fun _ : Fin b ↦ (channel lam hlam i).bind (regularLaw b lam hlam ℓ))).map
      (fun v j ↦ relabelRegular b σ ℓ (v j)) = _
    rw [productPMF_map]
    simp_rw [PMF.map_bind, ih]
    have he : (channel lam hlam i).bind (fun j ↦ regularLaw b lam hlam ℓ (σ j)) =
        (channel lam hlam (σ i)).bind (regularLaw b lam hlam ℓ) := by
      rw [← channel_permute hlam σ i, PMF.bind_map]
      rfl
    simp_rw [he]
    rfl

def channelNoise (b : ℕ) (c : ℝ) (hc : Admissible c) :
    (ℓ : ℕ) → RegularObservation b ℓ → PMF (RegularObservation b ℓ)
  | 0, i => PMF.pure i
  | ℓ+1, v => productPMF (fun j ↦
      (channel c hc 0).bind (fun s ↦ (channelNoise b c hc ℓ (v j)).map
        (relabelRegular b (Equiv.addRight s) ℓ)))

lemma regularLaw_noise (b : ℕ) (lam c : ℝ) (hlam : Admissible lam) (hc : Admissible c)
    (hprod : Admissible (lam*c)) (ℓ : ℕ) (i : Spin) :
    (regularLaw b lam hlam ℓ i).bind (channelNoise b c hc ℓ) =
      regularLaw b (lam*c) hprod ℓ i := by
  induction ℓ generalizing i with
  | zero => exact PMF.pure_bind _ _
  | succ ℓ ih =>
    change (productPMF (fun _ : Fin b ↦ (channel lam hlam i).bind (regularLaw b lam hlam ℓ))).bind
      (fun v ↦ productPMF (fun j ↦ (channel c hc 0).bind (fun s ↦
        (channelNoise b c hc ℓ (v j)).map (relabelRegular b (Equiv.addRight s) ℓ)))) =
      productPMF (fun _ : Fin b ↦ (channel (lam*c) hprod i).bind (regularLaw b (lam*c) hprod ℓ))
    rw [productPMF_bind (fun _ : Fin b ↦ (channel lam hlam i).bind (regularLaw b lam hlam ℓ))
      (fun _ a ↦ (channel c hc 0).bind (fun s ↦
        (channelNoise b c hc ℓ a).map (relabelRegular b (Equiv.addRight s) ℓ)))]
    congr 1
    funext j
    rw [PMF.bind_bind]
    have he (k : Spin) : (regularLaw b lam hlam ℓ k).bind (fun a ↦ (channel c hc 0).bind
        (fun s ↦ (channelNoise b c hc ℓ a).map (relabelRegular b (Equiv.addRight s) ℓ))) =
        (channel c hc k).bind (regularLaw b (lam*c) hprod ℓ) := by
      rw [PMF.bind_comm]
      simp_rw [← PMF.map_bind, ih, regularLaw_permute]
      change (channel c hc 0).bind (fun s ↦ regularLaw b (lam*c) hprod ℓ (k+s)) = _
      have hm := channel_permute hc (Equiv.addLeft k) 0
      simp only [Equiv.coe_addLeft, add_zero] at hm
      rw [← hm, PMF.bind_map]
      rfl
    simp_rw [he, ← PMF.bind_bind, channel_compose hlam hc hprod]

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

lemma regular_advantage_sq_moment (b : ℕ) (lam : ℝ) (hlam : Admissible lam) (ℓ : ℕ) :
    (advantage lam hlam (PMF.pure b) ℓ)^2 ≤
      (∫ m, xMoment m ∂(discreteProbability (regularLaw b lam hlam ℓ)).toMeasure)/2 := by
  have h := discrete_degradation_mu (regularLaw b lam hlam ℓ) (fun v ↦ PMF.pure (forgetRegular b ℓ v))
  change (∫ m, xMoment m ∂(discreteProbability (fun i ↦
    (regularLaw b lam hlam ℓ i).map (forgetRegular b ℓ))).toMeasure) ≤ _ at h
  simp only [regularLaw_forget] at h
  have ha := advantage_sq_bound lam hlam (PMF.pure b) ℓ
  linarith

lemma regular_channel_mu_le (b : ℕ) (lam c : ℝ) (hlam : Admissible lam)
    (hc : Admissible c) (hprod : Admissible (lam*c)) (ℓ : ℕ) :
    (∫ m, xMoment m ∂(discreteProbability (regularLaw b (lam*c) hprod ℓ)).toMeasure) ≤
      ∫ m, xMoment m ∂(discreteProbability (regularLaw b lam hlam ℓ)).toMeasure := by
  have h := discrete_degradation_mu (regularLaw b lam hlam ℓ) (channelNoise b c hc ℓ)
  simpa only [regularLaw_noise b lam c hlam hc hprod] using h

theorem regular_positive_nonreconstruction (b : ℕ) (hb : 2 ≤ b)
    (lam : ℝ) (hlam : Admissible lam) (hl₀ : 0 ≤ lam) (hKS : (b:ℝ)*lam^2 ≤ 1) :
    Tendsto (advantage lam hlam (PMF.pure b)) atTop (𝓝 0) := by
  have hb' : (2:ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0:ℝ) < b := by linarith
  let t : ℝ := 1/Real.sqrt b
  have ht : 0 < t := by dsimp [t]; exact div_pos (by norm_num) (Real.sqrt_pos.mpr hbpos)
  have htsq : (b:ℝ)*t^2 = 1 := by
    dsimp [t]
    rw [div_pow, one_pow, Real.sq_sqrt hbpos.le, mul_one_div_cancel (ne_of_gt hbpos)]
  have htone : t < 1 := by
    have h := mul_le_mul_of_nonneg_right hb' (sq_nonneg t)
    nlinarith
  have htadm : Admissible t := ⟨by linarith, htone.le⟩
  have hlt : lam ≤ t := by
    have hs : lam^2 ≤ t^2 := (mul_le_mul_iff_right₀ hbpos).mp (by nlinarith [hKS, htsq])
    nlinarith
  let c := lam/t
  have hcpos : 0 ≤ c := div_nonneg hl₀ ht.le
  have hcone : c ≤ 1 := (div_le_one ht).2 hlt
  have hcadm : Admissible c := ⟨by linarith, hcone⟩
  have he : t*c = lam := by dsimp [c]; field_simp
  have hprod : Admissible (t*c) := he.symm ▸ hlam
  have hm := regular_positive_critical_mu b hb ht htone htadm htsq
  have hu : Tendsto (fun ℓ ↦ Real.sqrt (regularPosteriorLaw b ht.le htone ℓ).mu) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hm
  apply squeeze_zero (fun ℓ ↦ advantage_nonneg lam hlam (PMF.pure b) ℓ) _ hu
  intro ℓ
  apply (sq_le_sq₀ (advantage_nonneg lam hlam (PMF.pure b) ℓ) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (regularPosteriorLaw b ht.le htone ℓ).mu_nonneg]
  have h := regular_channel_mu_le b t c htadm hcadm hprod ℓ
  have hw := regular_advantage_sq_moment b lam hlam ℓ
  have heq : regularLaw b (t*c) hprod ℓ = regularLaw b lam hlam ℓ := by
    congr 1
  rw [heq] at h
  rw [← regularPosteriorLaw_probability b ht.le htone htadm ℓ] at h
  change _ ≤ (regularPosteriorLaw b ht.le htone ℓ).mu at h
  linarith [(regularPosteriorLaw b ht.le htone ℓ).mu_nonneg]

end ThreeState.TreeClauses.Tree

end

end OAI
