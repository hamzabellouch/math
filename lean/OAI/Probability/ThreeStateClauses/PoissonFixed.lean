import Mathlib
import OAI.Probability.ThreeStateClauses.OffspringLaws
import OAI.Probability.ThreeStateClauses.PoissonCalculus

namespace OAI

/-! Poisson Fixed. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive ThreeState.TreeClauses.Probability

def uniformMessage : Message := ⟨fun _ ↦ 1, by norm_num, by norm_num [avg]⟩

lemma uniformMessage_x : xMoment uniformMessage = 0 := by norm_num [xMoment, momentX, centered, uniformMessage, avg]

lemma branch_uniform (lam : ℝ) (n : ℕ) :
    normalizer (branchEdges lam (fun _ : Fin n ↦ uniformMessage)) = 1 := by
  norm_num [normalizer, branchEdges, branchProduct, edgeMessage, edge, centered, uniformMessage, avg]

lemma branchOutput_uniform {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    branchOutput hl₀ hl₁ (fun _ : Fin n ↦ uniformMessage) = uniformMessage := by
  apply Subtype.ext
  funext i
  norm_num [branchOutput, normalizedProduct, branch_uniform, branchProduct, branchEdges,
    edgeMessage, edge, centered, uniformMessage, normalizer, avg]

lemma finite_uniform_atom (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    (Q.probability.toMeasure {uniformMessage})^n ≤
      (finiteProbability Q hl₀ hl₁ n).toMeasure {uniformMessage} := by
  change _ ≤ (Measure.map (branchOutput hl₀ hl₁) (tiltedProduct Q lam n)) {uniformMessage}
  rw [Measure.map_apply (continuous_branchOutput hl₀ hl₁ n).measurable (measurableSet_singleton _)]
  have he : (tiltedProduct Q lam n) {fun _ : Fin n ↦ uniformMessage} =
      (Q.probability.toMeasure {uniformMessage})^n := by
    rw [tiltedProduct, withDensity_apply _ (measurableSet_singleton _), lintegral_singleton]
    simp only [branch_uniform, ENNReal.ofReal_one, one_mul, Measure.pi_singleton,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← he]
  apply measure_mono
  intro m hm
  rcases hm with rfl
  exact branchOutput_uniform hl₀ hl₁ n

lemma poisson_generating (t q : ℝ) :
    HasSum (fun n ↦ poissonWeight t n*q^n) (Real.exp (t*(q-1))) := by
  have hx : HasSum (fun n : ℕ ↦ (t*q)^n/(n.factorial:ℝ)) (Real.exp (t*q)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (t*q)
  have h := hx.mul_left (Real.exp (-t))
  have he : Real.exp (-t)*Real.exp (t*q) = Real.exp (t*(q-1)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he] at h
  have hf : (fun n : ℕ ↦ poissonWeight t n*q^n) =
      (fun n ↦ Real.exp (-t)*((t*q)^n/(n.factorial:ℝ))) := by
    funext n
    dsimp [poissonWeight]
    rw [mul_pow]
    ring
  rw [hf]
  exact h

lemma poisson_uniform_atom (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (t : ℝ≥0) :
    Real.exp ((t:ℝ)*((Q.probability.toMeasure {uniformMessage}).toReal-1)) ≤
      ((poissonLaw Q hl₀ hl₁ t).probability.toMeasure {uniformMessage}).toReal := by
  let q := (Q.probability.toMeasure {uniformMessage}).toReal
  have hq : 0 ≤ q := ENNReal.toReal_nonneg
  have he : ENNReal.ofReal q = Q.probability.toMeasure {uniformMessage} :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  have h : ENNReal.ofReal (Real.exp ((t:ℝ)*(q-1))) ≤
      (poissonLaw Q hl₀ hl₁ t).probability.toMeasure {uniformMessage} := by
    rw [← (poisson_generating t q).tsum_eq, ENNReal.ofReal_tsum_of_nonneg
      (fun n ↦ mul_nonneg (poissonWeight_nonneg t.coe_nonneg n) (pow_nonneg hq n))
      (poisson_generating t q).summable]
    change _ ≤ (Measure.sum (fun n ↦ (poissonPMF t) n • (finiteProbability Q hl₀ hl₁ n).toMeasure)) _
    rw [Measure.sum_apply _ (measurableSet_singleton _)]
    apply ENNReal.tsum_le_tsum
    intro n
    rw [ENNReal.ofReal_mul (poissonWeight_nonneg t.coe_nonneg n), ENNReal.ofReal_pow hq, he,
      ← poissonPMF_real, ENNReal.ofReal_toReal ((poissonPMF t).apply_ne_top n)]
    exact mul_le_mul' le_rfl (finite_uniform_atom Q hl₀ hl₁ n)
  have hh := ENNReal.toReal_mono (measure_ne_top _ _) h
  rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at hh

def Law.nonuniformMass (Q : Law) : ℝ := 1-(Q.probability.toMeasure {uniformMessage}).toReal

lemma Law.nonuniformMass_nonneg (Q : Law) : 0 ≤ Q.nonuniformMass := by
  apply sub_nonneg.mpr
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 (prob_le_one)

lemma Law.nonuniformMass_le_one (Q : Law) : Q.nonuniformMass ≤ 1 := by
  unfold Law.nonuniformMass
  exact sub_le_self _ ENNReal.toReal_nonneg

lemma Law.nonuniform_second_moment (Q : Law) : Q.mu^2 ≤ Q.nonuniformMass*Q.nu := by
  have hi := compact_integrable continuous_xMoment (μ := Q.probability.toMeasure)
  have hi₂ := compact_integrable (continuous_xMoment.pow 2) (μ := Q.probability.toMeasure)
  have hquad (a : ℝ) : 0 ≤ Q.nonuniformMass*(a*a)+(-2*Q.mu)*a+Q.nu := by
    have h := integral_nonneg (μ := Q.probability.toMeasure.restrict {uniformMessage}ᶜ)
      (f := fun m : Message ↦ (xMoment m-a)^2) (fun m ↦ sq_nonneg (xMoment m-a))
    rw [setIntegral_compl (f := fun m : Message ↦ (xMoment m-a)^2) (measurableSet_singleton _)
      (compact_integrable ((continuous_xMoment.sub continuous_const).pow 2)),
      integral_singleton, uniformMessage_x] at h
    have hf : (fun m : Message ↦ (xMoment m-a)^2) =
        (fun m ↦ xMoment m^2-2*a*xMoment m+a^2) := by funext m; ring
    rw [hf, integral_add (f := fun m ↦ xMoment m^2-2*a*xMoment m)
      (g := fun _ ↦ a^2) (hi₂.sub (hi.const_mul _)) (integrable_const _),
      integral_sub (f := fun m : Message ↦ xMoment m^2) (g := fun m ↦ 2*a*xMoment m) hi₂ (hi.const_mul _), integral_const_mul] at h
    simp only [integral_const, measure_univ, Measure.real, ENNReal.toReal_one,
      smul_eq_mul, one_mul, zero_sub, neg_sq] at h
    change 0 ≤ Q.nu-2*a*Q.mu+a^2-(Q.probability.toMeasure {uniformMessage}).toReal*a^2 at h
    dsimp only [Law.nonuniformMass]
    nlinarith only [h]
  have h := discrim_le_zero hquad
  dsimp only [discrim] at h
  nlinarith only [h]

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set
namespace ThreeState.TreeClauses.Probability
open ThreeState.TreeClauses.Radial

lemma neg_log_one_sub_lower {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s < 1) :
    2*s/(2-s) ≤ -Real.log (1-s) := by
  let f : ℝ → ℝ := fun t ↦ -Real.log (1-t)-2*t/(2-t)
  let f' : ℝ → ℝ := fun t ↦ t^2/((1-t)*(2-t)^2)
  have hd (t : ℝ) (ht : t ∈ Icc 0 s) : HasDerivAt f (f' t) t := by
    have ht1 : 0 < 1-t := by linarith [ht.2]
    have ht2 : 0 < 2-t := by linarith
    apply (((((hasDerivAt_id t).const_sub 1).log (ne_of_gt ht1)).neg).sub
      (((hasDerivAt_id t).const_mul 2).div ((hasDerivAt_id t).const_sub 2) (ne_of_gt ht2))).congr_deriv
    dsimp only [f', id_eq]
    field_simp
    ring
  have hm : MonotoneOn f (Icc 0 s) := by
    apply monotoneOn_Icc_of_hasDerivAt_nonneg hd
    intro t ht
    dsimp only [f', id_eq]
    have : 0 < 1-t := by linarith [ht.2]
    positivity
  have h := hm ⟨le_rfl,hs₀⟩ ⟨hs₀,le_rfl⟩ hs₀
  dsimp only [f] at h
  norm_num at h
  linarith only [h]

lemma poisson_subfixed_mass_bound {d s : ℝ} (hd : 1 < d) (hs₀ : 0 ≤ s)
    (hs : Real.exp (-d*s) ≤ 1-s) : s ≤ 2*(1-1/d) := by
  have hs₁ : s < 1 := by linarith [Real.exp_pos (-d*s)]
  have hlog : -Real.log (1-s) ≤ d*s := by
    have h := Real.log_le_log (Real.exp_pos (-d*s)) hs
    rw [Real.log_exp] at h
    linarith only [h]
  have hl := neg_log_one_sub_lower hs₀ hs₁
  have hden : 0 < 2-s := by linarith
  have hmul := (div_le_iff₀ hden).mp (hl.trans hlog)
  rcases eq_or_lt_of_le hs₀ with h | h
  · have he : s = 0 := h.symm
    rw [he]
    have hdiv : 1/d < 1 := (div_lt_one (by linarith : 0 < d)).2 hd
    linarith only [hdiv]
  · have hh : 2 ≤ d*(2-s) := (mul_le_mul_iff_right₀ h).mp (by nlinarith only [hmul])
    have he : 2*(1-1/d) = (2*d-2)/d := by field_simp
    rw [he]
    apply (le_div_iff₀ (by linarith : 0 < d)).2
    nlinarith only [hh]

end ThreeState.TreeClauses.Probability

end 

noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability

lemma poisson_fixed_mass_bound (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1)
    (d : ℝ≥0) (hd : 1 < (d:ℝ)) (hcrit : (d:ℝ)*lam^2 = 1)
    (hfixed : Q.probability = (poissonLaw Q hl₀.le hl₁ d).probability) :
    Q.nonuniformMass ≤ 2*(1-lam^2) := by
  have ha := poisson_uniform_atom Q hl₀.le hl₁ d
  rw [← hfixed] at ha
  have hsub : Real.exp (-(d:ℝ)*Q.nonuniformMass) ≤ 1-Q.nonuniformMass := by
    calc
      _ = Real.exp ((d:ℝ)*((Q.probability.toMeasure {uniformMessage}).toReal-1)) := by
        congr 1; dsimp only [Law.nonuniformMass]; ring
      _ ≤ (Q.probability.toMeasure {uniformMessage}).toReal := ha
      _ = _ := by dsimp only [Law.nonuniformMass]; ring
  have hs := poisson_subfixed_mass_bound hd Q.nonuniformMass_nonneg hsub
  have he : 1/(d:ℝ) = lam^2 := (div_eq_iff (by positivity : (d:ℝ) ≠ 0)).2 (by nlinarith only [hcrit])
  rwa [he] at hs

theorem poisson_fixed_mu_zero (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1)
    (d : ℝ≥0) (hd : 1 < (d:ℝ)) (hcrit : (d:ℝ)*lam^2 = 1)
    (hfixed : Q.probability = (poissonLaw Q hl₀.le hl₁ d).probability) : Q.mu = 0 := by
  by_contra hmu0
  have hmu : 0 < Q.mu := lt_of_le_of_ne Q.mu_nonneg (Ne.symm hmu0)
  have hnu : 0 < Q.nu := (sq_pos_of_pos hmu).trans_le Q.second_moment_lower
  have hmoment := Q.nonuniform_second_moment
  have hs₀ : 0 < Q.nonuniformMass := by
    by_contra h
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hnu.le
    nlinarith only [hmoment, hh, sq_pos_of_pos hmu]
  have hinfo := poisson_fixed_moment_bounds Q hl₀ hl₁ d hcrit hfixed
  have hcl := cExact_lower hl₀.le hl₁.le
  have hc : 0 < cExact lam := (cLower_pos hl₀.le).trans_le hcl
  have hetaNonneg : 0 ≤ Q.eta := (mul_nonneg hc.le hnu.le).trans hinfo.2.2
  have hsq : (cExact lam*Q.nu)^2 ≤ Q.eta^2 :=
    (sq_le_sq₀ (mul_nonneg hc.le hnu.le) hetaNonneg).2 hinfo.2.2
  have hregion : cExact lam^2*Q.nu ≤ Q.mu := by
    apply (mul_le_mul_iff_right₀ hnu).mp
    nlinarith [Q.moment_discriminant]
  have hmuC : Q.mu*cExact lam^2 ≤ Q.nonuniformMass := by
    apply (mul_le_mul_iff_right₀ hmu).mp
    have hh := mul_le_mul_of_nonneg_left hmoment (sq_nonneg (cExact lam))
    have hh' := mul_le_mul_of_nonneg_left hregion hs₀.le
    nlinarith only [hh, hh']
  have hregionLower : Q.mu*cLower lam^2 ≤ Q.nonuniformMass := by
    have hs : cLower lam^2 ≤ cExact lam^2 :=
      (sq_le_sq₀ (cLower_pos hl₀.le).le hc.le).2 hcl
    exact (mul_le_mul_of_nonneg_left hs hmu.le).trans hmuC
  have hstrict := scalar_strict hl₀ hl₁ hmu.le hs₀ Q.nonuniformMass_le_one hregionLower
    (Or.inr (poisson_fixed_mass_bound Q hl₀ hl₁ d hd hcrit hfixed))
  have hJ := jMean_square_bound hl₀.le hl₁.le hmu.le hnu.le hinfo.1 hinfo.2.1 hregion
  have hH := poisson_fixed_correlation_bound Q hl₀ hl₁ d hcrit hfixed
  have hrad := poisson_fixed_entropy_radial Q hl₀ hl₁ d hcrit hfixed
  have hH' : 3*Q.mu^2/(2*(1+2*Q.mu/3))-(1/Real.sqrt 2)*(lam*Q.mu*Q.nu) ≤
      3*poissonCorrelation Q hl₀.le hl₁ d := by
    convert hH using 1
    ring
  have hg := mul_le_mul_of_nonneg_right (le_of_lt strict_correlation_coefficient)
    (show 0 ≤ lam*Q.mu*Q.nu by positivity)
  have hb₀ : (1-lam^2)/2*Q.nu+3*Q.mu^2/(2*(1+2*Q.mu/3))+
      (17/25)*lam*Q.mu*Q.nu ≤ (8/5)*Q.mu^2 := by
    nlinarith only [hJ,hH',hrad,hg]
  have hb : ((1-lam^2)/2+17*lam*Q.mu/25)*Q.nu+3*Q.mu^2/(2*(1+2*Q.mu/3)) ≤
      (8/5)*Q.mu^2 := by nlinarith only [hb₀]
  have halpha : 0 < 1-lam^2 := by nlinarith only [mul_pos (sub_pos.mpr hl₁) (by linarith : 0 < 1+lam)]
  have hcoef : 0 ≤ ((1-lam^2)/2+17*lam*Q.mu/25)/Q.nonuniformMass := by positivity
  have hsub := mul_le_mul_of_nonneg_left hmoment hcoef
  have hnecessary : scalarT lam Q.mu Q.nonuniformMass*Q.mu^2 ≤ (8/5)*Q.mu^2 := by
    calc
      _ = (((1-lam^2)/2+17*lam*Q.mu/25)/Q.nonuniformMass)*Q.mu^2+
          3*Q.mu^2/(2*(1+2*Q.mu/3)) := by unfold scalarT; ring
      _ ≤ (((1-lam^2)/2+17*lam*Q.mu/25)/Q.nonuniformMass)*(Q.nonuniformMass*Q.nu)+
          3*Q.mu^2/(2*(1+2*Q.mu/3)) := by linarith only [hsub]
      _ = ((1-lam^2)/2+17*lam*Q.mu/25)*Q.nu+3*Q.mu^2/(2*(1+2*Q.mu/3)) := by
        field_simp [ne_of_gt hs₀]
      _ ≤ _ := hb
  have hh := mul_lt_mul_of_pos_right hstrict (sq_pos_of_pos hmu)
  linarith only [hh,hnecessary]

end ThreeState.TreeClauses.Positive

end 

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

lemma ordered_advantage_sq_moment (ρ : PMF ℕ) (lam : ℝ) (hlam : Admissible lam) (ℓ : ℕ) :
    (advantage lam hlam ρ ℓ)^2 ≤
      (∫ m, xMoment m ∂(discreteProbability (orderedLaw ρ lam hlam ℓ)).toMeasure)/2 := by
  have h := discrete_degradation_mu (orderedLaw ρ lam hlam ℓ) (fun v ↦ PMF.pure (forgetOrdered ℓ v))
  change (∫ m, xMoment m ∂(discreteProbability (fun i ↦
    (orderedLaw ρ lam hlam ℓ i).map (forgetOrdered ℓ))).toMeasure) ≤ _ at h
  simp only [orderedLaw_forget] at h
  have ha := advantage_sq_bound lam hlam ρ ℓ
  linarith

lemma poisson_positive_critical_mu (d : ℝ≥0) (hd : 1 < (d:ℝ)) {lam : ℝ}
    (hl₀ : 0 < lam) (hl₁ : lam < 1) (hlam : Admissible lam) (hcrit : (d:ℝ)*lam^2 = 1) :
    Tendsto (fun ℓ ↦ (offspringPosteriorLaw (poissonPMF d) hl₀.le hl₁ ℓ).mu) atTop (𝓝 0) := by
  let ρ := poissonPMF d
  let Q := offspringPosteriorLaw ρ hl₀.le hl₁
  let C := fun ℓ ↦ degradationCoupling (orderedLaw ρ lam hlam ℓ) (orderedExpansion ρ lam hlam ℓ)
  have hf (ℓ : ℕ) : (C ℓ).map Prod.fst = (Q ℓ).probability := by
    rw [degradationCoupling_fst, offspringPosteriorLaw_probability ρ hl₀.le hl₁ hlam ℓ]
  have hs (ℓ : ℕ) : (C ℓ).map Prod.snd = (Q (ℓ+1)).probability := by
    rw [degradationCoupling_snd]
    have he : (fun i ↦ (orderedLaw ρ lam hlam ℓ i).bind (orderedExpansion ρ lam hlam ℓ)) =
        orderedLaw ρ lam hlam (ℓ+1) := funext (orderedLaw_degrades ρ lam hlam ℓ)
    rw [he]
    exact (offspringPosteriorLaw_probability ρ hl₀.le hl₁ hlam (ℓ+1)).symm
  have hl (ℓ : ℕ) : (∫ z, quadraticGap z ∂(C ℓ).toMeasure) = (Q ℓ).mu-(Q (ℓ+1)).mu := by
    rw [degradationCoupling_loss]
    have he : (fun i ↦ (orderedLaw ρ lam hlam ℓ i).bind (orderedExpansion ρ lam hlam ℓ)) =
        orderedLaw ρ lam hlam (ℓ+1) := funext (orderedLaw_degrades ρ lam hlam ℓ)
    rw [he]
    simp only [Q, Law.mu, offspringPosteriorLaw_probability ρ hl₀.le hl₁ hlam]
  obtain ⟨R,hR,hlim⟩ := degrading_offspring_fixed_point Q C hf hs hl hl₀.le hl₁ ρ (fun _ ↦ rfl)
  rw [poisson_fixed_mu_zero R hl₀ hl₁ d hd hcrit hR] at hlim
  exact hlim

theorem poisson_positive_nonreconstruction (d : ℝ≥0) (hd : 1 < (d:ℝ))
    (lam : ℝ) (hlam : Admissible lam) (hl₀ : 0 ≤ lam) (hKS : (d:ℝ)*lam^2 ≤ 1) :
    Tendsto (advantage lam hlam (poissonPMF d)) atTop (𝓝 0) := by
  have hdpos : 0 < (d:ℝ) := by linarith
  let t : ℝ := 1/Real.sqrt d
  have ht : 0 < t := by dsimp [t]; exact div_pos (by norm_num) (Real.sqrt_pos.mpr hdpos)
  have htsq : (d:ℝ)*t^2 = 1 := by
    dsimp [t]
    rw [div_pow, one_pow, Real.sq_sqrt hdpos.le, mul_one_div_cancel (ne_of_gt hdpos)]
  have htone : t < 1 := by
    have h := mul_lt_mul_of_pos_right hd (sq_pos_of_pos ht)
    nlinarith only [h, htsq, ht]
  have htadm : Admissible t := ⟨by linarith, htone.le⟩
  have hlt : lam ≤ t := by
    have hs : lam^2 ≤ t^2 := (mul_le_mul_iff_right₀ hdpos).mp (by nlinarith only [hKS,htsq])
    nlinarith only [hs,hl₀,ht]
  let c := lam/t
  have hcpos : 0 ≤ c := div_nonneg hl₀ ht.le
  have hcone : c ≤ 1 := (div_le_one ht).2 hlt
  have hcadm : Admissible c := ⟨by linarith, hcone⟩
  have he : t*c = lam := by dsimp [c]; field_simp
  have hprod : Admissible (t*c) := he.symm ▸ hlam
  let ρ := poissonPMF d
  have hm := poisson_positive_critical_mu d hd ht htone htadm htsq
  have hu : Tendsto (fun ℓ ↦ Real.sqrt (offspringPosteriorLaw ρ ht.le htone ℓ).mu) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hm
  apply squeeze_zero (fun ℓ ↦ advantage_nonneg lam hlam ρ ℓ) _ hu
  intro ℓ
  apply (sq_le_sq₀ (advantage_nonneg lam hlam ρ ℓ) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (offspringPosteriorLaw ρ ht.le htone ℓ).mu_nonneg]
  have h := ordered_channel_mu_le ρ t c htadm hcadm hprod ℓ
  have hw := ordered_advantage_sq_moment ρ lam hlam ℓ
  have heq : orderedLaw ρ (t*c) hprod ℓ = orderedLaw ρ lam hlam ℓ := by congr 1
  rw [heq] at h
  rw [← offspringPosteriorLaw_probability ρ ht.le htone htadm ℓ] at h
  change _ ≤ (offspringPosteriorLaw ρ ht.le htone ℓ).mu at h
  linarith [(offspringPosteriorLaw ρ ht.le htone ℓ).mu_nonneg]

end ThreeState.TreeClauses.Tree

end

end OAI
