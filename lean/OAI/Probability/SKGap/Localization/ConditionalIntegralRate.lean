import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianCompactTailRate
import OAI.Probability.SKGap.Localization.ScalarRelativeIsolation
import OAI.Probability.SKGap.Stability.ConditionalStability
import OAI.Probability.SKGap.Localization.ConditionalWeight
import OAI.Probability.SKGap.Entropy.WeightedRateAssembly

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

def badFieldFlat (n : ℕ) (j A ε m : ℝ) : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ)) :=
  {p | ((fun i k=>p.1 (i,k)),p.2)∈badFieldSet n j A ε m}

lemma measurableSet_badFieldFlat (n : ℕ) (j A ε m : ℝ) :
    MeasurableSet (badFieldFlat n j A ε m) :=
  ((isClosed_badFieldSet n j A ε m).preimage (by fun_prop)).measurableSet

def reducedBadDensity {n : ℕ} [NeZero n] (j t σ A ε m : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (sqrt (scalarS j (scalarEmpirical y t σ)/
    (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y)*
    conditionalFieldWeight j t σ (badFieldFlat n j A ε m) y

lemma reducedBadDensity_le {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ) (A ε m : ℝ) (y : Fin n → ℝ) :
    reducedBadDensity j t σ A ε m y ≤ ENNReal.ofReal (scalarIntegrand j t σ y) := by
  simpa only [reducedBadDensity,mul_one] using scalar_weighted_density_bound hj ht hσ y
    (conditionalFieldWeight_le_one j t σ (badFieldFlat n j A ε m) y)

lemma empirical_of_not_forbidden {n : ℕ} [NeZero n] {R t0 T t σ : ℝ} {U : Set (ScalarTimeDomain R t0 T)}
    {y : Fin n → ℝ} (hP : empiricalLaw y ∈ momentBall R) (ht : t∈Icc t0 T)
    (hF : scalarEmpirical y t σ ∉ scalarRelativeForbidden U) :
    (⟨empiricalLaw y,hP⟩,⟨t,ht⟩) ∈ U := by
  by_contra h
  exact hF ⟨(⟨empiricalLaw y,hP⟩,⟨t,ht⟩),h,rfl⟩

lemma reduced_bad_integral_bound {n : ℕ} [NeZero n] {j t σ R t0 T R1 ν A ε m c : ℝ}
    (hj : 0 ≤ j) (ht0 : 0 < t0) (ht : t∈Icc t0 T) (hσ : 0 < σ) (hR : 0 ≤ R)
    (U : Set (ScalarTimeDomain R t0 T)) (hU : IsOpen U)
    (hcond : ∀ x ∈ U, ∀ y : Fin n → ℝ, empiricalLaw y=(x.1:ProbabilityMeasure ℝ) →
      (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ) →
      (conditionalGoeLaw (j/(n:ℝ)) ((x.2:ℝ)+σ^2) (magnetization y)
        (empiricalObservation j x.2 σ y)).real
        {W | ((fun i k=>W (i,k)),y)∈badFieldSet n j A ε m} ≤ exp (-c*(n:ℝ))) :
    (∫⁻ y,reducedBadDensity (n := n) j t σ A ε m y) ≤
      (∫⁻ y in {y : Fin n → ℝ | (n:ℝ)*R < ∑ i,y i^2},ENNReal.ofReal (scalarIntegrand j t σ y))+
      (∫⁻ y in {y : Fin n → ℝ | ∑ i,y i^2 ≤ (n:ℝ)*R} ∩
        {y | scalarEmpirical y t σ ∈ scalarRelativeForbidden U},ENNReal.ofReal (scalarIntegrand j t σ y))+
      (∫⁻ y in {y : Fin n → ℝ | (n:ℝ)*ν ≤ ∑ i,squareTail R1 (y i)},ENNReal.ofReal (scalarIntegrand j t σ y))+
      (∫⁻ y,ENNReal.ofReal (scalarIntegrand (ι := Fin n) j t σ y))*ENNReal.ofReal (exp (-c*(n:ℝ))) := by
  let B : Set (Fin n → ℝ) := {y | ∑ i,y i^2 ≤ (n:ℝ)*R}
  let F : Set (Fin n → ℝ) := {y | scalarEmpirical y t σ ∈ scalarRelativeForbidden U}
  let D : Set (Fin n → ℝ) := {y | (n:ℝ)*ν ≤ ∑ i,squareTail R1 (y i)}
  have hB : MeasurableSet B := (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hF : MeasurableSet F := ((isClosed_scalarRelativeForbidden hU).preimage
    (continuous_empiricalLaw.prodMk continuous_const)).measurableSet
  have hD : MeasurableSet D := measurableSet_le measurable_const (Finset.measurable_sum _
    (fun i _=>(measurable_squareTail R1).comp (measurable_pi_apply i)))
  have hb := weighted_four_region_bound volume (reducedBadDensity (n := n) j t σ A ε m)
    (fun y=>ENNReal.ofReal (scalarIntegrand j t σ y)) (measurable_scalarIntegrand j t σ).ennreal_ofReal
    B F D hB hF hD (reducedBadDensity_le hj (ht0.le.trans ht.1) hσ A ε m)
    (ENNReal.ofReal (exp (-c*(n:ℝ)))) (by
      intro y hy
      have hP := empirical_momentBall y hR (by simpa only [B,mem_ofPred_eq,Fintype.card_fin] using hy.1.1)
      have hx := empirical_of_not_forbidden hP ht hy.1.2
      have htail : (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ) := by
        have hh := le_of_lt (not_le.mp (show ¬ (n:ℝ)*ν ≤ ∑ i,squareTail R1 (y i) from hy.2))
        simpa only [squareTail,mul_comm] using hh
      have hc' := hcond (⟨empiricalLaw y,hP⟩,⟨t,ht⟩) hx y rfl htail
      exact scalar_weighted_density_bound hj (ht0.le.trans ht.1) hσ y
        (conditionalFieldWeight_of_real_bound (badFieldFlat n j A ε m) y hc'))
  have hBc : Bᶜ={y : Fin n → ℝ | (n:ℝ)*R < ∑ i,y i^2} := by ext y; change (¬ ∑ i,y i^2 ≤ (n:ℝ)*R) ↔ _; exact not_le
  simpa only [hBc] using hb

theorem conditional_bad_integral_rate {j A t0 T : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hA : 1 ≤ A) (hsub : sqrt j*A < 1) (ht0 : 0 < t0) (hT : t0 ≤ T) :
    ∃ m ε σ0 a : ℝ, 0 < m ∧ 0 < ε ∧ 0 < σ0 ∧ 0 < a ∧ ∃ N : ℕ,
    ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ t ∈ Icc t0 T, ∀ σ ∈ Ioc 0 σ0,
    (∫⁻ y,reducedBadDensity (n := n) j t σ A ε m y) ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  have hT0 : 0 ≤ T := ht0.le.trans hT
  obtain ⟨R,hR,hTail⟩ := scalar_uniform_tail hj.le hT0 ht0 1
  obtain ⟨m,ν,σc,hm,hν,hσc,U,hU,hKU,hcond⟩ := conditional_field_stability hj hj1 hA hsub hR.le ht0 (T := T)
  obtain ⟨R1,aD,haD,ND,hD⟩ := scalar_rate_iv hj hj1 ht0 hT hν
  obtain ⟨ε,c,NC,hε,hc,_,hC⟩ := hcond (max R1 1) (le_max_right _ _)
  obtain ⟨aF,haF,δ,hδ,NF,hF⟩ := scalar_relative_neighborhood_rate hj hj1 ht0 hT hU hKU
  obtain ⟨NG,hG⟩ := scalar_unrestricted_rate hj hj1 hT0 ht0 (half_pos hc)
  let b := min 1 (min aF (min aD (c/2)))
  have hb : 0 < b := lt_min zero_lt_one (lt_min haF (lt_min haD (half_pos hc)))
  obtain ⟨M,hM⟩ := absorb_finite_exponential_factor 4 (half_pos hb)
  refine ⟨m,ε,min σc (min δ 1),b/2,hm,hε,lt_min hσc (lt_min hδ zero_lt_one),half_pos hb,
    max NC (max ND (max NF (max NG M))),?_⟩
  intro n _ hn t ht σ hσ
  have hn' : 0 < n := NeZero.pos n
  have hNC : NC ≤ n := (le_max_left _ _).trans hn
  have hND : ND ≤ n := (le_max_left ND _).trans ((le_max_right NC _).trans hn)
  have hNF : NF ≤ n := (le_max_left NF _).trans ((le_max_right ND _).trans ((le_max_right NC _).trans hn))
  have hNG : NG ≤ n := (le_max_left NG M).trans ((le_max_right NF _).trans ((le_max_right ND _).trans ((le_max_right NC _).trans hn)))
  have hMN : M ≤ n := (le_max_right NG M).trans ((le_max_right NF _).trans ((le_max_right ND _).trans ((le_max_right NC _).trans hn)))
  have hσ1 : σ∈Icc 0 1 := ⟨hσ.1.le,(min_le_right _ _).trans' ((min_le_right _ _).trans' hσ.2)⟩
  have hσδ : σ∈Icc 0 (min δ 1) := ⟨hσ.1.le,(min_le_right _ _).trans' hσ.2⟩
  have hσc' : |σ| ≤ σc := by rw [abs_of_pos hσ.1]; exact (min_le_left _ _).trans' hσ.2
  let B : Set (Fin n → ℝ) := {y | ∑ i,y i^2 ≤ (n:ℝ)*R}
  let F : Set (Fin n → ℝ) := {y | scalarEmpirical y t σ ∈ scalarRelativeForbidden U}
  let D : Set (Fin n → ℝ) := {y | (n:ℝ)*ν ≤ ∑ i,squareTail (max R1 1) (y i)}
  have hBm : MeasurableSet B := (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hFm : MeasurableSet F := ((isClosed_scalarRelativeForbidden hU).preimage
    (continuous_empiricalLaw.prodMk continuous_const)).measurableSet
  have hDm : MeasurableSet D := measurableSet_le measurable_const (Finset.measurable_sum _
    (fun i _=>(measurable_squareTail (max R1 1)).comp (measurable_pi_apply i)))
  have hs (y : Fin n → ℝ) : t0 ≤ scalarS j (scalarEmpirical y t σ) := by
    have hq := mul_nonneg hj.le (scalarQMoment_bounds (empiricalLaw y)).1
    change t0 ≤ t+σ^2+j*scalarQMoment (empiricalLaw y)
    linarith [ht.1,sq_nonneg σ]
  have htail := hTail n hn' t ⟨ht0.le.trans ht.1,ht.2⟩ σ hσ1 Bᶜ hBm.compl
    (fun y _=>hs y) (fun y hy=>le_of_lt (not_le.mp hy))
  have hforb := hF n hNF hn' t ht σ hσδ (B∩F) (hBm.inter hFm)
    (fun y hy=>empirical_momentBall y hR.le (by simpa only [B,mem_ofPred_eq,Fintype.card_fin] using hy.1)) (by
      intro y hy x hx
      obtain ⟨z,hz,hze⟩ := hy.2
      by_contra hh
      push Not at hh
      apply hz
      have he : z=x := by
        apply Prod.ext <;> apply Subtype.ext
        · exact (congrArg Prod.fst hze).trans hh.1
        · exact (congrArg Prod.snd hze).trans hh.2
      simpa only [he] using hx)
  have hdiag := hD (max R1 1) (le_max_left _ _) n hND hn' t ht σ hσ1 D hDm (fun _ hy=>hy)
  have hglobal := hG n hNG hn' t ⟨ht0.le.trans ht.1,ht.2⟩ σ hσ1 univ MeasurableSet.univ (fun y _=>hs y)
  simp only [Measure.restrict_univ] at hglobal
  have hgood := mul_le_mul' hglobal (le_rfl (a := ENNReal.ofReal (exp (-c*(n:ℝ)))))
  rw [← ENNReal.ofReal_mul (exp_pos _).le,← exp_add] at hgood
  have he : c/2*(n:ℝ)+ -c*(n:ℝ)= -(c/2)*(n:ℝ) := by ring
  rw [he] at hgood
  have hcoeff {r : ℝ} (hr : b ≤ r) : ENNReal.ofReal (exp (-r*(n:ℝ))) ≤ ENNReal.ofReal (exp (-b*(n:ℝ))) :=
    ENNReal.ofReal_le_ofReal (exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbF : b ≤ aF := (min_le_right _ _).trans (min_le_left _ _)
  have hbD : b ≤ aD := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbC : b ≤ c/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbound := reduced_bad_integral_bound hj.le ht0 ht hσ.1 hR.le U hU
    (fun x hx y hP hy=>hC n hNC x hx y hP hy σ hσc')
  have hBc : Bᶜ={y : Fin n → ℝ | (n:ℝ)*R < ∑ i,y i^2} := by ext y; change (¬ ∑ i,y i^2 ≤ (n:ℝ)*R) ↔ _; exact not_le
  rw [← hBc] at hbound
  have htotal := hbound.trans (add_le_add (add_le_add (add_le_add
    (htail.trans (hcoeff hb1)) (hforb.trans (hcoeff hbF))) (hdiag.trans (hcoeff hbD)))
    (hgood.trans (hcoeff hbC)))
  have hadd : ENNReal.ofReal (exp (-b*(n:ℝ)))+ENNReal.ofReal (exp (-b*(n:ℝ)))+
      ENNReal.ofReal (exp (-b*(n:ℝ)))+ENNReal.ofReal (exp (-b*(n:ℝ)))=
      ENNReal.ofReal (4*exp ((n:ℝ)*(-b))) := by
    rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le,
      ← ENNReal.ofReal_add (by positivity) (exp_pos _).le,
      ← ENNReal.ofReal_add (by positivity) (exp_pos _).le]
    congr 1
    ring_nf
  rw [hadd] at htotal
  apply htotal.trans (ENNReal.ofReal_le_ofReal _)
  convert hM n hMN (-b) using 1
  congr 1
  ring
end SKGap
end
end

end OAI
