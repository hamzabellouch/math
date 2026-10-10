import Mathlib
import OAI.Probability.SKGap.Matrix.LogDetIntegral
import OAI.Probability.SKGap.Stability.LogDetMean
import OAI.Probability.SKGap.Localization.BoundedIntervalFubini

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rare_logdet_coefficients {n j γ : ℝ} (hn : 0 < n) (hj : 0 ≤ j) (hγ : 0 < γ) :
    sqrt n*(1+j)/sqrt (n*γ)=(1+j)/sqrt γ ∧
    n^2*sqrt (2*j/n)/sqrt (n*γ)=n*sqrt (2*j)/sqrt γ := by
  have hs : 0 < sqrt n := sqrt_pos.mpr hn
  have hg : 0 < sqrt γ := sqrt_pos.mpr hγ
  rw [sqrt_mul hn.le,sqrt_div (by positivity : 0 ≤ 2*j)]
  constructor
  · field_simp
  · field_simp
    rw [sq_sqrt hn.le]
    ring

def logdetMeanError (j R B C rate γ : ℝ) : ℝ :=
  2*(2*j+1)*C+(|log γ|+(1+j)/sqrt γ+2*((2*j+R)*B))*(3/rate)+
    (sqrt (2*j)/sqrt γ)*(8*sqrt 3/rate^2)

lemma logdetMeanError_nonneg {j R B C rate γ : ℝ} (hj : 0 ≤ j) (hR : 0 ≤ R)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hrate : 0 < rate) (hγ : 0 < γ) :
    0 ≤ logdetMeanError j R B C rate γ := by unfold logdetMeanError; positivity

lemma logPath_regularized_expected [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R lo hi j C γ rate : ℝ}
    (hR : 0 ≤ R) (hlo : 0 < lo) (hf : ∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹)
    (hj : 0 ≤ j) (hC : 0 ≤ C) (hγ : 0 < γ) (hrate : 0 < rate)
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hK : ∀ z ∈ Icc (0:ℝ) 1, ∀ i, |pathExpected f R hR j a z i-1| ≤ C/(Fintype.card ι:ℝ))
    (hWK : ∀ z ∈ Icc (0:ℝ) 1, ∀ i,
      |(∫ g, (realProject R hR (goeMatrix (j/(Fintype.card ι:ℝ)) g)*
        pathK f R hR j a z (goeMatrix (j/(Fintype.card ι:ℝ)) g)) i i
        ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-
          z*((j/(Fintype.card ι:ℝ))*∑ b,a b)| ≤ C/(Fintype.card ι:ℝ))
    (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      {g | goeMatrix (j/(Fintype.card ι:ℝ)) g ∉ logPathGood R lo hi ((j/(Fintype.card ι:ℝ))*∑ b,a b) a} ≤
      3*Real.exp (-rate*(Fintype.card ι:ℝ))) :
    (∫ g, LogDet.regularizedLogDet γ (logPath ((j/(Fintype.card ι:ℝ))*∑ b,a b) a
      (goeMatrix (j/(Fintype.card ι:ℝ)) g) 1)
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) ≤
      j*((∑ i,a i)/(Fintype.card ι:ℝ))^2+γ*(pathBound f R j 1)^2+
        logdetMeanError j R (pathBound f R j 1) C rate γ/(Fintype.card ι:ℝ) := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  let r := j/(Fintype.card ι:ℝ)
  let q := r*∑ i,a i
  let B := pathBound f R j 1
  let D := (2*j+R)*B
  let T := fun p : ℝ × (MatrixCoordinates ι → ℝ) => logPathCutoffDerivative f R hR j a (goeMatrix r p.2) p.1
  let I := fun g => ∫ z in (0:ℝ)..1, T (z,g)
  let F := fun g => LogDet.regularizedLogDet γ (logPath q a (goeMatrix r g) 1)
  let s := {g | goeMatrix r g ∉ logPathGood R lo hi q a}
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hn1 : (1:ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hB : 0 ≤ B := (path_constants_nonneg f hR hj (by norm_num : (0:ℝ)≤1)).1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have ht : Continuous T := (continuous_logPathCutoffDerivative f hR j a).comp
    (continuous_fst.prodMk ((goeMatrix_pi_lipschitz r).continuous.comp continuous_snd))
  have htb (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) (g) : |T (z,g)| ≤ D :=
    logPathCutoffDerivative_bound f hR hj ha ha1 hz _
  have htm (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) :
      |(∫ g, T (z,g) ∂μ)-z*(j*((∑ i,a i)/(Fintype.card ι:ℝ))^2)| ≤ (2*j+1)*C/(Fintype.card ι:ℝ) := by
    simpa only [mul_assoc] using logPathCutoffDerivative_mean_error f hR hj hC ha ha1 hz (hK z hz) (hWK z hz)
  obtain ⟨hI,hIm⟩ := bounded_interval_mean (μ := μ) ht htb htm
  have hIb (g) : |I g| ≤ D := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (f := fun z => T (z,g)) (C := D) (fun z hz => by
        have hz' : z ∈ Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0:ℝ)≤1)] using hz
        simpa only [Real.norm_eq_abs] using htb z ⟨hz'.1.le,hz'.2⟩ g)
    simpa only [I,Real.norm_eq_abs,sub_zero,abs_one,mul_one] using hh
  have hs : MeasurableSet s := ((logPathGood_isClosed R lo hi q a).preimage (goeMatrix_pi_lipschitz r).continuous).measurableSet.compl
  have hF : Integrable F μ := logPath_regularized_integrable hγ ha ha1
  have hgood (g) (hg : g ∉ s) : F g ≤ 2*I g+γ*B^2 := by
    have hg' : goeMatrix r g ∈ logPathGood R lo hi q a := by simpa only [s,mem_ofPred_eq,not_not] using hg
    have hsymm : (goeMatrix r g)ᵀ=goeMatrix r g := goeMatrix_transpose r g
    have hev := logdetPath_integral f hlo hf hR j ha (goeMatrix r g) hsymm hg'
    have hu := pathK_agrees_at f hlo hf hR j ha (by norm_num : (0:ℝ)≤1) (goeMatrix r g) hsymm hg'.1
      (hg'.2 1 (by constructor <;> norm_num)).1 (hg'.2 1 (by constructor <;> norm_num)).2
    have hb : opNorm (logPath q a (goeMatrix r g) 1)⁻¹ ≤ B := by
      rw [← hu.2]
      exact (pathK_bounds f hR hj (by norm_num : (0:ℝ)≤1) ha ha1 (by constructor <;> norm_num)).1 _
    have hh := LogDet.regularizedLogDet_le_logdet_opNorm hγ.le _ hu.1 hb
    change F g ≤ 2*I g+γ*B^2
    dsimp only [I,T]
    rw [hev]
    exact hh.trans_eq (by ring)
  have hex := expectation_upper_good hs hF hI (mul_nonneg hγ.le (sq_nonneg B)) hIb hgood
  have hrare := logPath_regularized_rare hj hγ ha ha1 hs
  obtain ⟨hc₁,hc₂⟩ := rare_logdet_coefficients hn hj hγ
  rw [hc₁,hc₂] at hrare
  obtain ⟨hp₁,_,hp₃⟩ := exponential_tail_absorptions hrate hn1 hp
  have hsmall : (|log γ|+(1+j)/sqrt γ+2*D)*μ.real s+
      (sqrt (2*j)/sqrt γ)*((Fintype.card ι:ℝ)*sqrt (μ.real s)) ≤
      (|log γ|+(1+j)/sqrt γ+2*D)*((3/rate)/(Fintype.card ι:ℝ))+
      (sqrt (2*j)/sqrt γ)*((8*sqrt 3/rate^2)/(Fintype.card ι:ℝ)) := by
    exact add_le_add (mul_le_mul_of_nonneg_left hp₁ (by positivity))
      (mul_le_mul_of_nonneg_left hp₃ (by positivity))
  have hib := (abs_le.mp hIm).2
  dsimp only [F,I,T,q,r,μ,B,D,logdetMeanError] at hex hrare hib hsmall ⊢
  simp only [div_eq_mul_inv] at hex hrare hib hsmall ⊢
  nlinarith only [hex,hrare,hib,hsmall]
end SKGap
end
end

end OAI
