import Mathlib
import OAI.Probability.SKGap.Localization.LocalVolumeFull
import OAI.Probability.SKGap.Stability.FieldLogDet
import OAI.Probability.SKGap.Stability.FieldIntegralMeasure
import OAI.Probability.SKGap.Entropy.BadIntegralEndpoints

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

theorem positive_time_root_stability {j A K t₀ T : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hA : 1 ≤ A) (hsub : sqrt j*A < 1) (hK : 0 ≤ K)
    (ht₀ : 0 < t₀) (hT : t₀ ≤ T) :
    ∃ ε c ρ a : ℝ,0 < ε ∧ 0 < c ∧ 0 < ρ ∧ 0 < a ∧ ∃ N : ℕ,0 < N ∧
    ∀ (n : ℕ),N ≤ n → ∀ t ∈ Icc t₀ T,
    ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
      (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
      {p | (∀ z : Field n,vectorNorm (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1)*ᵥz) ≤ K*vectorNorm z) ∧
        ∃ y : Field n, vectorNorm (tapField j (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
          (fun i=>t+p.2 i) y) ≤ ρ*sqrt (n:ℝ) ∧
          (goeMatrix (j/(n:ℝ)) p.1,y)∈badFieldSet n j A ε c} ≤
        4*exp (-min 1 (1/(π^2*j))*(n:ℝ))+exp (-a*(n:ℝ)) := by
  obtain ⟨m,ε,σb,a,hm,hε,hσb,ha,Nb,hbad⟩ := positive_time_bad_integral hj hj1 hA hsub ht₀ hT
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  let r := min (ε/4) (m/(12*j*A))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrε : 2*r ≤ ε/2 := by have hh := min_le_left (ε/4) (m/(12*j*A));dsimp [r];linarith
  have hrm : 6*j*A*r ≤ m/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 12*j*A)).mp (min_le_right (ε/4) (m/(12*j*A)))
    dsimp [r]
    nlinarith only [hh]
  obtain ⟨ε₁,hε₁,hvol⟩ := local_volume_uniform hj.le hK hr (half_pos ha)
  obtain ⟨γ,hγ,Nd,hNd,hdet⟩ := field_logdet_uniform hj hj1 hε₁
  obtain ⟨σ₀,hσ₀,hσvol⟩ := hvol γ hγ
  let σ := min (σ₀/2) σb
  have hσ : 0 < σ := lt_min (by positivity) hσb
  have hσless : σ < σ₀ := (min_le_left _ _).trans_lt (by linarith)
  have hσle : σ ≤ σb := min_le_right _ _
  obtain ⟨ρ,hρ,Nv,hNv,hv⟩ := hσvol σ hσ hσless
  refine ⟨ε/2,m/2,ρ,a/2,half_pos hε,half_pos hm,hρ,half_pos ha,
    max Nb (max Nd Nv),hNd.trans_le ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro n hn t ht
  have hnb : Nb ≤ n := (le_max_left _ _).trans hn
  have hnd : Nd ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnv : Nv ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn0 : 0 < n := hNv.trans_le hnv
  let : NeZero n := ⟨Nat.ne_of_gt hn0⟩
  let μ := gaussianCoordinates (MatrixCoordinates (Fin n))
  let ν := Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
  let D : Set (MatrixCoordinates (Fin n) → ℝ) := {g | ∃ y : Field n,
    (n:ℝ)*(j*varianceAverage y^2+ε₁) <
      log ((fieldJacobian j (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) y)ᵀ*
        fieldJacobian j (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) y+γ • 1).det}
  let I : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) → ℝ≥0∞ := fun p=>
    fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1)) (fun i=>t+p.2 i)
      {y | (goeMatrix (j/(n:ℝ)) p.1,y)∈badFieldSet n j A ε m}
  have hI : Measurable I := measurable_fieldIntegral j t σ
    (badFieldFlat n j A ε m) (measurableSet_badFieldFlat _ _ _ _ _)
  have hInt : ∫⁻ p,I p ∂μ.prod ν ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
    rw [lintegral_prod _ hI.aemeasurable]
    exact hbad n hnb t ht σ ⟨hσ,hσle⟩
  have hMarkov := markov_exponential (μ.prod ν) hI (b := a/2) hInt
  have hrate : a-a/2=a/2 := by ring
  rw [hrate] at hMarkov
  have hDP : (μ.prod ν).real (D ×ˢ (Set.univ : Set (Fin n → ℝ))) ≤
      4*exp (-min 1 (1/(π^2*j))*(n:ℝ)) := by
    rw [measureReal_prod_prod]
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one]
    exact hdet n hnd
  apply measureReal_union_detector (μ.prod ν) _ (D ×ˢ Set.univ) I
    (exp (-(a/2)*(n:ℝ))) _ _ hDP hMarkov
  rintro p ⟨hJ,y,hres,hy⟩ hp
  have hp' : p.1∉D := fun hh=>hp ⟨hh,mem_univ _⟩
  dsimp [I]
  rw [fieldIntegral_eq_localVolume hσ]
  apply hv n hnv _ hJ _ y
    {z | (goeMatrix (j/(n:ℝ)) p.1,z)∈badFieldSet n j A ε m}
  · exact measurableSet_badField_section j A ε m _
  · intro d hd
    exact badField_neighborhood hn0 hj.le hA0.le hε hr.le hrε hrm _ y d hy hd
  · exact not_lt.mp (fun hh=>hp' ⟨y,hh⟩)
  · exact hres
end SKGap
end
end

end OAI
