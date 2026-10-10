import Mathlib
import OAI.Probability.SKGap.Localization.LocalVolumeChange

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set Filter
open scoped BigOperators ENNReal NNReal

lemma nonnegative_continuous_small {f : ℝ → ℝ} (hf : ContinuousAt f 0) (hzero : f 0=0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ,0 < δ ∧ ∀ x : ℝ,0 ≤ x → x < δ → f x < ε := by
  have hh : ∀ᶠ x in nhds (0:ℝ), f x < ε :=
    hf.tendsto.eventually_lt_const (by rw [hzero]; exact hε)
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨δ,hδ,fun x hx hxd => hnear ?_⟩
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hx] using hxd

lemma absorb_three_quarters_exp {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ,N ≤ n →
      exp (-ε*(n:ℝ)) ≤ (3/4:ℝ)*exp (-(3*ε/4)*(n:ℝ)) := by
  obtain ⟨N,hN⟩ := exists_nat_ge (4/ε)
  refine ⟨max N 1,by omega,?_⟩
  intro n hn
  have hnn : 4/ε ≤ (n:ℝ) := hN.trans (by exact_mod_cast (le_trans (le_max_left N 1) hn))
  have hx : 1 ≤ ε*(n:ℝ)/4 := by
    have hh := (div_le_iff₀ hε).mp hnn
    nlinarith
  have he : exp (-(ε*(n:ℝ)/4)) ≤ 3/4 := by
    rw [exp_neg,inv_eq_one_div,div_le_iff₀ (exp_pos _)]
    have hh := add_one_le_exp (ε*(n:ℝ)/4)
    nlinarith only [hh,hx]
  have hsplit : -ε*(n:ℝ)=-(ε*(n:ℝ)/4)+(-(3*ε/4)*(n:ℝ)) := by ring
  rw [hsplit,exp_add]
  exact mul_le_mul_of_nonneg_right he (exp_pos _).le

theorem local_volume_uniform {j K r ε : ℝ} (hj : 0 ≤ j) (hK : 0 ≤ K)
    (hr : 0 < r) (hε : 0 < ε) :
    ∃ ε₁ : ℝ,0 < ε₁ ∧ ∀ γ : ℝ,0 < γ →
    ∃ σ₀ : ℝ,0 < σ₀ ∧ ∀ σ : ℝ,0 < σ → σ < σ₀ →
    ∃ ρ : ℝ,0 < ρ ∧ ∃ N : ℕ,0 < N ∧ ∀ n,N ≤ n →
    ∀ J : Matrix (Fin n) (Fin n) ℝ,
    (∀ z : Field n,vectorNorm (J*ᵥz) ≤ K*vectorNorm z) →
    ∀ h y : Field n,∀ E : Set (Field n),MeasurableSet E →
    (∀ d : Field n,vectorNorm d ≤ r*sqrt (n:ℝ) → y+d ∈ E) →
    log ((fieldJacobian j J y)ᵀ*(fieldJacobian j J y)+γ • 1).det ≤
      (n:ℝ)*(j*varianceAverage y^2+ε₁) →
    vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ) →
    ENNReal.ofReal (exp (-ε*(n:ℝ))) ≤ localVolume j σ J h E := by
  let η := ε/16
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨ε/4,by positivity,?_⟩
  intro γ hγ
  let noise : ℝ → ℝ := fun σ => (1+η⁻¹)*(6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ
  have hncont : ContinuousAt noise 0 := by dsimp [noise]; fun_prop
  have hnzero : noise 0=0 := by simp [noise]
  obtain ⟨a,ha,hasmall⟩ := nonnegative_continuous_small hncont hnzero (show 0 < ε/4 by positivity)
  refine ⟨min a (r*sqrt γ/2),lt_min ha (by positivity),?_⟩
  intro σ hσ hσ₀
  have hsnoise : noise σ < ε/4 := hasmall σ hσ.le (lt_of_lt_of_le hσ₀ (min_le_left _ _))
  have hsr : 2*σ/sqrt γ ≤ r := by
    apply (div_le_iff₀ (sqrt_pos.mpr hγ)).mpr
    have hh := lt_of_lt_of_le hσ₀ (min_le_right _ _)
    linarith
  let residual : ℝ → ℝ := fun ρ => (1+η⁻¹)*ρ^2/σ^2
  have hrcont : ContinuousAt residual 0 := by dsimp [residual]; fun_prop
  have hrzero : residual 0=0 := by simp [residual]
  obtain ⟨b,hb,hbsmall⟩ := nonnegative_continuous_small hrcont hrzero (show 0 < ε/4 by positivity)
  obtain ⟨N,hN,habsorb⟩ := absorb_three_quarters_exp hε
  refine ⟨b/2,by positivity,N,hN,?_⟩
  intro n hn J hJ h y E hE hball hdet hres
  have hresmall : residual (b/2) < ε/4 := hbsmall _ (by positivity) (by linarith)
  have hloss : (ε/4)/2+2*η+
      (1+η⁻¹)*((b/2)^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ ≤ 3*ε/4 := by
    dsimp [noise] at hsnoise
    dsimp [residual] at hresmall
    dsimp [η] at *
    ring_nf at hsnoise hresmall ⊢
    linarith only [hsnoise,hresmall]
  have hnn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  calc
    _ ≤ ENNReal.ofReal ((3/4:ℝ)*exp (-(3*ε/4)*(n:ℝ))) :=
      ENNReal.ofReal_le_ofReal (habsorb n hn)
    _ ≤ ENNReal.ofReal ((3/4:ℝ)*exp (-(n:ℝ)*((ε/4)/2+2*η+
      (1+η⁻¹)*((b/2)^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
      nlinarith only [mul_le_mul_of_nonneg_left hloss hnn]
    _ ≤ _ := local_volume_quantitative (hN.trans_le hn) hj hK hγ hσ hη (by positivity)
      J hJ h y hE hball hsr hdet hres

end SKGap
end
end

end OAI
