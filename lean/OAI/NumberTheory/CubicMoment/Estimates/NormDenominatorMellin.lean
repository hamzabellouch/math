import OAI.NumberTheory.CubicMoment.Estimates.WideGramDecay

namespace OAI

/-! The norm denominator in the actual Poisson formula stays in its
Mellin kernel. No real power is inserted into the prime coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

def normDenominatorMultiplier (M : ℝ) (hM : 0 < M) : 𝓢(ℝ,ℂ) :=
  ((wideGramLogBump (2*M) (by positivity)).hasCompactSupport.smul_right
    (f' := fun u => (Real.exp (u/2):ℂ))).toSchwartzMap
    ((wideGramLogBump (2*M) (by positivity)).contDiff.smul
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_id.div_const 2))))

def normDenominatorLogSchwartz (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
    (wideGramLogSchwartz M hM W hW hW' ρ)

def normDenominatorMellinCoefficient (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ t : ℝ) : ℂ :=
  𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ) t

lemma normDenominatorMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    Integrable (normDenominatorMellinCoefficient M hM W hW hW' ρ) :=
  (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integrable

lemma normDenominatorLogSchwartz_apply (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ u : ℝ) :
    normDenominatorLogSchwartz M hM W hW hW' ρ u =
      (Real.exp (u/2):ℂ)*wideGramLogKernel M hM W ρ u := by
  rw [normDenominatorLogSchwartz,SchwartzMap.smulLeftCLM_apply_apply
    (normDenominatorMultiplier M hM).hasTemperateGrowth,wideGramLogSchwartz_apply]
  change ((wideGramLogBump (2*M) (by positivity) u:ℝ) • (Real.exp (u/2):ℂ)) •
    wideGramLogKernel M hM W ρ u = _
  by_cases hu : |u| ≤ 2*M
  · have he : wideGramLogBump (2*M) (by positivity) u = 1 :=
      (wideGramLogBump (2*M) (by positivity)).one_of_mem_closedBall
        (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,wideGramLogBump] using hu)
    rw [he,one_smul,smul_eq_mul]
  · have he : wideGramLogBump M hM u = 0 :=
      (wideGramLogBump M hM).zero_of_le_dist
        (by simpa only [Real.dist_eq,sub_zero,wideGramLogBump] using le_of_not_ge hu)
    simp only [wideGramLogKernel,he,zero_smul,smul_zero,mul_zero]

lemma normDenominatorLogSchwartz_eq_radial (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ u : ℝ} (hρ : 0 ≤ ρ) (hu : |u| ≤ M) :
    normDenominatorLogSchwartz M hM W hW hW' ρ u =
      (Real.exp (u/2):ℂ)*radialDualProfile W (ρ*Real.exp u) := by
  rw [normDenominatorLogSchwartz_apply,wideGramLogKernel_eq_radial M hM W hρ hu]


lemma normDenominatorLogSchwartz_eq_annular (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    normDenominatorLogSchwartz M hM W hW hW' ρ =
      SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
        (wideAnnularLogSchwartz M hM (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ)) := by
  rw [wideAnnularLogSchwartz_eq_wideGramLogSchwartz]
  rfl

lemma normDenominatorFourier_seminorm_uniform (M : ℝ) (hM : 0 < M)
    (F : 𝓢(ℂ,ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c → (1+c)^K * SchwartzMap.seminorm ℝ k n
      (𝓕 (SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
        (wideAnnularLogSchwartz M hM F c))) ≤ C := by
  let f : ℝ → 𝓢(ℝ,ℂ) := fun c => (1+c)^K • wideAnnularLogSchwartz M hM F c
  have hb : Bornology.IsVonNBounded ℝ (f '' Ici 0) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C,hC,hc⟩ := wideAnnularLogSchwartz_seminorm_uniform M hM F i.1 i.2 K
    refine ⟨C+1,by linarith,?_⟩
    intro c hc0
    have hc0' : 0 ≤ c := hc0
    change SchwartzMap.seminorm ℝ i.1 i.2 ((1+c)^K • wideAnnularLogSchwartz M hM F c) < _
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (pow_pos (by linarith [hc0']) _)]
    exact (hc c hc0).trans_lt (by linarith)
  let A : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.fourierTransformCLM ℝ (V := ℝ) (E := ℂ)).comp
      ((SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)).restrictScalars ℝ)
  have hA := hb.image A
  obtain ⟨C,hC,hc⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hA (k,n)
  refine ⟨C,hC,?_⟩
  intro c hc0
  have h := hc (A (f c)) ⟨f c,⟨c,hc0,rfl⟩,rfl⟩
  change SchwartzMap.seminorm ℝ k n (A ((1+c)^K • wideAnnularLogSchwartz M hM F c)) < C at h
  rw [map_smul,map_smul_eq_mul,Real.norm_eq_abs,
    abs_of_pos (pow_pos (by linarith) _)] at h
  exact h.le

theorem normDenominatorMellinCoefficient_pointwise_rapidDecay (M : ℝ) (hM : 0 < M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ t : ℝ,
      (1+ρ)^A * ‖t‖^B * ‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖ ≤ C := by
  obtain ⟨C,hC,hc⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') B 0 (2*A)
  refine ⟨C,hC,?_⟩
  intro ρ hρ t
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_nonneg ρ]
  have hb := SchwartzMap.le_seminorm ℝ B 0
    (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)) t
  simp only [norm_iteratedFDeriv_zero] at hb
  have h := hc (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [← normDenominatorLogSchwartz_eq_annular] at h
  calc
    _ = (1+ρ)^A * (‖t‖^B * ‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) := by ring
    _ ≤ (1+Real.sqrt ρ)^(2*A) * SchwartzMap.seminorm ℝ B 0
        (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)) :=
      mul_le_mul hs hb (by positivity) (by positivity)
    _ ≤ C := h

end CubicFirstMoment

end

end OAI
