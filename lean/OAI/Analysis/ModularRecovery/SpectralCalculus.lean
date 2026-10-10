import OAI.Analysis.ModularRecovery.Model

namespace OAI

/-! Unitary spectral characters, spectral support, and half-exponential bounds. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section

namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] lemma spectralCharacter_apply (t u : ℝ) :
    spectralCharacter t u = Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) := rfl

@[simp] lemma spectralCharacter_zero : spectralCharacter 0 = 1 := by
  ext u
  simp

lemma spectralCharacter_add (t r : ℝ) :
    spectralCharacter (t + r) = spectralCharacter t * spectralCharacter r := by
  ext u
  simp [add_mul, Complex.exp_add]

@[simp] lemma spectralCharacter_norm (t u : ℝ) : ‖spectralCharacter t u‖ = 1 := by
  simp [spectralCharacter, Complex.norm_exp]

lemma spectralCharacter_star (t : ℝ) : star (spectralCharacter t) = spectralCharacter (-t) := by
  ext u
  simp [← Complex.exp_conj]

lemma spectralCharacter_sub_norm_le (t r u : ℝ) :
    ‖spectralCharacter t u - spectralCharacter r u‖ ≤ 2 * |t - r| * |u| := by
  change ‖Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) -
    Complex.exp (((r * u : ℝ) : ℂ) * Complex.I)‖ ≤ _
  have h := Complex.norm_le_abs_re_add_abs_im
    (Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((r * u : ℝ) : ℂ) * Complex.I))
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_re, Complex.exp_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    mul_one, add_zero, Real.exp_zero, one_mul] at h
  have hc := Real.abs_cos_sub_cos_le (t * u) (r * u)
  have hs := Real.abs_sin_sub_sin_le (t * u) (r * u)
  rw [← sub_mul, abs_mul] at hc hs
  linarith

namespace RealSpectralCalculus

@[simp] lemma unitary_zero (D : RealSpectralCalculus H) : D.unitary 0 = 1 := by
  simp [unitary]

lemma unitary_add (D : RealSpectralCalculus H) (t r : ℝ) :
    D.unitary (t + r) = D.unitary t * D.unitary r := by
  simp [unitary, spectralCharacter_add]

@[simp] lemma unitary_star (D : RealSpectralCalculus H) (t : ℝ) :
    star (D.unitary t) = D.unitary (-t) := by
  simp [unitary, ← map_star, spectralCharacter_star]

@[simp] lemma unitary_neg_mul (D : RealSpectralCalculus H) (t : ℝ) :
    D.unitary (-t) * D.unitary t = 1 := by
  rw [← unitary_add, neg_add_cancel, unitary_zero]

@[simp] lemma unitary_mul_neg (D : RealSpectralCalculus H) (t : ℝ) :
    D.unitary t * D.unitary (-t) = 1 := by
  rw [← unitary_add, add_neg_cancel, unitary_zero]

lemma norm_unitary_apply (D : RealSpectralCalculus H) (t : ℝ) (h : H) :
    ‖D.unitary t h‖ = ‖h‖ := by
  have he : inner ℂ (D.unitary t h) (D.unitary t h) = inner ℂ h h := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ h ((star (D.unitary t) * D.unitary t) h) = _
    rw [unitary_star, unitary_neg_mul]
    rfl
  have he' : ‖D.unitary t h‖ ^ 2 = ‖h‖ ^ 2 := by
    simpa only [← norm_sq_eq_re_inner] using congrArg (@RCLike.re ℂ _) he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he'

lemma norm_calculus_le (D : RealSpectralCalculus H) (f : BoundedContinuousFunction ℝ ℂ) :
    ‖D.calculus f‖ ≤ ‖f‖ := NonUnitalStarAlgHom.norm_apply_le D.calculus f

def calculusCLM (D : RealSpectralCalculus H) :
    BoundedContinuousFunction ℝ ℂ →L[ℂ] (H →L[ℂ] H) :=
  D.calculus.toAlgHom.toLinearMap.mkContinuous 1 (by
    intro f
    change ‖D.calculus f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using D.norm_calculus_le f)

@[simp] lemma calculusCLM_apply (D : RealSpectralCalculus H)
    (f : BoundedContinuousFunction ℝ ℂ) : D.calculusCLM f = D.calculus f := rfl

lemma norm_calculus_apply_le (D : RealSpectralCalculus H)
    (f : BoundedContinuousFunction ℝ ℂ) (h : H) :
    ‖D.calculus f h‖ ≤ ‖f‖ * ‖h‖ :=
  (D.calculus f).le_opNorm h |>.trans (mul_le_mul_of_nonneg_right (D.norm_calculus_le f)
    (norm_nonneg _))

lemma HasSpectralSupport.zero (D : RealSpectralCalculus H) (I : Set ℝ) :
    D.HasSpectralSupport I 0 := by
  intro f hf
  exact map_zero _

lemma HasSpectralSupport.mono {D : RealSpectralCalculus H} {I J : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) (hIJ : I ⊆ J) : D.HasSpectralSupport J h := by
  intro f hf
  exact hh f (fun u hu => hf u (hIJ hu))

lemma HasSpectralSupport.add {D : RealSpectralCalculus H} {I : Set ℝ} {h k : H}
    (hh : D.HasSpectralSupport I h) (hk : D.HasSpectralSupport I k) :
    D.HasSpectralSupport I (h + k) := by
  intro f hf
  simp [map_add, hh f hf, hk f hf]

lemma HasSpectralSupport.smul {D : RealSpectralCalculus H} {I : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) (c : ℂ) : D.HasSpectralSupport I (c • h) := by
  intro f hf
  simp [map_smul, hh f hf]

lemma HasSpectralSupport.calculus {D : RealSpectralCalculus H} {I : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) (g : BoundedContinuousFunction ℝ ℂ) :
    D.HasSpectralSupport I (D.calculus g h) := by
  intro f hf
  change (D.calculus f * D.calculus g) h = 0
  rw [← map_mul]
  exact hh (f * g) (by intro u hu; simp [hf u hu])

lemma HasSpectralSupport.unitary {D : RealSpectralCalculus H} {I : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) (t : ℝ) : D.HasSpectralSupport I (D.unitary t h) :=
  hh.calculus (spectralCharacter t)

lemma HasSpectralSupport.congr {D : RealSpectralCalculus H} {I : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) {f g : BoundedContinuousFunction ℝ ℂ}
    (heq : ∀ u ∈ I, f u = g u) : D.calculus f h = D.calculus g h := by
  have hz := hh (f - g) (by intro u hu; simp [heq u hu])
  simpa only [map_sub, sub_apply, sub_eq_zero] using hz

lemma HasSpectralSupport.fixed {D : RealSpectralCalculus H} {I : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) {f : BoundedContinuousFunction ℝ ℂ}
    (heq : ∀ u ∈ I, f u = 1) : D.calculus f h = h := by
  simpa using hh.congr (g := 1) heq

lemma support_calculus_apply (D : RealSpectralCalculus H) (I : Set ℝ)
    (f : BoundedContinuousFunction ℝ ℂ) (hf : ∀ u ∉ I, f u = 0) (h : H) :
    D.HasSpectralSupport I (D.calculus f h) := by
  intro g hg
  change (D.calculus g * D.calculus f) h = 0
  rw [← map_mul]
  have heq : g * f = 0 := by
    ext u
    by_cases hu : u ∈ I
    · simp [hg u hu]
    · simp [hf u hu]
  simp [heq]

lemma continuous_character_mul (f : BoundedContinuousFunction ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ)) :
    Continuous (fun t : ℝ => spectralCharacter t * f) := by
  obtain ⟨R, hR, hRn⟩ := hf.isCompact.isBounded.exists_pos_norm_le
  have hl : LipschitzWith ⟨2 * R * ‖f‖, by positivity⟩
      (fun t : ℝ => spectralCharacter t * f) := by
    apply LipschitzWith.of_dist_le_mul
    intro t r
    rw [dist_eq_norm]
    change ‖spectralCharacter t * f - spectralCharacter r * f‖ ≤
      (2 * R * ‖f‖) * dist t r
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro u
    change ‖spectralCharacter t u * f u - spectralCharacter r u * f u‖ ≤ _
    rw [← sub_mul, norm_mul]
    by_cases hu : u ∈ tsupport (f : ℝ → ℂ)
    · have hu' : |u| ≤ R := by simpa only [Real.norm_eq_abs] using hRn u hu
      calc
        _ ≤ (2 * |t - r| * R) * ‖f‖ := by
          apply mul_le_mul
          · exact (spectralCharacter_sub_norm_le t r u).trans
              (mul_le_mul_of_nonneg_left hu' (by positivity))
          · exact f.norm_coe_le_norm u
          · positivity
          · positivity
        _ = (2 * R * ‖f‖) * dist t r := by rw [Real.dist_eq]; ring
    · rw [image_eq_zero_of_notMem_tsupport hu, norm_zero, mul_zero]
      positivity
  exact hl.continuous

lemma continuous_unitary_apply_compact (D : RealSpectralCalculus H)
    (f : BoundedContinuousFunction ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) (k : H) :
    Continuous (fun t : ℝ => D.unitary t (D.calculus f k)) := by
  have h : Continuous (fun t : ℝ => D.calculus (spectralCharacter t * f) k) :=
    (D.calculusCLM.continuous.comp (continuous_character_mul f hf)).clm_apply continuous_const
  simpa only [map_mul, mul_apply_eq_comp, unitary] using h

lemma continuous_unitary_apply (D : RealSpectralCalculus H) (h : H) :
    Continuous (fun t : ℝ => D.unitary t h) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨v, ⟨f, hf, k, rfl⟩, hv⟩ := D.nondegenerate.exists_dist_lt h (by positivity : 0 < ε / 3)
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp
    (D.continuous_unitary_apply_compact f hf k).continuousAt (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun {r} hr => ?_⟩
  have hes (q : ℝ) : dist (D.unitary q h) (D.unitary q (D.calculus f k)) < ε / 3 := by
    simpa only [dist_eq_norm, ← map_sub, D.norm_unitary_apply] using hv
  have ht := dist_triangle4 (D.unitary r h) (D.unitary r (D.calculus f k))
    (D.unitary t (D.calculus f k)) (D.unitary t h)
  have htr := hes t
  rw [dist_comm] at htr
  linarith [hes r, hd hr]

lemma continuous_unitary_apply_varying (D : RealSpectralCalculus H)
    {F : ℝ → H} (hF : Continuous F) :
    Continuous (fun t => D.unitary t (F t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro eps heps
  obtain ⟨d₁, hd₁, h₁⟩ := Metric.continuousAt_iff.mp hF.continuousAt
    (eps / 2) (by positivity)
  obtain ⟨d₂, hd₂, h₂⟩ := Metric.continuousAt_iff.mp
    (D.continuous_unitary_apply (F t)).continuousAt (eps / 2) (by positivity)
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, fun {r} hr => ?_⟩
  have hdist : dist (D.unitary r (F r)) (D.unitary r (F t)) = dist (F r) (F t) := by
    simp only [dist_eq_norm, ← map_sub, D.norm_unitary_apply]
  have hv := dist_triangle (D.unitary r (F r)) (D.unitary r (F t)) (D.unitary t (F t))
  rw [hdist] at hv
  linarith [h₁ (lt_of_lt_of_le hr (min_le_left _ _)),
    h₂ (lt_of_lt_of_le hr (min_le_right _ _))]

def upperHalfExponential (b : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (Real.exp (min b u / 2) : ℂ))
    (by fun_prop) (Real.exp (b / 2)) (by
      intro u
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)))

lemma norm_upperHalfExponential_le (b : ℝ) :
    ‖upperHalfExponential b‖ ≤ Real.exp (b / 2) := by
  apply (BoundedContinuousFunction.norm_le (Real.exp_pos _).le).mpr
  intro u
  change ‖(Real.exp (min b u / 2) : ℂ)‖ ≤ _
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))

lemma HasSpectralSupport.halfGraph {D : RealSpectralCalculus H} {I : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) {b : ℝ} (hb : ∀ u ∈ I, u ≤ b) :
    (h, D.calculus (upperHalfExponential b) h) ∈ D.halfGraph := by
  obtain ⟨N, hN⟩ := exists_nat_gt b
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  apply (hh.congr ?_).symm
  intro u hu
  have hun : u ≤ (n : ℝ) := (hb u hu).trans (hN.le.trans (Nat.cast_le.mpr hn))
  change (Real.exp (min (n : ℝ) u / 2) : ℂ) = (Real.exp (min b u / 2) : ℂ)
  rw [min_eq_right hun, min_eq_right (hb u hu)]

lemma norm_halfGraph_le {D : RealSpectralCalculus H} {I : Set ℝ} {h q : H}
    (hh : D.HasSpectralSupport I h) {b : ℝ} (hb : ∀ u ∈ I, u ≤ b)
    (hq : (h, q) ∈ D.halfGraph) : ‖q‖ ≤ Real.exp (b / 2) * ‖h‖ := by
  have he : q = D.calculus (upperHalfExponential b) h :=
    tendsto_nhds_unique hq (hh.halfGraph hb)
  rw [he]
  exact (D.norm_calculus_apply_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_upperHalfExponential_le b) (norm_nonneg _))

end RealSpectralCalculus

end BoundedRecovery

end

end OAI
