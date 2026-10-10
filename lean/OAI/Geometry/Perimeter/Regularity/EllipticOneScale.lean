import OAI.Geometry.Perimeter.Regularity.EllipticHarmonicBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem weak_curl_harmonic_comparison_norm {U : Set (Euc n)} {u e : VectorL2 n}
    (hu : CurlFreeLpOn u U)
    (h : ∀ φ : SmoothLocalTest U, (∫ x, inner ℝ (u x) (gradient φ.val x))=
      ∫ x, inner ℝ (e x) (gradient φ.val x)) :
    ∃ g : VectorL2 n, DivFreeLpOn g U ∧ CurlFreeLpOn g U ∧ ‖u-g‖≤‖e‖ ∧ ‖g‖≤‖u‖ := by
  let K := testGradientSpace U
  let g := u-K.starProjection u
  have hmem : u-g∈K := by
    dsimp [g]
    rw [sub_sub_cancel]
    exact (K.orthogonalProjectionOnto u).property
  have hcf := hu.sub (testGradientSpace_curlFree hmem)
  refine ⟨g,orthogonal_testGradient_divFree (K.sub_starProjection_mem_orthogonal u),?_,?_,?_⟩
  · simpa only [sub_sub_cancel] using hcf
  · exact harmonic_projection_error_le K
      (testGradient_pairing_ext (fun φ ↦ by simpa only [testGradient_inner] using h φ))
  · rw [show g=Kᗮ.starProjection u from (K.starProjection_orthogonal_val u).symm]
    exact Kᗮ.norm_starProjection_apply_le u

theorem vectorLp_integral_sq (u : VectorL2 n) : (∫ x, ‖u x‖^2)=‖u‖^2 := by
  rw [←real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem vectorLp_integrable_sq (u : VectorL2 n) : Integrable (fun x ↦ ‖u x‖^2) volume := by
  simpa only [real_inner_self_eq_norm_sq] using (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) u u)

theorem vectorLp_setIntegral_sq_le (u : VectorL2 n) (s : Set (Euc n)) :
    (∫ x in s, ‖u x‖^2)≤‖u‖^2 := by
  rw [←vectorLp_integral_sq]
  exact setIntegral_le_integral (vectorLp_integrable_sq u) (ae_of_all _ fun _ ↦ sq_nonneg _)

theorem norm_sub_sq_le_two {V : Type*} [SeminormedAddCommGroup V] (x y z : V) :
    ‖x-z‖^2≤2*‖x-y‖^2+2*‖y-z‖^2 := by
  have h := norm_add_le (x-y) (y-z)
  rw [sub_add_sub_cancel] at h
  have h' : ‖x-z‖^2≤(‖x-y‖+‖y-z‖)^2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖x-y‖-‖y-z‖)]

theorem weak_field_one_scale (hn : 0<n) :
    ∃ C : ℝ, 0≤C ∧ ∀ u e : VectorL2 n,
      CurlFreeLpOn u (Metric.ball 0 1) →
      (∀ φ : SmoothLocalTest (Metric.ball 0 1),
        (∫ x, inner ℝ (u x) (gradient φ.val x))=∫ x, inner ℝ (e x) (gradient φ.val x)) →
      ∃ q : Euc n, ‖q‖≤C*‖u‖ ∧ ∀ θ : ℝ, θ≤1/2 →
        (∫ x in Metric.ball 0 θ, ‖u x-q‖^2) ≤
          2*‖e‖^2+2*(C*‖u‖*θ)^2*volume.real (Metric.ball (0:Euc n) θ) := by
  obtain ⟨C,hC,hB⟩ := harmonic_field_representative_bounds hn
  refine ⟨C,hC,fun u e hu h ↦ ?_⟩
  obtain ⟨g,hd,hc,he,hgn⟩ := weak_curl_harmonic_comparison_norm hu h
  obtain ⟨G,hG,hGe,hG0,hGL⟩ := hB g hd hc
  refine ⟨G 0,(hG0 0).trans (mul_le_mul_of_nonneg_left hgn hC),fun θ hθ ↦ ?_⟩
  by_cases hθ0 : 0<θ
  swap
  · have hz : Metric.ball (0:Euc n) θ=∅ := Metric.ball_eq_empty.mpr (le_of_not_gt hθ0)
    simp only [hz,Measure.restrict_empty,integral_zero_measure,measureReal_empty,mul_zero,add_zero]
    positivity
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0:Euc n) θ)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hiug : Integrable (fun x ↦ ‖u x-g x‖^2) volume :=
    (vectorLp_integrable_sq (u-g)).congr (by filter_upwards [Lp.coeFn_sub u g] with x hx; rw [hx]; rfl)
  have hiu : IntegrableOn (fun x ↦ ‖u x-G 0‖^2) (Metric.ball 0 θ) volume := by
    have hcst : MemLp (fun _ : Euc n ↦ G 0) 2 (volume.restrict (Metric.ball 0 θ)) := memLp_const _
    exact (((Lp.memLp u).mono_measure Measure.restrict_le_self).sub hcst).integrable_norm_pow (by norm_num)
  have hib : IntegrableOn (fun x ↦ 2*‖u x-g x‖^2+2*(C*‖u‖*θ)^2) (Metric.ball 0 θ) volume :=
    (hiug.integrableOn.const_mul 2).add (integrable_const _)
  have hb : ∀ᵐ x ∂volume.restrict (Metric.ball (0:Euc n) θ),
      ‖u x-G 0‖^2≤2*‖u x-g x‖^2+2*(C*‖u‖*θ)^2 := by
    filter_upwards [ae_restrict_of_ae (ae_restrict_iff' measurableSet_ball |>.mp hGe),
      ae_restrict_mem measurableSet_ball] with x hx hxB
    have hxH : x∈Metric.ball (0:Euc n) (1/2) := Metric.ball_subset_ball hθ hxB
    have hnorm : ‖g x-G 0‖≤C*‖u‖*θ := by
      rw [hx hxH]
      have hb' := hGL x 0
      rw [sub_zero] at hb'
      exact hb'.trans (mul_le_mul (mul_le_mul_of_nonneg_left hgn hC)
        (by exact (show ‖x‖<θ by simpa only [Metric.mem_ball,dist_zero_right] using hxB).le)
        (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)))
    exact (norm_sub_sq_le_two (u x) (g x) (G 0)).trans (by
      have hh := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      linarith)
  calc
    _ ≤ ∫ x in Metric.ball 0 θ, 2*‖u x-g x‖^2+2*(C*‖u‖*θ)^2 := integral_mono_ae hiu hib hb
    _ = 2*(∫ x in Metric.ball 0 θ, ‖u x-g x‖^2)+
        2*(C*‖u‖*θ)^2*volume.real (Metric.ball (0:Euc n) θ) := by
      rw [integral_add (hiug.integrableOn.const_mul 2) (integrable_const _),integral_const_mul,integral_const]
      simp only [smul_eq_mul,measureReal_def,Measure.restrict_apply_univ]; ring
    _ ≤ _ := by
      have hsq : (∫ x in Metric.ball 0 θ, ‖u x-g x‖^2)≤‖u-g‖^2 := by
        have heq : (∫ x in Metric.ball 0 θ, ‖u x-g x‖^2)=∫ x in Metric.ball 0 θ, ‖(u-g) x‖^2 :=
          integral_congr_ae (ae_restrict_of_ae (by filter_upwards [Lp.coeFn_sub u g] with x hx; rw [hx]; rfl))
        rw [heq]
        exact vectorLp_setIntegral_sq_le _ _
      have hsq' := pow_le_pow_left₀ (norm_nonneg _) he 2
      linarith

end RPISingularHarnack

end

end OAI
