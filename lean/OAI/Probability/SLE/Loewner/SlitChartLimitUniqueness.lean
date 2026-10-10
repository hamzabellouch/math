import OAI.Probability.SLE.Loewner.InitialLimitInverse
import OAI.Probability.SLE.Loewner.VerticalDisplacementLimit

namespace OAI

/-! Identification of a terminal inverse-chart limit with the normalized
static chart. Only the preserved height and far-field bounds are used. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma SimpleSlitChart.eq_inverse_of_vertical_bounds {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hb : BijOn F upperHalfPlane (upperHalfPlane \ range p))
    (him : ∀ z∈upperHalfPlane, z.im≤(F z).im)
    {C R : ℝ} (hR : 0<R) (hp : ∀ u : unitInterval, ‖p u‖≤R)
    (hbound : ∀ z∈upperHalfPlane, ‖F z-z‖≤C/z.im)
    (hfar : ∀ z : ℂ, 2*R≤z.im → ‖invFunOn F upperHalfPlane z-z‖≤3*R^2/z.im) :
    EqOn F P.inverse upperHalfPlane := by
  let G := invFunOn F upperHalfPlane
  have hG : DifferentiableOn ℂ G (upperHalfPlane \ range p) := by
    have hh := hF.invFunOn isOpen_upperHalfPlane hb.injOn
    rw [hb.image_eq] at hh
    exact hh
  have hGm : MapsTo G (upperHalfPlane \ range p) upperHalfPlane := hb.surjOn.mapsTo_invFunOn
  have hGF : ∀ z∈upperHalfPlane, G (F z)=z := fun _ hz => hb.injOn.leftInvOn_invFunOn hz
  let A := P.forward ∘ F
  let B := G ∘ P.inverse
  have hA : DifferentiableOn ℂ A upperHalfPlane := P.forward_differentiable.comp hF hb.mapsTo
  have hB : DifferentiableOn ℂ B upperHalfPlane := hG.comp P.inverse_differentiable P.inverse_mapsTo
  have hAm : MapsTo A upperHalfPlane upperHalfPlane := P.bijOn.mapsTo.comp hb.mapsTo
  have hBm : MapsTo B upperHalfPlane upperHalfPlane := hGm.comp P.inverse_mapsTo
  have hBA : ∀ z∈upperHalfPlane, B (A z)=z := by
    intro z hz
    dsimp only [A,B,Function.comp_apply]
    rw [P.left_inverse _ (hb.mapsTo hz),hGF z hz]
  have hAbound {z : ℂ} (hz : 2*R≤z.im) : ‖A z-z‖≤(3*R^2+C)/z.im := by
    have hy : 0<z.im := by linarith
    have hf := him z hy
    have hfpos : 0<(F z).im := hy.trans_le hf
    have hpf := P.far_height_displacement hR hp (hz.trans hf)
    calc
      ‖A z-z‖ ≤ ‖P.forward (F z)-F z‖+‖F z-z‖ := by
        simpa only [A,Function.comp_apply,dist_eq_norm] using
          dist_triangle (P.forward (F z)) (F z) z
      _ ≤ 3*R^2/(F z).im+C/z.im := add_le_add hpf (hbound z hy)
      _ ≤ 3*R^2/z.im+C/z.im := add_le_add
        (div_le_div_of_nonneg_left (by positivity) hy hf) le_rfl
      _ = (3*R^2+C)/z.im := (add_div _ _ _).symm
  have hBbound {z : ℂ} (hz : 2*R≤z.im) : ‖B z-z‖≤(3*R^2+P.capacity)/z.im := by
    have hy : 0<z.im := by linarith
    have hf := P.inverse_im_ge hy
    have hgf := hfar (P.inverse z) (hz.trans hf)
    calc
      ‖B z-z‖ ≤ ‖G (P.inverse z)-P.inverse z‖+‖P.inverse z-z‖ := by
        simpa only [B,Function.comp_apply,dist_eq_norm] using
          dist_triangle (G (P.inverse z)) (P.inverse z) z
      _ ≤ 3*R^2/(P.inverse z).im+P.capacity/z.im :=
        add_le_add hgf (P.inverse_displacement hy)
      _ ≤ 3*R^2/z.im+P.capacity/z.im := add_le_add
        (div_le_div_of_nonneg_left (by positivity) hy hf) le_rfl
      _ = (3*R^2+P.capacity)/z.im := (add_div _ _ _).symm
  have hev : ∀ᶠ n : ℕ in atTop, 2*R≤(verticalInfinity n).im := by
    simpa only [verticalInfinity,mul_im,ofReal_re,I_im,mul_one,ofReal_im,I_re,mul_zero,add_zero]
      using verticalHeights_tendsto.eventually (eventually_ge_atTop (2*R))
  have hA0 : Tendsto (fun n : ℕ => A (verticalInfinity n)-verticalInfinity n) atTop (𝓝 0) := by
    apply vertical_displacement_zero_of_bound
    filter_upwards [hev] with n hn
    simpa only [verticalInfinity,mul_im,ofReal_re,I_im,mul_one,ofReal_im,I_re,mul_zero,add_zero]
      using hAbound hn
  have hB0 : Tendsto (fun n : ℕ => B (verticalInfinity n)-verticalInfinity n) atTop (𝓝 0) := by
    apply vertical_displacement_zero_of_bound
    filter_upwards [hev] with n hn
    simpa only [verticalInfinity,mul_im,ofReal_re,I_im,mul_one,ofReal_im,I_re,mul_zero,add_zero]
      using hBbound hn
  have hAid := vertical_halfPlane_left_inverse_eq_id hA hB hAm hBm hBA
    (vertical_normalization_of_displacement hA0) (vertical_normalization_of_displacement hB0) hA0
  intro z hz
  have he := P.left_inverse (F z) (hb.mapsTo hz)
  rw [show P.forward (F z)=z from hAid hz] at he
  exact he.symm

theorem initialInverse_limit_eq_final (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (P : SimpleSlitChart p) {t : ℕ → unitInterval} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) (ht : Tendsto t atTop (𝓝 1)) :
    EqOn F P.inverse upperHalfPlane := by
  obtain ⟨R0,hR0⟩ := (isCompact_range p.continuous).isBounded.exists_norm_le
  let R := max R0 1
  have hR : 0<R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hp (u : unitInterval) : ‖p u‖≤R := (hR0 _ (mem_range_self u)).trans (le_max_left _ _)
  exact P.eq_inverse_of_vertical_bounds hF
    (initialInverse_limit_bijOn_final p hi h0 hH hF hlim ht)
    (fun _ hz => initialInverse_limit_im_ge p hi h0 hH hlim hz)
    hR hp
    (fun _ hz => initialInverse_limit_uniform_displacement p hi h0 hH hlim hz)
    (fun _ hz => initialInverse_limit_inverse_far_height p hi h0 hH hF hlim hR hp hz)

end SLEExactGauge

end

end OAI
