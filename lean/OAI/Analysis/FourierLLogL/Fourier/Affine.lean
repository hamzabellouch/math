import OAI.Analysis.FourierLLogL.Fourier.Haar
/-! # Changing the size and origin of the top interval -/

open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology Real

namespace OAI

namespace FourierLLogL.Period
noncomputable section

lemma phase_add (u x y : ℝ) :
    phase u (x + y) = phase u x * phase u y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_freq_add (u v x : ℝ) :
    phase (u+v) x = phase u x * phase v x := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_mul_arg (u x y : ℝ) : phase u (x*y) = phase (u*x) y := by
  unfold phase; ring_nf

lemma norm_phase_sub (u x y : ℝ) :
    ‖phase u x - phase u y‖ ≤ |u| * (2*π* |x-y|) := by
  have heq : phase u x - phase u y = (phase u (x-y)-1) * phase u y := by
    rw [sub_mul, ← phase_add, sub_add_cancel, one_mul]
  rw [heq, norm_mul, phase_unimod, mul_one]
  unfold phase
  have HH : ‖Complex.exp (Complex.I * ↑(u * (2*π*(x-y)))) - 1‖ ≤ ‖u*(2*π*(x-y))‖ :=
    Real.norm_exp_I_mul_ofReal_sub_one_le
  refine HH.trans ?_
  simp [Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]

lemma norm_mod {ρ : ℝ → ℝ} (h0 : ∀ x, 0 ≤ ρ x) (u x : ℝ) :
    ‖modρ ρ u x‖ = ρ x := by
  simp only [modρ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 _),
    phase_unimod, mul_one]

lemma coeff_near {ρ : ℝ → ℝ} (hρ : Measurable ρ) (h0 : ∀ x, 0 ≤ ρ x)
    (B : ℝ) (hb : ∀ x, ρ x ≤ B)
    {u v a r x : ℝ} (hx : x ∈ box a r) (hu : |u-v| ≤ 1) :
    ‖coeffH (modρ ρ u) a r - phase (u-v) x * coeffH (modρ ρ v) a r‖ ≤
        density ρ a r * (2 * π * r) := by
  have h1 := hx.1
  have h2 := hx.2
  have hr : 0 < r := by linarith
  let w (t : ℝ) := a+r*t
  have hw : Measurable w := measurable_const.add (measurable_const.mul measurable_id)
  let F (u t : ℝ) := haarH t • modρ ρ u (w t)
  have hF (s : ℝ) : Integrable (F s) μ₁ := by
    apply Integrable.of_bound (Measurable.aestronglyMeasurable
      (measurableH.smul ((measurable_mod hρ s).comp hw))) B
    refine ae_of_all _ fun z => ?_
    change ‖haarH z • modρ ρ s (w z)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, norm_mod h0]
    exact (mul_le_of_le_one_left (h0 _) (H_bound z)).trans (hb _)
  let c := phase (u-v) x
  have ht (t) (ht : t ∈ unitInt) :
      ‖F u t - c * F v t‖ ≤ ρ (w t) * (2 * π * r) := by
    have heq : F u t = phase (u-v) (w t) * F v t := by
      dsimp only [F, modρ]
      nth_rw 1 [← sub_add_cancel u v]

      rw [phase_freq_add]
      simp only [Complex.real_smul]
      ring
    rw [heq, ← sub_mul, norm_mul]
    have hk : |w t - x| ≤ r := by
      rcases ht with ⟨t1,t2⟩
      dsimp [w]
      rw [abs_le]
      constructor <;> nlinarith
    calc
      ‖phase (u-v) (w t) - c‖ * ‖F v t‖ ≤ (2*π*r) * ρ (w t) :=
        mul_le_mul ((norm_phase_sub _ _ _).trans (by
          calc
            _ ≤ 1 * (2*π*r) := by gcongr
            _ = _ := one_mul _)) (by
              rw [show F v t = haarH t • modρ ρ v (w t) from rfl, norm_smul,
                Real.norm_eq_abs, norm_mod h0]
              exact mul_le_of_le_one_left (h0 _) (H_bound _))
          (norm_nonneg _) (by positivity)
      _ = _ := mul_comm _ _
  have hwi : Integrable (fun t => ρ (w t)) μ₁ :=
    Integrable.of_bound ((hρ.comp hw).aestronglyMeasurable) B
      (ae_of_all _ fun t => by
        change ‖ρ (w t)‖ ≤ B
        simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 _)] using hb _)
  change ‖(∫ t, F u t ∂μ₁) - c*(∫ t, F v t ∂μ₁)‖ ≤ (∫ t, ρ (w t) ∂μ₁)*_
  have hhcv : Integrable (fun t => c * F v t) μ₁ := (hF v).const_mul _
  rw [← integral_const_mul, ← integral_mul_const, ← integral_sub (hF u) hhcv]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono_ae ((hF u).sub hhcv).norm (hwi.mul_const _)
      ((ae_restrict_mem measurable_unitInt).mono ht))

lemma cell_unique (a s : ℝ) (hs : 0 < s) (n : ℕ) {k l : ℕ} {x : ℝ}
    (hx : x ∈ box (lft a s n k) (s*side n))
    (hy : x ∈ box (lft a s n l) (s*side n)) : k = l := by
  have hr : 0 < s*side n := mul_pos hs (side_pos _)
  have key : ∀ k l : ℕ, k < l →
      lft a s n k + s*side n ≤ lft a s n l := by
    intro k l h
    have H : ((k:ℝ)+1) ≤ (l:ℝ) := by exact_mod_cast h
    unfold lft
    exact le_trans (by rw [add_mul]; simp [add_assoc] :
      a + (k:ℝ)*(s*side n) + s * side n ≤ a + ((k:ℝ)+1) * (s*side n))
      (add_le_add_right (mul_le_mul_of_nonneg_right H hr.le) _)
  by_contra h
  rcases lt_or_gt_of_ne h with h|h
  · exact (not_lt_of_ge ((key k l h).trans hy.1)) hx.2
  · exact (not_lt_of_ge ((key l k h).trans hx.1)) hy.2

lemma shift_near_unit {ρ : ℝ → ℝ} (hρ : Measurable ρ) (h0 : ∀ x, 0 ≤ ρ x)
    (B : ℝ) (hb : ∀ x, ρ x ≤ B)
    {u v x D : ℝ} (J : ℕ) (hx : usable ρ 0 1 J D x) (hD : 0 ≤ D)
    (hu : |u-v| ≤ 1) :
    ‖shift (modρ ρ u) 0 1 J x‖ ≤ ‖shift (modρ ρ v) 0 1 J x‖ +
      D * (2 * π) * 2 := by
  let c := phase (u-v) x
  have hl (n : ℕ) (hn : n < J) : ‖haarLayer (modρ ρ u) 0 1 n x -
      c * haarLayer (modρ ρ v) 0 1 n x‖ ≤ D * (2 * π) * side n := by
    unfold haarLayer
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    let inP (k : ℕ) := x ∈ box (lft 0 1 n k) (1*side n)
    have hp : 0 < (1:ℝ)*side n := mul_pos zero_lt_one (side_pos n)
    by_cases h : ∃ k ∈ Finset.range (2^n), inP k
    · obtain ⟨k,hk,hxk⟩ := h
      rw [Finset.sum_eq_single k]
      · let a := lft 0 1 n k
        let r := 1 * side n
        change ‖haarG _ • coeffH _ a r - c * (haarG _ • coeffH _ a r)‖ ≤ _
        simp only [Complex.real_smul]
        rw [mul_left_comm c, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine (mul_le_of_le_one_left (norm_nonneg _) (G_bound _)).trans
          ((coeff_near hρ h0 B hb hxk hu).trans ?_)
        have Hk := hx n hn k (Finset.mem_range.mp hk) hxk
        refine (mul_le_mul_of_nonneg_right Hk (show 0 ≤ 2*π*(1*side n) by positivity)).trans ?_
        simp [mul_assoc]
      · intro l hl hlk
        have H : ¬ inP l := fun hh => hlk (cell_unique 0 1 zero_lt_one n hh hxk)
        rw [jump_outside hp H _, jump_outside hp H _]
        simp
      · intro h; exact (h hk).elim
    · rw [Finset.sum_eq_zero]
      · rw [norm_zero]; exact mul_nonneg (by positivity) (side_pos _).le
      · intro k hk
        have H : ¬ inP k := fun hh => h ⟨k,hk,hh⟩
        rw [jump_outside hp H _, jump_outside hp H _]
        simp
  have ht : ‖shift (modρ ρ u) 0 1 J x - c * shift (modρ ρ v) 0 1 J x‖ ≤ D*(2*π)*2 := by
    unfold shift
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun n hn => hl n (Finset.mem_range.mp hn))).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
  have hh := norm_sub_norm_le (shift (modρ ρ u) 0 1 J x) (c * shift (modρ ρ v) 0 1 J x)
  rw [norm_mul, phase_unimod, one_mul] at hh
  linarith

lemma shift_pull (F : ℝ → ℂ) (a s : ℝ) (hs : 0 < s) (J : ℕ) (x : ℝ) :
    shift F a s J (a+s*x) = shift (fun y => F (a+s*y)) 0 1 J x := by
  unfold shift
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
  let l := lft 0 1 n k
  have h1 : lft a s n k = a+s*l := by unfold l lft; ring
  rw [h1]
  unfold jump coeffH
  congr 2
  · dsimp only [l]
    field_simp
    all_goals ring
  all_goals
    simp_rw [show ∀ v : ℝ, a+s*l+(s*side n)*v = a+s*(l+(1*side n)*v) by intro v; ring]
    rfl

lemma shift_scale (F : ℝ → ℂ) (c : ℂ) (a s : ℝ) (J : ℕ) (x : ℝ) :
    shift (fun y => c * F y) a s J x = c * shift F a s J x := by
  unfold shift haarLayer
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
  dsimp only [jump, coeffH]
  simp only [Complex.real_smul]
  simp_rw [mul_left_comm (↑(haarH _)) c, integral_const_mul]
  ring

lemma map_affine (a : ℝ) {s : ℝ} (hs : 0 < s) :
    Measure.map (fun x : ℝ => a+s*x) volume = ENNReal.ofReal (s⁻¹) • volume := by
  rw [show (fun x : ℝ => a+s*x) = ((a+·) ∘ fun x : ℝ => s*x) from rfl]
  rw [← Measure.map_map (by fun_prop) (by fun_prop), Real.map_volume_mul_left hs.ne',
    Measure.map_smul]
  all_goals first
    | simp only [abs_of_pos (inv_pos.mpr hs), map_add_left_eq_self]
    | exact (measurable_const.add measurable_id).aemeasurable

lemma restrict_affine (a : ℝ) {s : ℝ} (hs : 0 < s) (G : Set ℝ) (hG : MeasurableSet G)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in G, f x) =
      ENNReal.ofReal s * ∫⁻ x in (fun y : ℝ => a+s*y) ⁻¹' G, f (a+s*x) := by
  let φ (x : ℝ) := a+s*x
  have hm : Measurable φ := by unfold φ; fun_prop
  have H : Measure.map φ (volume.restrict (φ ⁻¹' G)) =
      ENNReal.ofReal (s⁻¹) • volume.restrict G := by
    rw [← Measure.restrict_map hm hG, map_affine a hs, Measure.restrict_smul]
  change _ = ENNReal.ofReal s * ∫⁻ x in φ ⁻¹' G, f (φ x)
  rw [← lintegral_map hf hm, H, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hs.le, mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one, one_mul]

def shiftD (ρ : ℝ → ℝ) (D : ℝ) (G : Set ℝ) : Prop :=
  ∀ x ∈ G, ∀ (a s : ℝ), 0 < s → s ≤ 1 → x ∈ box a s →
    (∫ y in box a s, ρ y) ≤ D*s

def AffineTreeBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j : ℕ in atTop, ∀ (ρ : ℝ → ℝ),
    Measurable ρ → Periodic ρ 1 → (∀ x, 0 ≤ ρ x) → (∫ x, ρ x ∂μ₁) ≤ 1 →
    (∀ x, ρ x ≤ Real.exp ((2 : ℝ)^j)) →
    ∀ (J : ℕ) (G : Set ℝ), MeasurableSet G → shiftD ρ (((j:ℝ)+1)^3) G →
    ∀ (a s : ℝ), 1/2 ≤ s → s ≤ 1 →
    (∫⁻ x in G, maxShift ρ a s J x) ≤ ENNReal.ofReal (C * (2:ℝ)^j)

lemma cube_eventually :
    ∀ᶠ j : ℕ in atTop, ((j:ℝ)+1)^3 ≤ (8:ℝ) * 2^j := by
  filter_upwards [(tendsto_pow_const_div_const_pow_of_one_lt 3
    (show (1:ℝ)<2 by norm_num)).eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    eventually_ge_atTop 1] with j hj h
  change (j:ℝ)^3/(2:ℝ)^j < 1 at hj
  have hh := (div_lt_one (by positivity)).mp hj
  have H : (j:ℝ) + 1 ≤ 2 * (j:ℝ) := by exact_mod_cast (show j+1 ≤ 2*j by omega)
  calc
    _ ≤ (2*(j:ℝ))^3 := by gcongr
    _ ≤ 8*2^j := by rw [mul_pow]; linarith

theorem UnitTreeBound.affine (hunit : UnitTreeBound) : AffineTreeBound := by
  obtain ⟨C, hC, h⟩ := hunit
  refine ⟨C+8*(2*π)*2, by positivity, ?_⟩
  filter_upwards [h, cube_eventually] with j hj hcj
  intro ρ hρ hp h0 hm hB J G hG hGood a s hs hs'
  let φ (x : ℝ) := a+s*x
  let F (x : ℝ) := ρ (φ x)
  have hs0 : 0 < s := by linarith
  have hmφ : Measurable φ := by unfold φ; fun_prop
  have hF : Measurable F := hρ.comp hmφ
  let B := Real.exp ((2:ℝ)^j)
  let D := ((j:ℝ)+1)^3
  have hD : 0 ≤ D := by unfold D; positivity
  have hF0 (x) : 0 ≤ F x := h0 _
  have hFB (x) : F x ≤ B := hB _
  let Gt := G ∩ box a s
  have hbm : MeasurableSet (box a s) := measurableSet_Ico
  let H := φ ⁻¹' Gt
  have hH : MeasurableSet H := hmφ (hG.inter hbm)
  have hsub : H ⊆ unitInt := by
    intro x hx
    have ⟨h1,h2⟩ := (show φ x ∈ Gt from hx).2
    dsimp only [φ] at *
    constructor <;> nlinarith
  have hmF : (∫ x, F x ∂μ₁) ≤ 2 := by
    change (∫ x, ρ (a+s*x) ∂μ₁) ≤ 2
    rw [mean_translate_scale ρ a hs0, smul_eq_mul, ← div_eq_inv_mul]
    exact (div_le_iff₀ hs0).mpr ((density_short ρ hρ hp h0 B hB hm a s hs').trans (by linarith))
  have hu : ∀ x ∈ H, usable F 0 1 J D x := by
    intro x hx n _ k _ hk
    let l := lft 0 1 n k
    let r := (1:ℝ)*side n
    have hr : 0 < r := mul_pos zero_lt_one (side_pos _)
    have hrs := mul_pos hs0 hr
    change density F l r ≤ _
    have hgd := hGood _ ((show φ x ∈ Gt from hx).1) (φ l) (s*r) hrs
      (by simpa [r] using (show s * side n ≤ 1 from
        (mul_le_mul_of_nonneg_right hs' (side_pos n).le).trans
          (by simpa using side_le n)))
      (show φ x ∈ box (φ l) (s*r) by
        change l ≤ x ∧ x < l+r at hk
        change a+s*l ≤ a+s*x ∧ a+s*x < a+s*l+s*r
        constructor <;> nlinarith [hk.1,hk.2])
    change D*(s*r) ≥ _ at hgd
    change (∫ y, ρ (φ (l+r*y)) ∂μ₁) ≤ _
    simp_rw [show ∀ y, φ (l+r*y) = φ l + (s*r)*y by intro y; unfold φ; ring,
      mean_translate_scale ρ (φ l) hrs]
    rw [smul_eq_mul, ← div_eq_inv_mul, div_le_iff₀ hrs]
    exact hgd
  have htrans (x : ℝ) (hx : x ∈ H) :
      maxShift ρ a s J (φ x) ≤ maxShift F 0 1 J x + ENNReal.ofReal (D*(2*π)*2) := by
    refine iSup_le fun n => ?_
    let u := (n:ℝ)*s
    let k := ⌊u⌋
    have heq (y : ℝ) : modρ ρ (n:ℝ) (a+s*y) = phase n a * modρ F u y := by
      unfold modρ
      rw [phase_add, phase_mul_arg]
      dsimp only [F,φ,u]
      ring
    change ENNReal.ofReal ‖shift _ _ _ _ (a+s*x)‖ ≤ _
    simp_rw [shift_pull _ a s hs0, heq, shift_scale, norm_mul, phase_unimod, one_mul]
    have hnear : |u-(k:ℝ)| ≤ 1 :=
      abs_le.mpr (by have := Int.floor_le u; have := Int.lt_floor_add_one u; dsimp only [k]; constructor <;> linarith)
    refine (ENNReal.ofReal_le_ofReal (shift_near_unit hF hF0 B hFB J (hu _ hx) hD hnear)).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add_left (le_iSup (fun n : ℤ =>
      ENNReal.ofReal ‖shift (modρ F n) 0 1 J x‖) k) _
  let Z := maxShift ρ a s J
  have hZ : Measurable Z :=
    measurable_maxShift_comp hρ measurable_const measurable_const measurable_id _
  have hz (x) (hx : x ∉ box a s) : Z x = 0 := by
    unfold Z maxShift; simp only [shift_outside hs0 hx, norm_zero, ENNReal.ofReal_zero, iSup_const]
  have hiG : (∫⁻ x in G, Z x) = ∫⁻ x in Gt, Z x := by
    rw [← lintegral_indicator hG, ← lintegral_indicator (hG.inter hbm)]
    exact lintegral_congr (fun x => by
      by_cases hx : x ∈ box a s <;> by_cases hy : x ∈ G <;> simp_all only [
        mem_inter_iff, not_false_eq_true, and_self, and_false, false_and,
        indicator_of_mem, indicator_of_notMem])
  change (∫⁻ x in G, Z x) ≤ _
  rw [hiG, restrict_affine a hs0 Gt (hG.inter hbm) Z hZ]
  change ENNReal.ofReal s * ∫⁻ x in H, Z (φ x) ≤ _
  have hmH := hj F hF hF0 hmF hFB J H hH hsub hu
  refine le_trans (b := ∫⁻ x in H, Z (φ x)) (mul_le_of_le_one_left zero_le
    (by simpa using ENNReal.ofReal_le_ofReal hs')) ?_
  refine (lintegral_mono_ae ((ae_restrict_mem hH).mono htrans)).trans ?_
  rw [lintegral_add_right _ measurable_const]
  have Hvol : volume H ≤ 1 := (measure_mono hsub).trans (by simp [unitInt])
  have Hbound : (∫⁻ _ : ℝ in H, ENNReal.ofReal (D*(2*π)*2)) ≤ ENNReal.ofReal (D*(2*π)*2) := by
    simp only [setLIntegral_const]
    exact mul_le_of_le_one_right zero_le Hvol
  refine (add_le_add hmH Hbound).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [add_mul]
  apply add_le_add_right
  calc
    _ ≤ ((8:ℝ)*2^j)*(2*π)*2 := by gcongr
    _ = _ := by ring

end
end FourierLLogL.Period

end OAI
