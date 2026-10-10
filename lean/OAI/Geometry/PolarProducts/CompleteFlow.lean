import OAI.Geometry.PolarProducts.LocalODE

namespace OAI

universe u7 u8 u9 u10 u11 u12 u13

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u7} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

def variation {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) (t : ℝ) : E :=
  v + h • ∫ s in 0..t,
    fderiv ℝ V (extend (trajectory hV h hh x) s) (extend (tangentPath hV h hh x v) s)

theorem variation_coe {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) (t : Time) :
    variation hV h hh x v t = tangentPath hV h hh x v t :=
  (congrArg (fun u : C(Time, E) => u t) (tangentPath_eq hV hVs h hh x v)).symm

omit [ProperSpace E] in
@[simp] theorem variation_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) : variation hV h hh x v 0 = v := by
  simp [variation]

omit [ProperSpace E] in
theorem continuous_variation {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) :
    Continuous (variation hV h hh x v) := by
  have hc := ((hVs.continuous_fderiv (by simp)).comp
    (continuous_extend (trajectory hV h hh x))).clm_apply
      (continuous_extend (tangentPath hV h hh x v))
  exact continuous_const.add
    ((intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).const_smul h)

theorem hasDerivAt_variation {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) (t : Time) :
    HasDerivAt (variation hV h hh x v)
      (h • fderiv ℝ V (curve hV h hh x t) (variation hV h hh x v t)) (t : ℝ) := by
  have hc := ((hVs.continuous_fderiv (by simp)).comp
    (continuous_extend (trajectory hV h hh x))).clm_apply
      (continuous_extend (tangentPath hV h hh x v))
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) (hc.stronglyMeasurableAtFilter volume (𝓝 (t : ℝ)))
      hc.continuousAt
  rw [curve_coe, variation_coe hV hVs]
  change HasDerivAt (fun s : ℝ => v + h • ∫ r in 0..s,
    fderiv ℝ V (extend (trajectory hV h hh x) r) (extend (tangentPath hV h hh x v) r))
    _ (t : ℝ)
  simpa only [Pi.smul_apply, Function.comp_apply, extend_coe] using (hd.const_smul h).const_add v

theorem tangentPath_one {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) :
    tangentPath hV h hh x v ⟨1, by constructor <;> norm_num⟩ = fderiv ℝ (step hV h hh) x v := by
  let t : Time := ⟨1, by constructor <;> norm_num⟩
  have hd := (ContinuousMap.evalCLM ℝ (M := E) t).hasFDerivAt.comp x
    ((contDiff_trajectory hV hVs h hh).differentiable (by simp) x).hasFDerivAt
  exact (congrArg (fun L : E →L[ℝ] E => L v) hd.fderiv).symm

theorem variation_one {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) :
    variation hV h hh x v 1 = fderiv ℝ (step hV h hh) x v :=
  (variation_coe hV hVs h hh x v ⟨1, by constructor <;> norm_num⟩).trans
    (tangentPath_one hV hVs h hh x v)

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u8} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

theorem step_preserves_tensor {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} (hB : Differentiable ℝ B)
    (hInv : ∀ z a b, fderiv ℝ B z (V z) a b +
      B z (fderiv ℝ V z a) b + B z a (fderiv ℝ V z b) = 0) (x a b : E) :
    B (step hV h hh x) (fderiv ℝ (step hV h hh) x a)
      (fderiv ℝ (step hV h hh) x b) = B x a b := by
  let F : ℝ → ℝ := fun t => B (curve hV h hh x t)
    (variation hV h hh x a t) (variation hV h hh x b t)
  have hc : Continuous F :=
    ((hB.continuous.comp (continuous_curve hV h hh x)).clm_apply
      (continuous_variation hV hVs h hh x a)).clm_apply
      (continuous_variation hV hVs h hh x b)
  have hd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt F 0 (Ici t) t := by
    intro t ht
    let T : Time := ⟨t, ht.1, ht.2.le⟩
    have hv := hasDerivAt_curve hV h hh x T
    have ha := hasDerivAt_variation hV hVs h hh x a T
    have hb := hasDerivAt_variation hV hVs h hh x b T
    have hdb : HasDerivAt (fun s : ℝ => B (curve hV h hh x s))
        (fderiv ℝ B (curve hV h hh x t) (h • V (curve hV h hh x t))) t :=
      (hB (curve hV h hh x t)).hasFDerivAt.comp_hasDerivAt (l := B)
        (l' := fderiv ℝ B (curve hV h hh x t)) t hv
    have hdf := (hdb.clm_apply ha).clm_apply hb
    have hz :
        ((fderiv ℝ B (curve hV h hh x t) (h • V (curve hV h hh x t)))
          (variation hV h hh x a t) +
          B (curve hV h hh x t)
            (h • fderiv ℝ V (curve hV h hh x t) (variation hV h hh x a t)))
          (variation hV h hh x b t) +
          B (curve hV h hh x t) (variation hV h hh x a t)
            (h • fderiv ℝ V (curve hV h hh x t) (variation hV h hh x b t)) = 0 := by
      simp only [map_smul, smul_apply,
        add_apply, smul_eq_mul]
      calc
        _ = h * (fderiv ℝ B (curve hV h hh x t) (V (curve hV h hh x t))
            (variation hV h hh x a t) (variation hV h hh x b t) +
          B (curve hV h hh x t)
            (fderiv ℝ V (curve hV h hh x t) (variation hV h hh x a t))
            (variation hV h hh x b t) +
          B (curve hV h hh x t) (variation hV h hh x a t)
            (fderiv ℝ V (curve hV h hh x t) (variation hV h hh x b t))) := by ring
        _ = 0 := by rw [hInv, mul_zero]
    exact (hdf.congr_deriv hz).hasDerivWithinAt
  have he := constant_of_has_deriv_right_zero hc.continuousOn hd 1
    (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa only [F, curve_one, variation_one hV hVs, curve_zero, variation_zero] using he

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u9} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

omit [CompleteSpace E] [ProperSpace E] in

theorem contDiff_homeomorph_pow (f : E ≃ₜ E) (hf : ContDiff ℝ ∞ (f : E → E))
    (n : ℕ) : ContDiff ℝ ∞ ((f ^ n : E ≃ₜ E) : E → E) := by
  induction n with
  | zero =>
    rw [pow_zero]
    change ContDiff ℝ ∞ (id : E → E)
    exact contDiff_id
  | succ n ih =>
    rw [pow_succ']
    change ContDiff ℝ ∞ ((f : E → E) ∘ (f ^ n : E ≃ₜ E))
    exact hf.comp ih

omit [CompleteSpace E] [ProperSpace E] in

theorem homeomorph_pow_preserves_tensor (f : E ≃ₜ E)
    (hf : ContDiff ℝ ∞ (f : E → E))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x a b, B (f x) (fderiv ℝ (f : E → E) x a)
      (fderiv ℝ (f : E → E) x b) = B x a b) (n : ℕ) (x a b : E) :
    B ((f ^ n) x) (fderiv ℝ ((f ^ n : E ≃ₜ E) : E → E) x a)
      (fderiv ℝ ((f ^ n : E ≃ₜ E) : E → E) x b) = B x a b := by
  induction n with
  | zero =>
    rw [pow_zero]
    change B x (fderiv ℝ (id : E → E) x a) (fderiv ℝ (id : E → E) x b) = _
    simp
  | succ n ih =>
    rw [pow_succ']
    change B (f ((f ^ n) x)) (fderiv ℝ ((f : E → E) ∘ (f ^ n : E ≃ₜ E)) x a)
      (fderiv ℝ ((f : E → E) ∘ (f ^ n : E ≃ₜ E)) x b) = _
    rw [fderiv_comp x (hf.differentiable (by simp) _)
      ((contDiff_homeomorph_pow f hf n).differentiable (by simp) _)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hB]
    exact ih

omit [ProperSpace E] in

theorem curve_linear_component {F : Type u10} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (L : E →L[ℝ] F) (v : F)
    (hL : ∀ z, L (V z) = v) (x : E) (t : Time) :
    L (curve hV h hh x t) = L x + (t : ℝ) • h • v := by
  let G : ℝ → F := fun s => L (curve hV h hh x s) - s • h • v
  have hc : Continuous G :=
    (L.continuous.comp (continuous_curve hV h hh x)).sub (continuous_id.smul continuous_const)
  have hd : ∀ s ∈ Ico (0 : ℝ) 1, HasDerivWithinAt G 0 (Ici s) s := by
    intro s hs
    have hd := L.hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_curve hV h hh x ⟨s, hs.1, hs.2.le⟩)
    have hlin := (hasDerivAt_id s).smul_const (h • v)
    have hh' : HasDerivAt G 0 s := by
      change HasDerivAt ((L ∘ curve hV h hh x) - fun s : ℝ => s • h • v) 0 s
      simpa only [id_eq, map_smul, hL, one_smul, sub_self] using hd.sub hlin
    exact hh'.hasDerivWithinAt
  have he := constant_of_has_deriv_right_zero hc.continuousOn hd (t : ℝ) t.property
  simpa only [G, curve_zero, zero_smul, sub_zero, sub_eq_iff_eq_add] using he

omit [ProperSpace E] in
@[simp] theorem step_linear_component {F : Type u11} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (L : E →L[ℝ] F) (v : F)
    (hL : ∀ z, L (V z) = v) (x : E) :
    L (step hV h hh x) = L x + h • v := by
  simpa only [curve_one, one_smul] using
    curve_linear_component hV h hh L v hL x (⟨1, by constructor <;> norm_num⟩ : Time)

omit [CompleteSpace E] [ProperSpace E] in

theorem homeomorph_pow_linear_component {F : Type u12} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E ≃ₜ E) (L : E →L[ℝ] F) (v : F) (hL : ∀ x, L (f x) = L x + v)
    (n : ℕ) (x : E) : L ((f ^ n) x) = L x + n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Homeomorph.mul_apply, hL, ih, succ_nsmul]
    abel

theorem exists_transport {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : Differentiable ℝ B)
    (hInv : ∀ z a b, fderiv ℝ B z (V z) a b + B z (fderiv ℝ V z a) b +
      B z a (fderiv ℝ V z b) = 0)
    {F : Type u13} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (v : F) (hL : ∀ x, L (V x) = v) (T : ℝ) :
    ∃ f : E ≃ₜ E, ContDiff ℝ ∞ (f : E → E) ∧ ContDiff ℝ ∞ (f.symm : E → E) ∧
      (∀ x a b, B (f x) (fderiv ℝ (f : E → E) x a) (fderiv ℝ (f : E → E) x b) = B x a b) ∧
      (∀ x, L (f x) = L x + T • v) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (‖T‖ * (K : ℝ)) 0)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
  let h : ℝ := T / N
  have hh : ‖h‖₊ * K < 1 := by
    change ‖h‖ * (K : ℝ) < (1 : ℝ)
    dsimp [h]
    rw [abs_div, abs_of_pos hN0, div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr ((le_max_left _ _).trans_lt hN)
  let f := stepHomeomorph hV hVs h hh
  have hf : ContDiff ℝ ∞ (f : E → E) := contDiff_step hV hVs h hh
  have hfi : ContDiff ℝ ∞ (f.symm : E → E) := contDiff_step hV hVs (-h) (by simpa using hh)
  refine ⟨f ^ N, contDiff_homeomorph_pow f hf N, ?_, ?_, ?_⟩
  · change ContDiff ℝ ∞ ((f ^ N)⁻¹ : E ≃ₜ E)
    rw [← inv_pow]
    exact contDiff_homeomorph_pow f⁻¹ hfi N
  · exact homeomorph_pow_preserves_tensor f hf (step_preserves_tensor hV hVs h hh hB hInv) N
  · intro x
    have he := homeomorph_pow_linear_component f L (h • v)
      (step_linear_component hV h hh L v hL) N x
    have hs : (N : ℝ) * h = T := by dsimp [h]; field_simp
    simpa only [nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hs] using he

end
end SmoothODE

end LowerBoundInline

end OAI
