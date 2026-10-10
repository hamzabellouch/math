import OAI.Geometry.PolarProducts.CompleteFlow

namespace OAI

universe u14 u15 u16

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

variable {E : Type u14} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable section

theorem curve_injective {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (t : Time) :
    Function.Injective (fun x => curve hV h hh x t) := by
  intro x y he
  have heq : EqOn (curve hV h hh x) (curve hV h hh y) (Icc 0 t) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := fun _ y => h • V y) (s := fun _ => univ) (K := ‖h‖₊ * K)
    · intro _ _
      exact ((lipschitzWith_smul h).comp hV).lipschitzOnWith
    · exact (continuous_curve hV h hh x).continuousOn
    · intro s hs
      exact (hasDerivAt_curve hV h hh x ⟨s, hs.1.le, hs.2.trans t.property.2⟩).hasDerivWithinAt
    · intro _ _; trivial
    · exact (continuous_curve hV h hh y).continuousOn
    · intro s hs
      exact (hasDerivAt_curve hV h hh y ⟨s, hs.1.le, hs.2.trans t.property.2⟩).hasDerivWithinAt
    · intro _ _; trivial
    · exact he
  simpa only [curve_zero] using heq (show 0 ∈ Icc (0 : ℝ) t from ⟨le_rfl, t.property.1⟩)

theorem curve_of_const_along {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E)
    (hc : ∀ t : Time, V (x + (t : ℝ) • h • v) = v) :
    EqOn (curve hV h hh x) (fun t => x + t • h • v) (Icc 0 1) := by
  apply EqOn.symm
  apply curve_unique hV h hh x
  · exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  · intro t ht
    have he := hc ⟨t, ht.1, ht.2.le⟩
    have hd := ((hasDerivAt_id t).smul_const (h • v)).const_add x
    simpa only [he, one_smul, id_eq] using hd.hasDerivWithinAt (s := Ici t)
  · simp

theorem curve_spaceTime_outside {V : ℝ × E → ℝ × E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (h : ℝ) (hh : ‖h‖₊ * K < 1)
    {U : Set E} (hTime : ∀ z, (V z).1 = 1)
    (hOut : ∀ z, z.2 ∉ U → (V z).2 = 0) (x : ℝ × E) (hx : x.2 ∉ U) (t : Time) :
    curve hV h hh x t = (x.1 + (t : ℝ) * h, x.2) := by
  have hc : ∀ s : Time, V (x + (s : ℝ) • h • (1, (0 : E))) = (1, 0) := by
    intro s
    apply Prod.ext
    · exact hTime _
    · exact hOut _ (by simpa using hx)
  have he := curve_of_const_along hV h hh x (1, (0 : E)) hc t.property
  calc
    curve hV h hh x t = x + (t : ℝ) • h • (1, (0 : E)) := he
    _ = (x.1 + (t : ℝ) * h, x.2) := by ext <;> simp [smul_eq_mul]

theorem curve_spaceTime_mapsTo {V : ℝ × E → ℝ × E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (h : ℝ) (hh : ‖h‖₊ * K < 1)
    {U : Set E} (hTime : ∀ z, (V z).1 = 1)
    (hOut : ∀ z, z.2 ∉ U → (V z).2 = 0) (x : ℝ × E) (hx : x.2 ∈ U) (t : Time) :
    (curve hV h hh x t).2 ∈ U := by
  by_contra hout
  let y : ℝ × E := (x.1, (curve hV h hh x t).2)
  have he : curve hV h hh y t = curve hV h hh x t := by
    rw [curve_spaceTime_outside hV h hh hTime hOut y hout]
    apply Prod.ext
    · have he := curve_linear_component hV h hh (ContinuousLinearMap.fst ℝ ℝ E) 1 hTime x t
      simpa only [ContinuousLinearMap.coe_fst', smul_eq_mul, mul_one, y] using he.symm
    · rfl
  have hy := curve_injective hV h hh t he
  have hxy := congrArg Prod.snd hy
  exact hout (hxy ▸ hx)

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u15} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

theorem step_preserves_tensor_on {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E}
    (hB : ∀ z ∈ U, DifferentiableAt ℝ B z)
    (hInv : ∀ z ∈ U, ∀ a b, fderiv ℝ B z (V z) a b +
      B z (fderiv ℝ V z a) b + B z a (fderiv ℝ V z b) = 0) (x : E) (hpath : ∀ t : Time, curve hV h hh x t ∈ U) (a b : E) :
    B (step hV h hh x) (fderiv ℝ (step hV h hh) x a)
      (fderiv ℝ (step hV h hh) x b) = B x a b := by
  let F : ℝ → ℝ := fun t => B (curve hV h hh x t)
    (variation hV h hh x a t) (variation hV h hh x b t)
  have hBc : ContinuousOn B U := fun z hz => (hB z hz).continuousAt.continuousWithinAt
  have hc : ContinuousOn F (Icc 0 1) :=
    ((hBc.comp (continuous_curve hV h hh x).continuousOn (fun t ht => hpath ⟨t, ht⟩)).clm_apply
      (continuous_variation hV hVs h hh x a).continuousOn).clm_apply
      (continuous_variation hV hVs h hh x b).continuousOn
  have hd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt F 0 (Ici t) t := by
    intro t ht
    let T : Time := ⟨t, ht.1, ht.2.le⟩
    have hv := hasDerivAt_curve hV h hh x T
    have ha := hasDerivAt_variation hV hVs h hh x a T
    have hb := hasDerivAt_variation hV hVs h hh x b T
    have hdb : HasDerivAt (fun s : ℝ => B (curve hV h hh x s))
        (fderiv ℝ B (curve hV h hh x t) (h • V (curve hV h hh x t))) t :=
      (hB (curve hV h hh x t) (hpath T)).hasFDerivAt.comp_hasDerivAt (l := B)
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
        _ = 0 := by rw [hInv _ (hpath T), mul_zero]
    exact (hdf.congr_deriv hz).hasDerivWithinAt
  have he := constant_of_has_deriv_right_zero hc hd 1
    (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa only [F, curve_one, variation_one hV hVs, curve_zero, variation_zero] using he

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u16} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

omit [CompleteSpace E] [ProperSpace E] in

theorem homeomorph_pow_preserves_tensor_on (f : E ≃ₜ E)
    (hf : ContDiff ℝ ∞ (f : E → E)) {U : Set E} (hU : MapsTo f U U)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x ∈ U, ∀ a b, B (f x) (fderiv ℝ (f : E → E) x a)
      (fderiv ℝ (f : E → E) x b) = B x a b) (n : ℕ) (x : E) (hx : x ∈ U) :
    (f ^ n) x ∈ U ∧ ∀ a b,
      B ((f ^ n) x) (fderiv ℝ ((f ^ n : E ≃ₜ E) : E → E) x a)
        (fderiv ℝ ((f ^ n : E ≃ₜ E) : E → E) x b) = B x a b := by
  induction n with
  | zero =>
    refine ⟨hx, ?_⟩
    intro a b
    change B x (fderiv ℝ (id : E → E) x a) (fderiv ℝ (id : E → E) x b) = _
    simp
  | succ n ih =>
    rw [pow_succ']
    refine ⟨hU ih.1, ?_⟩
    intro a b
    change B (f ((f ^ n) x)) (fderiv ℝ ((f : E → E) ∘ (f ^ n : E ≃ₜ E)) x a)
      (fderiv ℝ ((f : E → E) ∘ (f ^ n : E ≃ₜ E)) x b) = _
    rw [fderiv_comp x (hf.differentiable (by simp) _)
      ((contDiff_homeomorph_pow f hf n).differentiable (by simp) _)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hB _ ih.1]
    exact ih.2 a b

theorem exists_spaceTime_transport {V : ℝ × E → ℝ × E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V) {U : Set E}
    (hTime : ∀ z, (V z).1 = 1) (hOut : ∀ z, z.2 ∉ U → (V z).2 = 0)
    {B : (ℝ × E) → (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ}
    (hB : ∀ z, z.2 ∈ U → DifferentiableAt ℝ B z)
    (hInv : ∀ z, z.2 ∈ U → ∀ a b, fderiv ℝ B z (V z) a b +
      B z (fderiv ℝ V z a) b + B z a (fderiv ℝ V z b) = 0) (T : ℝ) :
    ∃ f : (ℝ × E) ≃ₜ (ℝ × E),
      ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E)) ∧
      ContDiff ℝ ∞ (f.symm : (ℝ × E) → (ℝ × E)) ∧
      (∀ x, (f x).1 = x.1 + T) ∧
      (∀ x, x.2 ∉ U → (f x).2 = x.2) ∧
      (∀ x, x.2 ∈ U → (f x).2 ∈ U ∧ ∀ a b,
        B (f x) (fderiv ℝ (f : (ℝ × E) → (ℝ × E)) x a)
          (fderiv ℝ (f : (ℝ × E) → (ℝ × E)) x b) = B x a b) := by
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
  have hf : ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E)) := contDiff_step hV hVs h hh
  have hfi : ContDiff ℝ ∞ (f.symm : (ℝ × E) → (ℝ × E)) :=
    contDiff_step hV hVs (-h) (by simpa using hh)
  have hm : ∀ x, x.2 ∈ U → (f x).2 ∈ U := by
    intro x hx
    simpa only [Prod.mk.eta, curve_one, f, stepHomeomorph_apply] using
      curve_spaceTime_mapsTo hV h hh hTime hOut x hx ⟨1, by constructor <;> norm_num⟩
  have ho : ∀ x, x.2 ∉ U → (f x).2 = x.2 := by
    intro x hx
    have he := curve_spaceTime_outside hV h hh hTime hOut x hx ⟨1, by constructor <;> norm_num⟩
    simpa only [curve_one, f, stepHomeomorph_apply] using congrArg Prod.snd he
  refine ⟨f ^ N, contDiff_homeomorph_pow f hf N, ?_, ?_, ?_, ?_⟩
  · change ContDiff ℝ ∞ ((f ^ N)⁻¹ : (ℝ × E) ≃ₜ (ℝ × E))
    rw [← inv_pow]
    exact contDiff_homeomorph_pow f⁻¹ hfi N
  · intro x
    have hs : (N : ℝ) * h = T := by dsimp [h]; field_simp
    have he := homeomorph_pow_linear_component f (ContinuousLinearMap.fst ℝ ℝ E) h
      (by intro z; simpa only [smul_eq_mul, mul_one, f, stepHomeomorph_apply] using
        step_linear_component hV h hh (ContinuousLinearMap.fst ℝ ℝ E) 1 hTime z) N x
    simpa only [ContinuousLinearMap.coe_fst', nsmul_eq_mul, hs] using he
  · intro x hx
    have hi : ∀ n : ℕ, ((f ^ n) x).2 = x.2 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Homeomorph.mul_apply, ho _ (by simpa only [ih] using hx), ih]
    exact hi N
  · intro x hx
    apply homeomorph_pow_preserves_tensor_on f hf (U := Prod.snd ⁻¹' U)
      (fun _ hz => hm _ hz) (fun z hz a b => ?_) N x hx
    exact step_preserves_tensor_on hV hVs h hh (U := Prod.snd ⁻¹' U)
      (fun y hy => hB y hy) (fun y hy => hInv y hy) z
      (fun t => curve_spaceTime_mapsTo hV h hh hTime hOut z hz t) a b

end
end SmoothODE

end LowerBoundInline

end OAI
