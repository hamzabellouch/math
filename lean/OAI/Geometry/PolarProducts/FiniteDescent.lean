import OAI.Geometry.PolarProducts.SmoothDegree

namespace OAI

universe u80 u81 u82 u83

section NonsqueezingInline
section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace SmoothLinking
noncomputable section
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type u80} {F : Type u81} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def conePoint (e : F) (z : E × ℝ) : E × F := (z.1, z.2 • e)

def degreeMap (η : E × F → E × F) (e : F) (ρ : ℝ) (z : E × ℝ) : E × ℝ :=
  if 0 < z.2+ρ then
    ((η (z.1, (z.2+ρ) • e)).1, (‖(η (z.1, (z.2+ρ) • e)).2‖^2-ρ^2)/(z.2+2*ρ))
  else z

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem degreeMap_eq_self {η : E × F → E × F} {e : F} (he : ‖e‖ = 1)
    {ρ : ℝ} (hρ : 0 < ρ) {z : E × ℝ} (hz : 0 < z.2+ρ)
    (hη : η (z.1, (z.2+ρ) • e) = (z.1, (z.2+ρ) • e)) :
    degreeMap η e ρ z = z := by
  simp only [degreeMap, ite_eq_left hz, hη, norm_smul, he, mul_one,
    Real.norm_eq_abs, sq_abs]
  apply Prod.ext
  · rfl
  change ((z.2+ρ)^2-ρ^2)/(z.2+2*ρ) = z.2
  apply (div_eq_iff (by linarith : z.2+2*ρ ≠ 0)).mpr
  ring

theorem contDiffAt_degreeMap_pos {η : E × F → E × F} (hη : ContDiff ℝ ∞ η)
    (e : F) {ρ : ℝ} (hρ : 0 < ρ) {z : E × ℝ} (hz : 0 < z.2+ρ) :
    ContDiffAt ℝ ∞ (degreeMap η e ρ) z := by
  have hinput : ContDiff ℝ ∞ (fun w : E × ℝ => (w.1, (w.2+ρ) • e)) :=
    contDiff_fst.prodMk ((contDiff_snd.add contDiff_const).smul contDiff_const)
  have hout := hη.comp hinput
  have hn : z.2+2*ρ ≠ 0 := by linarith
  have hd : ContDiffAt ℝ ∞ (fun w : E × ℝ =>
      ((η (w.1, (w.2+ρ) • e)).1, (‖(η (w.1, (w.2+ρ) • e)).2‖^2-ρ^2)/(w.2+2*ρ))) z := by
    exact (contDiff_fst.comp hout).contDiffAt.prodMk
      (((contDiff_norm_sq ℝ).comp (contDiff_snd.comp hout)).contDiffAt.sub contDiffAt_const |>.div
        (contDiffAt_snd.add contDiffAt_const) hn)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const (continuous_snd.add continuous_const)).mem_nhds hz] with w hw
  change 0 < w.2+ρ at hw
  simp only [degreeMap, ite_eq_left hw]

theorem contDiff_degreeMap {η : E × F → E × F} (hη : ContDiff ℝ ∞ η)
    {e : F} (he : ‖e‖ = 1) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hfixed : ∀ (y : E) (s : ℝ), 0 < s → s < ε → η (y, s • e) = (y, s • e)) :
    ContDiff ℝ ∞ (degreeMap η e ρ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : 0 < z.2+ρ
  · exact contDiffAt_degreeMap_pos hη e hρ hz
  have hz' : z.2+ρ < ε := lt_of_le_of_lt (le_of_not_gt hz) hε
  apply (contDiffAt_id : ContDiffAt ℝ ∞ (id : E × ℝ → E × ℝ) z).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt (continuous_snd.add continuous_const) continuous_const).mem_nhds hz'] with w hw
  by_cases hp : 0 < w.2+ρ
  · exact degreeMap_eq_self he hρ hp (hfixed w.1 (w.2+ρ) hp hw)
  · simp only [degreeMap, ite_eq_right hp, id_eq]

omit [NormedSpace ℝ E] in
theorem norm_translate_le (z : E × ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖z‖ ≤ ‖(z.1, z.2+ρ)‖ + ρ := by
  have he : z = (z.1, z.2+ρ) - (0,ρ) := by ext <;> simp
  calc
    ‖z‖ = ‖(z.1, z.2+ρ) - (0,ρ)‖ := congrArg norm he
    _ ≤ ‖(z.1, z.2+ρ)‖+‖((0,ρ) : E × ℝ)‖ := norm_sub_le _ _
    _ = _ := by simp [Prod.norm_def, abs_of_nonneg hρ, hρ]

omit [NormedSpace ℝ E] in
theorem degreeMap_identity_outside {η : E × F → E × F} {e : F} (he : ‖e‖ = 1)
    {ρ R : ℝ} (hρ : 0 < ρ)
    (hfixed : ∀ (y : E) (s : ℝ), 0 < s → R ≤ ‖(y,s)‖ → η (y, s • e) = (y, s • e))
    (z : E × ℝ) (hz : R+ρ ≤ ‖z‖) : degreeMap η e ρ z = z := by
  by_cases hp : 0 < z.2+ρ
  · apply degreeMap_eq_self he hρ hp
    apply hfixed _ _ hp
    have hn := norm_translate_le z hρ.le
    linarith
  · simp only [degreeMap, ite_eq_right hp]

theorem sphere_linking [FiniteDimensional ℝ E]
    {η : E × F → E × F} (hη : ContDiff ℝ ∞ η) {e : F} (he : ‖e‖ = 1)
    {ρ ε R : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hR : ρ < R)
    (hnear : ∀ (y : E) (s : ℝ), 0 < s → s < ε → η (y, s • e) = (y, s • e))
    (hfar : ∀ (y : E) (s : ℝ), 0 < s → R ≤ ‖(y,s)‖ → η (y, s • e) = (y, s • e)) :
    ∃ (y : E) (s : ℝ), 0 < s ∧ ‖(y,s)‖ < R ∧ (η (y, s • e)).1 = 0 ∧ ‖(η (y, s • e)).2‖ = ρ := by
  obtain ⟨z, hz⟩ := SmoothDegree.exists_zero (contDiff_degreeMap hη he hρ hε hnear)
    (show 0 < R+ρ by linarith) (degreeMap_identity_outside he hρ hfar)
  have hp : 0 < z.2+ρ := by
    by_contra h
    have heq : z = 0 := by simpa only [degreeMap, ite_eq_right h] using hz
    simp only [heq, Prod.snd_zero, zero_add] at h
    exact h hρ
  have hfst : (η (z.1, (z.2+ρ) • e)).1 = 0 := by
    simpa only [degreeMap, ite_eq_left hp, Prod.fst_zero, Prod.fst] using congrArg Prod.fst hz
  have hsnd : ‖(η (z.1, (z.2+ρ) • e)).2‖ = ρ := by
    have h := congrArg Prod.snd hz
    simp only [degreeMap, ite_eq_left hp, Prod.snd_zero] at h
    have hd : z.2+2*ρ ≠ 0 := by linarith
    have hsq : ‖(η (z.1, (z.2+ρ) • e)).2‖^2 = ρ^2 :=
      sub_eq_zero.mp ((div_eq_zero_iff).mp h |>.resolve_right hd)
    nlinarith [norm_nonneg (η (z.1, (z.2+ρ) • e)).2]
  refine ⟨z.1, z.2+ρ, hp, ?_, hfst, hsnd⟩
  by_contra! hn
  have hid := hfar z.1 (z.2+ρ) hp hn
  rw [hid] at hfst hsnd
  simp only [norm_smul, he, mul_one, Real.norm_eq_abs,
    abs_of_pos hp] at hfst hsnd
  rw [hfst, hsnd] at hn
  have : ‖((0 : E),ρ)‖ = ρ := by simp [Prod.norm_def, abs_of_pos hρ, hρ.le]
  rw [this] at hn
  exact hR.not_ge hn

end
end SmoothLinking

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace FlowDescent
noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
variable {E : Type u82} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem curve_displacement {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {L : ℝ}
    (hL : ∀ x, ‖V x‖ ≤ L) (x : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖SmoothODE.curve hV h hh x t - x‖ ≤ h*L*t := by
  have hb (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) 1) :
      ‖h • V (SmoothODE.curve hV h hh x s)‖ ≤ h*L := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (hL _) h0
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (SmoothODE.hasDerivAt_curve hV h hh x ⟨s,hs⟩).hasDerivWithinAt)
    hb (convex_Icc (0 : ℝ) 1) (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) ht
  simpa only [SmoothODE.curve_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] using hm

 theorem curve_energy_deriv {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ)
    (x : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => Φ (SmoothODE.curve hV h hh x s))
      (h * fderiv ℝ Φ (SmoothODE.curve hV h hh x t) (V (SmoothODE.curve hV h hh x t))) t := by
  have hd := (hΦ (SmoothODE.curve hV h hh x t)).hasFDerivAt.comp_hasDerivAt t
    (SmoothODE.hasDerivAt_curve hV h hh x ⟨t,ht⟩)
  simpa only [Function.comp_def, map_smul, smul_eq_mul] using hd

 theorem curve_energy_antitone {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ)
    (hdec : ∀ x, fderiv ℝ Φ x (V x) ≤ 0) (x : E) :
    AntitoneOn (fun t => Φ (SmoothODE.curve hV h hh x t)) (Icc (0 : ℝ) 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1)
    (hΦ.continuous.comp (SmoothODE.continuous_curve hV h hh x)).continuousOn
    (fun t ht => (curve_energy_deriv hV hh hΦ x (interior_subset ht)).hasDerivWithinAt)
  intro t _
  exact mul_nonpos_of_nonneg_of_nonpos h0 (hdec _)

 theorem step_energy_le {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ)
    (hdec : ∀ x, fderiv ℝ Φ x (V x) ≤ 0) (x : E) :
    Φ (SmoothODE.step hV h hh x) ≤ Φ x := by
  simpa only [SmoothODE.curve_one, SmoothODE.curve_zero] using
    (curve_energy_antitone hV hh h0 hΦ hdec x (by simp) (by simp) zero_le_one)

 theorem step_energy_drop {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {h : ℝ} (hh : ‖h‖₊ * K < 1) (h0 : 0 ≤ h) {Φ : E → ℝ} (hΦ : Differentiable ℝ Φ)
    (hdec : ∀ x, fderiv ℝ Φ x (V x) ≤ 0) {L M a b : ℝ}
    (hL : ∀ x, ‖V x‖ ≤ L)
    (hrate : ∀ x, ‖x‖ ≤ M → a ≤ Φ x → Φ x ≤ b → fderiv ℝ Φ x (V x) ≤ -1)
    (x : E) (hx : ‖x‖+h*L ≤ M) (hxb : Φ x ≤ b) :
    Φ (SmoothODE.step hV h hh x) ≤ max a (Φ x-h) := by
  by_cases hxa : Φ (SmoothODE.step hV h hh x) ≤ a
  · exact hxa.trans (le_max_left _ _)
  have ha := le_of_lt (lt_of_not_ge hxa)
  have ham := curve_energy_antitone hV hh h0 hΦ hdec x
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      fderiv ℝ Φ (SmoothODE.curve hV h hh x t) (V (SmoothODE.curve hV h hh x t)) ≤ -1 := by
    apply hrate
    · have hdn := curve_displacement hV hh h0 hL x ht
      have hLn : 0 ≤ L := le_trans (norm_nonneg (V x)) (hL x)
      have hn := norm_le_norm_sub_add (SmoothODE.curve hV h hh x t) x
      have htime := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg h0 hLn)
      linarith
    · exact ha.trans (by simpa only [SmoothODE.curve_one] using ham ht (by simp) ht.2)
    · exact (show Φ (SmoothODE.curve hV h hh x t) ≤ Φ x from by
        simpa only [SmoothODE.curve_zero] using ham (by simp) ht ht.1).trans hxb
  have hm : AntitoneOn (fun t => Φ (SmoothODE.curve hV h hh x t)+h*t) (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1)
      (((hΦ.continuous.comp (SmoothODE.continuous_curve hV h hh x)).add
        (continuous_const.mul continuous_id)).continuousOn)
      (fun t ht => ((curve_energy_deriv hV hh hΦ x (interior_subset ht)).add
        ((hasDerivAt_id t).const_mul h)).hasDerivWithinAt)
    intro t ht
    have := mul_le_mul_of_nonneg_left (hb t (interior_subset ht)) h0
    linarith
  have hend := hm (by simp) (by simp) zero_le_one
  simp only [SmoothODE.curve_one, SmoothODE.curve_zero, mul_one, mul_zero, add_zero] at hend
  exact (by linarith : Φ (SmoothODE.step hV h hh x) ≤ Φ x-h).trans (le_max_right _ _)

end
end FlowDescent

namespace FlowDescent
noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
variable {E : Type u83} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem iterate_norm_le {f : E → E} {D : ℝ} (hD : ∀ x, ‖f x-x‖ ≤ D) (j : ℕ) (x : E) :
    ‖f^[j] x‖ ≤ ‖x‖+j*D := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hn := norm_le_norm_sub_add (f (f^[j] x)) (f^[j] x)
    have hd := hD (f^[j] x)
    push_cast
    linarith

 omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
 theorem iterate_energy_le {f : E → E} {Φ : E → ℝ} (hf : ∀ x, Φ (f x) ≤ Φ x)
    (j : ℕ) (x : E) : Φ (f^[j] x) ≤ Φ x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (hf (f^[j] x)).trans ih

 omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem iterate_energy_drop {f : E → E} {Φ : E → ℝ} {h D M a b : ℝ} (h0 : 0 ≤ h)
    (hD0 : 0 ≤ D) (hD : ∀ x, ‖f x-x‖ ≤ D) (hdec : ∀ x, Φ (f x) ≤ Φ x)
    (hdrop : ∀ x, ‖x‖+D ≤ M → Φ x ≤ b → Φ (f x) ≤ max a (Φ x-h))
    (N : ℕ) (x : E) (hx : ‖x‖+N*D ≤ M) (hb : Φ x ≤ b) :
    Φ (f^[N] x) ≤ max a (Φ x-N*h) := by
  suffices hs : ∀ j, j ≤ N → Φ (f^[j] x) ≤ max a (Φ x-j*h) by exact hs N le_rfl
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hij := ih (Nat.le_trans (Nat.le_succ j) hj)
    have hn := iterate_norm_le hD j x
    have hb' := (iterate_energy_le hdec j x).trans hb
    have hjR : (j : ℝ)+1 ≤ N := by exact_mod_cast hj
    have hx' : ‖f^[j] x‖+D ≤ M := by
      have := mul_le_mul_of_nonneg_right hjR hD0
      nlinarith
    have hd := hdrop (f^[j] x) hx' hb'
    rw [Function.iterate_succ_apply']
    apply hd.trans
    apply max_le (le_max_left _ _)
    apply (sub_le_sub_right hij h).trans
    rw [← max_sub_sub_right]
    apply max_le
    · exact (sub_le_self a h0).trans (le_max_left _ _)
    · apply le_trans _ (le_max_right _ _)
      push_cast
      linarith

 omit [CompleteSpace E] in
 theorem contDiff_iterate {f : E → E} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ContDiff ℝ ∞ (f^[j]) := by
  induction j with
  | zero => exact contDiff_id
  | succ j ih =>
    convert! hf.comp ih using 1
    ext x
    exact Function.iterate_succ_apply' f j x

 theorem exists_descent_map [ProperSpace E] {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V) {Φ : E → ℝ}
    (hΦ : Differentiable ℝ Φ) (hdec : ∀ x, fderiv ℝ Φ x (V x) ≤ 0)
    {L M a b B T : ℝ} (hT : 0 < T) (hba : b-T ≤ a)
    (hL : ∀ x, ‖V x‖ ≤ L) (hM : B+T*L ≤ M)
    (hrate : ∀ x, ‖x‖ ≤ M → a ≤ Φ x → Φ x ≤ b → fderiv ℝ Φ x (V x) ≤ -1) :
    ∃ η : E → E, ContDiff ℝ ∞ η ∧ (∀ x, Φ (η x) ≤ Φ x) ∧
      (∀ x, V x = 0 → η x = x) ∧
      ∀ x, ‖x‖ ≤ B → Φ x ≤ b → Φ (η x) ≤ a := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (T*(K : ℝ)) 0)
  have hN0 : (0 : ℝ) < N := (le_max_right _ _).trans_lt hN
  have hNne : (N : ℝ) ≠ 0 := hN0.ne'
  let h := T/N
  have h0 : 0 ≤ h := (div_pos hT hN0).le
  have hh : ‖h‖₊ * K < 1 := by
    change ‖h‖*(K : ℝ) < (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    dsimp [h]
    rw [div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr ((le_max_left _ _).trans_lt hN)
  have hNh : (N : ℝ)*h = T := by dsimp [h]; field_simp
  let f := SmoothODE.step hV h hh
  have hf : ContDiff ℝ ∞ f := SmoothODE.contDiff_step hV hVs h hh
  have hfd (x : E) : Φ (f x) ≤ Φ x := step_energy_le hV hh h0 hΦ hdec x
  have hfD (x : E) : ‖f x-x‖ ≤ h*L := by
    simpa only [SmoothODE.curve_one, mul_one] using
      (curve_displacement hV hh h0 hL x (t := 1) (by simp))
  have hL0 : 0 ≤ L := (norm_nonneg (V 0)).trans (hL 0)
  refine ⟨f^[N], contDiff_iterate hf N, iterate_energy_le hfd N, ?_, ?_⟩
  · intro x hx
    have hfix : f x = x := by
      simpa only [SmoothODE.curve_one] using
        (SmoothODE.curve_of_eq_zero hV h hh x hx (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1))
    exact Function.iterate_fixed hfix N
  · intro x hx hb
    have hbound : ‖x‖+(N : ℝ)*(h*L) ≤ M := by nlinarith [mul_assoc (N : ℝ) h L]
    have hd := iterate_energy_drop h0 (mul_nonneg h0 hL0) hfD hfd
      (fun y hy hby => step_energy_drop hV hh h0 hΦ hdec hL hrate y hy hby) N x hbound hb
    rw [hNh] at hd
    exact hd.trans (max_le le_rfl (by linarith))

end
end FlowDescent

end
end NonsqueezingInline

end OAI
