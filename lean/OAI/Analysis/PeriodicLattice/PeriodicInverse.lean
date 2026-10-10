import OAI.Analysis.PeriodicLattice.RapidBounds

namespace OAI

/-! Periodic primitives and regularity of the inverse operator. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingPeriodicInverse {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace PeriodicInverse

open Set Filter MeasureTheory TorusCalculus RapidCalculus
open scoped ContDiff Topology

section ParameterIntegral
variable {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
theorem hasFDerivAt_intervalIntegral {F : E × ℝ → A} (hF : ContDiff ℝ ∞ F)
    (a b : ℝ) (x : E) :
    HasFDerivAt (fun u => ∫ s in a..b, F (u, s))
      (∫ s in a..b, fderiv ℝ (fun u => F (u, s)) x) x := by
  let D : E × ℝ → E →L[ℝ] A := fun us => fderiv ℝ (fun v => F (v, us.2)) us.1
  have hD : ContDiff ℝ ∞ D := by
    let G : (E × ℝ) → E → A := fun us v => F (v, us.2)
    have hG : ContDiff ℝ ∞ (Function.uncurry G) := hF.comp (contDiff_snd.prodMk contDiff_fst.snd)
    exact hG.fderiv contDiff_fst (by simp)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hD.continuous.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (F := fun u s => F (u, s))
    (F' := fun u s => D (u, s)) (s := Metric.ball x 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds x (by norm_num))
  · exact Eventually.of_forall fun u => (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hD.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    intro u hu
    exact hC (u, s) ⟨Metric.ball_subset_closedBall hu, uIoc_subset_uIcc hs⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun s u _ =>
      ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) u).hasFDerivAt

theorem contDiff_intervalIntegral {F : E × ℝ → A} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun u => ∫ s in a..b, F (u, s)) := by
  have hn (n : ℕ) : ∀ {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
      (G : E × ℝ → B), ContDiff ℝ ∞ G →
      ContDiff ℝ n (fun u => ∫ s in a..b, G (u, s)) := by
    intro B _ _ _ G hG
    induction n generalizing B with
    | zero =>
      exact contDiff_zero.mpr (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun u s => G (u, s)) hG.continuous a b)
    | succ n ih =>
      let D : E × ℝ → E →L[ℝ] B := fun us => fderiv ℝ (fun u => G (u, us.2)) us.1
      have hD : ContDiff ℝ ∞ D := by
        have hh : ContDiff ℝ ∞ (fun p : (E × ℝ) × E => G (p.2, p.1.2)) :=
          hG.comp (contDiff_snd.prodMk contDiff_fst.snd)
        exact hh.fderiv contDiff_fst (by simp)
      have hd : ∀ u, HasFDerivAt (fun u => ∫ s in a..b, G (u, s))
          (∫ s in a..b, D (u, s)) u := fun u => hasFDerivAt_intervalIntegral hG a b u
      rw [Nat.cast_add, Nat.cast_one]
      exact contDiff_succ_iff_hasFDerivAt.mpr ⟨_, ih D hD, hd⟩
  exact contDiff_infty.mpr fun n => hn n F hF

end ParameterIntegral

theorem hasDerivAt_intervalIntegral {A : Type} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [CompleteSpace A] {F : ℝ × ℝ → A}
    (hF : ContDiff ℝ ∞ F) (a b x : ℝ) :
    HasDerivAt (fun u => ∫ s in a..b, F (u, s))
      (∫ s in a..b, deriv (fun u => F (u, s)) x) x := by
  have hD : ContDiff ℝ ∞ (fun us : ℝ × ℝ => fderiv ℝ (fun v => F (v, us.2)) us.1) := by
    have hh : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => F (p.2, p.1.2)) :=
      hF.comp (contDiff_snd.prodMk contDiff_fst.snd)
    exact hh.fderiv contDiff_fst (by simp)
  have hi : IntervalIntegrable (fun s => fderiv ℝ (fun u => F (u, s)) x) volume a b :=
    (hD.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  simpa only [ContinuousLinearMap.intervalIntegral_apply hi, fderiv_apply_one_eq_deriv] using
    (hasFDerivAt_intervalIntegral hF a b x).hasDerivAt

def first (lam : ℝ) (H : ℝ → ℝ → ℝ) (t y : ℝ) : ℝ :=
  (1 - Real.exp lam)⁻¹ * ∫ s in (0 : ℝ)..1, Real.exp (lam * s) * H t (y - s)

theorem first_contDiff (lam : ℝ) {H : ℝ → ℝ → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) :
    ContDiff ℝ ∞ (Function.uncurry (first lam H)) := by
  have hh : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ =>
      Real.exp (lam * p.2) * H p.1.1 (p.1.2 - p.2)) :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd)).mul
      (hH.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.sub contDiff_snd)))
  exact contDiff_const.mul (contDiff_intervalIntegral hh 0 1)

theorem first_periodic (lam : ℝ) {H : ℝ → ℝ → ℝ} (hH : ∀ t, Function.Periodic (H t) 1)
    (t : ℝ) : Function.Periodic (first lam H t) 1 := by
  intro y
  unfold first
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [show y + 1 - s = y - s + 1 by ring, hH t]

theorem first_space_deriv (lam : ℝ) {H : ℝ → ℝ → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) (t y : ℝ) :
    HasDerivAt (first lam H t) (first lam (biD false H) t y) y := by
  have hh : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (lam * p.2) * H t (p.1 - p.2)) :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd)).mul
      (hH.comp (contDiff_const.prodMk (contDiff_fst.sub contDiff_snd)))
  have he (s : ℝ) : deriv (fun u => Real.exp (lam * s) * H t (u - s)) y =
      Real.exp (lam * s) * biD false H t (y - s) := by
    have hs := (((hH.comp ((contDiff_const (c := t)).prodMk contDiff_id)).differentiable
      (by simp) (y - s)).hasDerivAt.comp y ((hasDerivAt_id y).sub_const s)).const_mul (Real.exp (lam * s))
    simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq, mul_one, biD, Bool.false_eq_true, ↓reduceIte] using hs.deriv
  have h := (hasDerivAt_intervalIntegral hh 0 1 y).const_mul ((1 - Real.exp lam)⁻¹)
  change HasDerivAt (fun z => first lam H t z) (first lam (biD false H) t y) y
  simp only [first]
  simpa only [he] using h

theorem first_time_deriv (lam : ℝ) {H : ℝ → ℝ → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) (t y : ℝ) :
    HasDerivAt (fun u => first lam H u y) (first lam (biD true H) t y) t := by
  have hh : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (lam * p.2) * H p.1 (y - p.2)) :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd)).mul
      (hH.comp (contDiff_fst.prodMk (contDiff_const.sub contDiff_snd)))
  have he (s : ℝ) : deriv (fun u => Real.exp (lam * s) * H u (y - s)) t =
      Real.exp (lam * s) * biD true H t (y - s) := by
    have hs := ((hH.comp (contDiff_id.prodMk (contDiff_const (c := y - s)))).differentiable
      (by simp) t).hasDerivAt.const_mul (Real.exp (lam * s))
    exact hs.deriv
  have h := (hasDerivAt_intervalIntegral hh 0 1 t).const_mul ((1 - Real.exp lam)⁻¹)
  dsimp only [first]
  simpa only [he] using h

theorem first_biD (lam : ℝ) {H : ℝ → ℝ → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) (i : Bool) :
    biD i (first lam H) = first lam (biD i H) := by
  funext t y
  cases i
  · exact (first_space_deriv lam hH t y).deriv
  · exact (first_time_deriv lam hH t y).deriv

theorem first_wordD (lam : ℝ) {H : ℝ → ℝ → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) (w : List Bool) :
    wordD w (first lam H) = first lam (wordD w H) := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [wordD_cons, ih, first_biD lam (wordD_contDiff hH w)]; rfl

theorem first_equation (lam : ℝ) (hlam : lam ≠ 0) {H : ℝ → ℝ → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) (hp : ∀ t, Function.Periodic (H t) 1)
    (t y : ℝ) : biD false (first lam H) t y = lam * first lam H t y + H t y := by
  have hs : ContDiff ℝ ∞ (H t) := hH.comp (contDiff_const.prodMk contDiff_id)
  have hu (s : ℝ) : HasDerivAt (fun s => Real.exp (lam * s)) (lam * Real.exp (lam * s)) s := by
    simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id s).const_mul lam).exp
  have hv (s : ℝ) : HasDerivAt (fun s => H t (y - s)) (-deriv (H t) (y - s)) s := by
    simpa only [Function.comp_def, id_eq, mul_neg_one] using
      ((hs.differentiable (by simp) (y - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub y))
  have hu' : IntervalIntegrable (fun s => lam * Real.exp (lam * s)) volume 0 1 :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun s => -deriv (H t) (y - s)) volume 0 1 :=
    (hs.continuous_deriv (by simp)).comp (continuous_const.sub continuous_id) |>.neg |>.intervalIntegrable _ _
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (fun s _ => hu s) (fun s _ => hv s) hu' hv'
  have hp' : H t (y - 1) = H t y := by
    have hh := hp t (y - 1)
    simpa only [sub_add_cancel] using hh.symm
  have hden : 1 - Real.exp lam ≠ 0 := by
    intro hh
    apply hlam
    apply (Real.exp_eq_one_iff lam).mp
    linarith
  simp only [mul_one, mul_zero, Real.exp_zero, one_mul, sub_zero, hp', mul_neg,
    intervalIntegral.integral_neg] at hi
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul] at hi
  rw [first_biD lam hH]
  simp only [first, biD, Bool.false_eq_true, ↓reduceIte]
  field_simp [hden]
  nlinarith [hi]

theorem first_weighted_bound (lam t : ℝ) {H : ℝ → ℝ → ℝ} {w C : ℝ} (hw : 0 ≤ w)
    (hC : ∀ y : ℝ, w * ‖H t y‖ ≤ C) (y : ℝ) :
    w * ‖first lam H t y‖ ≤ ‖(1 - Real.exp lam)⁻¹‖ * Real.exp |lam| * C := by
  have hC₀ : 0 ≤ C := (mul_nonneg hw (norm_nonneg _)).trans (hC 0)
  have hi : ‖∫ s in (0 : ℝ)..1, w * (Real.exp (lam * s) * H t (y - s))‖ ≤ Real.exp |lam| * C := by
    have hz := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := Real.exp |lam| * C) (f := fun s => w * (Real.exp (lam * s) * H t (y - s)))
    apply (by simpa only [sub_zero, abs_one, mul_one] using hz : (∀ s ∈ uIoc (0 : ℝ) 1,
        ‖w * (Real.exp (lam * s) * H t (y - s))‖ ≤ Real.exp |lam| * C) → _)
    intro s hs
    have hs' : 0 ≤ s ∧ s ≤ 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      exact ⟨hs.1.le, hs.2⟩
    have he : Real.exp (lam * s) ≤ Real.exp |lam| := by
      apply Real.exp_le_exp.mpr
      calc lam * s ≤ |lam| * s := mul_le_mul_of_nonneg_right (le_abs_self lam) hs'.1
           _ ≤ |lam| := by nlinarith [abs_nonneg lam]
    rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hw,
      Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    calc
      _ = Real.exp (lam * s) * (w * ‖H t (y - s)‖) := by ring
      _ ≤ Real.exp (lam * s) * C := mul_le_mul_of_nonneg_left (hC (y - s)) (Real.exp_pos _).le
      _ ≤ Real.exp |lam| * C := mul_le_mul_of_nonneg_right he hC₀
  rw [intervalIntegral.integral_const_mul, norm_mul, Real.norm_eq_abs w, abs_of_nonneg hw] at hi
  dsimp only [first]
  rw [norm_mul, mul_left_comm, mul_assoc]
  exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)

theorem first_rapid (lam : ℝ) {H : ℝ → ℝ → ℝ} (hH : Rapid2 H) : Rapid2 (first lam H) := by
  refine ⟨first_contDiff lam hH.smooth, fun w J => ?_⟩
  obtain ⟨C, hC⟩ := hH.bound w J
  refine ⟨‖(1 - Real.exp lam)⁻¹‖ * Real.exp |lam| * C, fun t ht y => ?_⟩
  rw [first_wordD lam hH.smooth]
  exact first_weighted_bound lam t (by positivity) (hC t ht) y

end PeriodicInverse

namespace RapidCalculus
open scoped ContDiff

section LinearWords
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem biD_add {F G : ℝ → ℝ → A}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (hG : ContDiff ℝ ∞ (Function.uncurry G))
    (i : Bool) : biD i (F + G) = biD i F + biD i G := by
  funext t y
  cases i
  · exact deriv_add ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y)
      ((hG.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y)
  · exact deriv_add ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
      ((hG.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)

theorem wordD_add {F G : ℝ → ℝ → A}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (hG : ContDiff ℝ ∞ (Function.uncurry G))
    (w : List Bool) : wordD w (F + G) = wordD w F + wordD w G := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [wordD_cons, ih, biD_add (wordD_contDiff hF w) (wordD_contDiff hG w)]; rfl

theorem biD_scale (c : ℝ) {F : ℝ → ℝ → A}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (i : Bool) :
    biD i (c • F) = c • biD i F := by
  funext t y
  cases i
  · exact (((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y).hasDerivAt.const_smul c).deriv
  · exact (((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt.const_smul c).deriv

theorem wordD_scale (c : ℝ) {F : ℝ → ℝ → A}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (w : List Bool) :
    wordD w (c • F) = c • wordD w F := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [wordD_cons, ih, biD_scale c (wordD_contDiff hF w)]; rfl

theorem Rapid2.add {F G : ℝ → ℝ → A} (hF : Rapid2 F) (hG : Rapid2 G) : Rapid2 (F + G) := by
  refine ⟨hF.smooth.add hG.smooth, fun w J => ?_⟩
  obtain ⟨C, hC⟩ := hF.bound w J
  obtain ⟨D, hD⟩ := hG.bound w J
  refine ⟨C + D, fun t ht y => ?_⟩
  rw [wordD_add hF.smooth hG.smooth]
  change (1 + t) ^ J * ‖wordD w F t y + wordD w G t y‖ ≤ C + D
  calc
    _ ≤ (1 + t) ^ J * (‖wordD w F t y‖ + ‖wordD w G t y‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ C + D := by rw [mul_add]; exact add_le_add (hC t ht y) (hD t ht y)

theorem Rapid2.scale {F : ℝ → ℝ → A} (hF : Rapid2 F) (c : ℝ) : Rapid2 (c • F) := by
  refine ⟨contDiff_const.smul hF.smooth, fun w J => ?_⟩
  obtain ⟨C, hC⟩ := hF.bound w J
  refine ⟨‖c‖ * C, fun t ht y => ?_⟩
  rw [wordD_scale c hF.smooth]
  change (1 + t) ^ J * ‖c • wordD w F t y‖ ≤ ‖c‖ * C
  rw [norm_smul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hC t ht y) (norm_nonneg _)

theorem Rapid2.neg {F : ℝ → ℝ → A} (hF : Rapid2 F) : Rapid2 (-F) := by
  simpa only [neg_one_smul] using hF.scale (-1)

theorem Rapid2.sub {F G : ℝ → ℝ → A} (hF : Rapid2 F) (hG : Rapid2 G) : Rapid2 (F - G) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg
end LinearWords

theorem biD_mul {F G : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (hG : ContDiff ℝ ∞ (Function.uncurry G))
    (i : Bool) : biD i (F * G) = biD i F * G + F * biD i G := by
  funext t y
  cases i
  · exact deriv_mul ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y)
      ((hG.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y)
  · exact deriv_mul ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
      ((hG.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)

theorem Rapid2.mul {F G : ℝ → ℝ → ℝ} (hF : Rapid2 F) (hG : Rapid2 G) : Rapid2 (F * G) := by
  refine ⟨hF.smooth.mul hG.smooth, fun w J => ?_⟩
  induction w using List.reverseRecOn generalizing F G with
  | nil =>
    obtain ⟨C, hC⟩ := hF.bound [] J
    obtain ⟨D, hD⟩ := hG.bound [] 0
    have hD₀ : 0 ≤ D := by
      have hz : ‖G 0 0‖ ≤ D := by simpa using hD 0 le_rfl 0
      exact (norm_nonneg _).trans hz
    refine ⟨C * D, fun t ht y => ?_⟩
    change (1 + t) ^ J * ‖F t y * G t y‖ ≤ C * D
    rw [norm_mul, ← mul_assoc]
    calc
      _ ≤ ((1 + t) ^ J * ‖F t y‖) * D := mul_le_mul_of_nonneg_left (by simpa using hD t ht y) (by positivity)
      _ ≤ C * D := mul_le_mul_of_nonneg_right (hC t ht y) hD₀
  | append_singleton w i ih =>
    obtain ⟨C, hC⟩ := ih (hF.biD i) hG
    obtain ⟨D, hD⟩ := ih hF (hG.biD i)
    refine ⟨C + D, fun t ht y => ?_⟩
    rw [wordD_append, wordD_cons, wordD_nil, biD_mul hF.smooth hG.smooth,
      wordD_add (F := RapidCalculus.biD i F * G) (G := F * RapidCalculus.biD i G) ((partial_contDiff hF.smooth i).mul hG.smooth) (hF.smooth.mul (partial_contDiff hG.smooth i))]
    change (1 + t) ^ J * ‖wordD w (RapidCalculus.biD i F * G) t y + wordD w (F * RapidCalculus.biD i G) t y‖ ≤ C + D
    calc
      _ ≤ (1 + t) ^ J * (‖wordD w (RapidCalculus.biD i F * G) t y‖ + ‖wordD w (F * RapidCalculus.biD i G) t y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ C + D := by rw [mul_add]; exact add_le_add (hC t ht y) (hD t ht y)

end RapidCalculus

namespace PeriodicInverse
open scoped ContDiff
open RapidCalculus

def screened (lam : ℝ) (H : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := first (-lam) (first lam H)

theorem screened_contDiff (lam : ℝ) {H : ℝ → ℝ → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) :
    ContDiff ℝ ∞ (Function.uncurry (screened lam H)) :=
  first_contDiff (-lam) (first_contDiff lam hH)

theorem screened_periodic (lam : ℝ) {H : ℝ → ℝ → ℝ}
    (hp : ∀ t, Function.Periodic (H t) 1) (t : ℝ) :
    Function.Periodic (screened lam H t) 1 :=
  first_periodic (-lam) (first_periodic lam hp) t

theorem screened_rapid (lam : ℝ) {H : ℝ → ℝ → ℝ} (hH : Rapid2 H) : Rapid2 (screened lam H) :=
  first_rapid (-lam) (first_rapid lam hH)

theorem screened_equation (lam : ℝ) (hlam : lam ≠ 0) {H : ℝ → ℝ → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) (hp : ∀ t, Function.Periodic (H t) 1)
    (t y : ℝ) : biD false (biD false (screened lam H)) t y =
      lam ^ 2 * screened lam H t y + H t y := by
  have hs : ContDiff ℝ ∞ (first lam H t) :=
    (first_contDiff lam hH).comp (contDiff_const.prodMk contDiff_id)
  have hw : ContDiff ℝ ∞ (screened lam H t) :=
    (screened_contDiff lam hH).comp (contDiff_const.prodMk contDiff_id)
  have hid : deriv (screened lam H t) = fun z => -lam * screened lam H t z + first lam H t z := by
    funext z
    exact first_equation (-lam) (neg_ne_zero.mpr hlam) (first_contDiff lam hH) (first_periodic lam hp) t z
  change deriv (deriv (screened lam H t)) y = _
  rw [hid]
  have hd := (((hw.differentiable (by simp) y).hasDerivAt).const_mul (-lam)).add
    ((hs.differentiable (by simp) y).hasDerivAt)
  have hd' : deriv (fun z => -lam * screened lam H t z + first lam H t z) y =
      -lam * deriv (screened lam H t) y + deriv (first lam H t) y := hd.deriv
  rw [hd', congrFun hid y]
  have hh := first_equation lam hlam hH hp t y
  change deriv (first lam H t) y = _ at hh
  rw [hh]
  ring

end PeriodicInverse

end
end PeriodicLattice

end OAI
