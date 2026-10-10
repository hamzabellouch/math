import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CappedWells

namespace OAI

/-! C² regularity of the manuscript's rational quintic nuclear cap. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

private theorem hasDerivAt_wellSplice (f g df dg : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (hvalue : f a = g a) (hderiv : df a = dg a) (x : ℝ) :
    HasDerivAt (fun t => if t ≤ a then f t else g t)
      (if x ≤ a then df x else dg x) x := by
  rcases lt_trichotomy x a with hx | he | hx
  · rw [ite_eq_left hx.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with t ht
    exact ite_eq_left ht.le
  · subst x
    rw [ite_eq_left (le_refl a)]
    have hl : HasDerivWithinAt (fun t => if t ≤ a then f t else g t)
        (df a) (Iic a) a :=
      (hf a).hasDerivWithinAt.congr_of_mem
        (fun t ht => ite_eq_left ht) (le_refl a)
    have hr : HasDerivWithinAt (fun t => if t ≤ a then f t else g t)
        (df a) (Ici a) a := by
      rw [hderiv]
      apply (hg a).hasDerivWithinAt.congr_of_mem _ (le_refl a)
      intro t ht
      by_cases hta : t ≤ a
      · have he : t = a := le_antisymm hta ht
        subst t
        simpa only [ite_eq_left (le_refl a)] using hvalue
      · exact ite_eq_right hta
    have h := hl.union hr
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using h
  · rw [ite_eq_right (not_le.mpr hx)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact ite_eq_right (not_le.mpr ht)

private theorem contDiff_two_wellSplice (f g : ℝ → ℝ) (a : ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hvalue : f a = g a) (hfirst : deriv f a = deriv g a)
    (hsecond : deriv (deriv f) a = deriv (deriv g) a) :
    ContDiff ℝ 2 (fun t => if t ≤ a then f t else g t) := by
  have hdf : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hdg : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hd := hasDerivAt_wellSplice f g (deriv f) (deriv g) a
    (fun x => (hf.differentiable (by norm_num) x).hasDerivAt)
    (fun x => (hg.differentiable (by norm_num) x).hasDerivAt) hvalue hfirst
  have hd' := hasDerivAt_wellSplice (deriv f) (deriv g)
    (deriv (deriv f)) (deriv (deriv g)) a
    (fun x => (hdf.differentiable (by norm_num) x).hasDerivAt)
    (fun x => (hdg.differentiable (by norm_num) x).hasDerivAt) hfirst hsecond
  have heq : deriv (fun t => if t ≤ a then f t else g t) =
      fun t => if t ≤ a then deriv f t else deriv g t := by
    funext t
    exact (hd t).deriv
  have heq' : deriv (fun t => if t ≤ a then deriv f t else deriv g t) =
      fun t => if t ≤ a then deriv (deriv f) t else deriv (deriv g) t := by
    funext t
    exact (hd' t).deriv
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hd x).differentiableAt, by simp, ?_⟩
  rw [heq, contDiff_one_iff_deriv, heq']
  refine ⟨fun x => (hd' x).differentiableAt, ?_⟩
  exact (hdf.continuous_deriv (by norm_num)).if_le
    (hdg.continuous_deriv (by norm_num)) continuous_id continuous_const
      (fun x hx => by simpa only [hx] using hsecond)

private def wellMiddle (t : ℝ) := wellTransition (16 * t - 1)
private def wellMiddlePrime (t : ℝ) := 480 * (16 * t - 1) ^ 2 * (16 * t - 2) ^ 2
private def wellMiddleSecond (t : ℝ) :=
  15360 * (16 * t - 1) * (16 * t - 2) * (32 * t - 3)

private theorem wellMiddle_hasDerivAt (t : ℝ) :
    HasDerivAt wellMiddle (wellMiddlePrime t) t := by
  have hlin := ((hasDerivAt_id t).const_mul 16).sub_const 1
  convert (((hlin.pow 5).const_mul 6).sub ((hlin.pow 4).const_mul 15)).add
    ((hlin.pow 3).const_mul 10) using 1 <;> (try funext y) <;>
    (dsimp [wellMiddle, wellTransition, wellMiddlePrime]; all_goals ring)

private theorem wellMiddlePrime_hasDerivAt (t : ℝ) :
    HasDerivAt wellMiddlePrime (wellMiddleSecond t) t := by
  have hlin := ((hasDerivAt_id t).const_mul 16).sub_const 1
  have hlin' := ((hasDerivAt_id t).const_mul 16).sub_const 2
  convert ((hlin.pow 2).const_mul 480).mul (hlin'.pow 2) using 1 <;> (try funext y) <;>
    (dsimp [wellMiddlePrime, wellMiddleSecond]; all_goals ring)

private theorem deriv_wellMiddle : deriv wellMiddle = wellMiddlePrime := by
  funext t
  exact (wellMiddle_hasDerivAt t).deriv

private theorem deriv2_wellMiddle : deriv (deriv wellMiddle) = wellMiddleSecond := by
  rw [deriv_wellMiddle]
  funext t
  exact (wellMiddlePrime_hasDerivAt t).deriv

/-- All cap data are rational polynomials; both derivatives match the constant
pieces at the endpoints of the transition interval. -/
theorem wellCap_contDiff_two : ContDiff ℝ 2 wellCap := by
  have hmiddle : ContDiff ℝ 2 wellMiddle := by
    unfold wellMiddle wellTransition
    fun_prop
  let upper : ℝ → ℝ := fun t => if t ≤ 1 / 8 then wellMiddle t else 1
  have hupper : ContDiff ℝ 2 upper := by
    apply contDiff_two_wellSplice wellMiddle (fun _ => 1) (1 / 8) hmiddle contDiff_const
    · norm_num [wellMiddle, wellTransition]
    · rw [deriv_wellMiddle]
      norm_num [wellMiddlePrime]
    · rw [deriv2_wellMiddle]
      norm_num [wellMiddleSecond]
  have hlocal : upper =ᶠ[𝓝 (1 / 16 : ℝ)] wellMiddle := by
    filter_upwards [Iio_mem_nhds (by norm_num : (1 / 16 : ℝ) < 1 / 8)] with t ht
    exact ite_eq_left ht.le
  have hcap : ContDiff ℝ 2 (fun t => if t ≤ 1 / 16 then 0 else upper t) := by
    apply contDiff_two_wellSplice (fun _ => 0) upper (1 / 16) contDiff_const hupper
    · norm_num [upper, wellMiddle, wellTransition]
    · rw [hlocal.deriv_eq, deriv_wellMiddle]
      norm_num [wellMiddlePrime]
    · rw [hlocal.deriv.deriv_eq, deriv2_wellMiddle]
      norm_num [wellMiddleSecond]
  convert hcap using 1
  funext t
  unfold wellCap upper
  by_cases h0 : t ≤ 1 / 16
  · simp only [ite_eq_left h0]
  · simp only [ite_eq_right h0]
    by_cases h1 : 1 / 8 ≤ t
    · rw [ite_eq_left h1]
      by_cases ht : t ≤ 1 / 8
      · have he : t = 1 / 8 := le_antisymm ht h1
        subst t
        norm_num [wellMiddle, wellTransition]
      · exact (ite_eq_right ht).symm
    · have ht : t ≤ 1 / 8 := (lt_of_not_ge h1).le
      simp only [ite_eq_right h1, ite_eq_left ht, wellMiddle]

/-- Despite the two Coulomb poles, the capped field is globally C². The proof
uses actual vanishing neighbourhoods at the poles and ordinary differentiation
away from them. -/
theorem cappedSitePotential_contDiff_two {D q q' : ℝ} (hD : 128 ≤ D)
    (center displacement : Position) (hdisp : ‖displacement‖ ≤ 4) :
    ContDiff ℝ 2 (cappedSitePotential D q q' center displacement) := by
  have hD0 : 0 < D := by linarith
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hprimary : x = center
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds center (by positivity : 0 < D / 16)] with y hy
    exact cappedSitePotential_zero_near_primary hD0 center displacement y
      (by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hy).le)
  by_cases hsecondary : x = center + displacement
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (center + displacement)
      (by positivity : 0 < D / 32)] with y hy
    apply cappedSitePotential_zero_near_secondary hD center displacement y hdisp
    have he : y - center - displacement = y - (center + displacement) := by abel
    rw [he]
    exact (Metric.mem_ball.mp hy).le
  have hp : x - center ≠ 0 := sub_ne_zero.mpr hprimary
  have hs : x - center - displacement ≠ 0 := by
    intro h
    apply hsecondary
    have he : x - center - displacement = x - (center + displacement) := by abel
    exact sub_eq_zero.mp (he.symm.trans h)
  have hnorm : ContDiffAt ℝ 2 (fun y : Position => ‖y - center‖) x :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ hp
  have hnorm' : ContDiffAt ℝ 2 (fun y : Position => ‖y - center - displacement‖) x :=
    ((contDiffAt_id.sub contDiffAt_const).sub contDiffAt_const).norm ℝ hs
  have hcap : ContDiffAt ℝ 2 (fun y : Position => wellCap (‖y - center‖ / D)) x :=
    wellCap_contDiff_two.contDiffAt.comp x (hnorm.div_const D)
  exact hcap.mul ((contDiffAt_const.mul (hnorm.inv (norm_ne_zero_iff.mpr hp))).add
    (contDiffAt_const.mul (hnorm'.inv (norm_ne_zero_iff.mpr hs))))

theorem backgroundPotential_contDiff_two {m : ℕ} {D q q' : ℝ} (hD : 128 ≤ D)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) : ContDiff ℝ 2 (backgroundPotential D q q' center displacement site) := by
  apply ContDiff.sum
  intro j _
  by_cases hj : j = site
  · simp only [ite_eq_left hj]
    exact contDiff_const
  · simp only [ite_eq_right hj]
    exact cappedSitePotential_contDiff_two hD _ _ (hdisp j)

end ContinuumCoulomb

end

end OAI
