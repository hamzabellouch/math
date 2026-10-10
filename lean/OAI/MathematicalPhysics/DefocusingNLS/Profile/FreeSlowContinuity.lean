import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowUniformGrowth

namespace OAI

/-! Joint continuity on the small real parameter rectangle used for the free profile. -/

open MeasureTheory Filter Topology
namespace DefocusingNLS

/-- A fixed rectangle containing the free-profile parameter disk. -/
def freeParameterRectangle : Set (ℝ × ℝ) :=
  {p | |p.1| ≤ 1 ∧ 1 ≤ p.2 ∧ p.2 ≤ 4}

noncomputable def freeShiftedQ (a : ℝ) (p : ℝ × ℝ) : ℂ := a-Complex.I*p.1
noncomputable def freeSpatialArgument (p : ℝ × ℝ) : ℂ := -Complex.I*p.2

private theorem continuous_freeShiftedQ (a : ℝ) : Continuous (freeShiftedQ a) := by
  unfold freeShiftedQ
  fun_prop

private theorem continuous_freeSpatialArgument : Continuous freeSpatialArgument := by
  unfold freeSpatialArgument
  fun_prop

private theorem freeSpatialArgument_slit {p : ℝ × ℝ} (hp : p ∈ freeParameterRectangle) :
    freeSpatialArgument p ∈ Complex.slitPlane := by
  simp only [Complex.mem_slitPlane_iff, freeSpatialArgument, Complex.mul_im,
    Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  right
  dsimp [freeParameterRectangle] at hp
  linarith

private theorem free_parameter_mass_bound (m : ℕ) (a : ℝ)
    {p : ℝ × ℝ} (hp : p ∈ freeParameterRectangle) :
    ‖(m : ℂ)-1-freeShiftedQ a p‖ ≤ |(m : ℝ)-1-a|+1 := by
  have he : (m : ℂ)-1-freeShiftedQ a p =
      (((m : ℝ)-1-a : ℝ) : ℂ)+Complex.I*p.1 := by
    simp only [freeShiftedQ, Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]
    ring
  rw [he]
  have hn := norm_add_le ((((m : ℝ)-1-a : ℝ) : ℂ)) (Complex.I*p.1)
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul] at hn
  exact hn.trans (add_le_add le_rfl hp.1)

private theorem continuousOn_free_regularizedSlowKernel (a : ℝ) (m : ℕ)
    {u : ℝ} (hu : 0 < u) :
    ContinuousOn (fun p => regularizedSlowKernel (freeShiftedQ a p) m
      (freeSpatialArgument p) u) freeParameterRectangle := by
  have hq : ContinuousOn (freeShiftedQ a) freeParameterRectangle :=
    (continuous_freeShiftedQ a).continuousOn
  have hx : ContinuousOn freeSpatialArgument freeParameterRectangle :=
    continuous_freeSpatialArgument.continuousOn
  have hx0 (p : ℝ × ℝ) (hp : p ∈ freeParameterRectangle) : freeSpatialArgument p ≠ 0 :=
    Complex.slitPlane_ne_zero (freeSpatialArgument_slit hp)
  have hbase : ContinuousOn (fun p => 1+(u : ℂ)/freeSpatialArgument p)
      freeParameterRectangle := continuousOn_const.add (continuousOn_const.div hx hx0)
  have hexp : ContinuousOn (fun p => (m : ℂ)-1-freeShiftedQ a p) freeParameterRectangle :=
    continuousOn_const.sub hq
  have hp := hbase.cpow hexp (fun p hp =>
    one_add_real_div_mem_slitPlane (freeSpatialArgument p) (by simp [freeSpatialArgument]) hu.le)
  have huq : ContinuousOn (fun p => (u : ℂ)^(freeShiftedQ a p-1)) freeParameterRectangle :=
    (hq.sub continuousOn_const).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hu.ne'))
  unfold regularizedSlowKernel regularizingBracket
  convert! (continuousOn_const.mul huq).mul (hp.sub continuousOn_const) using 1

/-- Joint continuity of the actual integral H, including the q=0 normalization. -/
theorem continuousOn_free_regularizedSlowSolution (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    ContinuousOn (fun p => regularizedSlowSolution (freeShiftedQ a p) m
      (freeSpatialArgument p)) freeParameterRectangle := by
  let M : ℝ := |(m : ℝ)-1-a|+1
  let K : ℝ := M*Real.exp (Real.pi*M)/1*(1+(1:ℝ)⁻¹)^(M+1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hint : ContinuousOn (fun p => ∫ u : ℝ in Set.Ioi 0,
      regularizedSlowKernel (freeShiftedQ a p) m (freeSpatialArgument p) u)
      freeParameterRectangle := by
    apply continuousOn_of_dominated
      (bound := fun u => K*slowParameterMajorant a a M u)
    · intro p _
      exact (measurable_regularizedSlowKernel _ _ _).aestronglyMeasurable.restrict
    · intro p hp
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      apply regularizedSlowKernel_uniform_spatial_bound (freeShiftedQ a p) m
        (freeSpatialArgument p) a a M 1 hM (by norm_num)
      · simp [freeShiftedQ]
      · simp [freeShiftedQ]
      · exact free_parameter_mass_bound m a hp
      · simp [freeSpatialArgument]
      · simpa [freeSpatialArgument, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hp.2.1] : 0 ≤ p.2)] using hp.2.1
      · exact hu
    · exact (integrable_slowParameterMajorant a a M (by linarith) le_rfl hM).const_mul K
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact continuousOn_free_regularizedSlowKernel a m hu
  have hq : ContinuousOn (freeShiftedQ a) freeParameterRectangle :=
    (continuous_freeShiftedQ a).continuousOn
  have hx : ContinuousOn freeSpatialArgument freeParameterRectangle :=
    continuous_freeSpatialArgument.continuousOn
  have hpow := hx.cpow hq.neg (fun _ hp => freeSpatialArgument_slit hp)
  have hgamma : ContinuousOn (fun p => (Complex.Gamma (freeShiftedQ a p))⁻¹)
      freeParameterRectangle := Complex.differentiable_one_div_Gamma.continuous.continuousOn.comp
        hq (Set.mapsTo_univ _ _)
  unfold regularizedSlowSolution
  convert! hpow.mul (continuousOn_const.add (hgamma.mul hint)) using 1

end DefocusingNLS

end OAI
