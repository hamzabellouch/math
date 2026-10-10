import OAI.Geometry.RCD.Coordinates.NormalizedUniformL2

namespace OAI

/-! # Passing uniform local square-integral bounds to an open ball -/

open Set Metric Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem ball_L2_of_local_integral_bound {n : ℕ} (μ : Measure (Euclidean n))
    {S B : ℝ} (hS : 0<S) (hB : 0≤B) (f : Euclidean n → ℝ) (hf : Measurable f)
    (hlocal : ∀ ρ : ℝ, 0<ρ → ρ<S → MemLp f 2 (μ.restrict (ball 0 ρ)))
    (hbound : ∀ ρ : ℝ, 0<ρ → ρ<S → (∫ z in ball 0 ρ, (f z)^2 ∂μ)≤B) :
    MemLp f 2 (μ.restrict (ball 0 S)) ∧ (∫ z in ball 0 S, (f z)^2 ∂μ)≤B := by
  let T : ℕ → ℝ := fun m => S*(1-1/((m+2:ℕ):ℝ))
  have hT (m : ℕ) : 0<T m := by
    apply mul_pos hS
    have hd : (1:ℝ)<((m+2:ℕ):ℝ) := by norm_cast; omega
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hd)
  have hTS (m : ℕ) : T m<S := by
    have hd : 0<1/((m+2:ℕ):ℝ) := by positivity
    dsimp only [T]
    nlinarith
  have hTm : Monotone T := by
    intro i j hij
    apply mul_le_mul_of_nonneg_left _ hS.le
    apply sub_le_sub_left
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 2)
  have hsets : Monotone (fun m => ball (0:Euclidean n) (T m)) :=
    fun i j hij => ball_subset_ball (hTm hij)
  have hTlim : Tendsto T atTop (𝓝 S) := by
    have hd : Tendsto (fun m : ℕ => 1/((m+2:ℕ):ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)
    simpa only [sub_zero,mul_one] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub hd).const_mul S
  have hunion : (⋃ m, ball (0:Euclidean n) (T m))=ball 0 S := by
    ext z
    constructor
    · intro hz
      obtain ⟨m,hm⟩ := mem_iUnion.mp hz
      exact ball_subset_ball (hTS m).le hm
    · intro hz
      have hzS : ‖z‖<S := by simpa only [mem_ball,dist_zero_right] using hz
      obtain ⟨m,hm⟩ := (hTlim.eventually (Ioi_mem_nhds hzS)).exists
      exact mem_iUnion.mpr ⟨m,by simpa only [mem_ball,dist_zero_right] using hm⟩
  have hE : (∫⁻ z in ball 0 S, ENNReal.ofReal ((f z)^2) ∂μ)≤ENNReal.ofReal B := by
    rw [← hunion,setLIntegral_iUnion_of_directed _ hsets.directed_le]
    apply iSup_le
    intro m
    rw [← ofReal_integral_eq_lintegral_ofReal (hlocal (T m) (hT m) (hTS m)).integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hbound (T m) (hT m) (hTS m))
  have hmeas : AEStronglyMeasurable f (μ.restrict (ball 0 S)) :=
    hf.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hi : Integrable (fun z => (f z)^2) (μ.restrict (ball 0 S)) :=
    ⟨hmeas.pow 2,(hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).mpr
      (hE.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨(memLp_two_iff_integrable_sq hmeas).mpr hi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)] at hE
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hE

end RegularPointCoordinates

end

end OAI
