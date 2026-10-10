import Mathlib
import OAI.Geometry.NearbyLagrangian.StepData

namespace OAI

/-! Logarithmic and spatial cutoffs with uniform small-step data. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

open Filter Set ContinuousLinearMap
open scoped ContDiff Topology

lemma smoothTransition_derivative_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, ‖deriv Real.smoothTransition t‖ ≤ B := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv_one
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))
    intro t ht
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        exact Real.smoothTransition.zero_of_nonpos hs.le
      rw [he.deriv_eq, deriv_const]
    · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      rw [he.deriv_eq, deriv_const]
  obtain ⟨B,hB⟩ := hs.exists_bound_of_continuous hc
  exact ⟨max B 0, le_max_right _ _, fun t => (hB t).trans (le_max_left _ _)⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def logCutoff (R T : ℝ) (w : E) : ℝ :=
  1 - Real.smoothTransition (Real.log (‖w‖ / R) / T)

omit [InnerProductSpace ℝ E] in
lemma logCutoff_range (R T : ℝ) (w : E) : logCutoff R T w ∈ Icc (0:ℝ) 1 := by
  have h0 := Real.smoothTransition.nonneg (Real.log (‖w‖ / R) / T)
  have h1 := Real.smoothTransition.le_one (Real.log (‖w‖ / R) / T)
  constructor <;> dsimp [logCutoff] <;> linarith

omit [InnerProductSpace ℝ E] in
lemma logCutoff_one {R T : ℝ} (hR : 0 < R) (hT : 0 < T) {w : E}
    (hw : ‖w‖ ≤ R) : logCutoff R T w = 1 := by
  have hl : Real.log (‖w‖/R) ≤ 0 := Real.log_nonpos
    (div_nonneg (norm_nonneg w) hR.le) ((div_le_one hR).mpr hw)
  rw [logCutoff, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hl hT.le)]
  ring

omit [InnerProductSpace ℝ E] in
lemma logCutoff_zero {R T : ℝ} (hR : 0 < R) (hT : 0 < T) {w : E}
    (hw : R * Real.exp T ≤ ‖w‖) : logCutoff R T w = 0 := by
  have hn : 0 < ‖w‖ / R := div_pos ((mul_pos hR (Real.exp_pos T)).trans_le hw) hR
  have he : Real.exp T ≤ ‖w‖/R := (le_div_iff₀ hR).mpr (by simpa only [mul_comm] using hw)
  have hl : T ≤ Real.log (‖w‖/R) := (Real.le_log_iff_exp_le hn).mpr he
  rw [logCutoff, Real.smoothTransition.one_of_one_le ((one_le_div hT).mpr hl)]
  ring

lemma contDiff_logCutoff {R T : ℝ} (hR : 0 < R) (hT : 0 < T) :
    ContDiff ℝ ∞ (logCutoff R T : E → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = 0
  · subst w
    have he : logCutoff R T =ᶠ[𝓝 (0:E)] fun _ => 1 := by
      filter_upwards [Metric.ball_mem_nhds (0:E) hR] with u hu
      exact logCutoff_one hR hT (mem_ball_zero_iff.mp hu).le
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hn : ContDiffAt ℝ ∞ (fun u : E => ‖u‖/R) w :=
      (contDiffAt_norm ℝ hw).div_const R
    have hl : ContDiffAt ℝ ∞ (fun u : E => Real.log (‖u‖/R)/T) w :=
      (hn.log (div_ne_zero (norm_ne_zero_iff.mpr hw) hR.ne')).div_const T
    exact contDiffAt_const.sub (Real.smoothTransition.contDiffAt.comp w hl)

omit [InnerProductSpace ℝ E] in
lemma hasCompactSupport_logCutoff [ProperSpace E] {R T : ℝ}
    (hR : 0 < R) (hT : 0 < T) : HasCompactSupport (logCutoff R T : E → ℝ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0:E) (R * Real.exp T))
  intro w hw
  apply logCutoff_zero hR hT
  exact (lt_of_not_ge (fun hh => hw (mem_closedBall_zero_iff.mpr hh))).le

lemma fderiv_logCutoff {R T : ℝ} (hR : 0 < R) (hT : 0 < T) {w : E} (hw : w ≠ 0) :
    fderiv ℝ (logCutoff R T) w =
      (-(deriv Real.smoothTransition (Real.log (‖w‖/R)/T)) / (T * ‖w‖)) •
        fderiv ℝ (norm : E → ℝ) w := by
  have hn : DifferentiableAt ℝ (norm : E → ℝ) w :=
    (contDiffAt_norm ℝ hw).differentiableAt (by simp : (1 : ℕ∞ω) ≠ 0)
  have hnorm : HasFDerivAt (fun u : E => ‖u‖/R)
      (R⁻¹ • fderiv ℝ (norm : E → ℝ) w) w := by
    simpa only [div_eq_mul_inv] using hn.hasFDerivAt.mul_const R⁻¹
  have hlog := (Real.hasDerivAt_log (div_ne_zero (norm_ne_zero_iff.mpr hw) hR.ne')).comp_hasFDerivAt w hnorm
  have ht : HasFDerivAt (𝕜 := ℝ) (fun u : E => Real.log (‖u‖/R)/T)
      (T⁻¹ • ((‖w‖/R)⁻¹ • (R⁻¹ • fderiv ℝ (norm : E → ℝ) w))) w := by
    convert! hlog.mul_const T⁻¹ using 1
  have hs := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
    (Real.log (‖w‖/R)/T)).hasDerivAt.comp_hasFDerivAt w ht
  have hd := (hasFDerivAt_const (1:ℝ) w).sub hs
  change HasFDerivAt (logCutoff R T) _ w at hd
  rw [hd.fderiv]
  ext v
  simp only [zero_sub, neg_apply, smul_apply, smul_eq_mul]
  field_simp [hR.ne', hT.ne', norm_ne_zero_iff.mpr hw]

lemma norm_fderiv_logCutoff_le {R T B : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hB : 0 ≤ B) (hb : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ B)
    {w : E} (hw : w ≠ 0) :
    ‖fderiv ℝ (logCutoff R T) w‖ ≤ (B/T)/‖w‖ := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hnd : ‖fderiv ℝ (norm : E → ℝ) w‖ ≤ 1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : E → ℝ)) (x₀ := w)
  rw [fderiv_logCutoff hR hT hw, norm_smul, norm_div, norm_neg, norm_mul,
    Real.norm_of_nonneg hT.le, Real.norm_of_nonneg hn.le]
  calc
    _ ≤ (B / (T * ‖w‖)) * 1 := by gcongr; exact hb _
    _ = (B/T)/‖w‖ := by ring

theorem exists_logarithmic_cutoff [ProperSpace E] {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ w, χ w ∈ Icc (0:ℝ) 1) ∧
      (∀ w, ‖w‖ ≤ R → χ w = 1) ∧
      ∀ w, w ≠ 0 → ‖fderiv ℝ χ w‖ ≤ ε/‖w‖ := by
  obtain ⟨B,hB,hb⟩ := smoothTransition_derivative_bound
  let T := (B+1)/ε
  have hT : 0 < T := div_pos (by linarith) hε
  have hBT : B/T ≤ ε := (div_le_iff₀ hT).mpr (by dsimp [T]; field_simp; nlinarith)
  refine ⟨logCutoff R T, contDiff_logCutoff hR hT,
    hasCompactSupport_logCutoff hR hT, logCutoff_range R T,
    fun w hw => logCutoff_one hR hT hw, ?_⟩
  intro w hw
  exact (norm_fderiv_logCutoff_le hR hT hB hb hw).trans
    (div_le_div_of_nonneg_right hBT (norm_nonneg w))

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open Filter Set ContinuousLinearMap
open scoped ContDiff Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_logarithmic_cutoff_finite {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ χ : V → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ w, χ w ∈ Icc (0:ℝ) 1) ∧
      (∀ w, ‖w‖ ≤ R → χ w = 1) ∧
      ∀ w, w ≠ 0 → ‖fderiv ℝ χ w‖ ≤ ε/‖w‖ := by
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    ((Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv).trans
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ V))).symm
  let A : ℝ := ‖e.toContinuousLinearMap‖
  let B : ℝ := ‖e.symm.toContinuousLinearMap‖
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hAB : 0 < A*B+1 := by positivity
  obtain ⟨χ,hχ,hχc,hχr,hχ1,hχb⟩ := exists_logarithmic_cutoff
    (E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))
    (show 0 < A*R+1 by positivity) (div_pos hε hAB)
  refine ⟨χ ∘ e, hχ.comp e.contDiff, ?_,fun w => hχr (e w),?_,?_⟩
  · apply HasCompactSupport.intro (hχc.image e.symm.continuous)
    intro w hw
    have hew : e w ∉ tsupport χ := fun hew => hw ⟨e w,hew,e.symm_apply_apply w⟩
    exact image_eq_zero_of_notMem_tsupport (f := χ) hew
  · intro w hw
    exact hχ1 (e w) ((e.toContinuousLinearMap.le_opNorm w).trans (by dsimp [A]; nlinarith))
  · intro w hw
    have hew : e w ≠ 0 := fun h => hw (e.injective (h.trans (map_zero e).symm))
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hn' : 0 < ‖e w‖ := norm_pos_iff.mpr hew
    have hcomp := ((hχ.differentiable (by simp) (e w)).hasFDerivAt.comp w e.toContinuousLinearMap.hasFDerivAt).fderiv
    rw [hcomp]
    have hnorm : ‖w‖ ≤ B * ‖e w‖ := by
      simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using e.symm.toContinuousLinearMap.le_opNorm (e w)
    calc
      ‖(fderiv ℝ χ (e w)).comp e.toContinuousLinearMap‖ ≤ ‖fderiv ℝ χ (e w)‖ * A := by
        exact ContinuousLinearMap.opNorm_comp_le (fderiv ℝ χ (e w)) e.toContinuousLinearMap
      _ ≤ (ε/(A*B+1)/‖e w‖)*A := mul_le_mul_of_nonneg_right (hχb _ hew) hA
      _ ≤ ε/‖w‖ := by
        rw [le_div_iff₀ hn]
        calc
          ε/(A*B+1)/‖e w‖*A*‖w‖ ≤ ε/(A*B+1)/‖e w‖*A*(B*‖e w‖) :=
            mul_le_mul_of_nonneg_left hnorm (by positivity)
          _ = ε * (A*B)/(A*B+1) := by field_simp
          _ ≤ ε := (div_le_iff₀ hAB).mpr (by nlinarith)

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open Filter Set Function
open scoped ContDiff Topology Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_spatial_cutoff {D U : Set E} (hD : IsCompact D)
    (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ ζ : E → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ U ∧
      (∀ x, ζ x ∈ Icc (0:ℝ) 1) ∧ ∀ x ∈ D, ζ =ᶠ[𝓝 x] fun _ => 1 := by
  obtain ⟨L,hL,hDL,hLU⟩ := exists_compact_between hD hU hDU
  obtain ⟨f,hf1,hf0,hfr⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ,E) hD.isClosed hDL (n := ⊤)
  have hfs : tsupport (f : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (hf0 x hn)
  refine ⟨f, f.contMDiff.contDiff, hL.of_isClosed_subset (isClosed_tsupport _) hfs,
    hfs.trans hLU, hfr, ?_⟩
  intro x hx
  exact (mem_nhdsSet_iff_forall.mp hf1) x hx

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in

theorem exists_shift_buffer {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ δ > 0, ∀ x ∈ K, ∀ v, ‖v‖ ≤ 2*δ → x+v ∈ U := by
  obtain ⟨η,hη,hηU⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨η/4, by positivity, ?_⟩
  intro x hx v hv
  apply hηU
  rw [Metric.mem_thickening_iff]
  refine ⟨x,hx,?_⟩
  rw [dist_eq_norm, add_sub_cancel_left]
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in

lemma cutoff_cover_of_projected_support {D : Set E} (hD : IsClosed D)
    {ζ : E → ℝ} {σ : E × E → ℝ}
    (hζ : ∀ x ∈ D, ζ =ᶠ[𝓝 x] fun _ => 1)
    (hσ : ∀ x ∉ D, ∀ p, σ (x,p) = 0) (x : E) :
    (ζ =ᶠ[𝓝 x] fun _ => 1) ∨ (∀ᶠ y in 𝓝 x, ∀ p, σ (y,p) = 0) := by
  by_cases hx : x ∈ D
  · exact Or.inl (hζ x hx)
  · right
    filter_upwards [hD.isOpen_compl.mem_nhds hx] with y hy
    exact hσ y hy

theorem exists_displacement_cutoff {δ : ℝ} (hδ : 0 < δ) :
    ∃ β : E → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      (∀ z, β z ∈ Icc (0:ℝ) 1) ∧
      (∀ z, ‖z‖ ≤ δ → β z = 1) ∧
      ∀ z, β z ≠ 0 → ‖z‖ < 2*δ := by
  let f : ContDiffBump (0:E) := ⟨δ,2*δ,hδ,by linarith⟩
  refine ⟨f,f.contDiff,f.hasCompactSupport,fun z => ⟨f.nonneg,f.le_one⟩,?_,?_⟩
  · intro z hz
    exact f.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hz)
  · intro z hz
    have hz' : z ∈ Function.support f := hz
    rw [f.support_eq, mem_ball_zero_iff] at hz'
    exact hz'

omit [FiniteDimensional ℝ E] in

lemma product_cutoff_shift_mem {U : Set E} {ζ β : E → ℝ} {δ : ℝ}
    (hζ : ∀ x, ζ x ∈ Icc (0:ℝ) 1) (hβ : ∀ z, β z ∈ Icc (0:ℝ) 1)
    (hβs : ∀ z, β z ≠ 0 → ‖z‖ < 2*δ)
    (hbuf : ∀ x ∈ tsupport ζ, ∀ v, ‖v‖ ≤ 2*δ → x+v ∈ U)
    (x : E) (hx : x ∈ U) (z : E) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    x + (ζ x * β z * t) • z ∈ U := by
  by_cases hzx : ζ x = 0
  · simpa only [hzx,zero_mul,zero_smul,add_zero] using hx
  by_cases hbz : β z = 0
  · simpa only [hbz,mul_zero,zero_mul,zero_smul,add_zero] using hx
  have hk0 : 0 ≤ ζ x * β z * t := mul_nonneg (mul_nonneg (hζ x).1 (hβ z).1) ht.1
  have hk1 : ζ x * β z * t ≤ 1 := by
    calc
      _ ≤ 1*1*1 := mul_le_mul
        (mul_le_mul (hζ x).2 (hβ z).2 (hβ z).1 (by norm_num)) ht.2 ht.1 (by norm_num)
      _ = 1 := by ring
  apply hbuf x (subset_closure (show x ∈ Function.support ζ from hzx))
  rw [norm_smul, Real.norm_of_nonneg hk0]
  exact (mul_le_mul_of_nonneg_right hk1 (norm_nonneg z)).trans
    (by simpa only [one_mul] using (hβs z hbz).le)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in

lemma base_mem_iff_of_compact_support {ψ : E × E → E × E}
    (hψ : Function.Injective ψ) {K : Set (E × E)} {U : Set E}
    (hKU : ∀ z ∈ K, z.1 ∈ U) (hst : ∀ z ∉ K, ψ z = z) (x p : E) :
    x ∈ U ↔ (ψ (x,p)).1 ∈ U := by
  have hfix : ∀ z : E × E, z.1 ∉ U → ψ z = z := by
    intro z hz
    exact hst z (fun hk => hz (hKU z hk))
  constructor
  · intro hx
    by_contra hn
    have he : ψ (ψ (x,p)) = ψ (x,p) := hfix _ hn
    have hh : ψ (x,p) = (x,p) := hψ he
    apply hn
    rw [hh]
    exact hx
  · intro hy
    by_contra hx
    exact hx (by simpa only [hfix (x,p) hx] using hy)

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open Filter Set ContinuousLinearMap
open scoped ContDiff Topology

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] in

theorem exists_uniform_spatial_data {U : Set E} (hU : IsOpen U)
    {K : Set (E × E)} (hK : IsCompact K) (hKU : ∀ z ∈ K, z.1 ∈ U) :
    ∃ (ζ : E → ℝ) (δ : ℝ), 0 < δ ∧ ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ U ∧ (∀ x, ζ x ∈ Icc (0:ℝ) 1) ∧
      (∀ x ∈ Prod.fst '' K, ζ =ᶠ[𝓝 x] fun _ => 1) ∧
      ∀ x ∈ tsupport ζ, ∀ v, ‖v‖ ≤ 2*δ → x+v ∈ U := by
  have hpK : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hpKU : Prod.fst '' K ⊆ U := by
    rintro x ⟨z,hz,rfl⟩
    exact hKU z hz
  obtain ⟨ζ,hζ,hζc,hζU,hζr,hζ1⟩ := exists_spatial_cutoff hpK hU hpKU
  obtain ⟨δ,hδ,hbuf⟩ := exists_shift_buffer hζc hU hζU
  exact ⟨ζ,δ,hδ,hζ,hζc,hζU,hζr,hζ1,hbuf⟩

theorem exists_stepData_of_mixed {U D : Set E} (hU : IsOpen U) (hD : IsClosed D)
    (F : E × W → ℝ) (σ : E × E → ℝ) (ψ : (E × E) ≃ₜ (E × E))
    {ζ : E → ℝ} {R c C δ : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hF : ∀ x ∈ U, ∀ w, ContDiffAt ℝ ∞ F (x,w))
    (hσ : ContDiff ℝ ∞ σ) (hζ : ContDiff ℝ ∞ ζ)
    (hζr : ∀ x, ζ x ∈ Icc (0:ℝ) 1)
    (hζ1 : ∀ x ∈ D, ζ =ᶠ[𝓝 x] fun _ => 1)
    (hbuf : ∀ x ∈ tsupport ζ, ∀ v, ‖v‖ ≤ 2*δ → x+v ∈ U)
    (hσ0 : ∀ x ∉ D, ∀ p, σ (x,p) = 0)
    (hσp : ∀ X p, ‖fderiv ℝ (fun p => σ (X,p)) p‖ < δ)
    (hbase : ∀ x ∈ U, ∀ w, R ≤ ‖w‖ → ‖baseDifferential F x w‖ ≤ C * ‖w‖^2)
    (hvert : ∀ x ∈ U, ∀ w, R ≤ ‖w‖ → c * ‖w‖ ≤ ‖verticalDifferential F x w‖)
    (hψU : ∀ x p, x ∈ U ↔ (ψ (x,p)).1 ∈ U)
    (hg : ∀ x p X, X ∈ U →
      ((ψ (x,p)).1 = X ↔ fderiv ℝ (fun p => σ (X,p)) p = innerSL ℝ (x-X)))
    (hgo : ∀ x p, x ∈ U → innerSL ℝ (ψ (x,p)).2 = innerSL ℝ p +
      fderiv ℝ (fun X => σ (X,p)) (ψ (x,p)).1) :
    ∃ S : StepData (E := E) (W := W), S.U = U ∧ S.F = F ∧ S.σ = σ ∧ S.ψ = ψ ∧
      S.ζ = ζ ∧ S.δ₀ = δ ∧ HasCompactSupport S.β ∧ HasCompactSupport S.χ := by
  let ε := c / (2 * (C*δ+1))
  have hden : 0 < 2 * (C*δ+1) := by positivity
  have hε : 0 < ε := div_pos hc hden
  have hsmall : C*δ*ε < c := by
    dsimp [ε]
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    have hcd : 0 ≤ C*δ := mul_nonneg hC hδ.le
    nlinarith
  obtain ⟨β,hβ,hβc,hβr,hβ1,hβs⟩ := exists_displacement_cutoff (E := E) hδ
  obtain ⟨χ,hχ,hχc,hχr,hχ1,hχb⟩ := exists_logarithmic_cutoff_finite (V := W)
    (show 0 < R+1 by linarith) hε
  let S : StepData (E := E) (W := W) := {
    U := U, open_U := hU, F := F, σ := σ, ζ := ζ, β := β, χ := χ, ψ := ψ
    R := R, c := c, C := C, δ₀ := δ, δ₁ := ε
    R_pos := hR, c_pos := hc, C_nonneg := hC, δ₀_pos := hδ
    δ₁_nonneg := hε.le, small := hsmall
    smooth_F := hF, smooth_σ := hσ, smooth_ζ := hζ, smooth_β := hβ, smooth_χ := hχ
    ζ_range := hζr, β_range := hβr
    β_one := fun z hz => hβ1 z hz.le
    χ_one := fun w hw => hχ1 w (by linarith)
    χ_bound := hχb, σ_bound := hσp, base_bound := hbase, vertical_bound := hvert
    shift_mem := fun X hX w z => product_cutoff_shift_mem hζr hβr hβs hbuf X hX z (hχr w)
    cover := fun X _ => cutoff_cover_of_projected_support hD hζ1 hσ0 X
    ψ_base_mem := hψU, graph := hg, graph_output := hgo }
  exact ⟨S,rfl,rfl,rfl,rfl,rfl,rfl,hβc,hχc⟩

end NearbyLagrangian.Transport

end

end OAI
