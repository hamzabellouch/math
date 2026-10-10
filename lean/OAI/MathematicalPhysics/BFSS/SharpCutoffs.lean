import Mathlib
import OAI.MathematicalPhysics.BFSS.KineticMeasures

namespace OAI

/-! Sharp weighted cutoff bounds and joint gradient lower limits. -/

namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Measure Set Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
variable (μ : Measure E) [IsAddHaarMeasure μ] [IsSeparable μ]
variable {ι : Type*} [Fintype ι] (e : ι → E)

omit [CompleteSpace F] [TopologicalSpace.SeparableSpace F] [IsSeparable μ] in
lemma closedGraph_unique {u : Lp F 2 μ} {v w : Gradient (F := F) μ (ι := ι)}
    (hv : (u,v) ∈ closedGraph μ e) (hw : (u,w) ∈ closedGraph μ e) : v = w := by
  have hz : ((0 : Lp F 2 μ),v-w) ∈ closedGraph μ e := by
    simpa only [Prod.mk_sub_mk,sub_self] using (closedGraph μ e).sub_mem hv hw
  exact sub_eq_zero.mp (closedGraph_vertical μ e hz)

theorem closedGraph_norm_sq_add_le {u : Lp F 2 μ} {v : Gradient (F := F) μ (ι := ι)}
    (hv : (u,v) ∈ closedGraph μ e)
    (f : ℕ → Core (E := E) (F := F)) (B : ℝ)
    (hf : Tendsto (fun n => toL2 μ (f n)) atTop (𝓝 u))
    (hB : ∀ n, ‖gradient μ e (f n)‖ ≤ B)
    (a b : ℕ → ℝ) (a₀ b₀ : ℝ)
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (hle : ∀ᶠ n in atTop, ‖gradient μ e (f n)‖^2+a n ≤ b n) :
    ‖v‖^2+a₀ ≤ b₀ := by
  obtain ⟨w,σ,hσ,hw,_,hweak⟩ := closedGraph_extract μ e f u B hf hB
  have hEq := closedGraph_unique μ e hv hw
  subst w
  apply BFSSNormalAnalysis.weak_norm_sq_add_le_limit
    (fun n => gradient μ e (f (σ n))) v (a ∘ σ) (b ∘ σ) a₀ b₀ hweak
    (ha.comp hσ.tendsto_atTop) (hb.comp hσ.tendsto_atTop)
  exact hσ.tendsto_atTop.eventually hle
end
end BFSSSliceSobolev
namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Set Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma norm_add_sq_young {ε : ℝ} (hε : 0 < ε) (a b : F) :
    ‖a+b‖^2 ≤ (1+ε)*‖a‖^2+(1+ε⁻¹)*‖b‖^2 := by
  have hsum := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  have hy : (‖a‖+‖b‖)^2 ≤ (1+ε)*‖a‖^2+(1+ε⁻¹)*‖b‖^2 := by
    apply (mul_le_mul_iff_right₀ hε).mp
    have hi : ε⁻¹*ε = 1 := inv_mul_cancel₀ hε.ne'
    have he : ((1+ε)*‖a‖^2+(1+ε⁻¹)*‖b‖^2)*ε - (‖a‖+‖b‖)^2*ε =
        (ε*‖a‖-‖b‖)^2 := by
      calc
        _ = (ε*‖a‖-‖b‖)^2+(ε⁻¹*ε-1)*‖b‖^2 := by ring
        _ = _ := by rw [hi,sub_self,zero_mul,add_zero]
    nlinarith [sq_nonneg (ε*‖a‖-‖b‖)]
  exact hsum.trans hy

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma scaledCutoff_fderiv_young (φ : ContDiffBump (0 : E)) {h D ε : ℝ}
    (hh : 0 ≤ h) (hε : 0 < ε) (hD : ∀ x, ‖fderiv ℝ (φ : E → ℝ) x‖ ≤ D)
    (f : Core (E := E) (F := F)) (x v : E) (hv : ‖v‖ = 1) :
    ‖fderiv ℝ (scaledCutoff φ h f : E → F) x v‖^2 ≤
      (1+ε)*(φ (h • x))^2*‖fderiv ℝ (f : E → F) x v‖^2 +
      (1+ε⁻¹)*(D*h)^2*‖f x‖^2 := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hb : ‖fderiv ℝ (φ : E → ℝ) (h • x) (h • v)‖ ≤ D*h := by
    calc
      _ ≤ ‖fderiv ℝ (φ : E → ℝ) (h • x)‖*‖h • v‖ := (fderiv ℝ (φ : E → ℝ) (h • x)).le_opNorm _
      _ ≤ D*‖h • v‖ := mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)
      _ = D*h := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh,hv,mul_one]
  rw [scaledCutoff_fderiv]
  have hy := norm_add_sq_young hε (φ (h • x) • fderiv ℝ (f : E → F) x v)
    (fderiv ℝ (φ : E → ℝ) (h • x) (h • v) • f x)
  simp only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs] at hy
  apply hy.trans
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [Real.norm_eq_abs,sq_abs] at hs
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (sq_nonneg ‖f x‖))
    (show 0 ≤ 1+ε⁻¹ by positivity)]

variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
variable {ι : Type*} [Fintype ι] (e : ι → E)

omit [CompleteSpace F] in
theorem scaledCutoff_sharp_bound (φ : ContDiffBump (0 : E)) {h D ε W A B : ℝ}
    (hh : 0 < h) (hε : 0 < ε) (hW : 0 ≤ W) (_hA : 0 ≤ A)
    (w : E → ℝ) (hw : Continuous w) (_hwN : ∀ x, 0 ≤ w x)
    (hφw : ∀ x ∈ Metric.closedBall 0 φ.rOut, W ≤ A*w x)
    (hD : ∀ x, ‖fderiv ℝ (φ : E → ℝ) x‖ ≤ D) (he : ∀ j, ‖e j‖ = 1)
    (f : Core (E := E) (F := F))
    (hB : (∫ x in Metric.closedBall 0 (φ.rOut/h), ‖f x‖^2 ∂μ) ≤ B) :
    ‖gradient μ e (W • scaledCutoff φ h f)‖^2 ≤
      (1+ε)*A^2*(∫ x, (w (h • x))^2*∑ j, ‖fderiv ℝ (f : E → F) x (e j)‖^2 ∂μ) +
      (Fintype.card ι : ℝ)*W^2*(1+ε⁻¹)*(D*h)^2*B := by
  classical
  let S : Set E := Metric.closedBall 0 (φ.rOut/h)
  let g := scaledCutoff φ h f
  have hsupport : tsupport (g : E → F) ⊆ S := scaledCutoff_support φ hh f
  have hfi : Integrable (fun x => ‖f x‖^2) μ :=
    (f.continuous.norm.pow 2).integrable_of_hasCompactSupport (norm_sq_compact f f.hasCompactSupport)
  have hcont (j : ι) : Continuous (fun x => ‖fderiv ℝ (f : E → F) x (e j)‖^2) := by
    exact (((f.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)
  have hcompact (j : ι) : HasCompactSupport (fun x => ‖fderiv ℝ (f : E → F) x (e j)‖^2) := by
    let fj : Core (E := E) (F := F) := TestFunction.lineDerivCLM ℝ (e j) f
    exact norm_sq_compact (fj : E → F) fj.hasCompactSupport
  have hwi (j : ι) : Integrable (fun x => (w (h • x))^2*‖fderiv ℝ (f : E → F) x (e j)‖^2) μ :=
    ((((hw.comp (continuous_const.smul continuous_id)).pow 2).mul (hcont j)).integrable_of_hasCompactSupport
      (hcompact j).mul_left)
  have hcoef : 0 ≤ (1+ε)*A^2 := mul_nonneg (by positivity) (sq_nonneg _)
  have hbound (j : ι) : W^2*(∫ x, ‖fderiv ℝ (g : E → F) x (e j)‖^2 ∂μ) ≤
      (1+ε)*A^2*(∫ x, (w (h • x))^2*‖fderiv ℝ (f : E → F) x (e j)‖^2 ∂μ)+
      W^2*(1+ε⁻¹)*(D*h)^2*B := by
    have hide : (∫ x, ‖fderiv ℝ (g : E → F) x (e j)‖^2 ∂μ) =
        ∫ x in S, ‖fderiv ℝ (g : E → F) x (e j)‖^2 ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : fderiv ℝ (g : E → F) x = 0 := by
        by_contra hn
        exact hx (hsupport (support_fderiv_subset ℝ hn))
      simp only [hz,zero_apply,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    rw [hide,←integral_const_mul]
    calc
      _ ≤ ∫ x in S, (1+ε)*A^2*((w (h • x))^2*‖fderiv ℝ (f : E → F) x (e j)‖^2)+
            W^2*(1+ε⁻¹)*(D*h)^2*‖f x‖^2 ∂μ := by
        apply setIntegral_mono_on ((derivative_sq_integrable μ g (e j)).const_mul (W^2)).integrableOn
          (((hwi j).const_mul ((1+ε)*A^2)).add (hfi.const_mul (W^2*(1+ε⁻¹)*(D*h)^2))).integrableOn
          Metric.isClosed_closedBall.measurableSet
        intro x hx
        have hxn : h • x ∈ Metric.closedBall 0 φ.rOut := by
          rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hh]
          have hxN : ‖x‖ ≤ φ.rOut/h := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hx
          simpa only [mul_comm] using (le_div_iff₀ hh).mp hxN
        have hwp : W*φ (h • x) ≤ A*w (h • x) :=
          (mul_le_of_le_one_right hW φ.le_one).trans (hφw _ hxn)
        have hwp2 := pow_le_pow_left₀ (mul_nonneg hW φ.nonneg) hwp 2
        have hy := mul_le_mul_of_nonneg_left
          (scaledCutoff_fderiv_young φ hh.le hε hD f x (e j) (he j)) (sq_nonneg W)
        have hh' := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hwp2 (show 0 ≤ 1+ε by positivity))
          (sq_nonneg ‖fderiv ℝ (f : E → F) x (e j)‖)
        calc
          _ ≤ W^2*((1+ε)*(φ (h • x))^2*‖fderiv ℝ (f : E → F) x (e j)‖^2+
              (1+ε⁻¹)*(D*h)^2*‖f x‖^2) := hy
          _ = (1+ε)*(W*φ (h • x))^2*‖fderiv ℝ (f : E → F) x (e j)‖^2+
              W^2*(1+ε⁻¹)*(D*h)^2*‖f x‖^2 := by ring
          _ ≤ (1+ε)*(A*w (h • x))^2*‖fderiv ℝ (f : E → F) x (e j)‖^2+
              W^2*(1+ε⁻¹)*(D*h)^2*‖f x‖^2 := add_le_add hh' le_rfl
          _ = _ := by simp only [Pi.add_apply]; ring
      _ = (1+ε)*A^2*(∫ x in S, (w (h • x))^2*‖fderiv ℝ (f : E → F) x (e j)‖^2 ∂μ)+
          W^2*(1+ε⁻¹)*(D*h)^2*(∫ x in S, ‖f x‖^2 ∂μ) := by
        rw [integral_add ((hwi j).integrableOn.const_mul _) (hfi.integrableOn.const_mul _)]
        simp only [integral_const_mul]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))) (hwi j)) hcoef)
        (mul_le_mul_of_nonneg_left hB (by positivity))
  rw [map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,gradient_norm_sq,integral_finsetSum]
  · rw [Finset.mul_sum]
    calc
      _ ≤ ∑ j : ι, ((1+ε)*A^2*(∫ x, (w (h • x))^2*‖fderiv ℝ (f : E → F) x (e j)‖^2 ∂μ)+
          W^2*(1+ε⁻¹)*(D*h)^2*B) := Finset.sum_le_sum (fun j _ => hbound j)
      _ = _ := by
        rw [Finset.sum_add_distrib,←Finset.mul_sum,←integral_finsetSum]
        · simp only [←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
          ring
        · intro j _
          exact hwi j
  · intro j _
    exact derivative_sq_integrable μ g (e j)
end
end BFSSSliceSobolev
namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Measure Set Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma exists_sharp_weight_cutoff (w : E → ℝ) (hw : Continuous w) (hw0 : 0 < w 0)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ φ : ContDiffBump (0 : E), φ.rOut < η ∧
      (∀ x ∈ Metric.closedBall 0 φ.rOut, w 0/2 ≤ w x) ∧
      (∀ x ∈ Metric.closedBall 0 φ.rOut, w 0 ≤ (1+ε)*w x) := by
  have h₁ : {x : E | w 0/2 < w x} ∈ 𝓝 0 :=
    hw.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith : w 0/2 < w 0))
  have h₂ : {x : E | w 0 < (1+ε)*w x} ∈ 𝓝 0 :=
    (hw.const_mul (1+ε)).continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (by nlinarith [mul_pos hε hw0] : w 0 < (1+ε)*w 0))
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp (inter_mem h₁ h₂)
  let s := min r η / 2
  have hs0 : 0 < s := half_pos (lt_min hr hη)
  have hsr : s < r := by dsimp [s]; nlinarith [min_le_left r η]
  have hsη : s < η := by dsimp [s]; nlinarith [min_le_right r η]
  let φ : ContDiffBump (0 : E) := ⟨s/2,s,half_pos hs0,by linarith⟩
  refine ⟨φ,hsη,?_,?_⟩
  · intro x hx
    exact (hs (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hsr))).1.le
  · intro x hx
    exact (hs (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hsr))).2.le

variable (μ : Measure E) [IsAddHaarMeasure μ] [IsSeparable μ]
variable {ι : Type*} [Fintype ι] (e : ι → E)

theorem weighted_gradient_add_liminf (w : E → ℝ) (hw : Continuous w)
    (hwN : ∀ x, 0 ≤ w x) (hw0 : 0 < w 0) (he : ∀ j, ‖e j‖ = 1)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (𝓝 0))
    (raw : ℕ → Core (E := E) (F := F))
    (hbound : ∀ n R, 0 ≤ R → h n*R < η →
      (∫ x in Metric.closedBall 0 R, ‖raw n x‖^2 ∂μ) ≤ B)
    (profiles : ℕ → Lp F 2 μ) (u : Lp F 2 μ)
    (hreps : ∀ n, (profiles n : E → F) =ᵐ[μ] fun x => w (h n • x) • raw n x)
    (hu : Tendsto profiles atTop (𝓝 u))
    (v : Gradient (F := F) μ (ι := ι)) (hv : (u,v) ∈ closedGraph μ e)
    (a b : ℕ → ℝ) (a₀ b₀ : ℝ) (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (hle : ∀ n,
      (∫ x, (w (h n • x))^2*∑ j, ‖fderiv ℝ (raw n : E → F) x (e j)‖^2 ∂μ)+a n ≤ b n) :
    ‖v‖^2+a₀ ≤ b₀ := by
  classical
  have hfor (ε : ℝ) (hε : 0 < ε) : ‖v‖^2+(1+ε)^3*a₀ ≤ (1+ε)^3*b₀ := by
    obtain ⟨φ,hφη,hφw,hφsharp⟩ := exists_sharp_weight_cutoff w hw hw0 hη hε
    have hφder : Continuous (fderiv ℝ (φ : E → ℝ)) :=
      (φ.contDiff : ContDiff ℝ 1 (φ : E → ℝ)).continuous_fderiv (by norm_num)
    obtain ⟨D₀,hD₀⟩ := ((φ.hasCompactSupport.fderiv ℝ).isCompact_range hφder).isBounded.exists_norm_le
    let D := max D₀ 0
    have hD0 : 0 ≤ D := le_max_right _ _
    have hD : ∀ x, ‖fderiv ℝ (φ : E → ℝ) x‖ ≤ D :=
      fun x => (hD₀ _ (mem_range_self x)).trans (le_max_left _ _)
    let f := fun n => w 0 • scaledCutoff φ (h n) (raw n)
    have hf : Tendsto (fun n => toL2 μ (f n)) atTop (𝓝 u) :=
      smooth_raw_tendsto μ w hw hw0 φ hφw h hzero raw profiles u hreps hu
    let α := (1+ε)^3
    have hα : 0 ≤ α := by positivity
    let K := (Fintype.card ι : ℝ)*(w 0)^2*(1+ε⁻¹)*B
    have hK : 0 ≤ K := by positivity
    have hfbound (n : ℕ) : ‖gradient μ e (f n)‖^2+α*a n ≤ α*b n+K*(D*h n)^2 := by
      have hR : 0 ≤ φ.rOut/h n := div_nonneg φ.rOut_pos.le (hh n).1.le
      have hRh : h n*(φ.rOut/h n) < η := by
        have heq : h n*(φ.rOut/h n) = φ.rOut := by field_simp [(hh n).1.ne']
        rw [heq]
        exact hφη
      have ht := scaledCutoff_sharp_bound μ e φ (hh n).1 hε hw0.le (by positivity)
        w hw hwN hφsharp hD he (raw n) (hbound n _ hR hRh)
      have henergy := mul_le_mul_of_nonneg_left (hle n) hα
      have hcoef : (1+ε)*(1+ε)^2 = α := by dsimp [α]; ring
      rw [hcoef] at ht
      change ‖gradient μ e (f n)‖^2 ≤ _ at ht
      dsimp only [K]
      nlinarith only [ht,henergy]
    obtain ⟨C,hC⟩ := (hb.sub ha).bddAbove_range
    let L := max (α*C+K*D^2) 0
    have hL : 0 ≤ L := le_max_right _ _
    have hnorm (n : ℕ) : ‖gradient μ e (f n)‖ ≤ Real.sqrt L := by
      apply (Real.le_sqrt (norm_nonneg _) hL).mpr
      have hCn : b n-a n ≤ C := hC (mem_range_self n)
      have hhD : (D*h n)^2 ≤ D^2 := pow_le_pow_left₀ (mul_nonneg hD0 (hh n).1.le)
        (mul_le_of_le_one_right hD0 (hh n).2) 2
      have h₁ := hfbound n
      have h₂ := mul_le_mul_of_nonneg_left hCn hα
      have h₃ := mul_le_mul_of_nonneg_left hhD hK
      have h₄ : α*C+K*D^2 ≤ L := le_max_left _ _
      nlinarith only [h₁,h₂,h₃,h₄]
    have hzero' : Tendsto (fun n => K*(D*h n)^2) atTop (𝓝 0) := by
      convert (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hzero).pow 2)) using 1
      simp
    have hhfinal := closedGraph_norm_sq_add_le μ e hv f (Real.sqrt L) hf hnorm
      (fun n => α*a n) (fun n => α*b n+K*(D*h n)^2) (α*a₀) (α*b₀)
      (ha.const_mul α) (by simpa only [add_zero] using (hb.const_mul α).add hzero')
      (Eventually.of_forall hfbound)
    exact hhfinal
  have hlim : Tendsto (fun ε : ℝ => (1+ε)^3*(b₀-a₀)) (𝓝[>] 0) (𝓝 (b₀-a₀)) := by
    have hc : Continuous (fun ε : ℝ => (1+ε)^3*(b₀-a₀)) := by fun_prop
    simpa only [add_zero,one_pow,one_mul] using
      (hc.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hresult : ‖v‖^2 ≤ b₀-a₀ := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have ht := hfor ε hε'
    nlinarith only [ht]
  linarith
end
end BFSSSliceSobolev
namespace BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} {G : M.GaugeData} {q : Boson N}
variable (P : G.MeasuredNormalPatch q)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
  AlgebraData.normalCoordinateField AlgebraData.normalCoordinateCore AlgebraData.normalCoreField
local instance : NormedAddCommGroup (M.NormalCoordinates q →L[ℝ] Fermion N) := inferInstance
local instance : NormedSpace ℝ (M.NormalCoordinates q →L[ℝ] Fermion N) := inferInstance
local instance : TopologicalSpace.SeparableSpace (Fermion N) := inferInstance
local instance : CompleteSpace (Fermion N) := inferInstance
local instance : InnerProductSpace ℝ (Fermion N) := inferInstance

theorem profile_gradient_add_le_limit (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (𝓝 0))
    (f : ℕ → G.invariantCore) (E : ℝ≥0)
    (hnorm : ∀ n, ‖coreToL2 (f n).val‖^2 ≤ E)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (hu : Tendsto (fun n => P.profile (h n) (f n)) atTop (𝓝 u))
    (v : BFSSSliceSobolev.Gradient (F := Fermion N) (volume : Measure (M.NormalCoordinates q))
      (ι := Fin (Module.finrank ℝ (M.normalSlice q))))
    (hv : (u,v) ∈ BFSSSliceSobolev.closedGraph volume
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (M.normalSlice q))) ℝ))
    (a : ℕ → ℝ) (a₀ b₀ : ℝ) (ha : Tendsto a atTop (𝓝 a₀))
    (hb : Tendsto (fun n => (∫ x, P.cutoff (h n • x)*kineticDensity (f n).val x)+a n)
      atTop (𝓝 b₀)) : ‖v‖^2+a₀ ≤ b₀ := by
  classical
  let w := M.normalCoordinateWeight q P.density P.cutoff
  have hw : Continuous w := M.normalCoordinateWeight_continuous q P.density P.cutoff
    P.density_continuous P.cutoff_continuous
  have hwN : ∀ x, 0 ≤ w x := fun _ => Real.sqrt_nonneg _
  have hw0 : 0 < w 0 := P.coordinateWeight_zero_pos
  have hlocal := @BFSSQuantum.AlgebraData.GaugeData.normalCoordinateCore_local_bounds N M G hN q
  rcases hlocal with ⟨η,B,_,hη,hB,_,hbound⟩
  let e := EuclideanSpace.basisFun (Fin (Module.finrank ℝ (M.normalSlice q))) ℝ
  let raw := fun n => M.normalCoordinateCore q (h n) (f n).val
  refine BFSSSliceSobolev.weighted_gradient_add_liminf volume e w hw hwN hw0
    (fun j => e.orthonormal.norm_eq_one j) hη (mul_nonneg hB.le E.property)
    h hh hzero raw ?_ (fun n => P.profile (h n) (f n)) u ?_ hu v hv
    a _ a₀ b₀ ha hb ?_
  · intro n R hR hhR
    exact (hbound (h n) R (hh n).1 (hh n).2 hR hhR (f n)).1.trans
      (mul_le_mul_of_nonneg_left (hnorm n) hB.le)
  · intro n
    filter_upwards [P.profile_ae (h n) (f n)] with x hx
    rw [hx,AlgebraData.normalMeasuredCoordinates]
    dsimp only [raw]
    rw [AlgebraData.normalCoordinateCore_apply]
  · intro n
    change (∫ x : M.NormalCoordinates q, (M.normalCoordinateWeight q P.density P.cutoff (h n • x))^2 *
      ∑ j, ‖fderiv ℝ (M.normalCoordinateCore q (h n) (f n).val : M.NormalCoordinates q → Fermion N) x
        (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (M.normalSlice q))) ℝ j)‖^2)+a n ≤ _
    rw [M.normalCoordinateCore_weighted_kinetic q (h n) (f n).val P.density P.cutoff
      P.density_nonneg (fun x => (P.cutoff_bounds x).1)]
    exact add_le_add (P.kinetic_le G hN (hh n).1 (f n)) le_rfl
end
end BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch

end OAI
