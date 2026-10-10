import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.RankPreimage

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
section SpectralChart
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

noncomputable def positiveProjection (A : M) : M := Ring.inverse A * A⁺

omit [Nonempty ν] in
lemma positiveProjection_action {A : M} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {v : E} (hv : v ∈ LinearMap.range (op A⁺).toLinearMap) :
    op (positiveProjection A) v = v := by
  obtain ⟨x,rfl⟩ := hv
  have hAP : A * A⁺ = A⁺ * A⁺ := by
    calc
      A * A⁺ = (A⁺ - A⁻) * A⁺ := by rw [CFC.posPart_sub_negPart A hA]
      _ = A⁺ * A⁺ := by rw [sub_mul,CFC.negPart_mul_posPart,sub_zero]
  have he : positiveProjection A * A⁺ = A⁺ := by
    dsimp [positiveProjection]
    rw [mul_assoc,← hAP,← mul_assoc,Ring.inverse_mul_cancel A hU,one_mul]
  have hh := congrArg (fun B : M => op B x) he
  simpa only [map_mul,mul_apply_eq_comp,ContinuousLinearMap.coe_coe] using hh

omit [Nonempty ν] in
lemma positiveProjection_kills {A : M} {u v : E} {lam : ℝ}
    (hP : A⁺ = lam • rankOne u) (hv : ⟪u,v⟫ = 0) :
    op (positiveProjection A) v = 0 := by
  simp only [positiveProjection,map_mul,mul_apply_eq_comp,hP,map_smul,
    smul_apply,rankOne_action,hv,zero_smul,map_zero,smul_zero]

omit [Nonempty ν] in
lemma positiveRange_separated_of_close {A B : M} (hB : IsSelfAdjoint B)
    (hBU : IsUnit B) {u : E} {lam : ℝ} (hP : A⁺ = lam • rankOne u)
    (hclose : ‖op (positiveProjection B) - op (positiveProjection A)‖ < 1)
    {v : E} (hv : v ∈ LinearMap.range (op B⁺).toLinearMap) (horth : ⟪u,v⟫ = 0) : v = 0 := by
  have he : (op (positiveProjection B) - op (positiveProjection A)) v = v := by
    rw [sub_apply,positiveProjection_action hB hBU hv,
      positiveProjection_kills hP horth,sub_zero]
  have hn := ContinuousLinearMap.le_opNorm (op (positiveProjection B) - op (positiveProjection A)) v
  rw [he] at hn
  apply norm_eq_zero.mp
  have hp := norm_nonneg v
  nlinarith

omit [Nonempty ν] in
lemma positive_eq_rankOne_of_separated {A : M} {w : E}
    (hAw : op A⁺ w ≠ 0)
    (hsep : ∀ v ∈ LinearMap.range (op A⁺).toLinearMap, ⟪w,v⟫ = 0 → v = 0) :
    ∃ u : E, ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u := by
  let v : E := op A⁺ w
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,norm_inv,hAw,v]
  have hur : u ∈ LinearMap.range (op A⁺).toLinearMap :=
    Submodule.smul_mem _ _ (LinearMap.mem_range_self _ w)
  have hwu : ⟪w,u⟫ ≠ 0 := by
    intro hz
    have hu0 := hsep u hur hz
    simp [hu0] at hu
  have hr := subspace_eq_span_of_inner_separates
    (LinearMap.range (op A⁺).toLinearMap) w u hur hwu hsep
  have he := symmetric_eq_rankOne_of_range (CFC.posPart_nonneg A).isSelfAdjoint hu hr.le
  have hl : 0 ≤ ⟪u,op A⁺ u⟫ := by
    rw [← sqrt_action_norm_sq A⁺ (CFC.posPart_nonneg A) u]
    positivity
  have hl0 : ⟪u,op A⁺ u⟫ ≠ 0 := by
    intro hz
    have hP0 : A⁺ = 0 := by simpa only [hz,zero_smul] using he
    apply hAw
    simp [hP0]
  exact ⟨u,hu,_,lt_of_le_of_ne hl (Ne.symm hl0),he⟩

omit [Nonempty ν] in
lemma positiveProjection_continuousAt {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x))
    {x : X} (hU : IsUnit (A x)) : ContinuousAt (positiveProjection ∘ A) x := by
  have hP : Continuous (fun x => (A x)⁺) :=
    (matrix_posPart_continuousOn.comp_continuous hA (fun y => hSA y))
  have hInv : ContinuousAt (fun y => Ring.inverse (A y)) x := by
    obtain ⟨a,ha⟩ := hU
    have hi := NormedRing.inverse_continuousAt a
    rw [ha] at hi
    exact hi.comp hA.continuousAt
  exact hInv.mul hP.continuousAt

omit [Nonempty ν] in
lemma positive_line_eventually {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x))
    {x : X} (hU : IsUnit (A x)) {w : E} (hw : ‖w‖ = 1)
    {lam : ℝ} (hlam : 0 < lam) (hP : (A x)⁺ = lam • rankOne w) :
    ∀ᶠ y in 𝓝 x, IsUnit (A y) ∧ ∃ u : E, ‖u‖ = 1 ∧
      ∃ t : ℝ, 0 < t ∧ (A y)⁺ = t • rankOne u := by
  have hop : Continuous (fun B : M => op B) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hQ := hop.continuousAt.comp (positiveProjection_continuousAt A hA hSA hU)
  have hclose : ∀ᶠ y in 𝓝 x, ‖op (positiveProjection (A y)) - op (positiveProjection (A x))‖ < 1 := by
    have ht := (hQ.sub (continuousAt_const (y := op (positiveProjection (A x))))).norm
    exact ht.eventually_lt continuousAt_const (by simp)
  have hPcont : Continuous (fun y => (A y)⁺) :=
    matrix_posPart_continuousOn.comp_continuous hA (fun y => hSA y)
  have hvcont : Continuous (fun y => op (A y)⁺ w) := (hop.comp hPcont).clm_apply continuous_const
  have hw0 : op (A x)⁺ w ≠ 0 := by
    rw [hP,map_smul,smul_apply,rankOne_action,real_inner_self_eq_norm_sq,hw]
    have hwne : w ≠ 0 := by intro he; simp only [he,norm_zero] at hw; norm_num at hw
    simpa only [one_pow,one_smul] using smul_ne_zero (ne_of_gt hlam) hwne
  have hv : ∀ᶠ y in 𝓝 x, op (A y)⁺ w ≠ 0 := hvcont.continuousAt.eventually_ne hw0
  have hunit : ∀ᶠ y in 𝓝 x, IsUnit (A y) :=
    hA.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hU)
  filter_upwards [hclose,hv,hunit] with y hy hyv hyU
  refine ⟨hyU,positive_eq_rankOne_of_separated hyv ?_⟩
  exact fun v hv he => positiveRange_separated_of_close (hSA y) hyU hP hy hv he

end SpectralChart
end BorsukNine

end OAI
