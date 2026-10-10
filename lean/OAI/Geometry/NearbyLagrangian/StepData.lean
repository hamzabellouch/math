import Mathlib
import OAI.Geometry.NearbyLagrangian.CriticalLocus

namespace OAI

/-! Small-step data and the homeomorphism of old and new critical loci. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

open Filter Set
open scoped Topology ContDiff InnerProductSpace

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup W] [NormedSpace ℝ W]

def baseGradient (F : E × W → ℝ) (x : E) (w : W) : E :=
  (InnerProductSpace.toDual ℝ E).symm (baseDifferential F x w)

@[simp] lemma innerSL_baseGradient (F : E × W → ℝ) (x : E) (w : W) :
    innerSL ℝ (baseGradient F x w) = baseDifferential F x w :=
  (InnerProductSpace.toDual ℝ E).apply_symm_apply _

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedSpace ℝ W] in
lemma eq_one_near_of_norm_lt {χ : W → ℝ} {R : ℝ} {w : W}
    (hχ : ∀ u, ‖u‖ < R → χ u = 1) (hw : ‖w‖ < R) :
    χ =ᶠ[𝓝 w] fun _ => 1 := by
  have h : ∀ᶠ u in 𝓝 w, ‖u‖ < R :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hw
  exact h.mono fun u hu => hχ u hu

structure StepData where
  U : Set E
  open_U : IsOpen U
  F : E × W → ℝ
  σ : E × E → ℝ
  ζ : E → ℝ
  β : E → ℝ
  χ : W → ℝ
  ψ : (E × E) ≃ₜ (E × E)
  R : ℝ
  c : ℝ
  C : ℝ
  δ₀ : ℝ
  δ₁ : ℝ
  R_pos : 0 < R
  c_pos : 0 < c
  C_nonneg : 0 ≤ C
  δ₀_pos : 0 < δ₀
  δ₁_nonneg : 0 ≤ δ₁
  small : C * δ₀ * δ₁ < c
  smooth_F : ∀ x ∈ U, ∀ w, ContDiffAt ℝ ∞ F (x,w)
  smooth_σ : ContDiff ℝ ∞ σ
  smooth_ζ : ContDiff ℝ ∞ ζ
  smooth_β : ContDiff ℝ ∞ β
  smooth_χ : ContDiff ℝ ∞ χ
  ζ_range : ∀ x, ζ x ∈ Icc (0:ℝ) 1
  β_range : ∀ z, β z ∈ Icc (0:ℝ) 1
  β_one : ∀ z, ‖z‖ < δ₀ → β z = 1
  χ_one : ∀ w, ‖w‖ < R → χ w = 1
  χ_bound : ∀ w, w ≠ 0 → ‖fderiv ℝ χ w‖ ≤ δ₁ / ‖w‖
  σ_bound : ∀ X p, ‖fderiv ℝ (fun p => σ (X,p)) p‖ < δ₀
  base_bound : ∀ x ∈ U, ∀ w, R ≤ ‖w‖ → ‖baseDifferential F x w‖ ≤ C * ‖w‖^2
  vertical_bound : ∀ x ∈ U, ∀ w, R ≤ ‖w‖ → c * ‖w‖ ≤ ‖verticalDifferential F x w‖
  shift_mem : ∀ X ∈ U, ∀ w z, X + productCutoff ζ β χ X w z • z ∈ U
  cover : ∀ X ∈ U, (ζ =ᶠ[𝓝 X] fun _ => 1) ∨
    (∀ᶠ Y in 𝓝 X, ∀ p, σ (Y,p) = 0)
  ψ_base_mem : ∀ x p, x ∈ U ↔ (ψ (x,p)).1 ∈ U
  graph : ∀ x p X, X ∈ U →
    ((ψ (x,p)).1 = X ↔ fderiv ℝ (fun p => σ (X,p)) p = innerSL ℝ (x-X))
  graph_output : ∀ x p, x ∈ U →
    innerSL ℝ (ψ (x,p)).2 = innerSL ℝ p +
      fderiv ℝ (fun X => σ (X,p)) (ψ (x,p)).1

namespace StepData

variable (S : StepData (E := E) (W := W))

def κ : E → W → E → ℝ := productCutoff S.ζ S.β S.χ

def shiftedBase (X : E) (w : W) (z : E) : E := X + S.κ X w z • z

omit [CompleteSpace E] in
lemma diff_F {X : E} (hX : X ∈ S.U) (w : W) : DifferentiableAt ℝ S.F (X,w) :=
  (S.smooth_F X hX w).differentiableAt (by simp)

omit [CompleteSpace E] in
lemma diff_σ_p (X p : E) : DifferentiableAt ℝ (fun p => S.σ (X,p)) p :=
  (S.smooth_σ.differentiable (by simp) (X,p)).comp p
    (differentiableAt_const X |>.prodMk differentiableAt_id)

omit [CompleteSpace E] in
lemma diff_σ_X (X p : E) : DifferentiableAt ℝ (fun X => S.σ (X,p)) X :=
  (S.smooth_σ.differentiable (by simp) (X,p)).comp X
    (differentiableAt_id.prodMk (differentiableAt_const p))

omit [CompleteSpace E] in
lemma diff_κ_w (X z : E) (w : W) : DifferentiableAt ℝ (fun w => S.κ X w z) w :=
  (S.smooth_χ.differentiable (by simp) w).const_smul (S.ζ X * S.β z)

omit [CompleteSpace E] in
lemma diff_κ_z (X z : E) (w : W) : DifferentiableAt ℝ (S.κ X w) z := by
  exact ((S.smooth_β.differentiable (by simp) z).const_mul (S.ζ X)).mul_const (S.χ w)

omit [CompleteSpace E] in
lemma diff_κ_X (X z : E) (w : W) : DifferentiableAt ℝ (fun X => S.κ X w z) X := by
  exact ((S.smooth_ζ.differentiable (by simp) X).mul_const (S.β z)).mul_const (S.χ w)

omit [CompleteSpace E] in
lemma diff_phase {X : E} (hX : X ∈ S.U) (w : W) (z p : E) :
    DifferentiableAt ℝ (verticalPhase S.F S.σ S.κ X) (w,z,p) := by
  apply differentiableAt_verticalPhase
    (S.diff_F (S.shift_mem X hX w z) w) (S.diff_σ_p X p)
  exact (((S.smooth_β.differentiable (by simp) z).comp (w,z,p)
    differentiableAt_snd.fst).const_mul (S.ζ X)).mul
      ((S.smooth_χ.differentiable (by simp) w).comp (w,z,p) differentiableAt_fst)

omit [CompleteSpace E] in
lemma old_critical_bound {x : E} {w : W} (hx : x ∈ S.U)
    (hcrit : verticalDifferential S.F x w = 0) : ‖w‖ < S.R := by
  by_contra h
  have hl := le_of_not_gt h
  have hp := mul_pos S.c_pos (S.R_pos.trans_le hl)
  have hb := S.vertical_bound x hx w hl
  rw [hcrit, norm_zero] at hb
  exact (not_lt_of_ge hb) hp

omit [CompleteSpace E] in
lemma new_critical_bounds {X : E} {w : W} {z p : E} (hX : X ∈ S.U)
    (hcrit : IsShiftedCritical S.F S.σ S.κ X w z p) : ‖w‖ < S.R ∧ ‖z‖ < S.δ₀ := by
  have hf := S.diff_phase hX w z p
  have hs := S.diff_F (S.shift_mem X hX w z) w
  have hb := norm_w_lt_of_shiftedCritical S.R_pos S.C_nonneg S.δ₀_pos.le S.δ₁_nonneg
    S.small hs (S.diff_σ_p X p) (S.smooth_χ.differentiable (by simp) w) hf
    (S.ζ_range X) (S.β_range z) (S.σ_bound X p) (S.χ_bound w)
    (S.base_bound _ (S.shift_mem X hX w z) w)
    (S.vertical_bound _ (S.shift_mem X hX w z) w) hcrit
  exact ⟨hb, displacement_bound_of_critical_p (S.diff_σ_p X p) (S.σ_bound X p)
    ((fderiv_triple_eq_zero_iff hf).mp hcrit).2.2⟩

omit [CompleteSpace E] in
lemma κ_one_w {X z : E} {w : W} (hζ : S.ζ X = 1) (hz : ‖z‖ < S.δ₀)
    (hw : ‖w‖ < S.R) : (fun w => S.κ X w z) =ᶠ[𝓝 w] fun _ => 1 := by
  filter_upwards [eq_one_near_of_norm_lt S.χ_one hw] with u hu
  simp only [κ, productCutoff, hζ, S.β_one z hz, hu, mul_one]

omit [CompleteSpace E] in
lemma κ_one_z {X z : E} {w : W} (hζ : S.ζ X = 1) (hz : ‖z‖ < S.δ₀)
    (hw : ‖w‖ < S.R) : S.κ X w =ᶠ[𝓝 z] fun _ => 1 := by
  filter_upwards [eq_one_near_of_norm_lt S.β_one hz] with u hu
  simp only [κ, productCutoff, hζ, S.χ_one w hw, hu, mul_one]

omit [CompleteSpace E] in
lemma κ_one_X {X z : E} {w : W} (hζ : S.ζ =ᶠ[𝓝 X] fun _ => 1)
    (hz : ‖z‖ < S.δ₀) (hw : ‖w‖ < S.R) :
    (fun X => S.κ X w z) =ᶠ[𝓝 X] fun _ => 1 := by
  filter_upwards [hζ] with Y hY
  simp only [κ, productCutoff, hY, S.χ_one w hw, S.β_one z hz, mul_one]

omit [CompleteSpace E] in
lemma κ_zero {X : E} {w : W} (hw : ‖w‖ < S.R) : S.κ X w 0 = S.ζ X := by
  simp only [κ, productCutoff, S.β_one 0 (by simpa only [norm_zero] using S.δ₀_pos),
    S.χ_one w hw, mul_one]

theorem new_to_old {X : E} {w : W} {z p : E} (hX : X ∈ S.U)
    (hc : IsShiftedCritical S.F S.σ S.κ X w z p) :
    verticalDifferential S.F (S.shiftedBase X w z) w = 0 ∧
    (S.ψ (S.shiftedBase X w z, baseGradient S.F (S.shiftedBase X w z) w)).1 = X ∧
    z = S.shiftedBase X w z - X ∧
    p = S.ζ X • baseGradient S.F (S.shiftedBase X w z) w := by
  obtain ⟨hw,hz⟩ := S.new_critical_bounds hX hc
  rcases S.cover X hX with hζ | hσ
  · have hζ0 : S.ζ X = 1 := hζ.eq_of_nhds
    have hκw := S.κ_one_w hζ0 hz hw
    have hκz := S.κ_one_z hζ0 hz hw
    have hb : S.shiftedBase X w z = X + z := by
      simp only [shiftedBase, hκw.eq_of_nhds, one_smul]
    have hF : DifferentiableAt ℝ S.F (X+z,w) := by
      have hf := S.diff_F (S.shift_mem X hX w z) w
      change DifferentiableAt ℝ S.F (S.shiftedBase X w z,w) at hf
      rwa [hb] at hf
    have H := (shiftedCritical_iff_supported hF (S.diff_σ_p X p) hκw hκz
      (S.diff_phase hX w z p)).mp hc
    have ha : baseGradient S.F (X+z) w = p :=
      (innerSL_inj (𝕜 := ℝ)).mp (by simpa only [innerSL_baseGradient] using H.2.1)
    refine ⟨by simpa only [hb] using H.1, ?_, ?_, ?_⟩
    · apply (S.graph _ _ X hX).mpr
      simpa only [hb, ha, add_sub_cancel_left] using H.2.2
    · simp only [hb, add_sub_cancel_left]
    · simp only [hb, ha, hζ0, one_smul]
  · have hσ0 : ∀ p, S.σ (X,p) = 0 := hσ.self_of_nhds
    have H := (shiftedCritical_iff_outside (S.diff_F (S.shift_mem X hX w z) w)
      hσ0 (S.diff_κ_w X z w) (S.diff_κ_z X z w) (S.diff_phase hX w z p)).mp hc
    have hb : S.shiftedBase X w z = X := by simp only [shiftedBase, H.1, smul_zero, add_zero]
    refine ⟨by simpa only [hb] using H.2.1, ?_, ?_, ?_⟩
    · apply (S.graph _ _ X hX).mpr
      have he : (fun p => S.σ (X,p)) = fun _ => 0 := funext hσ0
      simp only [he, hb, sub_self, map_zero,
        (hasFDerivAt_const (𝕜 := ℝ) (0:ℝ) (baseGradient S.F X w)).fderiv]
    · rw [hb, sub_self]
      exact H.1
    · apply (innerSL_inj (𝕜 := ℝ)).mp
      rw [hb]
      have he : innerSL ℝ (S.ζ X • baseGradient S.F X w) =
          S.ζ X • baseDifferential S.F X w := by
        ext v
        simp only [innerSL_apply_apply, real_inner_smul_left,
          smul_apply, smul_eq_mul, ← innerSL_baseGradient]
      rw [he, ← S.κ_zero hw]
      exact H.2.2.symm

theorem old_to_new {x : E} {w : W} (hx : x ∈ S.U)
    (hc : verticalDifferential S.F x w = 0) :
    let a := baseGradient S.F x w
    let X := (S.ψ (x,a)).1
    IsShiftedCritical S.F S.σ S.κ X w (x-X) (S.ζ X • a) := by
  dsimp only
  let a := baseGradient S.F x w
  let X := (S.ψ (x,a)).1
  change IsShiftedCritical S.F S.σ S.κ X w (x-X) (S.ζ X • a)
  have hX : X ∈ S.U := (S.ψ_base_mem x a).mp hx
  have hg : fderiv ℝ (fun p => S.σ (X,p)) a = innerSL ℝ (x-X) :=
    (S.graph x a X hX).mp rfl
  have hw := S.old_critical_bound hx hc
  have hz : ‖x-X‖ < S.δ₀ := by
    have H := S.σ_bound X a
    rwa [hg, innerSL_apply_norm] at H
  rcases S.cover X hX with hζ | hσ
  · have hζ0 : S.ζ X = 1 := hζ.eq_of_nhds
    rw [hζ0, one_smul]
    have he : X + (x-X) = x := by abel
    have hf : DifferentiableAt ℝ S.F (X+(x-X),w) := by rw [he]; exact S.diff_F hx w
    apply (shiftedCritical_iff_supported hf (S.diff_σ_p X a) (S.κ_one_w hζ0 hz hw)
      (S.κ_one_z hζ0 hz hw) (S.diff_phase hX w (x-X) a)).mpr
    refine ⟨by simpa only [he] using hc, ?_, hg⟩
    simp only [he, a, innerSL_baseGradient]
  · have hσ0 : ∀ p, S.σ (X,p) = 0 := hσ.self_of_nhds
    have hs : (fun p => S.σ (X,p)) = fun _ => 0 := funext hσ0
    have hz0 : x-X = 0 := (innerSL_inj (𝕜 := ℝ)).mp (by
      rw [hs, (hasFDerivAt_const (𝕜 := ℝ) (0:ℝ) a).fderiv] at hg
      simpa only [map_zero] using hg.symm)
    have hxX : x = X := sub_eq_zero.mp hz0
    apply (shiftedCritical_iff_outside (S.diff_F (S.shift_mem X hX w (x-X)) w)
      hσ0 (S.diff_κ_w X (x-X) w) (S.diff_κ_z X (x-X) w)
      (S.diff_phase hX w (x-X) (S.ζ X • a))).mpr
    refine ⟨hz0, by simpa only [hxX] using hc, ?_⟩
    change S.κ X w 0 • baseDifferential S.F X w = innerSL ℝ (S.ζ X • a)
    rw [S.κ_zero hw]
    ext v
    simp only [innerSL_apply_apply, real_inner_smul_left, smul_apply, smul_eq_mul]
    change S.ζ X * baseDifferential S.F X w v =
      S.ζ X * (innerSL ℝ (baseGradient S.F x w)) v
    rw [innerSL_baseGradient, hxX]

def carry (q : E × W) : E × (W × (E × E)) :=
  let a := baseGradient S.F q.1 q.2
  let X := (S.ψ (q.1,a)).1
  (X,q.2,q.1-X,S.ζ X • a)

def recover (q : E × (W × (E × E))) : E × W :=
  (S.shiftedBase q.1 q.2.1 q.2.2.1, q.2.1)

def OldCritical := {q : E × W // q.1 ∈ S.U ∧ verticalDifferential S.F q.1 q.2 = 0}

def NewCritical := {q : E × (W × (E × E)) //
  q.1 ∈ S.U ∧ IsShiftedCritical S.F S.σ S.κ q.1 q.2.1 q.2.2.1 q.2.2.2}

instance : TopologicalSpace S.OldCritical := inferInstanceAs
  (TopologicalSpace {q : E × W // q.1 ∈ S.U ∧ verticalDifferential S.F q.1 q.2 = 0})

instance : TopologicalSpace S.NewCritical := inferInstanceAs
  (TopologicalSpace {q : E × (W × (E × E)) //
    q.1 ∈ S.U ∧ IsShiftedCritical S.F S.σ S.κ q.1 q.2.1 q.2.2.1 q.2.2.2})

def carryCritical (q : S.OldCritical) : S.NewCritical :=
  ⟨S.carry q.val, (S.ψ_base_mem q.val.1 _).mp q.property.1,
    S.old_to_new q.property.1 q.property.2⟩

def recoverCritical (q : S.NewCritical) : S.OldCritical :=
  ⟨S.recover q.val, S.shift_mem _ q.property.1 _ _,
    (S.new_to_old q.property.1 q.property.2).1⟩

lemma recover_carry (q : S.OldCritical) : S.recoverCritical (S.carryCritical q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · have H := (S.new_to_old (S.carryCritical q).property.1
      (S.carryCritical q).property.2).2.2.1
    exact (sub_left_inj.mp H).symm
  · rfl

lemma carry_recover (q : S.NewCritical) : S.carryCritical (S.recoverCritical q) = q := by
  apply Subtype.ext
  have H := S.new_to_old q.property.1 q.property.2
  change S.carry (S.recover q.val) = q.val
  simp only [carry, recover, H.2.1]
  exact Prod.ext rfl (Prod.ext rfl (Prod.ext H.2.2.1.symm H.2.2.2.symm))

end StepData

lemma continuousAt_baseGradient {F : E × W → ℝ} {q : E × W}
    (hf : ContDiffAt ℝ ∞ F q) :
    ContinuousAt (fun q : E × W => baseGradient F q.1 q.2) q := by
  have hd : ContinuousAt (fderiv ℝ F) q :=
    (hf.fderiv_right (m := 0) (by simp)).continuousAt
  have hb : ContinuousAt (fun q : E × W => baseDifferential F q.1 q.2) q := by
    exact (((ContinuousLinearMap.compL ℝ E (E × W) ℝ).flip
      (inl ℝ E W)).continuous.continuousAt.comp hd)
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.continuousAt.comp hb

namespace StepData

variable (S : StepData (E := E) (W := W))

lemma continuousAt_carry {q : E × W} (hq : q.1 ∈ S.U) : ContinuousAt S.carry q := by
  have ha := continuousAt_baseGradient (S.smooth_F q.1 hq q.2)
  have hg : ContinuousAt (fun q : E × W => S.ψ (q.1,baseGradient S.F q.1 q.2)) q :=
    S.ψ.continuous.continuousAt.comp (continuousAt_fst.prodMk ha)
  have hX := hg.fst
  have hζ := S.smooth_ζ.continuous.continuousAt.comp hX
  exact hX.prodMk (continuousAt_snd.prodMk
    ((continuousAt_fst.sub hX).prodMk (hζ.smul ha)))

omit [CompleteSpace E] in
lemma continuousAt_recover : Continuous S.recover := by
  have hζ := S.smooth_ζ.continuous
  have hβ := S.smooth_β.continuous
  have hχ := S.smooth_χ.continuous
  unfold recover shiftedBase κ productCutoff
  fun_prop

lemma continuous_carryCritical : Continuous S.carryCritical := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro q
  exact (S.continuousAt_carry q.property.1).comp continuousAt_subtype_val

lemma continuous_recoverCritical : Continuous S.recoverCritical := by
  exact (S.continuousAt_recover.comp continuous_subtype_val).subtype_mk _

def criticalHomeomorph : S.OldCritical ≃ₜ S.NewCritical where
  toFun := S.carryCritical
  invFun := S.recoverCritical
  left_inv := S.recover_carry
  right_inv := S.carry_recover
  continuous_toFun := S.continuous_carryCritical
  continuous_invFun := S.continuous_recoverCritical

theorem new_output {X : E} {w : W} {z p : E} (hX : X ∈ S.U)
    (hc : IsShiftedCritical S.F S.σ S.κ X w z p) :
    fderiv ℝ (fun X => shiftedPhase S.F S.σ S.κ X w z p) X =
      innerSL ℝ (S.ψ (S.shiftedBase X w z,
        baseGradient S.F (S.shiftedBase X w z) w)).2 := by
  obtain ⟨hw,hz⟩ := S.new_critical_bounds hX hc
  have H := S.new_to_old hX hc
  have hout := S.graph_output (S.shiftedBase X w z)
    (baseGradient S.F (S.shiftedBase X w z) w) (S.shift_mem X hX w z)
  rw [H.2.1] at hout
  rcases S.cover X hX with hζ | hσ
  · have hζ0 : S.ζ X = 1 := hζ.eq_of_nhds
    have hk := S.κ_one_X hζ hz hw
    have hb : S.shiftedBase X w z = X+z := by
      simp only [shiftedBase, hk.eq_of_nhds, one_smul]
    have ha : baseGradient S.F (X+z) w = p := by
      simpa only [hb, hζ0, one_smul] using H.2.2.2.symm
    have hf : DifferentiableAt ℝ S.F (X+z,w) := by
      have hf := S.diff_F (S.shift_mem X hX w z) w
      change DifferentiableAt ℝ S.F (S.shiftedBase X w z,w) at hf
      rwa [hb] at hf
    rw [shifted_output_supported hf (S.diff_σ_X X p) hk
      (by rw [← innerSL_baseGradient, ha])]
    simpa only [hb, ha] using hout.symm
  · have hσ0 : ∀ p, S.σ (X,p) = 0 := hσ.self_of_nhds
    have hz0 := ((shiftedCritical_iff_outside (S.diff_F (S.shift_mem X hX w z) w)
      hσ0 (S.diff_κ_w X z w) (S.diff_κ_z X z w) (S.diff_phase hX w z p)).mp hc).1
    subst z
    have hb : S.shiftedBase X w 0 = X := by simp only [shiftedBase, smul_zero, add_zero]
    have hσp : (fun X => S.σ (X,p)) =ᶠ[𝓝 X] fun _ => 0 := hσ.mono fun Y hY => hY p
    rw [shifted_output_outside (S.diff_F hX w) hσp (S.diff_κ_X X 0 w)]
    have hσa : (fun Y => S.σ (Y,baseGradient S.F X w)) =ᶠ[𝓝 X] fun _ => 0 :=
      hσ.mono fun Y hY => hY _
    have hd := (hasFDerivAt_const (𝕜 := ℝ) (0:ℝ) X).congr_of_eventuallyEq hσa
    simpa only [hb, hd.fderiv, add_zero, innerSL_baseGradient] using hout.symm

end StepData

end NearbyLagrangian.Transport

end

end OAI
