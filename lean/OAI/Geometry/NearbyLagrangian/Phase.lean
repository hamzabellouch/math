import Mathlib

namespace OAI

/-! Shifted generating phases, partial derivatives and critical-point bounds. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def shiftedPhase (F : E × W → ℝ) (σ : E × E → ℝ) (κ : E → W → E → ℝ)
    (X : E) (w : W) (z p : E) : ℝ :=
  F (X + κ X w z • z, w) + σ (X,p) - inner ℝ z p

def baseDifferential (F : E × W → ℝ) (x : E) (w : W) : E →L[ℝ] ℝ :=
  (fderiv ℝ F (x,w)).comp (inl ℝ E W)

def verticalDifferential (F : E × W → ℝ) (x : E) (w : W) : W →L[ℝ] ℝ :=
  (fderiv ℝ F (x,w)).comp (inr ℝ E W)

lemma derivative_split (A : E × W →L[ℝ] ℝ) (u : E) (v : W) :
    A (u,v) = A.comp (inl ℝ E W) u + A.comp (inr ℝ E W) v := by
  change A (u,v) = A (u,0) + A (0,v)
  rw [← A.map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
lemma hasFDerivAt_shiftedPhase_p (F : E × W → ℝ) {σ : E × E → ℝ}
    (κ : E → W → E → ℝ) (X : E) (w : W) (z p : E)
    (hσ : DifferentiableAt ℝ (fun p => σ (X,p)) p) :
    HasFDerivAt (fun p => shiftedPhase F σ κ X w z p)
      (fderiv ℝ (fun p => σ (X,p)) p - innerSL ℝ z) p := by
  exact (hσ.hasFDerivAt.const_add _).sub (innerSL ℝ z).hasFDerivAt

lemma hasFDerivAt_shiftedPhase_z {F : E × W → ℝ} (σ : E × E → ℝ)
    {κ : E → W → E → ℝ} (X : E) (w : W) (z p : E)
    (hF : DifferentiableAt ℝ F (X + κ X w z • z,w))
    (hκ : DifferentiableAt ℝ (κ X w) z) :
    HasFDerivAt (fun z => shiftedPhase F σ κ X w z p)
      (κ X w z • baseDifferential F (X+κ X w z • z) w +
        (baseDifferential F (X+κ X w z • z) w z) • fderiv ℝ (κ X w) z -
        innerSL ℝ p) z := by
  have hshift := (hκ.hasFDerivAt.smul (hasFDerivAt_id z)).const_add X
  have hpair := hshift.prodMk (hasFDerivAt_const w z)
  have hcomp := (hF.hasFDerivAt.comp z (f := fun z' => (X + κ X w z' • z',w)) hpair).add_const (σ (X,p))
  have hi : HasFDerivAt (fun z => inner ℝ z p) (innerSL ℝ p) z := by
    simpa only [innerSL_apply_apply, real_inner_comm] using! (innerSL ℝ p).hasFDerivAt (x := z)
  convert! hcomp.sub hi using 1
  ext u
  simp only [sub_apply, comp_apply, add_apply, smul_apply, id_apply,
    smulRight_apply, prod_apply, zero_apply, baseDifferential, inl_apply,
    id_eq]
  rw [show (κ X w z • u + (fderiv ℝ (κ X w) z u) • z, (0:W)) =
      κ X w z • (u,(0:W)) + (fderiv ℝ (κ X w) z u) • (z,(0:W)) by simp]
  rw [map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

lemma hasFDerivAt_shiftedPhase_w {F : E × W → ℝ} (σ : E × E → ℝ)
    {κ : E → W → E → ℝ} (X : E) (w : W) (z p : E)
    (hF : DifferentiableAt ℝ F (X + κ X w z • z,w))
    (hκ : DifferentiableAt ℝ (fun w => κ X w z) w) :
    HasFDerivAt (fun w => shiftedPhase F σ κ X w z p)
      (verticalDifferential F (X+κ X w z • z) w +
        (baseDifferential F (X+κ X w z • z) w z) •
          fderiv ℝ (fun w => κ X w z) w) w := by
  have hshift := (hκ.hasFDerivAt.smul_const z).const_add X
  have hpair := hshift.prodMk (hasFDerivAt_id w)
  have H := (((hF.hasFDerivAt.comp w (f := fun w' => (X + κ X w' z • z,w')) hpair).add_const (σ (X,p))).sub_const
    (inner ℝ z p))
  convert! H using 1
  ext u
  simp only [add_apply, comp_apply, smul_apply, smulRight_apply, prod_apply,
    id_apply, verticalDifferential, baseDifferential, inl_apply, inr_apply]
  rw [show (fderiv ℝ (fun w => κ X w z) w u • z, u) =
      (fderiv ℝ (fun w => κ X w z) w u) • (z,(0:W)) + ((0:E),u) by simp]
  rw [map_add, map_smul]
  simp only [smul_eq_mul]
  ring

lemma hasFDerivAt_shiftedPhase_X {F : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} (X : E) (w : W) (z p : E)
    (hF : DifferentiableAt ℝ F (X + κ X w z • z,w))
    (hκ : DifferentiableAt ℝ (fun X => κ X w z) X)
    (hσ : DifferentiableAt ℝ (fun X => σ (X,p)) X) :
    HasFDerivAt (fun X => shiftedPhase F σ κ X w z p)
      (baseDifferential F (X+κ X w z • z) w +
        (baseDifferential F (X+κ X w z • z) w z) •
          fderiv ℝ (fun X => κ X w z) X + fderiv ℝ (fun X => σ (X,p)) X) X := by
  have hshift := (hasFDerivAt_id X).add (hκ.hasFDerivAt.smul_const z)
  have hpair := hshift.prodMk (hasFDerivAt_const w X)
  have H := ((hF.hasFDerivAt.comp X (f := fun X' => (X' + κ X' w z • z,w)) hpair).add hσ.hasFDerivAt).sub_const
    (inner ℝ z p)
  convert! H using 1
  ext u
  simp only [add_apply, comp_apply, smul_apply, smulRight_apply, prod_apply,
    id_apply, zero_apply, baseDifferential, inl_apply]
  rw [show (u + (fderiv ℝ (fun X => κ X w z) X u) • z, (0:W)) =
      (u,(0:W)) + (fderiv ℝ (fun X => κ X w z) X u) • (z,(0:W)) by simp]
  rw [map_add, map_smul]
  simp only [smul_eq_mul]
  ring

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open scoped InnerProductSpace
open ContinuousLinearMap
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in

lemma displacement_bound_of_critical_p {F : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} {X : E} {w : W} {z p : E} {δ : ℝ}
    (hσ : DifferentiableAt ℝ (fun p => σ (X,p)) p)
    (hσb : ‖fderiv ℝ (fun p => σ (X,p)) p‖ < δ)
    (hp : fderiv ℝ (fun p => shiftedPhase F σ κ X w z p) p = 0) : ‖z‖ < δ := by
  rw [(hasFDerivAt_shiftedPhase_p F κ X w z p hσ).fderiv] at hp
  have he := sub_eq_zero.mp hp
  rw [he, innerSL_apply_norm] at hσb
  exact hσb

lemma norm_shiftedPhase_w_lower {F : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} {X : E} {w : W} {z p : E} {c C δ₀ δ₁ : ℝ}
    (hF : DifferentiableAt ℝ F (X + κ X w z • z,w))
    (hκ : DifferentiableAt ℝ (fun w => κ X w z) w)
    (hw : w ≠ 0) (hC : 0 ≤ C) (hδ₀ : 0 ≤ δ₀) (_hδ₁ : 0 ≤ δ₁)
    (hbase : ‖baseDifferential F (X+κ X w z • z) w‖ ≤ C * ‖w‖^2)
    (hvertical : c * ‖w‖ ≤ ‖verticalDifferential F (X+κ X w z • z) w‖)
    (hz : ‖z‖ ≤ δ₀) (hcutoff : ‖fderiv ℝ (fun w => κ X w z) w‖ ≤ δ₁ / ‖w‖) :
    (c-C*δ₀*δ₁) * ‖w‖ ≤ ‖fderiv ℝ (fun w => shiftedPhase F σ κ X w z p) w‖ := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let a := baseDifferential F (X+κ X w z • z) w
  let b := verticalDifferential F (X+κ X w z • z) w
  let D := fderiv ℝ (fun w => κ X w z) w
  have ha : ‖a z‖ ≤ C*‖w‖^2*δ₀ := by
    calc
      ‖a z‖ ≤ ‖a‖ * ‖z‖ := a.le_opNorm z
      _ ≤ (C * ‖w‖^2) * δ₀ := mul_le_mul hbase hz (norm_nonneg _) (by positivity)
  have herr : ‖a z • D‖ ≤ C*δ₀*δ₁*‖w‖ := by
    calc
      ‖a z • D‖ = ‖a z‖ * ‖D‖ := norm_smul _ _
      _ ≤ (C*‖w‖^2*δ₀) * (δ₁/‖w‖) :=
        mul_le_mul ha hcutoff (norm_nonneg _) (by positivity)
      _ = C*δ₀*δ₁*‖w‖ := by field_simp
  rw [(hasFDerivAt_shiftedPhase_w σ X w z p hF hκ).fderiv]
  change (c-C*δ₀*δ₁) * ‖w‖ ≤ ‖b + a z • D‖
  have HT : ‖b‖ ≤ ‖b + a z • D‖ + ‖a z • D‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (b + a z • D) (a z • D)
  change c * ‖w‖ ≤ ‖b‖ at hvertical
  nlinarith

lemma shiftedPhase_w_ne_zero {F : E × W → ℝ} {σ : E × E → ℝ}
    {κ : E → W → E → ℝ} {X : E} {w : W} {z p : E} {c C δ₀ δ₁ : ℝ}
    (hF : DifferentiableAt ℝ F (X + κ X w z • z,w))
    (hκ : DifferentiableAt ℝ (fun w => κ X w z) w)
    (hw : w ≠ 0) (hC : 0 ≤ C) (hδ₀ : 0 ≤ δ₀) (hδ₁ : 0 ≤ δ₁)
    (hbase : ‖baseDifferential F (X+κ X w z • z) w‖ ≤ C * ‖w‖^2)
    (hvertical : c * ‖w‖ ≤ ‖verticalDifferential F (X+κ X w z • z) w‖)
    (hz : ‖z‖ ≤ δ₀) (hcutoff : ‖fderiv ℝ (fun w => κ X w z) w‖ ≤ δ₁ / ‖w‖)
    (hsmall : C*δ₀*δ₁ < c) :
    fderiv ℝ (fun w => shiftedPhase F σ κ X w z p) w ≠ 0 := by
  apply norm_ne_zero_iff.mp
  apply ne_of_gt
  exact (mul_pos (sub_pos.mpr hsmall) (norm_pos_iff.mpr hw)).trans_le
    (norm_shiftedPhase_w_lower hF hκ hw hC hδ₀ hδ₁ hbase hvertical hz hcutoff)

def productCutoff (ζ β : E → ℝ) (χ : W → ℝ) (X : E) (w : W) (z : E) : ℝ :=
  ζ X * β z * χ w

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma fderiv_productCutoff_w (ζ β : E → ℝ) {χ : W → ℝ} (X : E) (z : E) {w : W}
    (hχ : DifferentiableAt ℝ χ w) :
    fderiv ℝ (fun w => productCutoff ζ β χ X w z) w =
      (ζ X * β z) • fderiv ℝ χ w :=
  (hχ.hasFDerivAt.const_smul (ζ X * β z)).fderiv

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma norm_fderiv_productCutoff_w_le (ζ β : E → ℝ) {χ : W → ℝ} (X : E) (z : E)
    {w : W} (hχ : DifferentiableAt ℝ χ w)
    (hζ : ζ X ∈ Set.Icc (0:ℝ) 1) (hβ : β z ∈ Set.Icc (0:ℝ) 1) :
    ‖fderiv ℝ (fun w => productCutoff ζ β χ X w z) w‖ ≤ ‖fderiv ℝ χ w‖ := by
  rw [fderiv_productCutoff_w ζ β X z hχ, norm_smul,
    Real.norm_of_nonneg (mul_nonneg hζ.1 hβ.1)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul_of_nonneg_right hζ.2 hβ.1).trans (by simpa using hβ.2))

end NearbyLagrangian.Transport

end

end OAI
