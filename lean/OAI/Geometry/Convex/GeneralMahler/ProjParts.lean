import OAI.Geometry.Convex.GeneralMahler.HMatrix

namespace OAI
/-! Gaussian parts with an affine test; used to make moment continuity
independent of pointwise convergence of projection derivatives. -/
noncomputable section
open Set Filter Real Matrix MeasureTheory MeasureTheory.Measure Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
variable {m : ℕ}

namespace ProjField
variable (q : ProjField m)
variable [NeZero m]

omit [NeZero m] in
lemma weighted_P_integrable (z : ℝ) (l : Rn m→L[ℝ] ℝ) (c:ℝ) :
    Integrable (fun x:Rn m => (c+l x) • q.Pmat z x) (normal m) := by
  have hi := meanJac_integrable q.C q.root (q.shift z)
  apply PolyBound.gaussian_integrable
    (((PolyBound.const c).add (PolyBound.clm l)).smul
      (PolyBound.of_bound 1 fun x=>projJac_norm q.C (affineN q.root (q.shift z) x)))
  exact ((continuous_const.add l.continuous).aestronglyMeasurable.smul hi.aestronglyMeasurable)

omit [NeZero m] in
theorem weighted_P_ip (z : ℝ) (l : Rn m →L[ℝ] ℝ) (c:ℝ) (u v : Rn m) :
    (∫ g, (c+l g)*⟪v,op (q.Pmat z g) (op q.S u)⟫ ∂normal m) =
     (∫ g, ⟪g,u⟫*((c+l g)*⟪v,q.XT z g⟫) ∂normal m) -
        (∫ g, (l u)*⟪v,q.XT z g⟫ ∂normal m) := by
  let b := innerSL ℝ v
  let j := q.XT z
  obtain ⟨k,hk⟩ := q.XT_lipschitz z
  have hm : Continuous fun x => c+l x := continuous_const.add l.continuous
  have hi : LipschitzWith _ (b ∘ j) :=
    (innerSL ℝ v).lipschitzWith.comp hk
  let f := fun g => (c+l g)* ((b ∘ j) g)
  have hf : Continuous f := hm.mul hi.continuous
  have h₁ := (PolyBound.const c).add (PolyBound.clm l)
  have h₂ := PolyBound.lipschitz hi
  have he : PolyBound f := h₁.mul h₂
  let gD (g : Rn m) := b.comp ((op (q.Pmat z g)).comp (op q.S))
  have hd : ∀ᵐ x ∂normal m,
      HasFDerivAt f (((b∘j) x) • l + (c+l x) • gD x) x := by
    filter_upwards [q.XT_diff z] with x hx
    have he := ((hasFDerivAt_const c x).add l.hasFDerivAt).mul
      ((innerSL ℝ v).hasFDerivAt.comp x hx)
    convert he using 1
    all_goals first | rfl | (simp [b,j,gD] ; abel)
  let L : ℝ≥0 := ‖innerSL ℝ v‖₊*k
  have hi : LipschitzWith L (b ∘ j) := hi
  let bound := fun g => (‖c+l g‖ + ‖l‖)*(L:ℝ)+‖l‖*‖(b ∘ j) g‖
  have hbd : PolyBound bound :=
    ((h₁.norm.add (PolyBound.const _)).mul (PolyBound.const _)).add
      ((PolyBound.const _).mul h₂.norm)
  have hbc : Continuous bound := ((hm.norm.add continuous_const).mul continuous_const).add
    (continuous_const.mul hi.continuous.norm)
  have hg (x y : Rn m) (hy : ‖y‖<1) :
      ‖f (x+y)-f x‖ ≤ bound x *‖y‖ := by
    let z := x+y
    have hEq : f z-f x =
        (c+l z)*((b∘j) z-(b∘j) x) + l y*((b∘j) x) := by
      unfold f z; rw [_root_.map_add]; ring
    have hl : ‖c+l z‖ ≤ ‖c+l x‖+‖l‖ := by
      have hh := (l.le_opNorm y).trans (mul_le_of_le_one_right (norm_nonneg _) hy.le)
      unfold z; rw [_root_.map_add, ← add_assoc]
      exact (norm_add_le ..).trans (add_le_add le_rfl hh)
    have hj := hi.dist_le_mul (x+y) x
    rw [dist_eq_norm,dist_eq_norm,add_sub_cancel_left] at hj
    change ‖f z-f x‖≤_
    rw [hEq]
    apply (norm_add_le ..).trans
    rw [norm_mul,norm_mul]
    have H3 := mul_le_mul hl hj (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    have H4 := mul_le_mul_of_nonneg_right (l.le_opNorm y) (norm_nonneg ((b∘j) x))
    dsimp only [bound,z] at *
    linarith
  have hh := normal_IBP he hf (hd.mono fun _ h=>h.differentiableAt)
    (hbd.gaussian_integrable hbc.aestronglyMeasurable) hg u
  let g := fun x => (c+l x)*⟪v,op (q.Pmat z x) (op q.S u)⟫
  have hia : Integrable g (normal m) := by
    have H := integral_opPair (q.weighted_P_integrable z l c) v (op q.S u)
    simpa only [_root_.map_smul,_root_.smul_apply,real_inner_smul_right] using H
  have hib : Integrable (fun x=>l u*⟪v,q.XT z x⟫) (normal m) :=
    ((innerSL ℝ v).integrable_comp (q.X_int ..)).const_mul _
  have h₅ : (∫ x, fderiv ℝ f x u ∂normal m) =
      (∫ x,l u*⟪v,q.XT z x⟫ ∂normal m)+ ∫ x,g x ∂normal m := by
    rw [← integral_add hib hia]
    apply integral_congr_ae
    filter_upwards [hd] with x hx
    rw [hx.fderiv]
    simp [b,j,gD,g,mul_comm]
  change (∫ x, fderiv ℝ f x u ∂normal m) =
    ∫ x, ⟪x,u⟫ * ((c+l x)*⟪v,q.XT z x⟫) ∂normal m at hh
  rw [← hh,h₅]
  simp [g]
end ProjField
end GeneralMahler

end

end OAI
