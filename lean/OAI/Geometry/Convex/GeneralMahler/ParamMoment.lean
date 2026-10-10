import OAI.Geometry.Convex.GeneralMahler.Moving
import OAI.Geometry.Convex.GeneralMahler.ProjParts

namespace OAI
/-! §02 continuity of the Gaussian polynomial moments of P. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ} {R : ℝ}

-- generic dominated parameter expectation
theorem continuous_normal_integral {X F : Type*} [TopologicalSpace X] [FirstCountableTopology X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : X → Rn m → F} {g : Rn m→ℝ} (hg : Integrable g (normal m))
    (hm : ∀ x, AEStronglyMeasurable (f x) (normal m)) (he : ∀ x y, ‖f x y‖ ≤ g y)
    (hf : ∀ y, Continuous fun x=>f x y) : Continuous (fun x=>∫ y, f x y ∂normal m) :=
  continuous_iff_continuousAt.mpr (fun _x => continuousAt_of_dominated (Eventually.of_forall hm)
    (Eventually.of_forall fun x=>ae_of_all _ fun y=>he x y) hg (ae_of_all _ fun y=>(hf y).continuousAt))

lemma continuous_matrix_op {X : Type*} [TopologicalSpace X] (f:X → Mat m)
    (h : ∀ x y, Continuous fun z => ⟪x,op (f z) y⟫) :
    Continuous f := by
  apply continuous_matrix; intro i j
  let e := EuclideanSpace.basisFun (Fin m) ℝ
  convert h (e i) (e j) using 1
  ext z; rw [inner_toEuclideanCLM]
  simp [e,EuclideanSpace.basisFun_apply,EuclideanSpace.single,mulVec,dotProduct]

namespace Param
lemma rootNorm (p:Param m R) :
    ‖p.S‖ ≤ 2 ∧ ‖(equivPD p.S_pos).symm.toContinuousLinearMap‖ ≤ 2 :=
  inv_norm_box _ (by norm_num) (by simpa using p.S_box) _ (equivPD_spec _)
theorem S_action (x : Rn m) :
    Continuous (fun p:Param m R=>equivPD p.S_pos x) := by
  have he (p:Param m R) : equivPD p.S_pos x = op p.S x := by
    change (equivPD _).toContinuousLinearMap x=_; rw [equivPD_spec]
  simp_rw [he]
  exact ((continuous_op.comp cont_S).clm_apply continuous_const)

theorem iS_action (x : Rn m) :
    Continuous (fun p:Param m R=>(equivPD p.S_pos).symm x) := by
  apply continuous_iff_seqContinuous.mpr
  intro f a ha
  exact tendsto_inv_action _ (p := fun i=>equivPD (f i).S_pos)
    (fun i=>(f i).rootNorm.2) (fun x => ((S_action x).tendsto a).comp ha) (v := fun _=>x) tendsto_const_nhds

variable (q : ProjField m) (hr : 2 ≤ R) (h : 0 < R) (z : ℝ)
variable [NeZero m]
include hr

theorem XT_cont (x:Rn m) :
    Continuous (fun p:Param m R=>(p.instanceQ h q).XT z x) := by
  have hu := shift_cont q hr h z
  let F := fun p:Param m R=>(equivPD p.S_pos x)+(p.instanceQ h q).shift z
  have hv : Continuous (fun p:Param m R=>(p,F p)) := continuous_id.prodMk
    ((S_action x).add hu)
  convert (proj_cont q h).comp hv ; rfl

theorem XT_bound : ∃ C ≥ (0:ℝ), ∀ p:Param m R, ∀ x,
    ‖(p.instanceQ h q).XT z x‖≤C*(1+‖x‖) := by
  obtain ⟨K,hk⟩ := q.Field_isBound
  obtain ⟨C,hc,hh⟩ := ProjField.layers_growth m (K := K*R) (by nlinarith [hk.one_le])
  use 2+C*(1+|z|),by positivity
  intro p x
  let i := p.instanceQ h q
  have he := hh _ (p.Bound_instance hr h hk) z
  have hu := norm_proj i.C (i.Z x+i.shift z)
  apply hu.trans ((norm_add_le ..).trans ?_)
  have hb : ‖i.Z x‖ ≤ 2*‖x‖ := by
    rw [i.Z_def]; apply ((op i.S).le_opNorm _).trans
    rw [op_norm]
    exact mul_le_mul_of_nonneg_right p.rootNorm.1 (norm_nonneg x)
  change ‖i.shift z‖ ≤ _ at he
  nlinarith [norm_nonneg x,abs_nonneg z, show 0≤C*(1+|z|)*‖x‖ by positivity]

theorem weighted_P_cont (l : Rn m →L[ℝ] ℝ) (c:ℝ) :
    Continuous (fun p:Param m R=> ∫ x, (c+l x) • ((p.instanceQ h q).Pmat z x) ∂normal m) := by
  apply continuous_matrix_op; intro v u
  let g := fun p:Param m R=>p.instanceQ h q
  let w := fun p:Param m R=>(equivPD p.S_pos).symm u
  have hc := iS_action (R:=R) u
  have he (p:Param m R) : op (g p).S (w p)=u := by
    change op p.S _ = _
    rw [← equivPD_spec p.S_pos]; exact (equivPD p.S_pos).apply_symm_apply _
  let b (p:Param m R) (x : Rn m) := ⟪v,(g p).XT z x⟫
  let f (p:Param m R) (x : Rn m) := ⟪x,w p⟫ * ((c+l x)*b p x)
  have ha (p : Param m R) :
      ⟪v, op (∫ x, (c+l x) • ((g p).Pmat z x) ∂normal m) u⟫ =
      (∫ x, f p x ∂normal m) - l (w p)*⟪v,Layers.a z • (g p).U⟫ := by
    set a := g p
    rw [op_inner_integral (a.weighted_P_integrable ..)]
    simp_rw [_root_.map_smul,_root_.smul_apply,real_inner_smul_right]
    have H := a.weighted_P_ip z l c (w p) v
    rw [he p] at H
    rw [H,integral_const_mul]
    change _-l (w p)*(∫ x, innerSL ℝ v (a.XT z x) ∂_) = _
    rw [(innerSL ℝ v).integral_comp_comm (a.X_int ..),a.XT_mean,innerSL_apply_apply,real_inner_smul_right]
  change Continuous (fun p : Param m R => ⟪v,op _ u⟫)
  have heq : (fun p:Param m R=>⟪v,op (∫ x,(c+l x) • ((p.instanceQ h q).Pmat z x) ∂normal m) u⟫) =
      fun p=>(∫ x, f p x ∂normal m) - l (w p)*⟪v,Layers.a z • (g p).U⟫ := funext ha
  rw [heq]
  apply Continuous.sub
  · obtain ⟨C,hC,Hu⟩ := XT_bound q hr h z
    let J (x:Rn m) := ‖x‖*(2*‖u‖) * (‖c+l x‖*(‖v‖*(C*(1+‖x‖))))
    have hJ : PolyBound J :=
      let hnx := (PolyBound.id (X:=Rn m)).norm
      let h1 := ((PolyBound.const c).add (PolyBound.clm l)).norm
      let h2 := (PolyBound.const C).mul ((PolyBound.const 1).add hnx)
      (hnx.mul (PolyBound.const _)).mul (h1.mul ((PolyBound.const _).mul h2))
    have hJC : Continuous J := by unfold J; fun_prop
    have hlc (p:Param m R) : Continuous (f p) :=
      ((continuous_id.inner continuous_const).mul ((continuous_const.add l.continuous).mul
        (continuous_const.inner (continuous_sample ..))))
    apply continuous_normal_integral (hJ.gaussian_integrable hJC.aestronglyMeasurable)
      (fun p=>(hlc p).aestronglyMeasurable)
    · intro p x
      have hu : ‖w p‖ ≤ 2*‖u‖ := le_trans
        ((equivPD p.S_pos).symm.toContinuousLinearMap.le_opNorm _) (mul_le_mul_of_nonneg_right p.rootNorm.2 (norm_nonneg _))
      have h₁ : ‖b p x‖ ≤ ‖v‖ * (C*(1+‖x‖)) :=
        (abs_real_inner_le_norm v _).trans (mul_le_mul_of_nonneg_left (Hu p x) (norm_nonneg _))
      have h₂ : ‖(⟪x,w p⟫:ℝ)‖ ≤ ‖x‖*(2*‖u‖) :=
        (abs_real_inner_le_norm x _).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
      dsimp only [f,J]; rw [norm_mul,norm_mul]; gcongr
    intro x
    exact ((continuous_const.inner hc).mul (continuous_const.mul
      (continuous_const.inner (XT_cont q hr h z x))))
  · have hU : Continuous fun p:Param m R => Layers.a z • (g p).U :=
      (continuous_const (y := Layers.a z)).smul (U_cont q h)
    exact (l.continuous.comp hc).mul (continuous_const.inner hU)
end Param
end GeneralMahler

end

end OAI
