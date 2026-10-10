import OAI.Geometry.Convex.GeneralMahler.ParamA
import OAI.Geometry.Convex.GeneralMahler.LayerMeasure

namespace OAI
/-! Inward normalization estimate: layer as seen in a unit direction. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m : ℕ} [NeZero m]
namespace ProjField
variable (q : ProjField m) (v : Rn m)
def dimH (z : ℝ) : ℝ := ∫ x, ⟪v,op (q.Pmat z x) v⟫ ∂normal m

omit [NeZero m] in
lemma h_between (hv : ‖v‖=1) (z : ℝ) :
    0 ≤ q.dimH v z ∧ q.dimH v z ≤ 1 := by
  have hi := meanJac_integrable q.C q.root (q.shift z)
  constructor
  · apply integral_nonneg
    intro x; exact (op_posSemidef_iff.mp (q.Pmat_psd z x).posSemidef).2 v
  rw [← show (∫ x:Rn m,(1:ℝ) ∂normal m) = 1 by simp]
  apply integral_mono (integral_opPair hi v v) (integrable_const _)
  intro x
  have he := (op_order_iff (q.Pmat_herm z x) isHermitian_one).mp (q.Pmat_le z x) v
  rw [_root_.map_one] at he
  apply he.trans_eq; change ⟪v,v⟫=1; rw [real_inner_self_eq_norm_sq,hv]; norm_num

def vp := q.root.symm v
omit [NeZero m] in
lemma S_vp : op q.S (q.vp v)=v := by
  rw [← q.matrix_eq]; exact q.root.apply_symm_apply _
omit [NeZero m] in
lemma dimH_X (z : ℝ) :
    q.dimH v z = ∫ x:Rn m, ⟪x,q.vp v⟫*⟪v,q.XT z x⟫ ∂normal m := by
  have h := q.normal_XT_inner z (q.vp v) v
  rw [q.S_vp] at h; exact h

omit [NeZero m] in
lemma dimH_Y (hv : ‖v‖=1) (z : ℝ) :
    1-q.dimH v z = ∫ x:Rn m, ⟪x,q.vp v⟫*(-⟪v,q.YT z x⟫) ∂normal m := by
  let w := q.vp v
  let a (x : Rn m) := affineN q.root (q.shift z) x
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ v
  have hm : LipschitzWith _ (l ∘ a) :=
    l.lipschitzWith.comp ((q.root.toContinuousLinearMap.lipschitzWith).add (LipschitzWith.const _))
  have hf : (∫ x, ⟪x,w⟫*(l∘a) x ∂normal m)=1 := by
    have h := normal_IBP_lipschitz hm w
    have he (x:Rn m) : fderiv ℝ (l∘a) x w=1 := by
      have hi := (l.hasFDerivAt.comp x (q.root.hasFDerivAt.add_const (q.shift z))).fderiv
      change fderiv ℝ (l∘a) x = _ at hi
      rw [hi]
      change ⟪v,q.root w⟫=1
      rw [show q.root w=v from q.root.apply_symm_apply _,real_inner_self_eq_norm_sq,hv]; norm_num
    change (∫ x, ⟪x,w⟫ • (l∘a) x ∂normal m)=1
    rw [← h]; simp_rw [he]; simp
  have hi : Integrable (fun x=>⟪x,w⟫*(l∘a) x) (normal m) := by
    have he : PolyBound (fun x=>⟪x,w⟫) := by
      simp_rw [real_inner_comm w]
      exact PolyBound.clm (f := (show Rn m→L[ℝ] ℝ from innerSL ℝ w))
    exact (he.mul (PolyBound.lipschitz hm)).gaussian_integrable
      (((continuous_id.inner continuous_const).mul hm.continuous).aestronglyMeasurable)
  have hE (x) :
      ⟪x,q.vp v⟫*(-⟪v,q.YT z x⟫) = ⟪x,w⟫*(l∘a) x-⟪x,w⟫*⟪v,q.XT z x⟫ := by
    change ⟪x,w⟫*_ = ⟪x,w⟫*⟪v,q.Z x+q.shift z⟫-_
    rw [q.YT_sub,inner_sub_right]; ring
  simp_rw [hE]; rw [integral_sub hi (q.integrable_pair ..),hf,q.dimH_X]

lemma form_da (hv : ‖v‖=1) (z : ℝ) :
    opPair v v (q.da 0 1 z) = p z - q.dimH v z := by
  have hi := (q.int_aun_right 0 1 z)
  unfold da
  rw [← (opPair v v).integral_comp_comm hi]
  have he (x) : opPair v v (q.aun 0 1 z x) = p z-⟪v,op (q.Pmat z x) v⟫ := by
    simp only [aun,_root_.zero_apply,add_zero,one_smul,PD,_root_.map_sub,
      opPair_apply,_root_.map_smul,smul_eq_mul,_root_.map_one]
    change _*⟪v,v⟫-_ = _
    rw [real_inner_self_eq_norm_sq,hv]; ring
  simp_rw [he]
  rw [integral_sub (integrable_const _) (show Integrable (fun x:Rn m=>⟪v,op (q.Pmat z x) v⟫) (normal m) from integral_opPair
    (meanJac_integrable q.C q.root (q.shift z)) v v)]
  simp [dimH]

lemma whole (hv : ‖v‖=1) :
    ⟪v,op q.avgA v⟫ = ∫ z,(p z-q.dimH v z) := by
  have hh := q.weighted_A 0 1
  have he : q.avgA=∫ z,q.da 0 1 z := by simpa [avgA] using hh
  change opPair v v _=_
  rw [he, ← (opPair v v).integral_comp_comm (q.int_da ..)]
  simp_rw [q.form_da v hv]

lemma diff_int (hv : ‖v‖=1) : Integrable fun z=>p z-q.dimH v z := by
  simp_rw [← q.form_da v hv]
  exact (opPair v v).integrable_comp (q.int_da ..)

lemma int_pst : Integrable (fun z=>p z-st z) :=
  rapid_p.integrable_real (cp.measurable.sub measurable_st)

lemma p_step_zero : (∫ z,p z-st z)=0 := by
  have hi := integral_neg_eq_self (μ := volume) (fun z=>p z-st z)
  have he : (∫ z,p (-z)-st (-z)) = ∫ z,-(p z-st z) := by
    apply integral_congr_ae
    filter_upwards [show ∀ᵐ z:ℝ,z ≠ 0 by rw [ae_iff];simp] with z hz
    rw [neg_p]; unfold st; split_ifs <;> grind
  rw [integral_neg] at he
  linarith

lemma step_int (hv : ‖v‖=1) : Integrable fun z=> st z-q.dimH v z := by
  convert (q.diff_int v hv).sub int_pst using 1
  ext x; change _=(p x-_) - (p x-_); ring

def plus := ∫ z in Ici (0:ℝ), (1-q.dimH v z)
def minus := ∫ z in Iio (0:ℝ), q.dimH v z

lemma pn (hv : ‖v‖=1) : ⟪v,op q.avgA v⟫ = q.plus v - q.minus v := by
  rw [whole q v hv]
  have he : (fun z=>p z - q.dimH v z) = fun z=> (p z-st z)+(st z-q.dimH v z) := by ext; ring
  rw [he, integral_add int_pst (q.step_int v hv),p_step_zero,zero_add]
  rw [← integral_add_compl measurableSet_Ici (q.step_int v hv) (s := Ici (0:ℝ)), compl_Ici]
  have he₁ : (∫ z in Ici (0:ℝ), (st z-q.dimH v z))=q.plus v :=
    setIntegral_congr_fun measurableSet_Ici fun z hz => by simp [st,show 0 ≤ z from hz]
  have he₂ : (∫ z in Iio (0:ℝ), (st z-q.dimH v z))= -q.minus v := by
    rw [minus, ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Iio fun z hz => by
      have h : ¬0 ≤ z := not_le_of_gt hz
      simp [st,h]
  rw [he₁,he₂]; ring

lemma plus_int (hv : ‖v‖=1) :
    IntegrableOn (fun z=>1-q.dimH v z) (Ici (0:ℝ)) :=
  (q.step_int v hv).integrableOn.congr_fun (fun z hz=>by simp [st,show 0 ≤ z from hz]) measurableSet_Ici
lemma minus_int (hv : ‖v‖=1) : IntegrableOn (q.dimH v) (Iio (0:ℝ)) :=
  (q.step_int v hv).neg.integrableOn.congr_fun (fun z hz=>by simp only [Pi.neg_apply,st,ite_eq_right (not_le_of_gt (show z < 0 from hz)),zero_sub,neg_neg]) measurableSet_Iio
end ProjField
end GeneralMahler

end

end OAI
