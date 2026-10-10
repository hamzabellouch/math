import OAI.Geometry.Convex.GeneralMahler.NtLayer
import OAI.Geometry.Convex.GeneralMahler.ProfileGrowth

namespace OAI
/-! Combine the log-gains of the two matrices. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers Profile
variable {m:ℕ} [NeZero m]
-- trace-and-expectation paper notation
def et (A: Rn m→Mat m) := ∫ x,trN (A x) ∂normal m
def etw (B:Mat m) (A:Rn m→Mat m) := et fun x=> B*A x

def eGain (e:Edge m) := ∫ x,logD (e.Jedge x) ∂normal m
def surplus (e:Edge m) := ∫ x,(∫ z,e.beta x z) ∂normal m

lemma eGain_exact (e:Edge m) : eGain e= LC 0 +
    (∫ x,(∫ z,e.LinearT z x) ∂normal m)+surplus e := by
  unfold eGain surplus
  simp_rw [e.gain_exact]
  have hi := (mixed_integrable e.mixed_T (μ:=volume) (ν:=normal m)
    e.meas_T.aestronglyMeasurable).integral_prod_right
  have hh := (mixed_integrable e.beta_mixed (μ:=volume) (ν:=normal m)
    e.meas_beta.aestronglyMeasurable).integral_prod_right
  rw [integral_add,integral_add]
  · simp
  all_goals first | exact integrable_const _ | exact hi | exact hh |
    exact (integrable_const _).add hi

def eNt (e:Edge m) := ∫ u:Plane,∫ x,e.nt0 u x ∂normal m
lemma surplus_lower (e:Edge m) : eNt e/8 ≤ surplus e+surplus e.ref := by
  rw [div_le_iff₀ (by norm_num : 0 < (8:ℝ))]
  unfold eNt surplus; rw [integral_integral_swap]
  have hh (e:Edge m) := (mixed_integrable e.beta_mixed (μ:=volume) (ν:=normal m)
    e.meas_beta.aestronglyMeasurable).integral_prod_right
  · rw [← integral_add (show Integrable (fun x=>∫ z,e.beta x z) (normal m) from hh e)
      (show Integrable (fun x=>∫ z,e.ref.beta x z) (normal m) from hh e.ref),mul_comm _ 8,
      ← integral_const_mul]
    exact integral_mono e.n0_int.integral_prod_right (((hh e).add (hh e.ref)).const_mul _)
      (fun x=>e.total_surplus x)
  exact e.n0_int
namespace Edge
def Plin (e:Edge m) (z:ℝ) (x:Rn m) := MillsJ z*(e.h1 x z-p z)
lemma pm_lin (e:Edge m) : mixed e.Plin := by
  have h := mixed.of_rapid (Y:=Rn m) (rapid_p.product poly_mj)
  convert e.mixed_T.sub h using 1
  funext z x; unfold Plin LinearT; ring
omit [NeZero m] in
lemma plSM (e:Edge m) : StronglyMeasurable e.Plin.uncurry :=
  (((c_mj.measurable.comp measurable_fst)).mul
    (e.meas_h1.sub (cp.measurable.comp measurable_fst))).stronglyMeasurable

lemma lin_alt (e:Edge m) (x) :
    LC 0+(∫ z,e.LinearT z x)=(∫ z,phi z*LC z)+(∫ z,e.Plin z x) := by
  rw [lc_integral_equiv]
  have hi : Integrable (fun z=>e.Plin z x) := mixed_integrable_left e.pm_lin x
    ((e.plSM.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  have hh := (rapid_p.product poly_mj).integrable_real
    ((cp.measurable.sub measurable_st).mul c_mj.measurable)
  rw [add_assoc,← integral_add hh hi]
  congr 2; ext x; unfold LinearT Plin; ring

lemma gain_alt (e:Edge m) :
    eGain e=(∫ z,phi z*LC z) +
      (∫ x,(∫ z,e.Plin z x) ∂normal m)+surplus e := by
  rw [eGain_exact]
  have hi := (mixed_integrable e.pm_lin (μ:=volume) (ν:=normal m)
    e.plSM.aestronglyMeasurable).integral_prod_right
  have hh := (mixed_integrable e.mixed_T (μ:=volume) (ν:=normal m)
    e.meas_T.aestronglyMeasurable).integral_prod_right
  congr 1
  have he : (∫ x:Rn m,(LC 0+∫ z,e.LinearT z x) ∂normal m) =
      (∫ x:Rn m,((∫ z,phi z*LC z)+∫ z,e.Plin z x) ∂normal m) := by
    congr 1; ext x; rw [lin_alt]
  rw [integral_add,integral_add] at he
  · simpa using he
  all_goals first | exact integrable_const _ | exact hi | exact hh

lemma h1_ref (e:Edge m) (x z) : e.ref.h1 x (-z)=1-e.h1 x z := by
  unfold ref h1; simp only [neg_neg,trN_sub,trN_one]
end Edge
namespace ProjField
variable (q:ProjField m)
lemma vp_lin (x) : (∫ z,q.edge.Plin z x)+(∫ z,q.edge.ref.Plin z x) = -trN (q.Hmat Profile.v x) := by
  have hi (e:Edge m) : Integrable (fun z=>e.Plin z x) := mixed_integrable_left e.pm_lin x
    ((e.plSM.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  let g := fun z=>q.edge.ref.Plin z x
  have hh : Integrable (fun z:ℝ=>g (-z)) :=
    ((Measure.measurePreserving_neg volume).integrable_comp_emb
      (Homeomorph.neg ℝ).measurableEmbedding).mpr (hi _)
  change (∫ z,q.edge.Plin z x)+(∫ z,g z)=_
  rw [← integral_neg_eq_self g volume,← integral_add (hi _) hh]
  unfold Hmat; rw [← trL_apply,← trL.integral_comp_comm
    (q.H_left_int (v_test.der.poly) _), ← integral_neg]
  congr 1
  ext z
  unfold kerH g Edge.Plin
  rw [_root_.map_smul,trL_apply,Edge.h1_ref,neg_p,v_deriv, PD,trN_sub,trN_smul,trN_one]
  change _+ _ = -(_*((p z*1)-q.edge.h1 x z))
  ring

lemma gain_eq11 :
    2*(∫ z,phi z*LC z) - et (q.Hmat v) + eNt q.edge/8 ≤
      eGain q.edge + eGain q.edge.ref := by
  have hi (e:Edge m) : Integrable (fun x=>∫ z,e.Plin z x) (normal m) :=
    (mixed_integrable e.pm_lin (μ:=volume) (ν:=normal m)
      e.plSM.aestronglyMeasurable).integral_prod_right
  rw [Edge.gain_alt,Edge.gain_alt]
  have hh := integral_add (hi q.edge) (hi q.edge.ref)
  change (∫ x,(∫ z,q.edge.Plin z x)+(∫ z,q.edge.ref.Plin z x) ∂normal m) = _ at hh
  simp_rw [q.vp_lin] at hh; rw [integral_neg] at hh
  unfold et
  linarith [surplus_lower q.edge]
end ProjField
end GeneralMahler

end

end OAI
