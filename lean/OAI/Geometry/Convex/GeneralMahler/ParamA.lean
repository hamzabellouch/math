import OAI.Geometry.Convex.GeneralMahler.ParamMoment

namespace OAI
/-! §02: continuity of layer expectations in normalization parameters. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m : ℕ} [NeZero m] (l : Rn m →L[ℝ] ℝ) (c : ℝ)
namespace ProjField

variable (q : ProjField m)

def aun (z : ℝ) (x : Rn m) := (c+l x) • q.PD z x
def da (z : ℝ) := ∫ x,q.aun l c z x ∂normal m


omit [NeZero m] in
lemma PD_eq (z x) : q.PD z x = (p z-st z) • (1:Mat m) - q.Pstep z x := by
  simp [PD,Pstep,Gstep,sub_smul]

lemma mixed_aun : mixed (q.aun l c) :=
  q.mixed_PD.product (g := fun _ x=>c+l x)
    (((PolyBound.const c).add (PolyBound.clm l)).comp PolyBound.snd) (fun z x=>by
      rw [aun,norm_smul,mul_comm])

omit [NeZero m] in
lemma sm_aun : StronglyMeasurable (q.aun l c).uncurry :=
  (continuous_const.add (l.continuous.comp continuous_snd)).stronglyMeasurable.smul q.PD_sm

lemma int_aun : Integrable (q.aun l c).uncurry (volume.prod (normal m)) :=
  mixed_integrable (q.mixed_aun l c) (q.sm_aun l c).aestronglyMeasurable

lemma int_aun_right (z) : Integrable (q.aun l c z) (normal m) :=
  (((q.mixed_aun l c).poly.comp ((PolyBound.const z).prodMk PolyBound.id))).gaussian_integrable
    ((q.sm_aun l c).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable

lemma int_da : Integrable (q.da l c) := by
  exact (q.int_aun l c).integral_prod_left

lemma weighted_A : (∫ x,(c+l x) • q.Amat x ∂normal m) = ∫ z,q.da l c z := by
  have he (x) : (c+l x) • q.Amat x = ∫ z, q.aun l c z x := by
    rw [Amat,Hmat,← integral_smul]
    simp [kerH, aun]
  simp_rw [he]
  exact (integral_integral_swap (q.int_aun l c)).symm

omit [NeZero m] in
lemma da_eq (z : ℝ) :
    q.da l c z = (∫ x,(c+l x) • (p z • (1:Mat m)) ∂normal m)
      - (∫ x,(c+l x) • ((q.Pmat z x)) ∂normal m) := by
  have h : Integrable (fun x : Rn m => c+l x) (normal m) :=
    ((PolyBound.const c).add (PolyBound.clm l)).gaussian_integrable
      (continuous_const.add l.continuous).aestronglyMeasurable
  rw [← integral_sub (h.smul_const _) (q.weighted_P_integrable z l c)]
  simp [aun,da,PD,smul_sub]

variable (m) in
lemma da_uniform {K : ℝ} (hk : 1 ≤ K) (n : ℕ) :
    ∃ C ≥ (0:ℝ), ∀ q:ProjField m, q.Bound K → ∀ z,
      ‖q.da l c z‖*(1+‖z‖)^n ≤ C := by
  obtain ⟨C,hc,hC⟩ := uniform_Pstep m hk n
  obtain ⟨D,hd,hD⟩ := rapid_p n
  let g (x:Rn m) := ‖c+l x‖*(D+C*(1+‖x‖)^n)
  have hh (x:Rn m) : 0 ≤ g x := by unfold g; positivity
  have hg : PolyBound g :=
    (((PolyBound.const c).add (PolyBound.clm l)).norm).mul
      ((PolyBound.const D).add ((PolyBound.const C).mul (((PolyBound.const 1).add
        (PolyBound.id (X := Rn m)).norm).pow n)))
  have hi := hg.gaussian_integrable (μ := normal m)
    ((by unfold g; fun_prop : Continuous g).aestronglyMeasurable)
  refine ⟨∫ x,g x ∂normal m,integral_nonneg hh,fun q hq z=>?_⟩
  calc
    _ ≤ (∫ x, ‖q.aun l c z x‖ ∂normal m)*(1+‖z‖)^n := by unfold da; gcongr; exact norm_integral_le_integral_norm _
    _ = ∫ x, ‖q.aun l c z x‖*(1+‖z‖)^n ∂normal m := (integral_mul_const _ _).symm
    _ ≤ _ := by
      apply integral_mono ((q.int_aun_right l c z).norm.mul_const _) hi
      intro x
      have hb : ‖q.PD z x‖ * (1+‖z‖)^n ≤ D+C*(1+‖x‖)^n := by
        rw [q.PD_eq]
        apply le_trans (mul_le_mul_of_nonneg_right (norm_sub_le ..)
          (show 0 ≤ (1+‖z‖)^n by positivity))
        rw [add_mul,norm_smul]
        have he := mul_le_of_le_one_right (norm_nonneg (p z-st z)) (one_op_le (m := m))
        exact add_le_add (le_trans (mul_le_mul_of_nonneg_right he (by positivity)) (hD _))
          (hC q hq _ _)
      change ‖(c+l x) • q.PD z x‖ * (1+‖z‖)^n ≤ g x; rw [norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
end ProjField

namespace Param
variable {R : ℝ} (q : ProjField m) (hr : 2 ≤ R) (h:0<R)
include hr

theorem cont_weightedA :
    Continuous (fun p:Param m R => ∫ x,(c+l x) • (p.instanceQ h q).Amat x ∂normal m) := by
  obtain ⟨K,hk⟩ := q.Field_isBound
  have hh := hk.one_le
  let n := Module.finrank ℝ ℝ+1
  obtain ⟨C,hC,hd⟩ := ProjField.da_uniform m l c (show 1≤K*R by nlinarith) n
  let g := fun t:ℝ=> C*((1+‖t‖)^n)⁻¹
  have hi : Integrable g := envelope_inv_int.const_mul C
  simp_rw [ProjField.weighted_A]
  apply continuous_iff_continuousAt.mpr
  intro v
  apply continuousAt_of_dominated
    (Eventually.of_forall fun y => ((y.instanceQ h q).int_da l c).aestronglyMeasurable)
    _ hi
  · apply ae_of_all
    intro x
    have hh := weighted_P_cont q hr h x l c
    have he : Continuous (fun p:Param m R => (p.instanceQ h q).da l c x) := by
      simp_rw [ProjField.da_eq]
      exact continuous_const.sub hh
    exact he.continuousAt
  · apply Eventually.of_forall
    intro x
    apply ae_of_all
    intro z
    dsimp only [g]
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    exact hd _ (x.Bound_instance hr h hk) z

lemma cont_avgA : Continuous (fun p:Param m R => (p.instanceQ h q).avgA) := by
  simpa [ProjField.avgA] using cont_weightedA (m:=m) 0 1 q hr h

lemma cont_M (i:Fin m) : Continuous (fun p:Param m R => (p.instanceQ h q).M i) := by
  simpa [ProjField.M] using cont_weightedA (ProjField.coord i) 0 q hr h

lemma cont_L (x : Rn m) : Continuous (fun p:Param m R => (p.instanceQ h q).Lmat x) :=
  continuous_finsetSum _ (fun i _hi => (continuous_const (y := x i)).smul (cont_M q hr h i))
end Param
end GeneralMahler

end

end OAI
