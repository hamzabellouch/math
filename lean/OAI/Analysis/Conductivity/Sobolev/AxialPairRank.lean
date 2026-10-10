import Mathlib
import OAI.Analysis.Conductivity.Geometry.RegularPatch
import OAI.Analysis.Conductivity.Scalarization.CascadeConstitution

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def axialPair (f : Coord3 → ℝ) (x : Coord3) : Fin 2 → ℝ := ![x 0,f x]

lemma axialPair_smooth {f : Coord3 → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (axialPair f) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ 0
  · exact hf

lemma axialPair_gradient_zero {f : Coord3 → ℝ} {x : Coord3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    (gradientColumns (fderiv ℝ (axialPair f) x)).col 0 i=if (0:Fin 3)=i then 1 else 0 := by
  have hd (j : Fin 2) : DifferentiableAt ℝ (fun x => axialPair f x j) x := by
    fin_cases j
    · exact (differentiable_apply 0).differentiableAt
    · exact hf
  simp only [gradientColumns,Matrix.col,transpose_apply,LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe,fderiv_pi hd,ContinuousLinearMap.pi_apply]
  exact direction_coord i 0 x

lemma axialPair_gradient_one {f : Coord3 → ℝ} {x : Coord3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    (gradientColumns (fderiv ℝ (axialPair f) x)).col 1 i=direction (Pi.single i 1) f x := by
  have hd (j : Fin 2) : DifferentiableAt ℝ (fun x => axialPair f x j) x := by
    fin_cases j
    · exact (differentiable_apply 0).differentiableAt
    · exact hf
  simp only [gradientColumns,Matrix.col,transpose_apply,LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe,fderiv_pi hd,ContinuousLinearMap.pi_apply]
  rfl

lemma axialPair_gradient_independent {f : Coord3 → ℝ} {x : Coord3}
    (hf : DifferentiableAt ℝ f x) {i : Fin 3} (hi : i≠0)
    (hfi : direction (Pi.single i 1) f x≠0) :
    LinearIndependent ℝ (gradientColumns (fderiv ℝ (axialPair f) x)).col := by
  apply linearIndependent_fin2.mpr
  constructor
  · intro hz
    apply hfi
    have hh := congrFun hz i
    simpa only [axialPair_gradient_one hf,Pi.zero_apply] using hh
  · intro a he
    have hh := congrFun he i
    simp only [Pi.smul_apply,smul_eq_mul,axialPair_gradient_one hf,
      axialPair_gradient_zero hf,Ne.symm hi,ite_false] at hh
    have ha : a=0 := (mul_eq_zero.mp hh).resolve_right hfi
    have hh0 := congrFun he 0
    simp only [ha,Pi.smul_apply,zero_smul,axialPair_gradient_zero hf,
      ite_true] at hh0
    norm_num at hh0

lemma ae_sin_coord_ne_zero {r : ℝ} (hr : r≠0) (i : Fin 3) :
    ∀ᵐ x : Coord3,sin (r*x i)≠0 := by
  have h := ae_all_iff.mpr (fun n : ℤ => ae_coord3_ne i ((n:ℝ)*Real.pi/r))
  filter_upwards [h] with x hx
  intro hz
  obtain ⟨n,hn⟩ := sin_eq_zero_iff.mp hz
  exact hx n ((eq_div_iff hr).mpr (by linarith))

lemma axialPair_regularPatch {f : Coord3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f)
    {A : Coord3 → Symmetric3} (hA : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => (A x).val))
    {i : Fin 3} (hi : i≠0) {O : Set Coord3} (hO : IsOpen O)
    (hn : ∀ x∈O,direction (Pi.single i 1) f x≠0) :
    RegularPatch (axialPair f) A O := by
  exact ⟨hO,(axialPair_smooth hf).contDiffOn,hA.contDiffOn,
    Or.inl (fun x hx => axialPair_gradient_independent (hf.differentiable (by simp) x) hi (hn x hx))⟩

lemma axialPair_zero_rank (O : Set Coord3) : TwoFieldRankRegular (axialPair (fun _ => 0)) O := by
  refine Or.inr (Or.inl ⟨fun x : Coord3 => x 0,![1,0],0,(contDiff_apply ℝ ℝ (0:Fin 3)).contDiffOn,
    ⟨0,by norm_num⟩,?_,?_⟩)
  · intro x _ he
    have hh := congrArg (fun D : Coord3 →L[ℝ] ℝ => D (Pi.single 0 1)) he
    have hd := direction_coord 0 0 x
    change fderiv ℝ (fun y : Coord3 => y 0) x (Pi.single 0 1)=1 at hd
    simp only [he,_root_.zero_apply] at hd
    norm_num at hd
  · intro x _ j
    fin_cases j <;> simp [axialPair]

end ScalarConductivity

end

end OAI
