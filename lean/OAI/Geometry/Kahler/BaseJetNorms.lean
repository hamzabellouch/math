import OAI.Geometry.Kahler.BaseScaleSum

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def wirtingerCLM (b : Bool) (i : Fin 2) : (Base →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1/2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i 1)) +
    (if b then Complex.I else -Complex.I) •
      (ContinuousLinearMap.apply ℝ ℂ (Complex.I • EuclideanSpace.single i 1)))

lemma wirtingerCLM_apply (b : Bool) (i : Fin 2) (L : Base →L[ℝ] ℂ) :
    wirtingerCLM b i L = (L (EuclideanSpace.single i 1) +
      (if b then Complex.I else -Complex.I)*L (Complex.I • EuclideanSpace.single i 1))/2 := by
  simp only [wirtingerCLM,smul_apply,add_apply,
    ContinuousLinearMap.apply_apply,smul_eq_mul]
  ring

lemma wirtingerCLM_norm (b : Bool) (i : Fin 2) : ‖wirtingerCLM b i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  rw [wirtingerCLM_apply,norm_div]
  have h1 := L.le_opNorm (EuclideanSpace.single i 1)
  have h2 := L.le_opNorm (Complex.I • EuclideanSpace.single i 1)
  have hn : ‖(if b then Complex.I else -Complex.I)‖=1 := by cases b <;> simp
  have he : ‖(EuclideanSpace.single i 1 : Base)‖=1 := by simp
  simp only [he,norm_smul,Complex.norm_I,mul_one] at h1 h2
  have hh := norm_add_le (L (EuclideanSpace.single i 1))
    ((if b then Complex.I else -Complex.I)*L (Complex.I • EuclideanSpace.single i 1))
  rw [norm_mul,hn,one_mul] at hh
  norm_num only [Complex.norm_ofNat,one_mul]
  linarith

lemma dzBase_asCLM (f : Base → ℂ) (i : Fin 2) :
    (fun z => dzBase f z i)=wirtingerCLM false i ∘ fderiv ℝ f := by
  funext z
  rw [Function.comp_apply,wirtingerCLM_apply]
  simp only [Bool.false_eq_true,ite_false,neg_mul,dzBase,sub_eq_add_neg]

lemma dbarBase_asCLM (f : Base → ℂ) (i : Fin 2) :
    (fun z => dbarBase f z i)=wirtingerCLM true i ∘ fderiv ℝ f := by
  funext z
  rw [Function.comp_apply,wirtingerCLM_apply]
  rfl

lemma norm_jet_dzBase {f : Base → ℂ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (i : Fin 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => dzBase f x i) z‖ ≤ ‖iteratedFDeriv ℝ (n+1) f z‖ := by
  rw [dzBase_asCLM]
  have hd := hf.fderiv_right (m := ∞) (by simp)
  have hh := (wirtingerCLM false i).norm_iteratedFDeriv_comp_left hd
    (show (n:ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  exact hh.trans ((mul_le_mul_of_nonneg_right (wirtingerCLM_norm false i) (norm_nonneg _)).trans_eq (by rw [one_mul,norm_iteratedFDeriv_fderiv]))

lemma norm_jet_dbarBase {f : Base → ℂ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (i : Fin 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => dbarBase f x i) z‖ ≤ ‖iteratedFDeriv ℝ (n+1) f z‖ := by
  rw [dbarBase_asCLM]
  have hd := hf.fderiv_right (m := ∞) (by simp)
  have hh := (wirtingerCLM true i).norm_iteratedFDeriv_comp_left hd
    (show (n:ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  exact hh.trans ((mul_le_mul_of_nonneg_right (wirtingerCLM_norm true i) (norm_nonneg _)).trans_eq (by rw [one_mul,norm_iteratedFDeriv_fderiv]))

lemma norm_jet_ofReal {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => (f x:ℂ)) z‖ ≤ ‖iteratedFDeriv ℝ n f z‖ := by
  have hh := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hf
    (show (n:ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  simpa [Function.comp_def,Complex.ofRealCLM_norm] using hh

lemma norm_jet_baseHessian {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z)
    (i j : Fin 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => baseHessian f x i j) z‖ ≤ ‖iteratedFDeriv ℝ (n+2) f z‖ := by
  have hfc := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  exact (norm_jet_dzBase (_root_.OAI.ContDiffAt.hartogs_dbarBase hfc (m := ∞) (by simp) j) i n).trans
    ((norm_jet_dbarBase hfc j (n+1)).trans (norm_jet_ofReal hf (n+2)))

lemma norm_baseHessian_le {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z) (i j : Fin 2) :
    ‖baseHessian f z i j‖ ≤ ‖iteratedFDeriv ℝ 2 f z‖ := by
  simpa only [norm_iteratedFDeriv_zero,Nat.zero_add] using norm_jet_baseHessian hf i j 0

lemma norm_baseHessian_derivatives_le {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ ∞ f z)
    (i j k l : Fin 2) :
    ‖dzBase (fun x => baseHessian f x i j) z k‖+
    ‖dbarBase (fun x => baseHessian f x i j) z l‖+
    ‖dzBase (fun x => dbarBase (fun y => baseHessian f y i j) x l) z k‖ ≤
      2*‖iteratedFDeriv ℝ 3 f z‖+‖iteratedFDeriv ℝ 4 f z‖ := by
  have hh : ContDiffAt ℝ ∞ (fun x => baseHessian f x i j) z :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp (baseHessian_contDiffAt hf) i)) j
  have h1 := (norm_jet_dzBase hh k 0).trans (norm_jet_baseHessian hf i j 1)
  have h2 := (norm_jet_dbarBase hh l 0).trans (norm_jet_baseHessian hf i j 1)
  have h3 := (norm_jet_dzBase (_root_.OAI.ContDiffAt.hartogs_dbarBase hh (by simp) l) k 0).trans
    ((norm_jet_dbarBase hh l 1).trans (norm_jet_baseHessian hf i j 2))
  simp only [norm_iteratedFDeriv_zero] at h1 h2 h3
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
