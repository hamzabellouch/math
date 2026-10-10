import Mathlib
import OAI.Geometry.PrescribedRicci.CalabiTensorAlgebra
import OAI.Geometry.PrescribedRicci.CalabiTensorMetric
import OAI.Geometry.PrescribedRicci.ChernBianchi
import OAI.Geometry.PrescribedRicci.ChernPairDifferential
import OAI.Geometry.PrescribedRicci.ChernRough
import OAI.Geometry.PrescribedRicci.KahlerGradientEnergy
import OAI.Geometry.PrescribedRicci.MatrixWirtinger
import OAI.Geometry.PrescribedRicci.MatrixWirtingerExtra

namespace OAI

/-! Calabi Rough. -/

section

 

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ
local notation "TI" => TensorIndex (Fin d)

lemma holDeriv_neg (f : Coordinates d → ℂ) (z : Coordinates d) (a : Fin d) :
    holDeriv (fun y => -f y) z a = -holDeriv f z a := by
  unfold holDeriv
  rw [fderiv_fun_neg]
  simp only [_root_.neg_apply]
  ring

lemma barDeriv_neg (f : Coordinates d → ℂ) (z : Coordinates d) (a : Fin d) :
    barDeriv (fun y => -f y) z a = -barDeriv f z a := by
  unfold barDeriv
  rw [fderiv_fun_neg]
  simp only [_root_.neg_apply]
  ring

lemma calabiTensor_bar (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (b : Fin d) (i : TI) :
    barVector (g.calabiTensor q) z b i = -g.chernCurvature q z b i.1 i.2.1 i.2.2 := by
  change barDeriv (fun y => g.chernConnection q y i.1 i.2.1 i.2.2) z b = _
  rw [barDeriv_entry ((g.chernConnection_smooth q hz i.1).differentiableAt (by simp)),
    g.chernConnection_bar q hz]
  rfl

lemma calabiTensor_covHol_bar (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (u b a k j : Fin d) :
    covHol (g.calabiConnection q) (fun y => barVector (g.calabiTensor q) y b) z u (a,k,j) =
      -(holDerivative (fun y => g.chernCurvature q y b a) z u+
        g.chernConnection q z u*g.chernCurvature q z b a-
        g.chernCurvature q z b a*g.chernConnection q z u-
        ∑ v, g.chernConnection q z u v a • g.chernCurvature q z b v) k j := by
  have he : (fun y => barVector (g.calabiTensor q) y b (a,k,j)) =ᶠ[nhds z]
      (fun y => -g.chernCurvature q y b a k j) := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    exact g.calabiTensor_bar q hy b (a,k,j)
  change holDeriv (fun y => barVector (g.calabiTensor q) y b (a,k,j)) z u+
    (tensorConnection (g.chernConnection q z u)*ᵥ barVector (g.calabiTensor q) z b) (a,k,j) = _
  rw [holDeriv_congr he,holDeriv_neg,
    holDeriv_entry ((g.chernCurvature_smooth q hz b a).differentiableAt (by simp)),
    tensorConnection_mulVec]
  simp_rw [g.calabiTensor_bar q hz]
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul,mul_neg,Finset.sum_neg_distrib]
  simp only [mul_comm]
  ring

lemma calabiTensor_rough (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    ∑ u, ∑ b, ((g.matrix q z)⁻¹ u b) •
      covHol (g.calabiConnection q) (fun y => barVector (g.calabiTensor q) y b) z u =
      fun i : TI => (-(g.matrix q z)⁻¹*holDerivative (g.curvatureRicci q) z i.1+
        ((g.matrix q z)⁻¹*g.curvatureRicci q z)*g.chernConnection q z i.1) i.2.1 i.2.2 := by
  funext ⟨a,k,j⟩
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [g.calabiTensor_covHol_bar q hz]
  have he := congrArg (fun M : Mat => -(M k j)) (g.chernCurvature_rough q hz a)
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.sub_apply,Matrix.add_apply,
    Matrix.neg_apply,neg_mul,smul_eq_mul,mul_neg,Finset.sum_neg_distrib] at he ⊢
  convert he using 1
  ring

lemma barDeriv_mul_const {f : Coordinates d → ℂ} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (c : ℂ) (b : Fin d) :
    barDeriv (fun y => f y*c) z b = barDeriv f z b*c := by
  rw [barDeriv_mul hf (differentiableAt_const c)]
  simp [barDeriv]

lemma barDeriv_const_mul {f : Coordinates d → ℂ} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (c : ℂ) (b : Fin d) :
    barDeriv (fun y => c*f y) z b = c*barDeriv f z b := by
  rw [barDeriv_mul (differentiableAt_const c) hf]
  simp [barDeriv]

lemma barArray_tensorConnection {G : Coordinates d → Mat} {z : Coordinates d}
    (hG : DifferentiableAt ℝ G z) (b : Fin d) :
    barArray (fun y => tensorConnection (G y)) z b = tensorConnection (barDerivative G z b) := by
  have hg (i j : Fin d) := differentiableAt_pi.mp (differentiableAt_pi.mp hG i) j
  have hconst (c : ℂ) : DifferentiableAt ℝ (fun _ : Coordinates d => c) z :=
    differentiableAt_const c
  ext i j
  let f1 : Coordinates d → ℂ := fun y => -G y j.1 i.1*((1:Mat) i.2.1 j.2.1*(1:Mat) i.2.2 j.2.2)
  let f2 : Coordinates d → ℂ := fun y => (1:Mat) i.1 j.1*(G y i.2.1 j.2.1*(1:Mat) i.2.2 j.2.2)
  let f3 : Coordinates d → ℂ := fun y => (1:Mat) i.1 j.1*((1:Mat) i.2.1 j.2.1*(-G y j.2.2 i.2.2))
  have h1 : DifferentiableAt ℝ f1 z := (hg _ _).neg.fun_mul (hconst _)
  have h2 : DifferentiableAt ℝ f2 z := (hconst _).fun_mul ((hg _ _).fun_mul (hconst _))
  have h3 : DifferentiableAt ℝ f3 z := (hconst _).fun_mul ((hconst _).fun_mul (hg _ _).neg)
  have h12 : DifferentiableAt ℝ (fun y => f1 y+f2 y) z := h1.fun_add h2
  change barDeriv (fun y => f1 y+f2 y+f3 y) z b = _
  rw [barDeriv_add h12 h3,barDeriv_add h1 h2]
  dsimp only [f1,f2,f3]
  rw [barDeriv_mul_const (f := fun y => -G y j.1 i.1) (hg _ _).neg,
    barDeriv_const_mul (f := fun y => G y i.2.1 j.2.1*(1:Mat) i.2.2 j.2.2)
      ((hg _ _).fun_mul (hconst _)),
    barDeriv_mul_const (f := fun y => G y i.2.1 j.2.1) (hg _ _),
    barDeriv_const_mul (f := fun y => (1:Mat) i.2.1 j.2.1*(-G y j.2.2 i.2.2))
      ((hconst _).fun_mul (hg _ _).neg),
    barDeriv_const_mul (f := fun y => -G y j.2.2 i.2.2) (hg _ _).neg]
  simp only [barDeriv_neg,barDeriv_entry hG,Matrix.add_apply,tensorConnection,tensor3_apply,
    Matrix.transpose_apply,Matrix.neg_apply]

lemma tensorConnection_sum_smul {ι : Type*} [Fintype ι] (c : ι → ℂ) (M : ι → Mat) :
    tensorConnection (∑ i, c i • M i) = ∑ i, c i • tensorConnection (M i) := by
  ext a b
  simp only [tensorConnection,tensor3_apply,Matrix.transpose_apply,Matrix.neg_apply,
    Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Finset.mul_sum,Finset.sum_mul,mul_add,neg_mul,mul_neg,
    ← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma calabiConnection_contracted_curvature (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    ∑ a, ∑ b, ((g.matrix q z)⁻¹ a b) •
      barArray (fun y => g.calabiConnection q y a) z b =
        tensorConnection (-((g.matrix q z)⁻¹*g.curvatureRicci q z)) := by
  have hb (a b : Fin d) : barArray (fun y => g.calabiConnection q y a) z b =
      tensorConnection (-g.chernCurvature q z b a) := by
    exact (barArray_tensorConnection
      ((g.chernConnection_smooth q hz a).differentiableAt (by simp)) b).trans
        (congrArg tensorConnection (g.chernConnection_bar q hz a b))
  simp_rw [hb]
  have hs := tensorConnection_sum_smul
    (fun ab : Fin d × Fin d => (g.matrix q z)⁻¹ ab.1 ab.2)
    (fun ab : Fin d × Fin d => -g.chernCurvature q z ab.2 ab.1)
  simp only [Fintype.sum_prod_type] at hs
  rw [← hs]
  congr 1
  simp only [smul_neg,Finset.sum_neg_distrib,
    g.chernCurvature_contraction q hz]

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
