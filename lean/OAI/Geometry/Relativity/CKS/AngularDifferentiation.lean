import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.AngularGeometry
import OAI.Geometry.Relativity.CKS.SmoothOuterDEC

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
def actualJet (q : Point → Mat) (x : Point) : Jet :=
  (q x, (fun a i k => D (basis a) (fun y => q y i k) x),
    fun a b i k => D (basis a) (D (basis b) (fun y => q y i k)) x)

def actualScalarJet (z : Point → ℝ) (x : Point) : ScalarJet :=
  (z x, (fun a => D (basis a) z x), fun a b => D (basis a) (D (basis b) z) x)

lemma component_diff {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x) (i k : I) :
    ContDiffAt ℝ 2 (fun y => q y i k) x := by
  exact contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k

lemma inverse_component_diff {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (i k : I) :
    DifferentiableAt ℝ (fun y => inverse (q y) i k) x := by
  unfold inverse
  apply CKSCalculus.diffAt_div
  · fin_cases i <;> fin_cases k <;> dsimp <;>
      first | exact (component_diff hq _ _).differentiableAt (by norm_num)
            | exact ((component_diff hq _ _).differentiableAt (by norm_num)).neg
  · exact ((determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq).differentiableAt (by norm_num)
  · exact h0

lemma D_determinant {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x) (e : Point) :
    D e (fun y => determinant (q y)) x =
      q x 0 0 * D e (fun y => q y 1 1) x + q x 1 1 * D e (fun y => q y 0 0) x -
      (q x 0 1 * D e (fun y => q y 1 0) x + q x 1 0 * D e (fun y => q y 0 1) x) := by
  have hd i k := (component_diff hq i k).differentiableAt (by norm_num)
  unfold determinant
  rw [D_sub e ((hd 0 0).fun_mul (hd 1 1)) ((hd 0 1).fun_mul (hd 1 0)),
    D_mul e (hd 0 0) (hd 1 1), D_mul e (hd 0 1) (hd 1 0)]

theorem derivative_inverse {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (s a b : I) :
    D (basis s) (fun y => inverse (q y) a b) x =
      inverseDerivative (actualJet q x) s a b := by
  have hd i k := (component_diff hq i k).differentiableAt (by norm_num)
  have hdet : DifferentiableAt ℝ (fun y => determinant (q y)) x :=
    ((determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq).differentiableAt (by norm_num)
  have hdneg i k : D (basis s) (fun y => -(q y i k)) x =
      - D (basis s) (fun y => q y i k) x := by
    unfold D
    rw [fderiv_fun_neg]
    rfl
  unfold inverseDerivative
  simp only [actualJet, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> dsimp [inverse] <;>
    rw [D_div _ (by first | exact hd _ _ | exact (hd _ _).neg) hdet h0, D_determinant hq] <;>
    (try rw [hdneg]) <;> dsimp [inverse,determinant] <;> field_simp <;> ring

def connection (q : Point → Mat) (a i k : I) (x : Point) : ℝ := christoffel (actualJet q x) a i k

def curvatureRicci (q : Point → Mat) (x : Point) (i k : I) : ℝ :=
  (∑ a, (D (basis a) (connection q a i k) x - D (basis k) (connection q a i a) x)) +
  ∑ a, ∑ b, (connection q a a b x * connection q b i k x -
    connection q a k b x * connection q b i a x)

def physicalScalar (q : Point → Mat) (x : Point) : ℝ :=
  ∑ i, ∑ k, inverse (q x) i k * curvatureRicci q x i k

end
end CKSAngularGeometry

end

end OAI
