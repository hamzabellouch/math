import OAI.Geometry.Relativity.CKS.AngularDifferentiation

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma D_sum {α : Type*} (u : Finset α) (f : α → Point → ℝ) (e x : Point)
    (hf : ∀ i ∈ u, DifferentiableAt ℝ (f i) x) :
    D e (fun y => ∑ i ∈ u, f i y) x = ∑ i ∈ u, D e (f i) x := by
  simp only [D, fderiv_fun_sum hf, sum_apply]

lemma D_div_const (e : Point) {f : Point → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    D e (fun y => f y/c) x = D e f x/c := by
  simp only [div_eq_mul_inv]
  rw [D_mul e hf (differentiableAt_const _),D_const]
  ring

lemma first_diff {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x) (a i k : I) :
    DifferentiableAt ℝ (D (basis a) (fun y => q y i k)) x :=
  (contDiffAt_D (component_diff hq i k) (m := 1) (by norm_num) (basis a)).differentiableAt (by norm_num)

theorem derivative_connection {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (s a i k : I) :
    D (basis s) (connection q a i k) x = christoffelDerivative (actualJet q x) s a i k := by
  let b (l : I) (y : Point) :=
    D (basis i) (fun z => q z k l) y + D (basis k) (fun z => q z i l) y - D (basis l) (fun z => q z i k) y
  have hb l : DifferentiableAt ℝ (b l) x :=
    ((first_diff hq i k l).fun_add (first_diff hq k i l)).fun_sub (first_diff hq l i k)
  have hterm l : DifferentiableAt ℝ (fun y => inverse (q y) a l * b l y) x :=
    (inverse_component_diff hq h0 a l).fun_mul (hb l)
  have hsum : DifferentiableAt ℝ (fun y => ∑ l : I, inverse (q y) a l*b l y) x :=
    DifferentiableAt.fun_sum fun l hl => hterm l
  change D (basis s) (fun y => (∑ l : I, inverse (q y) a l*b l y)/2) x = _
  rw [D_div_const _ hsum]
  have hdsum := D_sum Finset.univ (fun l y => inverse (q y) a l*b l y) (basis s) x (fun l hl => hterm l)
  rw [hdsum]
  unfold christoffelDerivative
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [D_mul _ (inverse_component_diff hq h0 a l) (hb l), derivative_inverse hq h0]
  have hdb : D (basis s) (b l) x =
      D (basis s) (D (basis i) (fun y => q y k l)) x +
      D (basis s) (D (basis k) (fun y => q y i l)) x -
      D (basis s) (D (basis l) (fun y => q y i k)) x := by
    dsimp [b]
    rw [D_sub _ ((first_diff hq i k l).fun_add (first_diff hq k i l)) (first_diff hq l i k),
      D_add _ (first_diff hq i k l) (first_diff hq k i l)]
  rw [hdb]
  dsimp [actualJet,b]
  ring

theorem physicalScalar_eq {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) : physicalScalar q x = scalarCurvature (actualJet q x) := by
  simp only [physicalScalar,curvatureRicci,derivative_connection hq h0,connection,
    scalarCurvature,ricci,actualJet]

def reciprocalJet (z : ScalarJet) : ScalarJet :=
  (1/z.1, (fun a => -z.2.1 a/z.1^2), fun a b =>
    2*z.2.1 a*z.2.1 b/z.1^3-z.2.2 a b/z.1^2)

lemma actual_reciprocal {z : Point → ℝ} {x : Point} (hz : ContDiffAt ℝ 2 z x) (h0 : z x ≠ 0) :
    actualScalarJet (fun y => 1/z y) x = reciprocalJet (actualScalarJet z x) := by
  dsimp only [actualScalarJet, reciprocalJet]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext a
    exact D_inv_inv (basis a) (hz.differentiableAt (by norm_num)) h0
  · ext a b
    dsimp [actualScalarJet,reciprocalJet]
    rw [D_D_inv (basis b) (basis a) hz h0]
    ring

lemma lapseLaplacian_eq (j : Jet) (z : ScalarJet) (h0 : z.1 ≠ 0) :
    lapseLaplacian j z = z.1*laplace j (reciprocalJet z) := by
  unfold lapseLaplacian laplace
  simp only [Finset.mul_sum,reciprocalJet]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  have hs : (∑ a, christoffel j a i k * (-z.2.1 a / z.1^2)) =
      -(∑ a, christoffel j a i k * z.2.1 a)/z.1^2 := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hs]
  field_simp [h0]
  ring

theorem actual_lapseLaplacian {z : Point → ℝ} {x : Point} (hz : ContDiffAt ℝ 2 z x)
    (h0 : z x ≠ 0) (j : Jet) :
    lapseLaplacian j (actualScalarJet z x) =
      z x * laplace j (actualScalarJet (fun y => 1/z y) x) := by
  rw [actual_reciprocal hz h0]
  exact lapseLaplacian_eq j (actualScalarJet z x) h0

end
end CKSAngularGeometry

end

end OAI
