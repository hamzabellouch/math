import OAI.Geometry.Relativity.CKS.AngularWeighted
import OAI.Geometry.Relativity.CKS.CollarExpansionJet

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def physicalExpansion (r : ℝ) (γ γr : Point → Mat) (s : Point → Point) (x : Point) : ℝ :=
  (r/4)*∑ i, ∑ k, inverse (γ x) i k*(γr x k i-normalizedLie γ s x k i)

lemma inverse_trace (q : Mat) (hq : determinant q ≠ 0) :
    (∑ i, ∑ k, inverse q i k * q k i) = 2 := by
  simp only [Fin.sum_univ_two,inverse]
  field_simp
  dsimp [determinant] at *
  ring

lemma lie_normalization (r : ℝ) (hr : r ≠ 0) {q : Point → Mat} {S : Point → Point} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x) (i k : I) :
    normalizedLie (fun y => r^2 • q y) (fun y => (1/r) • S y) x i k =
      r*normalizedLie q S x i k := by
  have hqa (i k : I) := (component_three hq i k).differentiableAt (by norm_num)
  have hSa (a : I) := (contDiffAt_pi.mp hS a).differentiableAt (by norm_num)
  unfold normalizedLie
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  change (1/r*S x a)*D (basis a) (fun y => r^2*q y i k) x+
    (r^2*q x a k)*D (basis i) (fun y => (1/r)*S y a) x+
    (r^2*q x i a)*D (basis k) (fun y => (1/r)*S y a) x = _
  rw [D_const_mul _ (r^2) (hqa i k),D_const_mul _ (1/r) (hSa a),D_const_mul _ (1/r) (hSa a)]
  field_simp

theorem physicalExpansion_normalized (r : ℝ) (hr : r ≠ 0)
    {q Q : Point → Mat} {S : Point → Point} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x)
    (h0 : determinant (q x) ≠ 0) :
    physicalExpansion r (fun y => r^2 • q y) (fun y => (2*r) • q y+r • Q y)
      (fun y => (1/r) • S y) x = normalizedExpansion q Q S x := by
  have hi (i k : I) : inverse (r^2 • q x) i k = inverse (q x) i k/r^2 :=
    inverse_rescale (r^2) (q x,0,0) (pow_ne_zero _ hr) i k
  have hterm (i k : I) :
      (r/4)*(inverse (r^2 • q x) i k *
        (((2*r) • q x+r • Q x) k i-normalizedLie (fun y => r^2 • q y)
          (fun y => (1/r) • S y) x k i)) =
      (1/2:ℝ)*(inverse (q x) i k*q x k i)+
        (1/4:ℝ)*(inverse (q x) i k*(Q x k i-normalizedLie q S x k i)) := by
    rw [hi,lie_normalization r hr hq hS]
    dsimp
    field_simp
    ring
  unfold physicalExpansion
  simp only [Finset.mul_sum]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  rw [inverse_trace _ h0]
  unfold normalizedExpansion
  ring

theorem radial_metric_deriv {q : ℝ → ℝ} {r : ℝ} (hq : DifferentiableAt ℝ q r) :
    deriv (fun ρ => ρ^2*q ρ) r = 2*r*q r+r*(r*deriv q r) := by
  have hh := ((hasDerivAt_id r).pow 2).mul hq.hasDerivAt
  have hd : HasDerivAt (fun ρ => ρ^2*q ρ) (2*r*q r+r*(r*deriv q r)) r := by
    convert! hh using 1
    dsimp
    ring
  exact hd.deriv

end
end CKSAngularGeometry

end

end OAI
