import OAI.Geometry.Relativity.CKS.CKSMetricInput
import OAI.Geometry.Relativity.CKS.MixedMassCoefficient

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma matrixThreeJets_smul (c : ℝ) {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) :
    matrixThreeJets (fun y => c • q y) x = c • matrixThreeJets q x := by
  funext i k
  exact actualThreeJet_smul c (component_three hq i k)
lemma matrixThreeJets_add {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hp : ContDiffAt ℝ 3 p x) :
    matrixThreeJets (fun y => q y+p y) x = matrixThreeJets q x+matrixThreeJets p x := by
  funext i k
  exact actualThreeJet_add (component_three hq i k) (component_three hp i k)
lemma matrixThreeJets_mul {f : Point → ℝ} {q : Point → Mat} {x : Point}
    (hf : ContDiffAt ℝ 3 f x) (hq : ContDiffAt ℝ 3 q x) :
    matrixThreeJets (fun y => f y • q y) x = mulMatrixThreeJet (actualThreeJet f x) (matrixThreeJets q x) := by
  funext i k
  exact actualThreeJet_mul hf (component_three hq i k)
lemma matrixScalarJets_smul (c : ℝ) {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) :
    matrixScalarJets (fun y => c • q y) x = c • matrixScalarJets q x := by
  funext i k
  exact actualScalarJet_smul c (component_diff hq i k)
lemma matrixScalarJets_add {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    matrixScalarJets (fun y => q y+p y) x = matrixScalarJets q x+matrixScalarJets p x := by
  funext i k
  exact actualScalarJet_add (component_diff hq i k) (component_diff hp i k)
lemma matrixScalarJets_sub {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    matrixScalarJets (fun y => q y-p y) x = matrixScalarJets q x-matrixScalarJets p x := by
  funext i k
  exact actualScalarJet_sub (component_diff hq i k) (component_diff hp i k)
lemma matrixScalarJets_mul {f : Point → ℝ} {q : Point → Mat} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (hq : ContDiffAt ℝ 2 q x) :
    matrixScalarJets (fun y => f y • q y) x = mulMatrixJet (actualScalarJet f x) (matrixScalarJets q x) := by
  funext i k
  exact actualScalarJet_mul hf (component_diff hq i k)

def normalizedLie (q : Point → Mat) (S : Point → A → ℝ) (x : Point) (i k : A) : ℝ := ∑ a,
  (S x a*D (basis a.succ) (fun y => q y i k) x+
    q x a k*D (basis i.succ) (fun y => S y a) x+q x i a*D (basis k.succ) (fun y => S y a) x)

lemma normalizedLie_diff {q : Point → Mat} {S : Point → A → ℝ} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x) (i k : A) :
    ContDiffAt ℝ 2 (fun y => normalizedLie q S y i k) x := by
  have hSa (a : A) := contDiffAt_pi.mp hS a
  have hqa := component_three hq
  have h23 : (2:ℕ∞ω) ≤ 3 := by norm_num
  apply ContDiffAt.sum
  intro a ha
  exact ((((hSa a).of_le h23).mul (contDiffAt_D (hqa i k) (by norm_num) (basis a.succ))).add
      (((hqa a k).of_le h23).mul (contDiffAt_D (hSa a) (by norm_num) (basis i.succ)))).add
      (((hqa i a).of_le h23).mul (contDiffAt_D (hSa a) (by norm_num) (basis k.succ)))

lemma actual_normalizedLieJet {q : Point → Mat} {S : Point → A → ℝ} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hS : ContDiffAt ℝ 3 S x) (i k : A) :
    actualScalarJet (fun y => normalizedLie q S y i k) x =
      lieJet (matrixThreeJets q x) (fun a => actualThreeJet (fun y => S y a) x) i k := by
  have hSa (a : A) := contDiffAt_pi.mp hS a
  have hqa := component_three hq
  have h23 : (2:ℕ∞ω) ≤ 3 := by norm_num
  have hdS (a b : A) : ContDiffAt ℝ 2 (D (basis a.succ) (fun y => S y b)) x :=
    contDiffAt_D (hSa b) (by norm_num) (basis a.succ)
  have hdq (a i k : A) : ContDiffAt ℝ 2 (D (basis a.succ) (fun y => q y i k)) x :=
    contDiffAt_D (hqa i k) (by norm_num) (basis a.succ)
  have hterm (a : A) : ContDiffAt ℝ 2 (fun y =>
      S y a*D (basis a.succ) (fun z => q z i k) y+
      q y a k*D (basis i.succ) (fun z => S z a) y+q y i a*D (basis k.succ) (fun z => S z a) y) x :=
    ((((hSa a).of_le h23).mul (hdq a i k)).add
      (((hqa a k).of_le h23).mul (hdS i a))).add
      (((hqa i a).of_le h23).mul (hdS k a))
  unfold normalizedLie lieJet
  rw [actualScalarJet_sum _ (fun a _ => hterm a)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [actualScalarJet_add ((((hSa a).of_le h23).mul (hdq a i k)).add
      (((hqa a k).of_le h23).mul (hdS i a))) (((hqa i a).of_le h23).mul (hdS k a)),
    actualScalarJet_add (((hSa a).of_le h23).mul (hdq a i k)) (((hqa a k).of_le h23).mul (hdS i a)),
    actualScalarJet_mul ((hSa a).of_le h23) (hdq a i k),
    actualScalarJet_mul ((hqa a k).of_le h23) (hdS i a),
    actualScalarJet_mul ((hqa i a).of_le h23) (hdS k a)]
  rfl

end
end CKSMixedGeometry

end

end OAI
