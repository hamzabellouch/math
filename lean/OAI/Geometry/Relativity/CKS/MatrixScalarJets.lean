import OAI.Geometry.Relativity.CKS.ScalarJetCalculus

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev MatrixScalarJet := Matrix I I ScalarJet

def matrixScalarJets (q : Point → Mat) (x : Point) : MatrixScalarJet :=
  fun i k => actualScalarJet (fun y => q y i k) x

def determinantJet (q : MatrixScalarJet) : ScalarJet :=
  productJet (q 0 0) (q 1 1)-productJet (q 0 1) (q 1 0)

def inverseMatrixJet (q : MatrixScalarJet) (i k : I) : ScalarJet :=
  productJet ((!![q 1 1, -q 0 1; -q 1 0, q 0 0] : MatrixScalarJet) i k)
    (reciprocalJet (determinantJet q))

lemma actualScalarJet_neg {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 2 f x) :
    actualScalarJet (fun y => -(f y)) x = -actualScalarJet f x := by
  simpa using actualScalarJet_smul (-1) hf

lemma actualScalarJet_sum {α : Type*} (s : Finset α) {f : α → Point → ℝ} {x : Point}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    actualScalarJet (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, actualScalarJet (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change actualScalarJet (fun _ => 0) x = constantJet 0
    exact actualScalarJet_const 0 x
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [actualScalarJet_add (hf a (Finset.mem_insert_self _ _))
      (ContDiffAt.sum (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma actual_determinantJet {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x) :
    actualScalarJet (fun y => determinant (q y)) x = determinantJet (matrixScalarJets q x) := by
  unfold determinant determinantJet matrixScalarJets
  rw [actualScalarJet_sub ((component_diff hq 0 0).mul (component_diff hq 1 1))
    ((component_diff hq 0 1).mul (component_diff hq 1 0)),
    actualScalarJet_mul (component_diff hq 0 0) (component_diff hq 1 1),
    actualScalarJet_mul (component_diff hq 0 1) (component_diff hq 1 0)]

lemma actual_inverseMatrixJet {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (i k : I) :
    actualScalarJet (fun y => inverse (q y) i k) x = inverseMatrixJet (matrixScalarJets q x) i k := by
  have hd : ContDiffAt ℝ 2 (fun y => determinant (q y)) x :=
    (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq
  have hg : ContDiffAt ℝ 2 (fun y => 1/determinant (q y)) x := contDiffAt_const.div hd h0
  have hi (a b : I) := component_diff hq a b
  have hh : (fun y => inverse (q y) i k) =
      (fun y => (!![q y 1 1, -q y 0 1; -q y 1 0, q y 0 0] : Mat) i k * (1/determinant (q y))) := by
    funext y
    simp [inverse,div_eq_mul_inv]
  rw [hh]
  have hc : ContDiffAt ℝ 2 (fun y => (!![q y 1 1, -q y 0 1; -q y 1 0, q y 0 0] : Mat) i k) x := by
    fin_cases i <;> fin_cases k <;> dsimp <;> first | exact hi _ _ | exact (hi _ _).neg
  rw [actualScalarJet_mul hc hg,actual_reciprocal hd h0,actual_determinantJet hq]
  unfold inverseMatrixJet
  congr 1
  fin_cases i <;> fin_cases k <;> dsimp [matrixScalarJets] <;>
    first | rfl | exact actualScalarJet_neg (hi _ _)

lemma determinantJet_value (q : MatrixScalarJet) :
    (determinantJet q).1 = determinant (fun i k => (q i k).1) := rfl

lemma determinantJet_smooth : ContDiff ℝ ∞ determinantJet := by
  unfold determinantJet
  exact (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun q : MatrixScalarJet => (q 0 0,q 1 1)))).sub
    (productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun q : MatrixScalarJet => (q 0 1,q 1 0))))

lemma inverseMatrixJet_smooth {q : MatrixScalarJet}
    (h0 : determinant (fun i k => (q i k).1) ≠ 0) (i k : I) :
    ContDiffAt ℝ ∞ (fun p : MatrixScalarJet => inverseMatrixJet p i k) q := by
  have hc : ContDiffAt ℝ ∞ (fun p : MatrixScalarJet =>
      (!![p 1 1, -p 0 1; -p 1 0, p 0 0] : MatrixScalarJet) i k) q := by
    fin_cases i <;> fin_cases k <;> dsimp <;> fun_prop
  exact productJet_smooth.contDiffAt.comp q
    (hc.prodMk ((reciprocalJet_smooth h0).comp q determinantJet_smooth.contDiffAt))

end
end CKSAngularGeometry

end

end OAI
