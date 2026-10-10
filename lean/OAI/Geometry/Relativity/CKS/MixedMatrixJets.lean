import OAI.Geometry.Relativity.CKS.MatrixThreeJets
import OAI.Geometry.Relativity.CKS.MixedThreeJets

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma component_diff {n : ℕ∞ω} {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ n q x) (i k : A) : ContDiffAt ℝ n (fun y => q y i k) x :=
  contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k
lemma component_three {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (i k : A) : ContDiffAt ℝ 3 (fun y => q y i k) x :=
  component_diff hq i k

abbrev MatrixScalarJet := Matrix A A ScalarJet

def matrixScalarJets (q : Point → Mat) (x : Point) : MatrixScalarJet :=
  fun i k => actualScalarJet (fun y => q y i k) x

def determinantJet (q : MatrixScalarJet) : ScalarJet :=
  productJet (q 0 0) (q 1 1)-productJet (q 0 1) (q 1 0)

def inverseMatrixJet (q : MatrixScalarJet) (i k : A) : ScalarJet :=
  productJet ((!![q 1 1, -q 0 1; -q 1 0, q 0 0] : MatrixScalarJet) i k)
    (reciprocalJet (determinantJet q))

lemma actual_determinantJet {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x) :
    actualScalarJet (fun y => determinant (q y)) x = determinantJet (matrixScalarJets q x) := by
  unfold determinant determinantJet matrixScalarJets
  rw [actualScalarJet_sub ((component_diff hq 0 0).mul (component_diff hq 1 1))
    ((component_diff hq 0 1).mul (component_diff hq 1 0)),
    actualScalarJet_mul (component_diff hq 0 0) (component_diff hq 1 1),
    actualScalarJet_mul (component_diff hq 0 1) (component_diff hq 1 0)]

lemma actual_inverseMatrixJet {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 2 q x)
    (h0 : determinant (q x) ≠ 0) (i k : A) :
    actualScalarJet (fun y => inverse (q y) i k) x = inverseMatrixJet (matrixScalarJets q x) i k := by
  have hd : ContDiffAt ℝ 2 (fun y => determinant (q y)) x :=
    (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq
  have hg : ContDiffAt ℝ 2 (fun y => 1/determinant (q y)) x := contDiffAt_const.div hd h0
  have hi (a b : A) := component_diff hq a b
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
    (h0 : determinant (fun i k => (q i k).1) ≠ 0) (i k : A) :
    ContDiffAt ℝ ∞ (fun p : MatrixScalarJet => inverseMatrixJet p i k) q := by
  have hc : ContDiffAt ℝ ∞ (fun p : MatrixScalarJet =>
      (!![p 1 1, -p 0 1; -p 1 0, p 0 0] : MatrixScalarJet) i k) q := by
    fin_cases i <;> fin_cases k <;> dsimp <;> fun_prop
  exact productJet_smooth.contDiffAt.comp q
    (hc.prodMk ((reciprocalJet_smooth h0).comp q determinantJet_smooth.contDiffAt))

abbrev MatrixThreeJet := Matrix A A ScalarThreeJet

def matrixThreeJets (q : Point → Mat) (x : Point) : MatrixThreeJet :=
  fun i k => actualThreeJet (fun y => q y i k) x

def determinantThreeJet (q : MatrixThreeJet) : ScalarThreeJet :=
  productThreeJet (q 0 0) (q 1 1)-productThreeJet (q 0 1) (q 1 0)

def inverseMatrixThreeJet (q : MatrixThreeJet) (i k : A) : ScalarThreeJet :=
  productThreeJet ((!![q 1 1, -q 0 1; -q 1 0, q 0 0] : MatrixThreeJet) i k)
    (reciprocalThreeJet (determinantThreeJet q))

lemma actualThreeJet_sum {α : Type*} (s : Finset α) {f : α → Point → ℝ} {x : Point}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 3 (f i) x) :
    actualThreeJet (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, actualThreeJet (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change actualThreeJet (fun _ => 0) x = constantThreeJet 0
    exact actualThreeJet_const 0 x
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [actualThreeJet_add (hf a (Finset.mem_insert_self _ _))
      (ContDiffAt.sum (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma actual_determinantThreeJet {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 3 q x) :
    actualThreeJet (fun y => determinant (q y)) x = determinantThreeJet (matrixThreeJets q x) := by
  unfold determinant determinantThreeJet matrixThreeJets
  rw [actualThreeJet_sub ((component_three hq 0 0).mul (component_three hq 1 1))
    ((component_three hq 0 1).mul (component_three hq 1 0)),
    actualThreeJet_mul (component_three hq 0 0) (component_three hq 1 1),
    actualThreeJet_mul (component_three hq 0 1) (component_three hq 1 0)]

lemma actual_inverseMatrixThreeJet {q : Point → Mat} {x : Point} (hq : ContDiffAt ℝ 3 q x)
    (h0 : determinant (q x) ≠ 0) (i k : A) :
    actualThreeJet (fun y => inverse (q y) i k) x = inverseMatrixThreeJet (matrixThreeJets q x) i k := by
  have hd : ContDiffAt ℝ 3 (fun y => determinant (q y)) x :=
    (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffAt.comp x hq
  have hg : ContDiffAt ℝ 3 (fun y => 1/determinant (q y)) x := contDiffAt_const.div hd h0
  have hi (a b : A) := component_three hq a b
  have hh : (fun y => inverse (q y) i k) =
      (fun y => (!![q y 1 1, -q y 0 1; -q y 1 0, q y 0 0] : Mat) i k * (1/determinant (q y))) := by
    funext y
    simp [inverse,div_eq_mul_inv]
  rw [hh]
  have hc : ContDiffAt ℝ 3 (fun y => (!![q y 1 1, -q y 0 1; -q y 1 0, q y 0 0] : Mat) i k) x := by
    fin_cases i <;> fin_cases k <;> dsimp <;> first | exact hi _ _ | exact (hi _ _).neg
  rw [actualThreeJet_mul hc hg,actualThreeJet_reciprocal hd h0,actual_determinantThreeJet hq]
  unfold inverseMatrixThreeJet
  congr 1
  fin_cases i <;> fin_cases k <;> dsimp [matrixThreeJets] <;>
    first | rfl | exact actualThreeJet_neg (hi _ _)

lemma determinantThreeJet_value (q : MatrixThreeJet) :
    (determinantThreeJet q).1.1 = determinant (fun i k => (q i k).1.1) := rfl

lemma determinantThreeJet_smooth : ContDiff ℝ ∞ determinantThreeJet := by
  unfold determinantThreeJet
  exact (productThreeJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun q : MatrixThreeJet => (q 0 0,q 1 1)))).sub
    (productThreeJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun q : MatrixThreeJet => (q 0 1,q 1 0))))

lemma inverseMatrixThreeJet_smooth {q : MatrixThreeJet}
    (h0 : determinant (fun i k => (q i k).1.1) ≠ 0) (i k : A) :
    ContDiffAt ℝ ∞ (fun p : MatrixThreeJet => inverseMatrixThreeJet p i k) q := by
  have hc : ContDiffAt ℝ ∞ (fun p : MatrixThreeJet =>
      (!![p 1 1, -p 0 1; -p 1 0, p 0 0] : MatrixThreeJet) i k) q := by
    fin_cases i <;> fin_cases k <;> dsimp <;> fun_prop
  exact productThreeJet_smooth.contDiffAt.comp q
    (hc.prodMk ((reciprocalThreeJet_smooth h0).comp q determinantThreeJet_smooth.contDiffAt))

end
end CKSMixedGeometry

end

end OAI
