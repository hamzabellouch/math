import OAI.Probability.DilutedSpin.ShiftedTree

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] {N : ℕ}

/-- Pairwise projection retains both sampled vectors and their correlation
with any later old test. Only the separate sides are independent. -/
theorem pairProjectionSq_le_of_contractions (P : FiniteLaw Ω) (X Y : Ω → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) (hY : ∀ x i, |Y x i|≤1) (A : ℝ)
    (hA : ∀ B : Fin N → ℝ, (∀ i, |B i|≤1) →
      P.expect (fun x => (dot (fun i => X x i-Y x i) B)^2) ≤ A) :
    pairProjectionSq P X Y ≤ 4*A := by
  let F := fun x y => dot (fun i => X y i-Y y i) (X x)
  let G := fun x y => dot (fun i => X x i-Y x i) (Y y)
  have he (x y : Ω) : dot (X x) (X y)-dot (Y x) (Y y)=F x y+G x y := by
    simp only [F,G,dot,← sub_div,← add_div,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hF : P.expect (fun x => P.expect (fun y => (F x y)^2)) ≤ A :=
    (P.expect_mono (fun x => hA (X x) (hX x))).trans_eq (P.expect_const _)
  have hG : P.expect (fun x => P.expect (fun y => (G x y)^2)) ≤ A := by
    rw [expect_comm]
    exact (P.expect_mono (fun y => hA (Y y) (hY y))).trans_eq (P.expect_const _)
  have hh := P.expect_mono (fun x => P.expect_mono (fun y =>
    show (dot (X x) (X y)-dot (Y x) (Y y))^2 ≤ 2*(F x y)^2+2*(G x y)^2 from by
      rw [he]
      nlinarith [sq_nonneg (F x y-G x y)]))
  simp only [expect_add,expect_mul_left] at hh
  exact hh.trans (by linarith)

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N n : ℕ}

/-- The complete two-sided projection at a prescribed later first split.
Both products and both projected means use the same original sampled paths.
The right side contains genuine proper-child covariance energies only. -/
theorem stem_node_two_side_projection_sq (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r : ℕ)
    (T : KernelTower Ω (n+1+r)) (f : FinitePath Ω (n+1+r) → Fin N → ℝ)
    (hf : ∀ x i, |f x i|≤1) :
    let S := PrescribedTree.node k C
    let P := (stem S r).sampleLaw T
    let X := fun z i => leafProduct (stem S r) (fun x => f x i) z
    let Y := fun z i => tailMean S r T (fun x => f x i) ((stem S r).pathAt (stemLeaf S r a) z)
    P.pairProjectionSq X Y ≤ 4*(k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) r T f) := by
  dsimp only
  rw [mul_assoc]
  apply FiniteLaw.pairProjectionSq_le_of_contractions
  · exact fun z i => leafProduct_bound _ (fun x => hf x i) z
  · exact fun z i => tailMean_bound _ _ _ _ (fun x => hf x i) _
  · exact fun B hB => stem_node_contraction_sq_le k C a r T f hf B hB

/-- Same error in L2, allowing arbitrary bounded correlated old scalar tests
by Cauchy--Schwarz in the subsequent shifted-matrix identity. -/
theorem stem_node_two_side_projection_l2 (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r : ℕ)
    (T : KernelTower Ω (n+1+r)) (f : FinitePath Ω (n+1+r) → Fin N → ℝ)
    (hf : ∀ x i, |f x i|≤1) :
    let S := PrescribedTree.node k C
    let P := (stem S r).sampleLaw T
    let X := fun z i => leafProduct (stem S r) (fun x => f x i) z
    let Y := fun z i => tailMean S r T (fun x => f x i) ((stem S r).pathAt (stemLeaf S r a) z)
    (P.bind (fun _ => P)).l2 (fun z => FiniteLaw.dot (X z.1) (X z.2)-
      FiniteLaw.dot (Y z.1) (Y z.2)) ≤
        2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) r T f)) := by
  dsimp only
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [FiniteLaw.expect_bind]
    have h := stem_node_two_side_projection_sq k C a r T f hf
    have hn : 0 ≤ (k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) r T f) := by positivity
    simpa only [FiniteLaw.pairProjectionSq,mul_pow,Real.sq_sqrt hn,show (2:ℝ)^2=4 by norm_num,mul_assoc] using h

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
