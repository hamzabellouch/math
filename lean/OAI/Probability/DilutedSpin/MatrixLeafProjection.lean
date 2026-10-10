import OAI.Probability.DilutedSpin.ShapeMatrix
import OAI.Probability.DilutedSpin.StemCovarianceTransfer

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

omit [Fintype Ω] [DecidableEq I] in
/-- The physical color-indexed spatial product is exactly the product of
all actual target leaves whenever colors enumerate those leaves bijectively. -/
lemma spatialProduct_leafProduct (S : PrescribedTree n) (q : I → S.Leaf)
    (hq : Function.Bijective q) (f : FinitePath Ω n → Fin N → ℝ) (z : Sample Ω S) :
    spatialProduct (fun _ : I => f) (fun c => S.pathAt (q c) z) =
      (∑ i, leafProduct S (fun x => f x i) z)/(N:ℝ) := by
  unfold spatialProduct
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [leafProduct_eq_prod]
  exact Fintype.prod_bijective q hq _ _ (fun _ => rfl)

omit [Fintype Ω] in
lemma doubledOverlap_bound (S : PrescribedTree n) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (hf : ∀ x i, |f x i|≤1) (z : Sample Ω (doubled S)) : |doubledOverlap S f z|≤1 :=
  FiniteLaw.abs_dot_le_one _ _
    (fun i => leafProduct_bound S (fun x => hf ((z 0).1,x) i) (z 0).2)
    (fun i => leafProduct_bound S (fun x => hf ((z 1).1,x) i) (z 1).2)

omit [DecidableEq I] in
/-- Literal target error in the matrix identity, retaining the exact color
positions and full all-leaf target overlap. -/
lemma matrixProjectionError_doubled (S : PrescribedTree n) (q : I → (doubled S).Leaf)
    (hq : Function.Bijective q) (T : KernelTower Ω (n+1)) (a c : I) (b : S.Leaf)
    (ha : q a=⟨0,b⟩) (hc : q c=⟨1,b⟩) (f X : FinitePath Ω (n+1) → Fin N → ℝ) :
    matrixProjectionError (doubled S) q T a c (spatialProduct (fun _ : I => f)) X =
      oldProjectionError (doubled S) T ⟨0,b⟩ ⟨1,b⟩ (doubledOverlap S f) X := by
  unfold matrixProjectionError oldProjectionError FiniteLaw.l2
  congr 1
  apply FiniteLaw.expect_congr
  intro z
  dsimp only
  have he := spatialProduct_leafProduct (doubled S) q hq f z
  rw [← doubledOverlap_eq S f z] at he
  change (spatialProduct (fun _ : I => f) (fun b => (doubled S).pathAt (q b) z)-
    FiniteLaw.dot (X ((doubled S).pathAt (q a) z)) (X ((doubled S).pathAt (q c) z)))^2=_
  rw [he,ha,hc]
  exact sub_sq_comm _ _

omit [DecidableEq I] in
/-- Thus the target's own later-first-split projection has the genuine
proper-child covariance bound required before making the depth comparison. -/
theorem matrixProjectionError_stem_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (b : (PrescribedTree.node k C).Leaf) (r : ℕ)
    (q : I → (doubled (stem (.node k C) r)).Leaf) (hq : Function.Bijective q)
    (T : KernelTower Ω (n+1+r+1)) (a c : I)
    (ha : q a=⟨0,stemLeaf (.node k C) r b⟩) (hc : q c=⟨1,stemLeaf (.node k C) r b⟩)
    (f : FinitePath Ω (n+1+r+1) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    matrixProjectionError (doubled (stem (.node k C) r)) q T a c
      (spatialProduct (fun _ : I => f))
      (fun x i => tailMean (.node k C) (r+1) T (fun y => f y i) x) ≤
       2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f)) := by
  rw [matrixProjectionError_doubled _ q hq T a c _ ha hc]
  exact oldProjectionError_doubled_stem_le k C b r T f hf

omit [Fintype I] [DecidableEq I] in
/-- Changing the target's projected means to the old projected means costs
their actual coupled L2 difference in the target law, uniformly over extension
histories after marginalization. -/
theorem matrixProjectionError_change (S : PrescribedTree n) (q : I → S.Leaf)
    (T : KernelTower Ω n) (a c : I) (A : (I → FinitePath Ω n) → ℝ)
    (X Y : FinitePath Ω n → Fin N → ℝ) :
    matrixProjectionError S q T a c A X ≤ matrixProjectionError S q T a c A Y +
      (S.sampleLaw T).l2 (fun z => FiniteLaw.dot (Y (S.pathAt (q a) z)) (Y (S.pathAt (q c) z))-
        FiniteLaw.dot (X (S.pathAt (q a) z)) (X (S.pathAt (q c) z))) := by
  have h := (S.sampleLaw T).l2_add_le
    (fun z => A (fun c => S.pathAt (q c) z)-FiniteLaw.dot (Y (S.pathAt (q a) z)) (Y (S.pathAt (q c) z)))
    (fun z => FiniteLaw.dot (Y (S.pathAt (q a) z)) (Y (S.pathAt (q c) z))-
      FiniteLaw.dot (X (S.pathAt (q a) z)) (X (S.pathAt (q c) z)))
  simpa only [matrixProjectionError,sub_add_sub_cancel] using h

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
