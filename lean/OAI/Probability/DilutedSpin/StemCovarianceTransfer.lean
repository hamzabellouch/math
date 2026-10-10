import OAI.Probability.DilutedSpin.DoubledStemProjection

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

/-- The old projection error and the physical two-copy projection energy
are exactly the same coupling, not only equal separate marginal errors. -/
lemma oldProjectionError_doubled_sq (S : PrescribedTree n) (a : S.Leaf)
    (T : KernelTower Ω (n+1)) (f X : FinitePath Ω (n+1) → Fin N → ℝ) :
    (oldProjectionError (doubled S) T ⟨0,a⟩ ⟨1,a⟩ (doubledOverlap S f) X)^2 =
      branchProjectionSq S T a f X := by
  unfold oldProjectionError
  rw [FiniteLaw.l2_sq]
  unfold branchProjectionSq FiniteLaw.pairProjectionSq
  change (FiniteLaw.pi (fun _ : Fin 2 => T.1.bind (fun x => S.sampleLaw (T.2 x)))).expect _ = _
  refine Eq.trans ?_ (FiniteLaw.expect_pi_pair
    (fun _ : Fin 2 => T.1.bind (fun x => S.sampleLaw (T.2 x))) 0 1 (by decide)
    (fun z w => (FiniteLaw.dot
      (fun i => leafProduct S (fun y => f (z.1,y) i) z.2)
      (fun i => leafProduct S (fun y => f (w.1,y) i) w.2)-
      FiniteLaw.dot (X (z.1,S.pathAt a z.2)) (X (w.1,S.pathAt a w.2)))^2))
  apply FiniteLaw.expect_congr
  intro z
  exact sub_sq_comm _ _

/-- The proper-child covariance estimate for the exact coupled projection
energy required by the three-copy transfer. -/
theorem branchProjectionSq_stem_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r : ℕ)
    (T : KernelTower Ω (n+1+r+1)) (f : FinitePath Ω (n+1+r+1) → Fin N → ℝ)
    (hf : ∀ x i, |f x i|≤1) :
    branchProjectionSq (stem (.node k C) r) T (stemLeaf (.node k C) r a) f
      (fun x i => tailMean (.node k C) (r+1) T (fun y => f y i) x) ≤
      4*(k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f) := by
  rw [← oldProjectionError_doubled_sq]
  have hh := oldProjectionError_doubled_stem_le k C a r T f hf
  have hs := mul_self_le_mul_self (FiniteLaw.l2_nonneg _ _) hh
  have hn : 0 ≤ (k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f) := by positivity
  simpa only [oldProjectionError,← pow_two,mul_pow,Real.sq_sqrt hn,show (2:ℝ)^2=4 by norm_num,mul_assoc] using hs

/-- The left side is the covariance energy of the actual entire multileaf
shape. Thus the full projected THREE-copy observable, not just projected
covariance, is the only outstanding scalar in this transfer. -/
theorem stem_covariance_three_copy_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r : ℕ)
    (T : KernelTower Ω (n+1+r+1)) (f : FinitePath Ω (n+1+r+1) → Fin N → ℝ)
    (hf : ∀ x i, |f x i|≤1) :
    childEnergy (stem (.node k C) r) T f ≤
      2*KernelTower.halfTripleDifferenceAt (n+1+r+1) T 0
        (fun x i => tailMean (.node k C) (r+1) T (fun y => f y i) x) +
      16*(k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f) := by
  have h := branch_energy_projection_transfer (stem (.node k C) r) T (stemLeaf (.node k C) r a)
    f (fun x i => tailMean (.node k C) (r+1) T (fun y => f y i) x)
  have he := branchProjectionSq_stem_le k C a r T f hf
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
