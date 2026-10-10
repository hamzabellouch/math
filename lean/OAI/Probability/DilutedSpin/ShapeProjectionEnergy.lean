import OAI.Probability.DilutedSpin.RootMatrixTriple

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω] {N n : ℕ}

/-- Pulling three independent copies of one sampled branch back to any one
leaf keeps exactly the three independent path law. -/
lemma branch_leaf_triple (C : PrescribedTree n) (T : KernelTower Ω (n+1))
    (a : C.Leaf) (F : FinitePath Ω (n+1) → FinitePath Ω (n+1) →
      FinitePath Ω (n+1) → ℝ) :
    (T.1.bind (fun z => C.sampleLaw (T.2 z))).expect (fun x =>
      (T.1.bind (fun z => C.sampleLaw (T.2 z))).expect (fun y =>
        (T.1.bind (fun z => C.sampleLaw (T.2 z))).expect (fun w =>
          F (x.1,C.pathAt a x.2) (y.1,C.pathAt a y.2) (w.1,C.pathAt a w.2)))) =
    KernelTower.tripleExpectAt (n+1) T 0 F := by
  change _ = (KernelTower.law (n+1) T).expect (fun x =>
    (KernelTower.law (n+1) T).expect (fun y => (KernelTower.law (n+1) T).expect (F x y)))
  calc
    _ = (T.1.bind (fun z => C.sampleLaw (T.2 z))).expect (fun x =>
      (T.1.bind (fun z => C.sampleLaw (T.2 z))).expect (fun y =>
        (KernelTower.law (n+1) T).expect (fun w =>
          F (x.1,C.pathAt a x.2) (y.1,C.pathAt a y.2) w))) := by
      apply FiniteLaw.expect_congr; intro x
      apply FiniteLaw.expect_congr; intro y
      exact branch_leaf_marginal C T.1 T.2 a (fun w =>
        F (x.1,C.pathAt a x.2) (y.1,C.pathAt a y.2) w)
    _ = (T.1.bind (fun z => C.sampleLaw (T.2 z))).expect (fun x =>
        (KernelTower.law (n+1) T).expect (fun y =>
          (KernelTower.law (n+1) T).expect (fun w => F (x.1,C.pathAt a x.2) y w))) := by
      apply FiniteLaw.expect_congr; intro x
      exact branch_leaf_marginal C T.1 T.2 a (fun y =>
        (KernelTower.law (n+1) T).expect (fun w => F (x.1,C.pathAt a x.2) y w))
    _ = _ := branch_leaf_marginal C T.1 T.2 a (fun x =>
      (KernelTower.law (n+1) T).expect (fun y => (KernelTower.law (n+1) T).expect (F x y)))

/-- The error is measured in the genuine two-copy branch law, in the same
coupling as the physical spin products, not in a surrogate law. -/
noncomputable def branchProjectionSq (C : PrescribedTree n) (T : KernelTower Ω (n+1))
    (a : C.Leaf) (f Y : FinitePath Ω (n+1) → Fin N → ℝ) : ℝ :=
  (T.1.bind (fun z => C.sampleLaw (T.2 z))).pairProjectionSq
    (fun z i => C.leafProduct (fun w => f (z.1,w) i) z.2)
    (fun z => Y (z.1,C.pathAt a z.2))

lemma branch_energy_projection_transfer (C : PrescribedTree n) (T : KernelTower Ω (n+1))
    (a : C.Leaf) (f Y : FinitePath Ω (n+1) → Fin N → ℝ) :
    childEnergy C T f ≤ 2*KernelTower.halfTripleDifferenceAt (n+1) T 0 Y +
      4*branchProjectionSq C T a f Y := by
  have h := FiniteLaw.covariance_projection_transfer
    (T.1.bind (fun z => C.sampleLaw (T.2 z)))
    (fun z i => C.leafProduct (fun w => f (z.1,w) i) z.2)
    (fun z => Y (z.1,C.pathAt a z.2))
  rw [branch_leaf_triple C T a (fun x y z =>
    (FiniteLaw.dot (Y x) (Y y)-FiniteLaw.dot (Y x) (Y z))^2)] at h
  simpa only [childEnergy,branchProjectionSq,KernelTower.halfTripleDifferenceAt,
    ← mul_assoc,show (2:ℝ)*(1/2)=1 by norm_num,one_mul] using h

/-- Conditional covariance of the actual shape with d preceding unary
transitions, averaged over their genuine kernel prefix. -/
noncomputable def shapeEnergyAt (C : PrescribedTree n) : (d : ℕ) →
    KernelTower Ω (n+1+d) → (FinitePath Ω (n+1+d) → Fin N → ℝ) → ℝ
  | 0, T, f => childEnergy C T f
  | d+1, T, f => T.1.expect (fun z => shapeEnergyAt C d (T.2 z) (fun y => f (z,y)))

noncomputable def shapeProjectionSqAt (C : PrescribedTree n) (a : C.Leaf) : (d : ℕ) →
    KernelTower Ω (n+1+d) → (FinitePath Ω (n+1+d) → Fin N → ℝ) →
      (FinitePath Ω (n+1+d) → Fin N → ℝ) → ℝ
  | 0, T, f, Y => branchProjectionSq C T a f Y
  | d+1, T, f, Y => T.1.expect (fun z =>
      shapeProjectionSqAt C a d (T.2 z) (fun y => f (z,y)) (fun y => Y (z,y)))

/-- Three-copy transfer at an arbitrary prefix above a complete literal
multileaf shape. The shape's actual covariance is on the left. -/
theorem shape_energy_projection_transfer (C : PrescribedTree n) (a : C.Leaf)
    (d : ℕ) (T : KernelTower Ω (n+1+d))
    (f Y : FinitePath Ω (n+1+d) → Fin N → ℝ) :
    shapeEnergyAt C d T f ≤ 2*KernelTower.halfTripleDifferenceAt (n+1+d) T d Y +
      4*shapeProjectionSqAt C a d T f Y := by
  induction d with
  | zero => exact branch_energy_projection_transfer C T a f Y
  | succ d ih =>
    have h := T.1.expect_mono (fun z => ih (T.2 z) (fun y => f (z,y)) (fun y => Y (z,y)))
    convert h using 1
    · rfl
    · simp only [shapeProjectionSqAt,KernelTower.halfTripleDifferenceAt,
        KernelTower.tripleExpectAt,FiniteLaw.expect_add,FiniteLaw.expect_mul_left]
      rfl

lemma shapeEnergyAt_nonneg (C : PrescribedTree n) (d : ℕ) (T : KernelTower Ω (n+1+d))
    (f : FinitePath Ω (n+1+d) → Fin N → ℝ) : 0 ≤ shapeEnergyAt C d T f := by
  induction d with
  | zero => unfold shapeEnergyAt childEnergy FiniteLaw.covarianceEnergy; positivity
  | succ d ih => exact T.1.expect_nonneg (fun z => ih (T.2 z) (fun y => f (z,y)))

lemma shapeProjectionSqAt_nonneg (C : PrescribedTree n) (a : C.Leaf) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (f Y : FinitePath Ω (n+1+d) → Fin N → ℝ) :
    0 ≤ shapeProjectionSqAt C a d T f Y := by
  induction d with
  | zero => exact FiniteLaw.expect_nonneg _ (fun _ => FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _))
  | succ d ih => exact T.1.expect_nonneg (fun z => ih (T.2 z) (fun y => f (z,y)) (fun y => Y (z,y)))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
