import OAI.Probability.DilutedSpin.ShapeProjectionEnergy

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N n : ℕ}

/-- The two-sided projection error at the first branching vertex, with both
copies sampled independently from the full genuine prescribed-tree law. -/
theorem node_two_side_projection (k : ℕ+) (C : Fin k → PrescribedTree n)
    (T : KernelTower Ω (n+1)) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (hf : ∀ x v, |f x v| ≤ 1) :
    let S := PrescribedTree.node k C
    let P := S.sampleLaw T
    let X := fun z v => S.leafProduct (fun x => f x v) z
    let μ := fun v => S.treeMean T (fun x => f x v)
    (P.bind (fun _ => P)).l2 (fun z => FiniteLaw.dot (X z.1) (X z.2)-FiniteLaw.dot μ μ) ≤
      2*∑ i, Real.sqrt (Real.sqrt (childEnergy (C i) T f)) := by
  dsimp only
  let S := PrescribedTree.node k C
  let P := S.sampleLaw T
  let X := fun (z : Sample Ω S) v => S.leafProduct (fun x => f x v) z
  let μ := fun v => S.treeMean T (fun x => f x v)
  let F := fun z : Sample Ω S × Sample Ω S => FiniteLaw.dot (fun v => X z.2 v-μ v) (X z.1)
  let G := fun z : Sample Ω S × Sample Ω S => FiniteLaw.dot (fun v => X z.1 v-μ v) μ
  have hX (z : Sample Ω S) (v : Fin N) : |X z v| ≤ 1 := leafProduct_bound S (fun x => hf x v) z
  have hμ (v : Fin N) : |μ v| ≤ 1 := treeMean_bound S T (fun x => hf x v)
  have hF : (P.bind (fun _ => P)).l2 F ≤ ∑ i, Real.sqrt (Real.sqrt (childEnergy (C i) T f)) :=
    node_projection_independent P k C T f hf X hX
  have hG : (P.bind (fun _ => P)).l2 G ≤ ∑ i, Real.sqrt (Real.sqrt (childEnergy (C i) T f)) := by
    have h := node_projection k C T f hf μ hμ
    have he : (P.bind (fun _ => P)).l2 G = P.l2 (fun z => FiniteLaw.dot (fun v => X z v-μ v) μ) := by
      simp only [FiniteLaw.l2,FiniteLaw.expect_bind,G,FiniteLaw.expect_const]
    rw [he]
    exact h
  have he (z : Sample Ω S × Sample Ω S) :
      FiniteLaw.dot (X z.1) (X z.2)-FiniteLaw.dot μ μ = F z+G z := by
    simp only [F,G,FiniteLaw.dot,← sub_div,← add_div,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (P.bind (fun _ => P)).l2 _ ≤ _
  calc
    _ = (P.bind (fun _ => P)).l2 (fun z => F z+G z) := by
      unfold FiniteLaw.l2
      exact congrArg Real.sqrt ((P.bind (fun _ => P)).expect_congr (fun z => congrArg (·^2) (he z)))
    _ ≤ (P.bind (fun _ => P)).l2 F+(P.bind (fun _ => P)).l2 G := FiniteLaw.l2_add_le _ F G
    _ ≤ _ := by linarith

/-- The squared contraction error permits arbitrary bounded old scalar
multipliers through Cauchy--Schwarz; no independence of that test is used. -/
theorem node_two_side_projection_test (k : ℕ+) (C : Fin k → PrescribedTree n)
    (T : KernelTower Ω (n+1)) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (hf : ∀ x v, |f x v| ≤ 1)
    (g : Sample Ω (.node k C) × Sample Ω (.node k C) → ℝ) (hg : ∀ z, |g z| ≤ 1) :
    let S := PrescribedTree.node k C
    let P := S.sampleLaw T
    let X := fun z v => S.leafProduct (fun x => f x v) z
    let μ := fun v => S.treeMean T (fun x => f x v)
    |(P.bind (fun _ => P)).expect (fun z => g z *
      (FiniteLaw.dot (X z.1) (X z.2)-FiniteLaw.dot μ μ))| ≤
      2*∑ i, Real.sqrt (Real.sqrt (childEnergy (C i) T f)) := by
  dsimp only
  apply le_trans _ (node_two_side_projection k C T f hf)
  let S := PrescribedTree.node k C
  let P := (S.sampleLaw T).bind (fun _ => S.sampleLaw T)
  let R := fun z : Sample Ω S × Sample Ω S =>
    FiniteLaw.dot (fun v => S.leafProduct (fun x => f x v) z.1)
      (fun v => S.leafProduct (fun x => f x v) z.2)-
      FiniteLaw.dot (fun v => S.treeMean T (fun x => f x v))
        (fun v => S.treeMean T (fun x => f x v))
  change |P.expect (fun z => g z*R z)| ≤ P.l2 R
  have h : |P.expect (fun z => g z*R z)| ≤ P.l2 (fun z => g z*R z) := by
    apply (sq_le_sq₀ (abs_nonneg _) (P.l2_nonneg _)).mp
    rw [sq_abs,FiniteLaw.l2_sq]
    exact P.sq_expect_le_expect_sq _
  exact h.trans (by simpa only [mul_comm] using P.l2_mul_le R g hg)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
