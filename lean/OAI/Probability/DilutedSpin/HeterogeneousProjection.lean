import OAI.Probability.DilutedSpin.FiniteProjection
import OAI.Probability.DilutedSpin.ShapeMean

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω Λ I : Type} [Fintype Ω] [Fintype Λ]
  {A : I → Type} [∀ i, Fintype (A i)] {k L : ℕ}

/-- Adjoining an unused physical coordinate preserves every realized mark
prior, also when the mark spaces have type-dependent dimensions. -/
theorem tower_projects (π : Ω → Λ) (roots : Fin k → I)
    (T : KernelTower Ω L) (U : KernelTower Λ L) (h : KernelTower.Projects π L T U)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    KernelTower.Projects (fun z : Ω × Row (A := A) roots => (π z.1,z.2)) L
      (tower roots L T Q) (tower roots L U Q) := by
  induction L with
  | zero => trivial
  | succ L ih =>
    refine ⟨h.1.bind (FiniteLaw.pi (fun j => Q (roots j) 0)),?_⟩
    intro z
    exact ih (T.2 z.1) (U.2 (π z.1)) (h.2 z.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [Fintype Λ] [∀ i, Fintype (A i)] in
@[simp] theorem physical_pathMap (π : Ω → Λ) (roots : Fin k → I)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    physical roots L (KernelTower.pathMap (fun z : Ω × Row (A := A) roots => (π z.1,z.2)) L y) =
      KernelTower.pathMap π L (physical roots L y) := by
  induction L with
  | zero => rfl
  | succ L ih => exact congrArg (fun z => (π y.1.1,z)) (ih y.2)

omit [Fintype Ω] [Fintype Λ] [∀ i, Fintype (A i)] in
@[simp] theorem mark_pathMap (π : Ω → Λ) (roots : Fin k → I) (q : Fin k)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    mark q L (KernelTower.pathMap (fun z : Ω × Row (A := A) roots => (π z.1,z.2)) L y) =
      mark q L y := by
  induction L with
  | zero => rfl
  | succ L ih => exact congrArg (fun z => (y.1.2 q,z)) (ih y.2)

/-- Exact projection through the literal perturbed power-mean root. -/
theorem root_projection (π : Ω → Λ) (roots : Fin k → I)
    (T : KernelTower Ω L) (U : KernelTower Λ L) (h : KernelTower.Projects π L T U)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Λ L → ℝ)
    (factor : (i : I) → FinitePath Λ L → FinitePath (A i) L → ℝ) :
    root T Q m (fun y => base (KernelTower.pathMap π L y)) roots
      (fun i x y => factor i (KernelTower.pathMap π L x) y) =
    root U Q m base roots factor := by
  have hh := KernelTower.backwardLog_of_projects L (tower_projects π roots T U h Q) m
    (logWeight base roots factor)
  unfold root
  convert hh using 1
  congr 1
  funext y
  simp only [logWeight,physical_pathMap,mark_pathMap]

 
theorem root_projection_stability (π : Ω → Λ) (roots : Fin k → I)
    (T : KernelTower Ω L) (U : KernelTower Λ L) (h : KernelTower.Projects π L T U)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Λ L → ℝ) (base' : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Λ L → FinitePath (A i) L → ℝ)
    (factor' : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B : ℝ} (D : I → ℝ)
    (hb : ∀ y, |base' y-base (KernelTower.pathMap π L y)| ≤ B)
    (hf : ∀ i x y, |Real.log (factor' i x y)-Real.log (factor i (KernelTower.pathMap π L x) y)| ≤ D i) :
    |root T Q m base' roots factor'-root U Q m base roots factor| ≤ B+∑ q, D (roots q) := by
  rw [← root_projection π roots T U h Q m base factor]
  apply (abs_sub_le _ (root T Q m (fun y => base (KernelTower.pathMap π L y)) roots factor') _).trans
  exact add_le_add (root_base_stability T Q m hm base' _ roots factor' hb)
    (root_factor_stability T Q m hm _ roots factor' _ D hf)

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- Covariance energy of one actual child, including its incoming transition.
The rest of the tree has not been sampled or conditioned upon. -/
noncomputable def childEnergy {n : ℕ} (C : PrescribedTree n)
    (T : KernelTower Ω (n+1)) (f : FinitePath Ω (n+1) → Fin N → ℝ) : ℝ :=
  (T.1.bind (fun a => C.sampleLaw (T.2 a))).covarianceEnergy
    (fun z v => C.leafProduct (fun y => f (z.1,y) v) z.2)

/-- Literal child-by-child projection of a prescribed-tree multioverlap.
Each factor is a spin product sampled from an actual independent child law.
This is the projection error used before signed-history charging. -/
theorem node_projection {n : ℕ} (k : ℕ+) (C : Fin k → PrescribedTree n)
    (T : KernelTower Ω (n+1)) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (hf : ∀ x v, |f x v| ≤ 1) (B : Fin N → ℝ) (hB : ∀ v, |B v| ≤ 1) :
    ((PrescribedTree.node k C).sampleLaw T).l2 (fun z => FiniteLaw.dot
      (fun v => (PrescribedTree.node k C).leafProduct (fun x => f x v) z -
        (PrescribedTree.node k C).treeMean T (fun x => f x v)) B) ≤
      ∑ i, Real.sqrt (Real.sqrt (childEnergy (C i) T f)) := by
  have hm (i : Fin k) (v : Fin N) :
      (T.1.bind (fun a => (C i).sampleLaw (T.2 a))).expect
        (fun z => (C i).leafProduct (fun y => f (z.1,y) v) z.2) =
      T.1.expect (fun a => (C i).treeMean (T.2 a) (fun y => f (a,y) v)) := by
    rw [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    exact (treeMean_eq_expect (C i) (T.2 a) (fun y => f (a,y) v)).symm
  have h := FiniteLaw.product_contraction
    (fun i : Fin k => T.1.bind (fun a => (C i).sampleLaw (T.2 a)))
    (fun i z v => (C i).leafProduct (fun y => f (z.1,y) v) z.2)
    (fun i z v => leafProduct_bound (C i) (fun y => hf (z.1,y) v) z.2) B hB
  simp_rw [hm] at h
  exact h

/-- The multiplying side is allowed to be an independently sampled complete
shape, not merely a deterministic vector. This retains its full joint law. -/
theorem node_projection_independent {n : ℕ} {Λ : Type*} [Fintype Λ]
    (Q : FiniteLaw Λ) (k : ℕ+) (C : Fin k → PrescribedTree n)
    (T : KernelTower Ω (n+1)) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (hf : ∀ x v, |f x v| ≤ 1) (B : Λ → Fin N → ℝ) (hB : ∀ z v, |B z v| ≤ 1) :
    (Q.bind (fun _ => (PrescribedTree.node k C).sampleLaw T)).l2 (fun z => FiniteLaw.dot
      (fun v => (PrescribedTree.node k C).leafProduct (fun x => f x v) z.2 -
        (PrescribedTree.node k C).treeMean T (fun x => f x v)) (B z.1)) ≤
      ∑ i, Real.sqrt (Real.sqrt (childEnergy (C i) T f)) := by
  let A := ∑ i, Real.sqrt (Real.sqrt (childEnergy (C i) T f))
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have he (z : Λ) : ((PrescribedTree.node k C).sampleLaw T).expect (fun w => (FiniteLaw.dot
      (fun v => (PrescribedTree.node k C).leafProduct (fun x => f x v) w -
        (PrescribedTree.node k C).treeMean T (fun x => f x v)) (B z))^2) ≤ A^2 := by
    have h := node_projection k C T f hf (B z) (hB z)
    have hs := mul_self_le_mul_self (FiniteLaw.l2_nonneg _ _) h
    simpa only [← pow_two,FiniteLaw.l2_sq] using hs
  change _ ≤ A
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hA,?_⟩
  rw [FiniteLaw.expect_bind]
  exact (Q.expect_mono he).trans_eq (Q.expect_const _)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
