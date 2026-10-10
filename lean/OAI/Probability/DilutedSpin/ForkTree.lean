import OAI.Probability.DilutedSpin.LabeledColorHistory
import OAI.Probability.DilutedSpin.TreeMarkLaw

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

/-- k paths with a common d-coordinate prefix, no contracted unary levels. -/
def fork (h : ℕ) (k : ℕ+) : (d : ℕ) → PrescribedTree (h+1+d)
  | 0 => .node k (fun _ => single h)
  | d+1 => .node 1 (fun _ => fork h k d)

def forkLeaf (h : ℕ) (k : ℕ+) : (d : ℕ) → Fin k → (fork h k d).Leaf
  | 0, i => ⟨i,singleLeaf h⟩
  | d+1, i => ⟨0,forkLeaf h k d i⟩

def forkVertex (h : ℕ) (k : ℕ+) : (d : ℕ) → (fork h k d).Internal
  | 0 => none
  | d+1 => some ⟨0,forkVertex h k d⟩

lemma leaf_single_unique (n : ℕ) (a : (single n).Leaf) : a = singleLeaf n := by
  induction n with
  | zero => cases a; rfl
  | succ n ih =>
    rcases a with ⟨i,a⟩
    have hi := Fin.eq_zero i
    subst i
    exact congrArg (fun a : (single n).Leaf => (⟨0,a⟩ : (single (n+1)).Leaf)) (ih a)

lemma forkLeaf_surjective (h : ℕ) (k : ℕ+) (d : ℕ) :
    Function.Surjective (forkLeaf h k d) := by
  induction d with
  | zero =>
    rintro ⟨i,a⟩
    refine ⟨i,?_⟩
    exact congrArg (fun a : (single h).Leaf => (⟨i,a⟩ : (fork h k 0).Leaf)) (leaf_single_unique h a).symm
  | succ d ih =>
    rintro ⟨i,a⟩
    have hi := Fin.eq_zero i
    subst i
    obtain ⟨j,rfl⟩ := ih a
    exact ⟨j,rfl⟩

lemma forkLeaf_injective (h : ℕ) (k : ℕ+) (d : ℕ) :
    Function.Injective (forkLeaf h k d) := by
  induction d with
  | zero => intro i j he; exact congrArg Sigma.fst he
  | succ d ih =>
    intro i j he
    exact ih (Sigma.mk.inj he).2.eq

lemma fork_split {h d : ℕ} {k : ℕ+} (i j : Fin k) (hij : i ≠ j) :
    splitDepth (fork h k d) (forkLeaf h k d i) (forkLeaf h k d j) = d := by
  induction d with
  | zero => exact splitDepth_diff_child (fun _ => single h) i j hij (singleLeaf h) (singleLeaf h)
  | succ d ih =>
    exact (splitDepth_same_child (fun _ : Fin (1:ℕ+) => fork h k d) 0
      (forkLeaf h k d i) (forkLeaf h k d j)).trans (by rw [ih]; omega)

lemma fork_gamma (h d : ℕ) (k : ℕ+) (m : Fin (h+1+d+1) → ℝ) :
    gamma (fork h k d) m (forkVertex h k d) =
      m ⟨d,by omega⟩ - (k:ℝ)*m ⟨d+1,by omega⟩ := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih (fun j => m j.succ)

lemma fork_fresh_split (h d : ℕ) (k : ℕ+) (i : Fin k) :
    freshSplitDepth (fork h k d) (forkVertex h k d) (forkLeaf h k d i) = d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    exact (freshSplitDepth_same_child (fun _ : Fin (1:ℕ+) => fork h k d) 0
      (forkVertex h k d) (forkLeaf h k d i)).trans (by rw [ih]; omega)

/-- At the actual branching vertex every child is a full independent kernel
path. Proves the full joint law, not just product moments. -/
lemma fork_zero_expect (h : ℕ) (k : ℕ+) (T : KernelTower Ω (h+1))
    (F : (Fin k → FinitePath Ω (h+1)) → ℝ) :
    ((fork h k 0).sampleLaw T).expect
      (fun x => F (fun i => (fork h k 0).pathAt (forkLeaf h k 0 i) x)) =
      (FiniteLaw.pi (fun _ : Fin k => KernelTower.law (h+1) T)).expect F := by
  classical
  rcases T with ⟨μ,K⟩
  change (FiniteLaw.pi (fun _ : Fin k => μ.bind (fun z => sampleLaw (single h) (K z)))).expect
    (fun x => F (fun i => ((x i).1,pathAt (single h) (singleLeaf h) (x i).2))) = _
  have he : ∀ (test : FinitePath Ω (h+1) → ℝ),
      (μ.bind (fun z => sampleLaw (single h) (K z))).expect
        (fun x => (1:ℝ)*test (x.1,pathAt (single h) (singleLeaf h) x.2)) =
      (KernelTower.law (h+1) (μ,K)).expect (fun y => (1:ℝ)*test y) := by
    intro test
    simp only [one_mul,FiniteLaw.expect_bind]
    erw [KernelTower.law_succ_expect]
    apply FiniteLaw.expect_congr
    intro z
    exact leaf_marginal (single h) (K z) (singleLeaf h) (fun y => test (z,y))
  simpa only [Finset.prod_const_one,mul_one] using FiniteLaw.expect_pi_weighted_map
    (fun _ : Fin k => μ.bind (fun z => sampleLaw (single h) (K z)))
    (fun _ : Fin k => KernelTower.law (h+1) (μ,K))
    (fun _ x => (x.1,pathAt (single h) (singleLeaf h) x.2))
    (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) (fun _ => he) F

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
