import OAI.Probability.DilutedSpin.ActualTreeSelector

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω Λ : Type}

def firstLeaf : {n : ℕ} → (S : PrescribedTree n) → S.Leaf
  | 0, .leaf => ()
  | _+1, .node k C => ⟨⟨0,k.pos⟩, firstLeaf (C ⟨0,k.pos⟩)⟩

/-- The paths at all leaf positions determine the entire sample. -/
lemma sample_ext {n : ℕ} (S : PrescribedTree n) {x y : Sample Ω S}
    (h : ∀ a : S.Leaf, S.pathAt a x = S.pathAt a y) : x = y := by
  induction S with
  | leaf => exact @Subsingleton.elim Unit inferInstance x y
  | @node n k C ih =>
    funext i
    apply Prod.ext
    · exact congrArg (fun z : FinitePath Ω (n+1) => z.1) (h ⟨i,firstLeaf (C i)⟩)
    · apply ih i
      intro a
      exact congrArg (fun z : FinitePath Ω (n+1) => z.2) (h ⟨i,a⟩)

lemma sampleFst_oldSample {n : ℕ} (S : PrescribedTree n) (v : S.Internal)
    (x : Sample (Ω×Λ) (grow S v)) :
    sampleFst S (oldSample S v x) = oldSample S v (sampleFst (grow S v) x) := by
  apply sample_ext S
  intro a
  calc
    _ = KernelTower.pathFst n (S.pathAt a (oldSample S v x)) := pathAt_sampleFst S a _
    _ = KernelTower.pathFst n ((grow S v).pathAt (oldLeaf S v a) x) := by rw [pathAt_oldLeaf]
    _ = (grow S v).pathAt (oldLeaf S v a) (sampleFst (grow S v) x) := (pathAt_sampleFst _ _ _).symm
    _ = _ := pathAt_oldLeaf _ _ _ _

lemma sampleSnd_oldSample {n : ℕ} (S : PrescribedTree n) (v : S.Internal)
    (x : Sample (Ω×Λ) (grow S v)) :
    sampleSnd S (oldSample S v x) = oldSample S v (sampleSnd (grow S v) x) := by
  apply sample_ext S
  intro a
  calc
    _ = KernelTower.pathSnd n (S.pathAt a (oldSample S v x)) := pathAt_sampleSnd S a _
    _ = KernelTower.pathSnd n ((grow S v).pathAt (oldLeaf S v a) x) := by rw [pathAt_oldLeaf]
    _ = (grow S v).pathAt (oldLeaf S v a) (sampleSnd (grow S v) x) := (pathAt_sampleSnd _ _ _).symm
    _ = _ := pathAt_oldLeaf _ _ _ _

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
