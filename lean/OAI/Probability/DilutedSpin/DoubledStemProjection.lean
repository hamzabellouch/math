import OAI.Probability.DilutedSpin.StemCoupling

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

/-- The overlap of every old leaf, with two complete independent descendant
sides retained. This is also the normalized full leaf product. -/
noncomputable def doubledOverlap (S : PrescribedTree n) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (z : Sample Ω (doubled S)) : ℝ :=
  FiniteLaw.dot (fun i => leafProduct S (fun x => f ((z 0).1,x) i) (z 0).2)
    (fun i => leafProduct S (fun x => f ((z 1).1,x) i) (z 1).2)

omit [Fintype Ω] in
lemma doubledOverlap_eq (S : PrescribedTree n) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (z : Sample Ω (doubled S)) :
    doubledOverlap S f z=(∑ i, leafProduct (doubled S) (fun x => f x i) z)/(N:ℝ) := by
  unfold doubledOverlap FiniteLaw.dot
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change _ = ∏ j : Fin 2, leafProduct S (fun x => f ((z j).1,x) i) (z j).2
  rw [Fin.prod_univ_two]
  rfl

/-- The old-tree projection error in the signed matrix bound, on the literal
doubled old tree, is controlled by the actual proper-child energies at its
later first split. No conditional concentration assumption is imposed. -/
theorem oldProjectionError_doubled_stem_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r : ℕ)
    (T : KernelTower Ω (n+1+r+1)) (f : FinitePath Ω (n+1+r+1) → Fin N → ℝ)
    (hf : ∀ x i, |f x i|≤1) :
    let S := PrescribedTree.node k C
    let X := fun x i => tailMean S (r+1) T (fun y => f y i) x
    oldProjectionError (doubled (stem S r)) T ⟨0,stemLeaf S r a⟩ ⟨1,stemLeaf S r a⟩
      (doubledOverlap (stem S r) f) X ≤
      2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f)) := by
  dsimp only
  let S := PrescribedTree.node k C
  let Q := T.1.bind (fun x => (stem S r).sampleLaw (T.2 x))
  let X := fun z : Ω × Sample Ω (stem S r) =>
    fun i => leafProduct (stem S r) (fun y => f (z.1,y) i) z.2
  let Y := fun z : Ω × Sample Ω (stem S r) =>
    fun i => tailMean S r (T.2 z.1) (fun y => f (z.1,y) i)
      ((stem S r).pathAt (stemLeaf S r a) z.2)
  have h := FiniteLaw.pairProjectionSq_le_of_contractions Q X Y
    (fun z i => leafProduct_bound _ (fun y => hf (z.1,y) i) z.2)
    (fun z i => tailMean_bound _ _ _ _ (fun y => hf (z.1,y) i) _) 
    ((k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f))
  have hc : ∀ B : Fin N → ℝ, (∀ i, |B i|≤1) →
      Q.expect (fun z => (FiniteLaw.dot (fun i => X z i-Y z i) B)^2) ≤
        (k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f) := by
    intro B hB
    rw [FiniteLaw.expect_bind]
    have hh := T.1.expect_mono (fun x => stem_node_contraction_sq_le k C a r (T.2 x)
      (fun y => f (x,y)) (fun y => hf (x,y)) B hB)
    rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro i _
    exact T.1.expect_sqrt_le _ (fun x => shapeEnergyAt_nonneg (C i) r (T.2 x) (fun y => f (x,y)))
  specialize h hc
  have he : (sampleLaw (doubled (stem S r)) T).expect (fun z =>
      (FiniteLaw.dot (Y (z 0)) (Y (z 1))-doubledOverlap (stem S r) f z)^2) =
        Q.pairProjectionSq X Y := by
    change (FiniteLaw.pi (fun _ : Fin 2 => Q)).expect _ = _
    refine Eq.trans ?_ (FiniteLaw.expect_pi_pair (fun _ : Fin 2 => Q) 0 1 (by decide)
      (fun x y => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (Y x) (Y y))^2))
    apply FiniteLaw.expect_congr
    intro z
    exact sub_sq_comm _ _
  unfold oldProjectionError FiniteLaw.l2
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · have hn : 0 ≤ (k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f) := by positivity
    rw [mul_pow,Real.sq_sqrt hn]
    change (sampleLaw (doubled (stem S r)) T).expect (fun z =>
      (FiniteLaw.dot (Y (z 0)) (Y (z 1))-doubledOverlap (stem S r) f z)^2) ≤ _
    rw [he]
    norm_num only [show (2:ℝ)^2=4 by norm_num]
    exact h

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

def stemInternal (S : PrescribedTree n) : (r : ℕ) → S.Internal → (stem S r).Internal
  | 0,v => v
  | r+1,v => some ⟨0,stemInternal S r v⟩

lemma splitDepth_stem (S : PrescribedTree n) (r : ℕ) (a b : S.Leaf) :
    splitDepth (stem S r) (stemLeaf S r a) (stemLeaf S r b)=splitDepth S a b+r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change splitDepth (.node 1 (fun _ => stem S r)) ⟨0,stemLeaf S r a⟩ ⟨0,stemLeaf S r b⟩=_
    rw [splitDepth_same_child,ih]
    omega

lemma freshSplitDepth_stem (S : PrescribedTree n) (r : ℕ) (v : S.Internal) (a : S.Leaf) :
    freshSplitDepth (stem S r) (stemInternal S r v) (stemLeaf S r a)=freshSplitDepth S v a+r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change 1+freshSplitDepth (stem S r) (stemInternal S r v) (stemLeaf S r a)=_
    rw [ih]
    omega

/-- A later-split projector lifted through an arbitrary actual ancestral
prefix, without flattening the dependent tuple representation of paths. -/
noncomputable def splitProjector (S : PrescribedTree n) (r : ℕ) :
    (d : ℕ) → KernelTower Ω (n+r+1+d) → (FinitePath Ω (n+r+1+d) → ℝ) →
      FinitePath Ω (n+r+1+d) → ℝ
  | 0,T,f,x => tailMean S (r+1) T f x
  | d+1,T,f,x => splitProjector S r d (T.2 x.1) (fun y => f (x.1,y)) x.2

lemma splitProjector_bound (S : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+r+1+d)) (f : FinitePath Ω (n+r+1+d) → ℝ)
    (hf : ∀ x, |f x|≤1) (x : FinitePath Ω (n+r+1+d)) :
    |splitProjector S r d T f x|≤1 := by
  induction d with
  | zero => exact tailMean_bound S (r+1) T f hf x
  | succ d ih => exact ih (T.2 x.1) (fun y => f (x.1,y)) (fun y => hf (x.1,y)) x.2

/-- The old-side geometric premise of the full signed matrix identity at an
arbitrary evaluation depth d. All old leaves and sampled ancestors remain. -/
theorem stem_doubled_projector_old_side (S : PrescribedTree n) (r d : ℕ)
    (a b : (stem S r).Leaf) (T : KernelTower Ω (n+r+1+d))
    (f : FinitePath Ω (n+r+1+d) → Fin N → ℝ)
    (c : (stem (doubled (stem S r)) d).Leaf)
    (hc : splitDepth (stem (doubled (stem S r)) d)
      (stemLeaf (doubled (stem S r)) d ⟨0,a⟩) c=d)
    (z : Sample Ω (stem (doubled (stem S r)) d)) :
    (fun i => splitProjector S r d T (fun x => f x i)
      ((stem (doubled (stem S r)) d).pathAt c z)) =
    (fun i => splitProjector S r d T (fun x => f x i)
      ((stem (doubled (stem S r)) d).pathAt
        (stemLeaf (doubled (stem S r)) d ⟨1,b⟩) z)) := by
  induction d with
  | zero => exact doubled_stem_projector_old_side S r a b T f c hc z
  | succ d ih =>
    rcases c with ⟨j,c⟩
    have hj := Fin.eq_zero j
    subst j
    change splitDepth (.node 1 (fun _ => stem (doubled (stem S r)) d))
      ⟨0,stemLeaf (doubled (stem S r)) d ⟨0,a⟩⟩ ⟨0,c⟩=d+1 at hc
    rw [splitDepth_same_child] at hc
    have hc' : splitDepth (stem (doubled (stem S r)) d)
      (stemLeaf (doubled (stem S r)) d ⟨0,a⟩) c=d := by omega
    exact ih (T.2 (z 0).1) (fun y => f ((z 0).1,y)) c hc' (z 0).2

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
