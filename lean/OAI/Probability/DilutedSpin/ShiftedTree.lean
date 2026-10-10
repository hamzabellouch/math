import OAI.Probability.DilutedSpin.RootMatrixTriple
import OAI.Probability.DilutedSpin.SizeSpinRoot
import OAI.Probability.DilutedSpin.TwoSideProjection

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance shiftedTreeDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

/-- Extending the final unary edge keeps every internal branching depth.
In contrast, `unary S` delays all of them by exactly one. -/
def bottomUnary : {n : ℕ} → PrescribedTree n → PrescribedTree (n+1)
  | 0, .leaf => unary .leaf
  | _+1, .node k C => .node k (fun i => bottomUnary (C i))

def bottomLeaf : {n : ℕ} → (S : PrescribedTree n) → S.Leaf → (bottomUnary S).Leaf
  | 0, .leaf, _ => ⟨0,()⟩
  | _+1, .node _ C, a => ⟨a.1,bottomLeaf (C a.1) a.2⟩

lemma bottomLeaf_bijective {n : ℕ} (S : PrescribedTree n) : Function.Bijective (bottomLeaf S) := by
  induction S with
  | leaf =>
    constructor
    · intro a b _; cases a; cases b; rfl
    · rintro ⟨i,a⟩
      have hi := Fin.eq_zero i
      cases a
      subst i
      exact ⟨(),rfl⟩
  | @node n k C ih =>
    constructor
    · rintro ⟨i,a⟩ ⟨j,b⟩ h
      have hi := congrArg Sigma.fst h
      change i = j at hi
      subst j
      have ha := (Sigma.mk.inj h).2.eq
      have hab := (ih i).1 ha
      change a=b at hab
      subst b
      rfl
    · rintro ⟨i,a⟩
      obtain ⟨b,rfl⟩ := (ih i).2 a
      exact ⟨⟨i,b⟩,rfl⟩

lemma splitDepth_bottom_ne {n : ℕ} (S : PrescribedTree n) (a b : S.Leaf) (hab : a ≠ b) :
    splitDepth (bottomUnary S) (bottomLeaf S a) (bottomLeaf S b) = splitDepth S a b := by
  induction S with
  | leaf => cases a; cases b; exact False.elim (hab rfl)
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    by_cases hij : i=j
    · subst j
      have hab' : a ≠ b := fun he => hab (congrArg (Sigma.mk i) he)
      change splitDepth (.node k (fun i => bottomUnary (C i))) ⟨i,bottomLeaf (C i) a⟩
        ⟨i,bottomLeaf (C i) b⟩ = _
      rw [splitDepth_same_child,splitDepth_same_child,ih i a b hab']
    · exact (splitDepth_diff_child (fun i => bottomUnary (C i)) i j hij _ _).trans
        (splitDepth_diff_child C i j hij a b).symm

lemma branchingCount_bottom {n : ℕ} (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount (bottomUnary S) P = branchingCount S P := by
  classical
  induction S generalizing P with
  | leaf =>
    change (if P 0 ∧ 1 < (1:ℕ) then 1 else 0)+(∑ _ : Fin 1, (0:ℕ)) = 0
    simp
  | @node n k C ih => simp only [bottomUnary,branchingCount,ih]

lemma branchingCount_unary {n : ℕ} (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount (unary S) P = branchingCount S (fun d => P (d+1)) := by
  classical
  change (if P 0 ∧ 1 < (1:ℕ) then 1 else 0)+
    (∑ _ : Fin 1, branchingCount S (fun d => P (d+1))) = _
  simp

lemma leaves_bottom {n : ℕ} (S : PrescribedTree n) : leaves (bottomUnary S) = leaves S := by
  induction S with
  | leaf =>
    change (∑ _ : Fin 1, (1:ℕ)) = 1
    simp
  | @node n k C ih => simp only [bottomUnary,leaves,ih]

lemma leaves_unary {n : ℕ} (S : PrescribedTree n) : leaves (unary S) = leaves S := by
  change (∑ _ : Fin 1, leaves S) = _
  simp

/-- Literal branching-vertex count as a sum. Distinct vertices at equal
depths occur separately; no count by distinct depth values is substituted. -/
lemma branchingCount_eq_vertexSum {n : ℕ} (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount S P = ∑ v : S.Internal,
      if 1 < vertexArity S v ∧ P (vertexDepth S v) then 1 else 0 := by
  classical
  induction S generalizing P with
  | leaf =>
    change 0 = ∑ v : Empty, _
    simp
  | @node n k C ih =>
    change _ = ∑ v : Option ((i : Fin k) × Internal (C i)), _
    rw [Fintype.sum_option]
    simp only [vertexArity,vertexDepth,Fintype.sum_sigma,branchingCount,ih,and_comm]

noncomputable def branchingDepths {n : ℕ} (S : PrescribedTree n) : Finset ℕ := by
  classical
  exact (Finset.univ.filter (fun v => 1 < vertexArity S v)).image (vertexDepth S)

lemma mem_branchingDepths {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    d ∈ branchingDepths S ↔ ∃ v : S.Internal, 1 < vertexArity S v ∧ vertexDepth S v=d := by
  classical
  simp only [branchingDepths,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

lemma branchingCount_congr_on {n : ℕ} (S : PrescribedTree n) (P Q : ℕ → Prop)
    (h : ∀ d ∈ branchingDepths S, P d ↔ Q d) : branchingCount S P = branchingCount S Q := by
  classical
  rw [branchingCount_eq_vertexSum,branchingCount_eq_vertexSum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : 1 < vertexArity S v
  · have hd := h (vertexDepth S v) ((mem_branchingDepths S _).mpr ⟨v,hv,rfl⟩)
    simp only [hv,true_and,hd]
  · simp only [hv,false_and,ite_false]


lemma branchingCount_eq_zero_iff {n : ℕ} (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount S P = 0 ↔ ∀ d ∈ branchingDepths S, ¬P d := by
  classical
  rw [branchingCount_eq_vertexSum,Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  constructor
  · intro h d hd hp
    obtain ⟨v,hv,rfl⟩ := (mem_branchingDepths S d).mp hd
    have he := h v (Finset.mem_univ v)
    rw [ite_eq_left ⟨hv,hp⟩] at he
    contradiction
  · intro h v _
    by_cases hv : 1 < vertexArity S v
    · have hp := h (vertexDepth S v) ((mem_branchingDepths S _).mpr ⟨v,hv,rfl⟩)
      simp only [hv,hp,and_false,ite_false]
    · simp only [hv,false_and,ite_false]

/-- Both copies are aligned, but the two occurrences are different vertices. -/
def doubled {n : ℕ} (S : PrescribedTree n) : PrescribedTree (n+1) := .node 2 (fun _ => S)

noncomputable def shiftedTwinDepths {n : ℕ} (S : PrescribedTree n) : Finset ℕ :=
  (branchingDepths S).image (fun d => d+2)

lemma zero_not_mem_shiftedTwinDepths {n : ℕ} (S : PrescribedTree n) :
    0 ∉ shiftedTwinDepths S := by
  classical
  simp [shiftedTwinDepths]

/-- Regular depth assignments imply this no-adjacent-depth condition once
eta L > 1. It is precisely the geometric premise of shifted charging. -/
def NoAdjacentBranchDepths {n : ℕ} (S : PrescribedTree n) : Prop :=
  ∀ a ∈ branchingDepths S, ∀ b ∈ branchingDepths S, a+1 ≠ b

lemma shifted_twin_old_count {n : ℕ} (S : PrescribedTree n) (hs : NoAdjacentBranchDepths S) :
    branchingCount (doubled (bottomUnary S)) (· ∈ shiftedTwinDepths S) = 0 := by
  classical
  have hC : branchingCount S (fun d => d+1 ∈ shiftedTwinDepths S)=0 := by
    apply (branchingCount_eq_zero_iff S _).mpr
    intro d hd h
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h
    exact hs a ha d hd (by omega)
  simp only [doubled,branchingCount]

  simp only [zero_not_mem_shiftedTwinDepths,false_and,ite_false,branchingCount_bottom,hC,
    Finset.sum_const_zero,add_zero]

lemma shifted_twin_target_count {n : ℕ} (S : PrescribedTree n) :
    branchingCount (doubled (unary S)) (· ∈ shiftedTwinDepths S) =
      2*branchingCount S (fun _ => True) := by
  classical
  have hC : branchingCount S (fun d => d+1+1 ∈ shiftedTwinDepths S) =
      branchingCount S (fun _ => True) := by
    apply branchingCount_congr_on
    intro d hd
    exact iff_of_true (Finset.mem_image.mpr ⟨d,hd,by omega⟩) trivial
  simp only [doubled,branchingCount]

  simp only [zero_not_mem_shiftedTwinDepths,false_and,ite_false,branchingCount_unary,hC,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,zero_add]
  norm_num

lemma shifted_twin_total_count {n : ℕ} (S : PrescribedTree n) :
    branchingCount (doubled (unary S)) (fun _ => True) =
      branchingCount (doubled (unary S)) (· ∈ shiftedTwinDepths S)+1 := by
  classical
  rw [shifted_twin_target_count]
  simp only [doubled,branchingCount]

  simp only [branchingCount_unary,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num at *
  omega

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N n : ℕ}

/-- Retain a specified descendant leaf through the actual unary prefix. -/
def stemLeaf (S : PrescribedTree n) : (r : ℕ) → S.Leaf → (stem S r).Leaf
  | 0, a => a
  | r+1, a => ⟨0,stemLeaf S r a⟩

lemma sampleLaw_unary_expect (S : PrescribedTree n) (T : KernelTower Ω (n+1))
    (F : Ω × Sample Ω S → ℝ) :
    ((unary S).sampleLaw T).expect (fun z => F (z 0)) =
      T.1.expect (fun a => (S.sampleLaw (T.2 a)).expect (fun w => F (a,w))) := by
  change (FiniteLaw.pi (fun _ : Fin 1 => T.1.bind (fun a => S.sampleLaw (T.2 a)))).expect
    (fun z => F (z 0)) = _
  rw [FiniteLaw.expect_pi_marginal,FiniteLaw.expect_bind]

omit [Fintype Ω] in
@[simp] lemma leafProduct_unary (S : PrescribedTree n) (f : FinitePath Ω (n+1) → ℝ)
    (z : Sample Ω (unary S)) :
    leafProduct (unary S) f z=leafProduct S (fun y => f ((z 0).1,y)) (z 0).2 := by
  change (∏ i : Fin 1, leafProduct S (fun y => f ((z i).1,y)) (z i).2)=_
  simp only [Fin.prod_univ_one]
  rfl

/-- The true L2 contraction projection error, retaining the entire sampled
prefix to the designated branching node. The projector is the literal
conditional descendant mean evaluated on the chosen leaf's path. -/
noncomputable def stemContractionSq (S : PrescribedTree n) (a : S.Leaf) (r : ℕ)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → Fin N → ℝ) (B : Fin N → ℝ) : ℝ :=
  ((stem S r).sampleLaw T).expect (fun z => (FiniteLaw.dot (fun i =>
    leafProduct (stem S r) (fun x => f x i) z-
      tailMean S r T (fun x => f x i) ((stem S r).pathAt (stemLeaf S r a) z)) B)^2)

lemma stemContractionSq_step (S : PrescribedTree n) (a : S.Leaf) (r : ℕ)
    (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → Fin N → ℝ) (B : Fin N → ℝ) :
    stemContractionSq S a (r+1) T f B =
      T.1.expect (fun x => stemContractionSq S a r (T.2 x) (fun y => f (x,y)) B) := by
  unfold stemContractionSq
  let F := fun z : Ω × Sample Ω (stem S r) => (FiniteLaw.dot (fun i =>
    leafProduct (stem S r) (fun y => f (z.1,y) i) z.2-
      tailMean S r (T.2 z.1) (fun y => f (z.1,y) i)
        ((stem S r).pathAt (stemLeaf S r a) z.2)) B)^2
  refine Eq.trans ?_ (sampleLaw_unary_expect (stem S r) T F)
  apply FiniteLaw.expect_congr
  intro z
  apply congrArg (fun u : Fin N → ℝ => (FiniteLaw.dot u B)^2)
  funext i
  exact congrArg₂ (·-·) (leafProduct_unary (stem S r) (fun x => f x i) z) rfl

/-- Actual projection at an arbitrary later first split; child covariances
are averaged over the very same ancestral prefix. No decorrelation premise
is assumed. Constants are dimension-free, including zero spatial size. -/
theorem stem_node_contraction_sq_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r : ℕ)
    (T : KernelTower Ω (n+1+r)) (f : FinitePath Ω (n+1+r) → Fin N → ℝ)
    (hf : ∀ x i, |f x i|≤1) (B : Fin N → ℝ) (hB : ∀ i, |B i|≤1) :
    stemContractionSq (.node k C) a r T f B ≤
      (k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) r T f) := by
  induction r with
  | zero =>
    have h := node_projection k C T f hf B hB
    have hs := mul_self_le_mul_self (FiniteLaw.l2_nonneg _ _) h
    rw [← pow_two,← pow_two,FiniteLaw.l2_sq] at hs
    have hc := @sq_sum_le_card_mul_sum_sq (Fin k) ℝ _ _ _ _ Finset.univ
      (fun i : Fin k => Real.sqrt (Real.sqrt (childEnergy (C i) T f)))
    simp only [Real.sq_sqrt (Real.sqrt_nonneg _),Finset.card_univ,Fintype.card_fin] at hc
    exact hs.trans hc
  | succ r ih =>
    rw [stemContractionSq_step]
    have h := T.1.expect_mono (fun x => ih (T.2 x) (fun y => f (x,y)) (fun y => hf (x,y)))
    rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro i _
    exact T.1.expect_sqrt_le _ (fun x => shapeEnergyAt_nonneg (C i) r (T.2 x) (fun y => f (x,y)))

/-- A separate complete sampled side may multiply the contraction. It is
independent below the common evaluation prefix, not averaged away. -/
theorem stem_node_projection_independent {Λ : Type*} [Fintype Λ]
    (Q : FiniteLaw Λ) (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r : ℕ)
    (T : KernelTower Ω (n+1+r)) (f : FinitePath Ω (n+1+r) → Fin N → ℝ)
    (hf : ∀ x i, |f x i|≤1) (B : Λ → Fin N → ℝ) (hB : ∀ x i, |B x i|≤1) :
    let S := PrescribedTree.node k C
    (Q.bind (fun _ => (stem S r).sampleLaw T)).l2 (fun z => FiniteLaw.dot (fun i =>
      leafProduct (stem S r) (fun x => f x i) z.2-
      tailMean S r T (fun x => f x i) ((stem S r).pathAt (stemLeaf S r a) z.2)) (B z.1)) ≤
        Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) r T f)) := by
  dsimp only
  apply Real.sqrt_le_sqrt
  rw [FiniteLaw.expect_bind]
  exact (Q.expect_mono (fun x => stem_node_contraction_sq_le k C a r T f hf (B x) (hB x))).trans_eq
    (Q.expect_const _)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
