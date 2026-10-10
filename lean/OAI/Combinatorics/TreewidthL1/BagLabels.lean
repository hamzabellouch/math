import OAI.Combinatorics.TreewidthL1.TreeMarkov

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1.BagLabels
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]
abbrev Local (B : I → Set V) := (i : I) → B i → Bool
noncomputable def assemble (B : I → Set V) (hcover : ∀ v, ∃ i, v ∈ B i)
    (x : Local B) : V → Bool := fun v =>
  x (Classical.choose (hcover v)) ⟨v,Classical.choose_spec (hcover v)⟩
noncomputable def restrict (B : I → Set V) (ω : V → Bool) : Local B :=
  fun _ v => ω v
noncomputable def globalMass (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (R : (i j : I) → (B i → Bool) → (B j → Bool) → ℝ)
    (hs : TreeMarkov.Symmetric (fun i => B i → Bool) R) (ω : V → Bool) : ℝ :=
  ∑ x : Local B, if assemble B hcover x = ω then TreeMarkov.density
    (fun i => B i → Bool) T μ R hs x else 0

lemma coherent_equal
    {V : Type treewidthLevel1} {I : Type treewidthLevel2} [Fintype V] [Fintype I]
    (T : SimpleGraph I) (B : I → Set V)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected) (x : Local B)
    (hx : ∀ i j, T.Adj i j → ∀ v hi hj, x i ⟨v,hi⟩ = x j ⟨v,hj⟩)
    (i j : I) (v : V) (hi : v ∈ B i) (hj : v ∈ B j) :
    x i ⟨v,hi⟩ = x j ⟨v,hj⟩ := by
  obtain ⟨p⟩ := hrun v ⟨i,hi⟩ ⟨j,hj⟩
  let val : {i | v ∈ B i} → Bool := fun a => x a ⟨v,a.2⟩
  change val ⟨i,hi⟩ = val ⟨j,hj⟩
  have he : ∀ {a b : {i | v ∈ B i}} (q : (T.induce {i | v ∈ B i}).Walk a b), val a = val b := by
    intro a b q
    induction q with
    | nil => rfl
    | @cons a b c hab q ih =>
      exact (hx a b hab v a.2 b.2).trans ih
  exact he p

lemma assemble_on_support (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (R : (i j : I) → (B i → Bool) → (B j → Bool) → ℝ)
    (hs : TreeMarkov.Symmetric (fun i => B i → Bool) R)
    (hcomp : ∀ i j, T.Adj i j → ∀ a b, R i j a b ≠ 0 →
      ∀ v hi hj, a ⟨v,hi⟩ = b ⟨v,hj⟩)
    (x : Local B) (hx : TreeMarkov.density (fun i => B i → Bool) T μ R hs x ≠ 0) :
    restrict B (assemble B hcover x) = x := by
  have he : ∀ i j, T.Adj i j → R i j (x i) (x j) ≠ 0 := by
    intro i j hij
    have hprod := (mul_ne_zero_iff.mp hx).2
    have hmem : s(i,j) ∈ T.edgeFinset := by simpa using hij
    exact Finset.prod_ne_zero_iff.mp hprod _ hmem
  have hco : ∀ i j, T.Adj i j → ∀ v hi hj, x i ⟨v,hi⟩ = x j ⟨v,hj⟩ :=
    fun i j hij => hcomp i j hij (x i) (x j) (he i j hij)
  funext i v
  exact coherent_equal T B hrun x hco _ i v _ v.2

lemma expectation_global (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (R : (i j : I) → (B i → Bool) → (B j → Bool) → ℝ)
    (hs : TreeMarkov.Symmetric (fun i => B i → Bool) R) (f : (V → Bool) → ℝ) :
    (∑ ω : V → Bool, globalMass T B hcover μ R hs ω * f ω) =
      ∑ x : Local B, TreeMarkov.density (fun i => B i → Bool) T μ R hs x *
        f (assemble B hcover x) := by
  simp only [globalMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul,zero_mul]
  simp

lemma expectation_local (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (R : (i j : I) → (B i → Bool) → (B j → Bool) → ℝ)
    (hs : TreeMarkov.Symmetric (fun i => B i → Bool) R)
    (hcomp : ∀ i j, T.Adj i j → ∀ a b, R i j a b ≠ 0 →
      ∀ v hi hj, a ⟨v,hi⟩ = b ⟨v,hj⟩) (f : Local B → ℝ) :
    (∑ ω : V → Bool, globalMass T B hcover μ R hs ω * f (restrict B ω)) =
      ∑ x : Local B, TreeMarkov.density (fun i => B i → Bool) T μ R hs x * f x := by
  rw [expectation_global]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hz : TreeMarkov.density (fun i => B i → Bool) T μ R hs x = 0
  · simp [hz]
  · rw [assemble_on_support T B hcover hrun μ R hs hcomp x hz]

/-- The canonical junction law is a genuine measure on global vertex labels,
with exact connected-subtree marginals. Compatibility is enforced by the local
edge support, never assumed for independently sampled bag states. -/
theorem global_bag_law (T : SimpleGraph I) (hT : T.IsTree) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (R : (i j : I) → (B i → Bool) → (B j → Bool) → ℝ)
    (hs : TreeMarkov.Symmetric (fun i => B i → Bool) R)
    (hn : TreeMarkov.Normalized (fun i => B i → Bool) T μ R)
    (hcomp : ∀ i j, T.Adj i j → ∀ a b, R i j a b ≠ 0 →
      ∀ v hi hj, a ⟨v,hi⟩ = b ⟨v,hj⟩) :
    let ρ := globalMass T B hcover μ R hs
    (∀ ω, 0 ≤ ρ ω) ∧ (∑ ω, ρ ω) = 1 ∧
    (∀ i a, (∑ ω : V → Bool, if restrict B ω i = a then ρ ω else 0) = μ i a) ∧
    ∀ {K : Type*} [Fintype K] (e : K ↪ I), (T.comap e).Connected →
      ∀ (f : ((j : K) → B (e j) → Bool) → ℝ),
      (∑ ω : V → Bool, ρ ω * f (fun j => restrict B ω (e j))) =
        ∑ x, TreeMarkov.density (fun j => B (e j) → Bool) (T.comap e)
          (fun j => μ (e j)) (fun j k => R (e j) (e k))
          (fun j k => hs (e j) (e k)) x * f x := by
  dsimp only
  obtain ⟨hnon,hprob,hmarg⟩ := TreeMarkov.tree_density (fun i => B i → Bool) T hT μ R hs hn
  refine ⟨?_,?_,?_,?_⟩
  · intro ω
    apply Finset.sum_nonneg
    intro x hx
    split_ifs
    · exact hnon x
    · exact le_rfl
  · have he := expectation_global T B hcover μ R hs (fun _ => 1)
    simpa using he.trans (by simpa using hprob)
  · intro i a
    have he := expectation_local T B hcover hrun μ R hs hcomp
      (fun x => if x i = a then 1 else 0)
    simp only [mul_ite,mul_one,mul_zero] at he
    apply he.trans
    convert hmarg i a using 1
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl
  · intro K _ e hc f
    exact (expectation_local T B hcover hrun μ R hs hcomp
      (fun x => f (fun j => x (e j)))).trans
        (TreeMarkov.expectation_comap (fun i => B i → Bool) T hT μ R hs hn e hc f)
end BoundedTreewidthL1.BagLabels

namespace BoundedTreewidthL1

/-- Pushforward mass at a point, for a finite real nonnegative measure. -/
noncomputable def marginal {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (c : C) : ℝ := by
  classical
  exact ∑ a, if f a = c then μ a else 0

/-- The two-part conditional product, with zero denominator interpreted as zero.
Only compatible pairs receive mass. -/
noncomputable def glueWeights {A B C : Type*} [Fintype A]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ) (a : A) (b : B) : ℝ := by
  classical
  exact if f a = g b then μ a * ν b / marginal f μ (f a) else 0

end BoundedTreewidthL1

namespace BoundedTreewidthL1

lemma marginal_nonneg {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (c : C) :
    0 ≤ marginal f μ c := by
  classical
  exact Finset.sum_nonneg (fun a _ => by split_ifs <;> simp_all)

lemma le_marginal {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (a : A) :
    μ a ≤ marginal f μ (f a) := by
  classical
  unfold marginal
  have := Finset.single_le_sum
    (s := Finset.univ) (f := fun b => if f b = f a then μ b else 0)
    (fun b _ => by split_ifs <;> simp_all) (Finset.mem_univ a)
  simpa using this

lemma weight_eq_zero_of_marginal_eq_zero {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (a : A)
    (hzero : marginal f μ (f a) = 0) : μ a = 0 := by
  have := le_marginal f μ hμ a
  exact le_antisymm (hzero ▸ this) (hμ a)

lemma glueWeights_nonneg {A B C : Type*} [Fintype A]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (a : A) (b : B) :
    0 ≤ glueWeights f g μ ν a b := by
  classical
  unfold glueWeights
  split_ifs
  · exact div_nonneg (mul_nonneg (hμ a) (hν b)) (marginal_nonneg f μ hμ _)
  · exact le_rfl

lemma glueWeights_row {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hconsistent : ∀ c, marginal f μ c = marginal g ν c) (a : A) :
    (∑ b, glueWeights f g μ ν a b) = μ a := by
  classical
  have hform : (∑ b, glueWeights f g μ ν a b) =
      μ a * marginal g ν (f a) / marginal f μ (f a) := by
    simp only [marginal, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    unfold glueWeights marginal
    by_cases h : f a = g b
    · simp only [h, ↓reduceIte]
    · simp [h, Ne.symm h]
  rw [hform, ← hconsistent]
  by_cases h : marginal f μ (f a) = 0
  · rw [h, weight_eq_zero_of_marginal_eq_zero f μ hμ a h]
    simp
  · exact mul_div_cancel_right₀ (μ a) h

lemma glueWeights_swap {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ)
    (hconsistent : ∀ c, marginal f μ c = marginal g ν c) (a : A) (b : B) :
    glueWeights f g μ ν a b = glueWeights g f ν μ b a := by
  classical
  unfold glueWeights
  by_cases h : f a = g b
  · simp [h, ← hconsistent, mul_comm]
  · simp [h, Ne.symm h]

theorem glueWeights_marginals {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b)
    (hconsistent : ∀ c, marginal f μ c = marginal g ν c) :
    (∀ a b, 0 ≤ glueWeights f g μ ν a b) ∧
    (∀ a, (∑ b, glueWeights f g μ ν a b) = μ a) ∧
    (∀ b, (∑ a, glueWeights f g μ ν a b) = ν b) := by
  refine ⟨glueWeights_nonneg f g μ ν hμ hν, glueWeights_row f g μ ν hμ hconsistent, ?_⟩
  intro b
  simp_rw [glueWeights_swap f g μ ν hconsistent]
  exact glueWeights_row g f ν μ hν (fun c => (hconsistent c).symm) b

end BoundedTreewidthL1

namespace BoundedTreewidthL1.BagLabels
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]
noncomputable def leftTrace (B : I → Set V) (i j : I) (a : B i → Bool) : ↥(B i ∩ B j) → Bool :=
  fun v => a ⟨v,v.2.1⟩
noncomputable def rightTrace (B : I → Set V) (i j : I) (b : B j → Bool) : ↥(B i ∩ B j) → Bool :=
  fun v => b ⟨v,v.2.2⟩
noncomputable def pairMass (T : SimpleGraph I) (B : I → Set V)
    (μ : (i : I) → (B i → Bool) → ℝ) (i j : I) (a : B i → Bool) (b : B j → Bool) : ℝ :=
  if T.Adj i j then glueWeights (leftTrace B i j) (rightTrace B i j) (μ i) (μ j) a b else 0

lemma glueWeights_map {A B C D : Type*} [Fintype A]
    (f : A → C) (g : B → C) (E : C → D) (hE : Function.Injective E)
    (μ : A → ℝ) (ν : B → ℝ) (a : A) (b : B) :
    glueWeights (E ∘ f) (E ∘ g) μ ν a b = glueWeights f g μ ν a b := by
  simp [glueWeights,marginal,hE.eq_iff]

noncomputable def overlapSwap (B : I → Set V) (i j : I) :
    (↥(B i ∩ B j) → Bool) ≃ (↥(B j ∩ B i) → Bool) where
  toFun f v := f ⟨v,⟨v.2.2,v.2.1⟩⟩
  invFun f v := f ⟨v,⟨v.2.2,v.2.1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma pairMass_symmetric
    {V : Type treewidthLevel1} {I : Type treewidthLevel2} [Fintype V] [Fintype I]
    (T : SimpleGraph I) (B : I → Set V)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (μ i) c = marginal (rightTrace B i j) (μ j) c) :
    TreeMarkov.Symmetric (fun i => B i → Bool) (pairMass T B μ) := by
  intro i j a b
  by_cases hij : T.Adj i j
  · simp only [pairMass,hij,T.adj_symm hij,↓reduceIte]
    rw [glueWeights_swap _ _ _ _ (hcons i j hij)]
    exact (glueWeights_map (rightTrace B i j) (leftTrace B i j)
      (overlapSwap B i j) (overlapSwap B i j).injective (μ j) (μ i) b a).symm
  · have hji : ¬T.Adj j i := fun h => hij h.symm
    simp [pairMass,hij,hji]

lemma pairMass_row
    {V : Type treewidthLevel1} {I : Type treewidthLevel2} [Fintype V] [Fintype I]
    (T : SimpleGraph I) (B : I → Set V)
    (μ : (i : I) → (B i → Bool) → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (μ i) c = marginal (rightTrace B i j) (μ j) c)
    (i j : I) (hij : T.Adj i j) (a : B i → Bool) :
    (∑ b, pairMass T B μ i j a b) = μ i a := by
  simp only [pairMass,hij,↓reduceIte]
  exact glueWeights_row _ _ _ _ (hμ i) (hcons i j hij) a

theorem bag_couplings (T : SimpleGraph I) (B : I → Set V)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hμ₁ : ∀ i, (∑ a, μ i a) = 1)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (μ i) c = marginal (rightTrace B i j) (μ j) c) :
    let R := TreeMarkov.interaction (fun i => B i → Bool) μ (pairMass T B μ)
    ∃ _ : TreeMarkov.Symmetric (fun i => B i → Bool) R,
      TreeMarkov.Normalized (fun i => B i → Bool) T μ R ∧
      ∀ i j, T.Adj i j → ∀ a b, R i j a b ≠ 0 →
        ∀ v hi hj, a ⟨v,hi⟩ = b ⟨v,hj⟩ := by
  dsimp only
  have hs := pairMass_symmetric T B μ hcons
  have hJ : ∀ i j, T.Adj i j → ∀ a b, 0 ≤ pairMass T B μ i j a b := by
    intro i j hij a b
    simp only [pairMass,hij,↓reduceIte]
    exact glueWeights_nonneg _ _ _ _ (hμ i) (hμ j) a b
  refine ⟨TreeMarkov.interaction_symmetric (fun i => B i → Bool) μ _ hs,
    TreeMarkov.interaction_normalized (fun i => B i → Bool) T μ _ hμ hμ₁ hs hJ
      (pairMass_row T B μ hμ hcons),?_⟩
  intro i j hij a b hn v hi hj
  have he : leftTrace B i j a = rightTrace B i j b := by
    by_contra he
    apply hn
    simp [TreeMarkov.interaction,pairMass,hij,glueWeights,he]
  exact congrFun he ⟨v,hi,hj⟩
end BoundedTreewidthL1.BagLabels

namespace BoundedTreewidthL1.BagLabels
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]

def flip (A : Type*) : (A → Bool) ≃ (A → Bool) where
  toFun x := fun a => !(x a)
  invFun x := fun a => !(x a)
  left_inv x := by funext a; simp
  right_inv x := by funext a; simp

noncomputable def flipLocal (B : I → Set V) : Local B ≃ Local B where
  toFun x := fun i => flip (B i) (x i)
  invFun x := fun i => flip (B i) (x i)
  left_inv x := by funext i v; simp [flip]
  right_inv x := by funext i v; simp [flip]

lemma marginal_equivariant {A C : Type*} [Fintype A]
    (e : A ≃ A) (d : C ≃ C) (f : A → C) (μ : A → ℝ)
    (hμ : ∀ a, μ (e a) = μ a) (hf : ∀ a, f (e a) = d (f a)) (c : C) :
    marginal f μ (d c) = marginal f μ c := by
  unfold marginal
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [hf, hμ, d.injective.eq_iff]

lemma pairMass_flip
    {V : Type treewidthLevel1} {I : Type treewidthLevel2} [Fintype V] [Fintype I]
    (T : SimpleGraph I) (B : I → Set V)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (hflip : ∀ i a, μ i (flip (B i) a) = μ i a)
    (i j : I) (a : B i → Bool) (b : B j → Bool) :
    pairMass T B μ i j (flip (B i) a) (flip (B j) b) = pairMass T B μ i j a b := by
  have hl : ∀ a, leftTrace B i j (flip (B i) a) = flip ↥(B i ∩ B j) (leftTrace B i j a) := fun _ => rfl
  have hr : rightTrace B i j (flip (B j) b) = flip ↥(B i ∩ B j) (rightTrace B i j b) := rfl
  simp only [pairMass, glueWeights, hl, hr, (flip ↥(B i ∩ B j)).injective.eq_iff, hflip,
    marginal_equivariant (flip (B i)) (flip ↥(B i ∩ B j)) (leftTrace B i j) (μ i) (hflip i) hl]
  split_ifs <;> rfl

lemma density_flip (T : SimpleGraph I) (B : I → Set V)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (μ i) c = marginal (rightTrace B i j) (μ j) c)
    (hflip : ∀ i a, μ i (flip (B i) a) = μ i a) (x : Local B) :
    let R := TreeMarkov.interaction (fun i => B i → Bool) μ (pairMass T B μ)
    let hs := TreeMarkov.interaction_symmetric (fun i => B i → Bool) μ _
      (pairMass_symmetric T B μ hcons)
    TreeMarkov.density (fun i => B i → Bool) T μ R hs (flipLocal B x) =
      TreeMarkov.density (fun i => B i → Bool) T μ R hs x := by
  dsimp only
  unfold TreeMarkov.density
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact hflip i (x i)
  · apply Finset.prod_congr rfl
    intro e he
    induction e using Sym2.ind with
    | _ i j =>
      change pairMass T B μ i j (flip (B i) (x i)) (flip (B j) (x j)) /
        (μ i (flip (B i) (x i)) * μ j (flip (B j) (x j))) =
        pairMass T B μ i j (x i) (x j) / (μ i (x i) * μ j (x j))
      rw [pairMass_flip T B μ hflip, hflip, hflip]

theorem canonical_symmetric (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (μ i) c = marginal (rightTrace B i j) (μ j) c)
    (hflip : ∀ i a, μ i (flip (B i) a) = μ i a) :
    let R := TreeMarkov.interaction (fun i => B i → Bool) μ (pairMass T B μ)
    let hs := TreeMarkov.interaction_symmetric (fun i => B i → Bool) μ _
      (pairMass_symmetric T B μ hcons)
    ∀ ω, globalMass T B hcover μ R hs (flip V ω) =
      globalMass T B hcover μ R hs ω := by
  dsimp only
  intro ω
  unfold globalMass
  rw [← (flipLocal B).sum_comp]
  apply Finset.sum_congr rfl
  intro x hx
  have he : assemble B hcover (flipLocal B x) = flip V (assemble B hcover x) := rfl
  simp only [he, (flip V).injective.eq_iff, density_flip T B μ hcons hflip]
end BoundedTreewidthL1.BagLabels

namespace BoundedTreewidthL1

noncomputable def cutDistance {V ι : Type*} [Fintype ι]
    (w : ι → ℝ) (cut : ι → V → Bool) (u v : V) : ℝ :=
  ∑ a, if cut a u = cut a v then 0 else w a

/-- The coordinate function of a vertex in the finite weighted cut space. -/
noncomputable def finiteCutMap {V ι : Type*} (w : ι → ℝ)
    (cut : ι → V → Bool) (v : V) : PiLp (1 : ENNReal) (fun _ : ι => ℝ) :=
  WithLp.toLp 1 (fun a => if cut a v then w a else 0)

lemma finiteCutMap_norm_sub {V ι : Type*} [Fintype ι]
    (w : ι → ℝ) (cut : ι → V → Bool) (hw : ∀ a, 0 ≤ w a) (u v : V) :
    ‖finiteCutMap w cut u - finiteCutMap w cut v‖ = cutDistance w cut u v := by
  rw [PiLp.norm_eq_of_L1]
  unfold cutDistance
  apply Finset.sum_congr rfl
  intro a _
  simp only [PiLp.sub_apply, finiteCutMap, Real.norm_eq_abs]
  cases hcu : cut a u <;> cases hcv : cut a v <;> simp [hw a, abs_of_nonneg, abs_neg]

theorem finite_cut_realization {V ι : Type*} [Fintype ι]
    (w : ι → ℝ) (cut : ι → V → Bool) (hw : ∀ a, 0 ≤ w a) :
    ∃ m : ℕ, ∃ F : V → PiLp (1 : ENNReal) (fun _ : Fin m => ℝ),
      ∀ u v, ‖F u - F v‖ = cutDistance w cut u v := by
  let e := LinearIsometryEquiv.piLpCongrLeft (1 : ENNReal) ℝ ℝ (Fintype.equivFin ι)
  refine ⟨Fintype.card ι, fun v => e (finiteCutMap w cut v), ?_⟩
  intro u v
  rw [← e.map_sub, e.norm_map]
  exact finiteCutMap_norm_sub w cut hw u v

end BoundedTreewidthL1

namespace BoundedTreewidthL1.BagLabels
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]

lemma marginal_div {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (m : ℝ) (c : C) :
    marginal f (fun a => μ a / m) c = marginal f μ c / m := by
  unfold marginal
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp

lemma marginal_mul {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (m : ℝ) (c : C) :
    marginal f (fun a => m * μ a) c = m * marginal f μ c := by
  unfold marginal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp

lemma global_path (T : SimpleGraph I) (hT : T.IsTree) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (R : (i j : I) → (B i → Bool) → (B j → Bool) → ℝ)
    (hs : TreeMarkov.Symmetric (fun i => B i → Bool) R)
    (hn : TreeMarkov.Normalized (fun i => B i → Bool) T μ R)
    (hcomp : ∀ i j, T.Adj i j → ∀ a b, R i j a b ≠ 0 →
      ∀ v hi hj, a ⟨v,hi⟩ = b ⟨v,hj⟩)
    (r : ℕ) (e : Fin (r+1) ↪ I) (he : T.comap e = SimpleGraph.pathGraph (r+1)) :
    MarkovFlow.IsMarkovLaw (fun j => B (e j) → Bool)
      (marginal (fun ω j => restrict B ω (e j)) (globalMass T B hcover μ R hs)) := by
  have hc : (T.comap e).Connected := he ▸ SimpleGraph.pathGraph_connected r
  have hsub := (global_bag_law T hT B hcover hrun μ R hs hn hcomp).2.2.2 e hc
  have hd : marginal (fun ω j => restrict B ω (e j)) (globalMass T B hcover μ R hs) =
      TreeMarkov.density (fun j => B (e j) → Bool) (T.comap e)
        (fun j => μ (e j)) (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k)) := by
    funext x
    have hh := hsub (fun y => if y = x then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at hh
    apply Eq.trans ?_ hh
    unfold marginal
    apply Finset.sum_congr rfl
    intro ω hω
    split_ifs <;> rfl
  rw [hd]
  have hn' : TreeMarkov.Normalized (fun j => B (e j) → Bool) (T.comap e)
      (fun j => μ (e j)) (fun j k => R (e j) (e k)) := by
    exact ⟨fun j => hn.1 (e j), fun j => hn.2.1 (e j),
      fun j k h => hn.2.2.1 (e j) (e k) h,
      fun j k h => hn.2.2.2 (e j) (e k) h⟩
  rw [he] at hn' ⊢
  exact TreeMarkov.path_markov _ _ _ _ hn'

/-- Exact common-positive-mass gluing and genuine finite real L1 realization,
from the actual local bag masses. The path assertion concerns full bag states;
separator-only projection is a further required transport obligation. -/
theorem canonical_gluing (T : SimpleGraph I) (hT : T.IsTree) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (μ : (i : I) → (B i → Bool) → ℝ) (m : ℝ) (hm : 0 < m)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, (∑ a, μ i a) = m)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (μ i) c = marginal (rightTrace B i j) (μ j) c)
    (hflip : ∀ i a, μ i (flip (B i) a) = μ i a) :
    ∃ ρ : (V → Bool) → ℝ,
      (∀ ω, 0 ≤ ρ ω) ∧ (∑ ω, ρ ω) = m ∧
      (∀ ω, ρ (flip V ω) = ρ ω) ∧
      (∀ i a, marginal (fun ω => restrict B ω i) ρ a = μ i a) ∧
      (∀ (r : ℕ) (e : Fin (r+1) ↪ I), T.comap e = SimpleGraph.pathGraph (r+1) →
        MarkovFlow.IsMarkovLaw (fun j => B (e j) → Bool)
          (marginal (fun ω j => restrict B ω (e j)) (fun ω => ρ ω / m))) ∧
      ∃ n : ℕ, ∃ F : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        ∀ u v, ‖F u - F v‖ = cutDistance ρ (fun ω => ω) u v := by
  let p : (i : I) → (B i → Bool) → ℝ := fun i a => μ i a / m
  have hp : ∀ i a, 0 ≤ p i a := fun i a => div_nonneg (hμ i a) hm.le
  have hp₁ : ∀ i, (∑ a, p i a) = 1 := by
    intro i
    simp only [p,← Finset.sum_div,hmass,div_self hm.ne']
  have hpcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (p i) c = marginal (rightTrace B i j) (p j) c := by
    intro i j h c
    dsimp only [p]
    rw [marginal_div,marginal_div,hcons i j h]
  have hpflip : ∀ i a, p i (flip (B i) a) = p i a := by
    intro i a
    dsimp only [p]
    rw [hflip]
  let R := TreeMarkov.interaction (fun i => B i → Bool) p (pairMass T B p)
  let hs := TreeMarkov.interaction_symmetric (fun i => B i → Bool) p _
    (pairMass_symmetric T B p hpcons)
  obtain ⟨hs',hn,hcomp⟩ := bag_couplings T B p hp hp₁ hpcons
  let q := globalMass T B hcover p R hs
  obtain ⟨hq,hq₁,hqmarg,hqsub⟩ := global_bag_law.{_,_,0} T hT B hcover hrun p R hs hn hcomp
  have hqflip : ∀ ω, q (flip V ω) = q ω := canonical_symmetric T B hcover p hpcons hpflip
  let ρ := fun ω => m * q ω
  have hρ : ∀ ω, 0 ≤ ρ ω := fun ω => mul_nonneg hm.le (hq ω)
  refine ⟨ρ,hρ,?_,?_,?_,?_,finite_cut_realization ρ (fun ω => ω) hρ⟩
  · change (∑ ω, m * q ω) = m
    rw [← Finset.mul_sum,hq₁,mul_one]
  · intro ω
    exact congrArg (m * ·) (hqflip ω)
  · intro i a
    change marginal _ (fun ω => m * q ω) a = _
    rw [marginal_mul]
    have hh : marginal (fun ω => restrict B ω i) q a = p i a := by
      apply Eq.trans ?_ (hqmarg i a)
      unfold marginal
      apply Finset.sum_congr rfl
      intro ω hω
      split_ifs <;> rfl
    rw [hh]
    exact mul_div_cancel₀ (μ i a) hm.ne'
  · intro r e he
    have hscale : (fun ω => ρ ω / m) = q := by
      funext ω
      exact mul_div_cancel_left₀ (q ω) hm.ne'
    rw [hscale]
    exact global_path T hT B hcover hrun p R hs hn hcomp r e he
end BoundedTreewidthL1.BagLabels

end OAI
