import OAI.Probability.SwitchChain.SwitchFlip
import OAI.Probability.SwitchChain.FourVertexSwitch

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossToggle

open SwitchFlip

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}

def crossProposal (i j k l : Fin n) (h : FourDistinct i j k l) : SwitchProposal n :=
  fourVertexProposal i k l j
    (show FourDistinct i k l j from
      ⟨h.2.1, h.2.2.1, h.1, h.2.2.2.2.2, h.2.2.2.1.symm, h.2.2.2.2.1.symm⟩)

theorem crossProposal_left (i j k l : Fin n) (h : FourDistinct i j k l) :
    SwitchPairFiber.Crosses (crossProposal i j k l h) {i, j} := by
  rcases h with ⟨hij, hik, hil, hjk, hjl, hkl⟩
  intro u v huv
  simp only [crossProposal, removedMatching_fourVertexProposal,
    addedMatching_fourVertexProposal] at huv
  rcases huv with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  all_goals simp_all [Ne.symm]

theorem crossProposal_right (i j k l : Fin n) (h : FourDistinct i j k l) :
    SwitchPairFiber.Crosses (crossProposal i j k l h) {k, l} := by
  rcases h with ⟨hij, hik, hil, hjk, hjl, hkl⟩
  intro u v huv
  simp only [crossProposal, removedMatching_fourVertexProposal,
    addedMatching_fourVertexProposal] at huv
  rcases huv with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  all_goals simp_all [Ne.symm]

theorem crossProposal_swap_pairs (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct k l i j) :
    crossProposal i j k l h = crossProposal k l i j h' := by
  apply SwitchProposal.ext_matchings
  · ext u v
    simp only [crossProposal, removedMatching_fourVertexProposal]
    tauto
  · ext u v
    simp only [crossProposal, addedMatching_fourVertexProposal]
    tauto

theorem crossProposal_swap_left (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct j i k l) :
    crossProposal j i k l h' = reverseProposal (crossProposal i j k l h) := by
  apply SwitchProposal.ext_matchings
  · ext u v
    simp only [crossProposal, removedMatching_reverse,
      removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]
    tauto
  · ext u v
    simp only [crossProposal, addedMatching_reverse,
      removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]
    tauto

theorem crossProposal_swap_right (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct i j l k) :
    crossProposal i j l k h' = reverseProposal (crossProposal i j k l h) := by
  apply SwitchProposal.ext_matchings
  · ext u v
    simp only [crossProposal, removedMatching_reverse,
      removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]
  · ext u v
    simp only [crossProposal, addedMatching_reverse,
      removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]

theorem crossProjection_swap_left (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct j i k l) :
    projection (d := d) (crossProposal j i k l h') =
      projection (crossProposal i j k l h) := by
  rw [crossProposal_swap_left i j k l h h', projection_reverse]

theorem crossProjection_swap_right (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct i j l k) :
    projection (d := d) (crossProposal i j l k h') =
      projection (crossProposal i j k l h) := by
  rw [crossProposal_swap_right i j k l h h', projection_reverse]

abbrev VertexPair (n : ℕ) := {a : Finset (Fin n) // a.card = 2}

def first (a : VertexPair n) : Fin n :=
  Classical.choose (Finset.card_eq_two.mp a.property)

def second (a : VertexPair n) : Fin n :=
  Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp a.property))

theorem first_ne_second (a : VertexPair n) : first a ≠ second a :=
  (Classical.choose_spec (Classical.choose_spec (Finset.card_eq_two.mp a.property))).1

theorem pair_eq (a : VertexPair n) : a.val = {first a, second a} :=
  (Classical.choose_spec (Classical.choose_spec (Finset.card_eq_two.mp a.property))).2

theorem endpoints_cases (a : VertexPair n) (i j : Fin n) (h : a.val = {i, j}) :
    (first a = i ∧ second a = j) ∨ (first a = j ∧ second a = i) := by
  have hf : first a = i ∨ first a = j := by
    have hm : first a ∈ a.val := by rw [pair_eq]; simp
    simpa only [h, Finset.mem_insert, Finset.mem_singleton] using hm
  have hs : second a = i ∨ second a = j := by
    have hm : second a ∈ a.val := by rw [pair_eq]; simp
    simpa only [h, Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hf with hf | hf <;> rcases hs with hs | hs
  · exact False.elim (first_ne_second a (hf.trans hs.symm))
  · exact Or.inl ⟨hf, hs⟩
  · exact Or.inr ⟨hf, hs⟩
  · exact False.elim (first_ne_second a (hf.trans hs.symm))

theorem endpoints_distinct (a b : VertexPair n) (h : Disjoint a.val b.val) :
    FourDistinct (first a) (second a) (first b) (second b) := by
  have hfirst (x : VertexPair n) : first x ∈ x.val := by rw [pair_eq]; simp
  have hsecond (x : VertexPair n) : second x ∈ x.val := by rw [pair_eq]; simp
  have hn := Finset.disjoint_left.mp h
  refine ⟨first_ne_second a, ?_, ?_, ?_, ?_, first_ne_second b⟩
  · intro he; exact hn (hfirst a) (he ▸ hfirst b)
  · intro he; exact hn (hfirst a) (he ▸ hsecond b)
  · intro he; exact hn (hsecond a) (he ▸ hfirst b)
  · intro he; exact hn (hsecond a) (he ▸ hsecond b)

def pairProposal (a b : VertexPair n) (h : Disjoint a.val b.val) : SwitchProposal n :=
  crossProposal (first a) (second a) (first b) (second b) (endpoints_distinct a b h)

theorem pairProposal_symm (a b : VertexPair n) (h : Disjoint a.val b.val) :
    pairProposal a b h = pairProposal b a h.symm :=
  crossProposal_swap_pairs _ _ _ _ _ _

theorem pairProposal_crosses_left (a b : VertexPair n) (h : Disjoint a.val b.val) :
    SwitchPairFiber.Crosses (pairProposal a b h) a.val := by
  rw [pair_eq a]
  exact crossProposal_left _ _ _ _ _

theorem pairProposal_crosses_right (a b : VertexPair n) (h : Disjoint a.val b.val) :
    SwitchPairFiber.Crosses (pairProposal a b h) b.val := by
  rw [pair_eq b]
  exact crossProposal_right _ _ _ _ _

def pairProjection (a b : VertexPair n) :
    PairResampling.StateSpace n d →L[ℝ] PairResampling.StateSpace n d :=
  if h : Disjoint a.val b.val then projection (pairProposal a b h) else 0

theorem pairProjection_of_disjoint (a b : VertexPair n) (h : Disjoint a.val b.val) :
    pairProjection (d := d) a b = projection (pairProposal a b h) := by
  simp [pairProjection, h]

theorem pairProjection_eq_explicit (a b : VertexPair n)
    (h : Disjoint a.val b.val) (i j k l : Fin n)
    (ha : a.val = {i, j}) (hb : b.val = {k, l}) (hf : FourDistinct i j k l) :
    pairProjection (d := d) a b = projection (crossProposal i j k l hf) := by
  rw [pairProjection_of_disjoint a b h]
  obtain (⟨hi, hj⟩ | ⟨hi, hj⟩) := endpoints_cases a i j ha
  all_goals obtain (⟨hk, hl⟩ | ⟨hk, hl⟩) := endpoints_cases b k l hb
  all_goals simp only [pairProposal, hi, hj, hk, hl]
  · exact crossProjection_swap_right i j k l hf _
  · exact crossProjection_swap_left i j k l hf _
  · have hm : FourDistinct j i k l :=
      ⟨hf.1.symm, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.1, hf.2.2.1, hf.2.2.2.2.2⟩
    rw [crossProjection_swap_right j i k l hm, crossProjection_swap_left i j k l hf]

theorem pairProjection_symm (a b : VertexPair n) :
    pairProjection (d := d) a b = pairProjection b a := by
  by_cases h : Disjoint a.val b.val
  · rw [pairProjection_of_disjoint a b h, pairProjection_of_disjoint b a h.symm,
      pairProposal_symm a b h]
  · have hr : ¬ Disjoint b.val a.val := fun hr => h hr.symm
    simp [pairProjection, h, hr]

theorem pairProjection_isSymmetric (a b : VertexPair n) :
    (pairProjection (d := d) a b).toLinearMap.IsSymmetric := by
  by_cases h : Disjoint a.val b.val
  · rw [pairProjection_of_disjoint a b h]
    exact projection_symmetric _
  · simp only [pairProjection, dite_eq_right h]
    intro f g
    simp

theorem pairProjection_idempotent (a b : VertexPair n)
    (f : PairResampling.StateSpace n d) :
    pairProjection a b (pairProjection a b f) = pairProjection a b f := by
  by_cases h : Disjoint a.val b.val
  · rw [pairProjection_of_disjoint a b h, projection_idempotent]
  · simp [pairProjection, h]

theorem pairProjection_mem_left_orthogonal (a b : VertexPair n)
    (f : PairResampling.StateSpace n d) :
    pairProjection a b f ∈ (PairResampling.fiberSpace n d a.val)ᗮ := by
  by_cases h : Disjoint a.val b.val
  · rw [pairProjection_of_disjoint a b h]
    exact projection_mem_orthogonal _ _ (pairProposal_crosses_left a b h) f
  · simp [pairProjection, h]

theorem pairProjection_mem_right_orthogonal (a b : VertexPair n)
    (f : PairResampling.StateSpace n d) :
    pairProjection a b f ∈ (PairResampling.fiberSpace n d b.val)ᗮ := by
  rw [pairProjection_symm a b]
  exact pairProjection_mem_left_orthogonal b a f

theorem pairProjection_mem_common (a b : VertexPair n)
    (f : PairResampling.StateSpace n d) :
    pairProjection a b f ∈
      (PairResampling.fiberSpace n d a.val ⊔ PairResampling.fiberSpace n d b.val)ᗮ := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [inner_add_left, pairProjection_mem_left_orthogonal a b f y hy,
    pairProjection_mem_right_orthogonal a b f z hz, add_zero]

theorem pairProjection_energy (a b : VertexPair n)
    (f : PairResampling.StateSpace n d) :
    ⟪f, pairProjection a b f⟫ = ‖pairProjection a b f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h := pairProjection_isSymmetric a b f (pairProjection a b f)
  change ⟪pairProjection a b f, pairProjection a b f⟫ =
    ⟪f, pairProjection a b (pairProjection a b f)⟫ at h
  simpa only [pairProjection_idempotent] using h.symm

end Problem315.CrossToggle

end

end OAI
