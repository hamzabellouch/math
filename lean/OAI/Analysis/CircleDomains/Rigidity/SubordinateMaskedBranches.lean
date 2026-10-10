import OAI.Analysis.CircleDomains.Rigidity.MaskBranchCollars
import OAI.Analysis.CircleDomains.Topology.GraphBoundaryBranches

namespace OAI

/-! A boundary lying in a common local branch neighborhood gives the
actual masked collar data. The finite graph condition then chooses one
active coordinate on each filling boundary. -/

open Set Function Filter Classical
open scoped Topology ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem exists_subordinate_masked_branches
    {I : Type*} {n : ℕ} (L : Fin n → Type*)
    (G K : Set (ℝ × ℝ)) (hG : IsOpen G) (hK : IsClosed K)
    (M : Fin n → Set (ℝ × ℝ)) (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (P : ∀ l, L l → Set (ℝ × ℝ))
    (v : ∀ l, L l → (ℝ × ℝ) → ℝ)
    (hv : ∀ l a, ContDiffOn ℝ ∞ (v l a) (G ∩ P l a))
    (hproj : ∀ l a x, x ∈ G ∩ P l a → (v l a x : UnitAddCircle) = f l x)
    (B Nbh : I → Set (ℝ × ℝ)) (hNbh : ∀ i, IsOpen (Nbh i))
    (hBN : ∀ i, B i ⊆ Nbh i)
    (hbranch : ∀ i l, Disjoint (Nbh i) (M l) ∨ ∃ a, Nbh i ⊆ interior (M l) ∩ P l a)
    (χ : (ℝ × ℝ) → ℝ)
    (hBG : ∀ i, B i ⊆ G) (hBK : ∀ i, Disjoint (B i) K)
    (hBχ : ∀ i, B i ⊆ interior {x | χ x = 1}) :
    ∃ (O : I → Set (ℝ × ℝ)) (present : I → Fin n → Prop)
      (u : I → Fin n → (ℝ × ℝ) → ℝ),
      (∀ i, IsOpen (O i) ∧ B i ⊆ O i ∧ O i ⊆ G ∧ Disjoint (O i) K ∧
        ∀ x ∈ O i, χ x = 1) ∧
      (∀ i l, ¬present i l → Disjoint (O i) (M l)) ∧
      (∀ i l, present i l → ContDiffOn ℝ ∞ (u i l) (O i)) ∧
      (∀ i l, present i l → ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x) ∧
      ∀ i l, present i l → O i ⊆ interior (M l) := by
  let present (i : I) (l : Fin n) : Prop := ¬Disjoint (Nbh i) (M l)
  have ha (i : I) (l : Fin n) (h : present i l) : ∃ a, Nbh i ⊆ interior (M l) ∩ P l a :=
    (hbranch i l).resolve_left h
  let u (i : I) (l : Fin n) : (ℝ × ℝ) → ℝ :=
    if h : present i l then v l (Classical.choose (ha i l h)) else fun _ => 0
  let O (i : I) := ((G ∩ Nbh i) ∩ interior {x | χ x = 1}) ∩ Kᶜ
  have hON (i : I) : O i ⊆ Nbh i := fun _ hx => hx.1.1.2
  refine ⟨O, present, u, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨((hG.inter (hNbh i)).inter isOpen_interior).inter hK.isOpen_compl,
      ?_, fun _ hx => hx.1.1.1, ?_, fun x hx => (show x ∈ {y | χ y = 1} from interior_subset hx.1.2)⟩
    · intro x hx
      exact ⟨⟨⟨hBG i hx, hBN i hx⟩, hBχ i hx⟩,
        fun hk => Set.disjoint_left.mp (hBK i) hx hk⟩
    · exact disjoint_compl_left.mono_left inter_subset_right
  · intro i l h
    exact (not_not.mp h).mono_left (hON i)
  · intro i l h
    simp only [u, dite_eq_left h]
    apply (hv l (Classical.choose (ha i l h))).mono
    intro x hx
    exact ⟨hx.1.1.1, (Classical.choose_spec (ha i l h) (hON i hx)).2⟩
  · intro i l h x hx
    simp only [u, dite_eq_left h]
    exact hproj l (Classical.choose (ha i l h)) x
      ⟨hx.1.1.1, (Classical.choose_spec (ha i l h) (hON i hx)).2⟩
  · intro i l h x hx
    exact (Classical.choose_spec (ha i l h) (hON i hx)).1

end CircleDomainRigidity.FiniteTransfer

end

end OAI
