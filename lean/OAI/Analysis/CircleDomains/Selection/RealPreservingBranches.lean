import OAI.Analysis.CircleDomains.Rigidity.SubordinateMaskedBranches

namespace OAI

/-! Choose the supplied global real branch on real coordinates and the
local atlas branch on all remaining coordinates. -/

open Set Function Filter Classical
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_real_preserving_subordinate_branches
    {I : Type*} {n : ℕ} (L : Fin n → Type*)
    (G K : Set (ℝ × ℝ)) (hG : IsOpen G) (hK : IsClosed K)
    (M : Fin n → Set (ℝ × ℝ)) (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (P : ∀ l, L l → Set (ℝ × ℝ)) (v : ∀ l, L l → (ℝ × ℝ) → ℝ)
    (hv : ∀ l a, ContDiffOn ℝ ∞ (v l a) (G ∩ P l a))
    (hproj : ∀ l a x, x ∈ G ∩ P l a → (v l a x : UnitAddCircle) = f l x)
    (B Nbh : I → Set (ℝ × ℝ)) (hNbh : ∀ i, IsOpen (Nbh i))
    (hBN : ∀ i, B i ⊆ Nbh i)
    (hbranch : ∀ i l, Disjoint (Nbh i) (M l) ∨ ∃ a, Nbh i ⊆ interior (M l) ∩ P l a)
    (χ : (ℝ × ℝ) → ℝ) (hBG : ∀ i, B i ⊆ G) (hBK : ∀ i, Disjoint (B i) K)
    (hBχ : ∀ i, B i ⊆ interior {x | χ x = 1})
    {J : Type*} (ι : J → Fin n) (hι : Injective ι)
    (r : J → (ℝ × ℝ) → ℝ) (hr : ∀ j, ContDiffOn ℝ ∞ (r j) G)
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x) :
    ∃ (O : I → Set (ℝ × ℝ)) (present : I → Fin n → Prop)
      (u : I → Fin n → (ℝ × ℝ) → ℝ),
      (∀ i, IsOpen (O i) ∧ B i ⊆ O i ∧ O i ⊆ G ∧ Disjoint (O i) K ∧
        ∀ x ∈ O i, χ x = 1) ∧
      (∀ i l, ¬present i l → Disjoint (O i) (M l)) ∧
      (∀ i l, present i l → ContDiffOn ℝ ∞ (u i l) (O i)) ∧
      (∀ i l, present i l → ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x) ∧
      (∀ i l, present i l → O i ⊆ interior (M l)) ∧
      ∀ i j, u i (ι j) = r j := by
  obtain ⟨O, present, u, hO, habsent, hu, hproj', hOM⟩ :=
    exists_subordinate_masked_branches L G K hG hK M f P v hv hproj
      B Nbh hNbh hBN hbranch χ hBG hBK hBχ
  let u' (i : I) (l : Fin n) : (ℝ × ℝ) → ℝ :=
    if h : ∃ j, ι j = l then r (Classical.choose h) else u i l
  refine ⟨O, present, u', hO, habsent, ?_, ?_, hOM, ?_⟩
  · intro i l hl
    by_cases h : ∃ j, ι j = l
    · simpa only [u', dite_eq_left h] using (hr (Classical.choose h)).mono (hO i).2.2.1
    · simpa only [u', dite_eq_right h] using hu i l hl
  · intro i l hl x hx
    by_cases h : ∃ j, ι j = l
    · simpa only [u', dite_eq_left h, Classical.choose_spec h] using hrproj (Classical.choose h) x
    · simpa only [u', dite_eq_right h] using hproj' i l hl x hx
  · intro i j
    have h : ∃ j', ι j' = ι j := ⟨j, rfl⟩
    have hj : Classical.choose h = j := hι (Classical.choose_spec h)
    simp only [u', dite_eq_left h, hj]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
