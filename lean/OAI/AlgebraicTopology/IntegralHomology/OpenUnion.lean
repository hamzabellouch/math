import OAI.AlgebraicTopology.IntegralHomology.Excision

namespace OAI

noncomputable section

namespace Kaplansky

/-! Vanishing of homology under open unions and finite covers. -/

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X]

/-- Actual open-cover Mayer–Vietoris vanishing, with all three adjacent
groups explicit. No contractibility hypothesis is required. -/
theorem openCoverHomology_isZero (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hu : IsZero ((integralSingularHomology (n+1)).obj (TopCat.of U)))
    (hv : IsZero ((integralSingularHomology (n+1)).obj (TopCat.of V)))
    (hi : IsZero ((integralSingularHomology n).obj (TopCat.of ↥(U ∩ V)))) :
    IsZero ((integralSingularHomology (n+1)).obj (TopCat.of X)) := by
  have hs := homology_biprod_isZero _ _ (n+1) hu hv
  have he := (smallMayerVietorisSequence_shortExact U V).homology_exact₃ (n+1) n rfl
  exact (he.isZero_of_both_isZero hs hi).of_iso
    (openCoverSmallHomologyIso U V hU hV hUV (n+1)).symm

/-- Remove a redundant enclosing subtype without changing its topology. -/
def subspaceSubsetHomeomorph (U W : Set X) (h : U ⊆ W) :
    (Subtype.val ⁻¹' U : Set W) ≃ₜ U where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Mayer–Vietoris for an open union viewed as a subspace of the ambient space. -/
theorem openUnionHomology_isZero (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (n : ℕ)
    (hu : IsZero ((integralSingularHomology (n+1)).obj (TopCat.of U)))
    (hv : IsZero ((integralSingularHomology (n+1)).obj (TopCat.of V)))
    (hi : IsZero ((integralSingularHomology n).obj (TopCat.of ↥(U ∩ V)))) :
    IsZero ((integralSingularHomology (n+1)).obj (TopCat.of ↥(U ∪ V))) := by
  let U' : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let V' : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  have hcov : U' ∪ V' = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact x.property
  apply openCoverHomology_isZero U' V' (hU.preimage continuous_subtype_val)
    (hV.preimage continuous_subtype_val) hcov n
  · exact hu.of_iso (integralHomologyHomotopyIso
      (subspaceSubsetHomeomorph U (U ∪ V) Set.subset_union_left).toHomotopyEquiv (n+1))
  · exact hv.of_iso (integralHomologyHomotopyIso
      (subspaceSubsetHomeomorph V (U ∪ V) Set.subset_union_right).toHomotopyEquiv (n+1))
  · exact hi.of_iso (integralHomologyHomotopyIso
      (subspaceSubsetHomeomorph (U ∩ V) (U ∪ V)
        (fun x hx => Or.inl hx.1)).toHomotopyEquiv n)

end

open CategoryTheory Limits Set
section
variable {X ι : Type} [TopologicalSpace X]

/-- Finite open-cover homology vanishing from explicit bounds on every
nonempty intersection. The degree shift is the number of intersected sets. -/
theorem finiteOpenUnionHomology_isZero (S : Finset ι) (U : ι → Set X)
    (hS : S.Nonempty) (hopen : ∀ i ∈ S, IsOpen (U i)) (n : ℕ) (hcard : S.card ≤ n+1)
    (hinter : ∀ T : Finset ι, T.Nonempty → T ⊆ S → ∀ q : ℕ, n < q + T.card →
      IsZero ((integralSingularHomology q).obj (TopCat.of (⋂ i ∈ T, U i)))) :
    IsZero ((integralSingularHomology n).obj (TopCat.of (⋃ i ∈ S, U i))) := by
  classical
  induction S using Finset.induction_on generalizing U n with
  | empty => exact (Finset.not_nonempty_empty hS).elim
  | @insert a S ha ih =>
    by_cases hs : S.Nonempty
    · have hn : 0 < n := by
        rw [Finset.card_insert_of_notMem ha] at hcard
        have := Finset.card_pos.mpr hs
        omega
      have hU := hinter {a} (by simp) (by simp) n (by simp)
      have hea : (⋂ i ∈ ({a} : Finset ι), U i) = U a := by ext x; simp
      rw [hea] at hU
      have hV : IsZero ((integralSingularHomology n).obj (TopCat.of (⋃ i ∈ S, U i))) :=
        ih U hs (fun i hi => hopen i (Finset.mem_insert_of_mem hi)) n
          (by rw [Finset.card_insert_of_notMem ha] at hcard; omega)
          (fun T ht hts q hq => hinter T ht (hts.trans (Finset.subset_insert a S)) q hq)
      have hI : IsZero ((integralSingularHomology (n-1)).obj
          (TopCat.of (⋃ i ∈ S, U a ∩ U i))) := by
        apply ih (fun i => U a ∩ U i) hs
          (fun i hi => (hopen a (by simp)).inter (hopen i (Finset.mem_insert_of_mem hi)))
          (n-1) (by rw [Finset.card_insert_of_notMem ha] at hcard; omega)
        intro T ht hts q hq
        have hat : a ∉ T := fun h => ha (hts h)
        have hb := hinter (insert a T) (by simp)
          (Finset.insert_subset_insert a hts) q (by
            rw [Finset.card_insert_of_notMem hat]
            omega)
        have he : (⋂ i ∈ T, U a ∩ U i) = ⋂ i ∈ insert a T, U i := by
          ext x
          simp only [mem_iInter, Finset.mem_insert]
          constructor
          · intro hx i hi
            rcases hi with rfl | hi
            · obtain ⟨j, hj⟩ := ht
              exact (hx j hj).1
            · exact (hx i hi).2
          · intro hx i hi
            exact ⟨hx a (Or.inl rfl), hx i (Or.inr hi)⟩
        rw [he]
        exact hb
      have heI : (⋃ i ∈ S, U a ∩ U i) = U a ∩ (⋃ i ∈ S, U i) := by
        ext x
        simp only [mem_iUnion, mem_inter_iff]
        constructor
        · rintro ⟨i, hi, hxa, hxi⟩
          exact ⟨hxa, i, hi, hxi⟩
        · rintro ⟨hxa, i, hi, hxi⟩
          exact ⟨i, hi, hxa, hxi⟩
      rw [heI] at hI
      have heN : (n-1)+1 = n := by omega
      have hz := openUnionHomology_isZero (U a) (⋃ i ∈ S, U i)
        (hopen a (by simp))
        (isOpen_iUnion (fun i => isOpen_iUnion (fun hi => hopen i (Finset.mem_insert_of_mem hi))))
        (n-1) (heN.symm ▸ hU) (heN.symm ▸ hV) hI
      have heW : (⋃ i ∈ insert a S, U i) = U a ∪ (⋃ i ∈ S, U i) := by
        ext x; simp
      rw [heW]
      simpa only [heN] using hz
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst S
      have hz := hinter {a} (by simp) (by simp) n (by simp)
      have hea : (⋂ i ∈ ({a} : Finset ι), U i) = U a := by ext x; simp
      have heb : (⋃ i ∈ insert a (∅ : Finset ι), U i) = U a := by ext x; simp
      rw [hea] at hz
      rw [heb]
      exact hz

end

end Kaplansky

end

end OAI
