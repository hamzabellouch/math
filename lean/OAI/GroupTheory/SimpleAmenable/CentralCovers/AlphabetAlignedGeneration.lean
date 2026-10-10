import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AlignedPolygonGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AlphabetAlignedGeneration

noncomputable def alphabetHom {n m : ℕ} (ι : Fin n ↪ Fin m) :
    alternatingGroup (Fin n) →* Equiv.Perm (Fin m) :=
  (Equiv.Perm.viaEmbeddingHom ι).comp (alternatingGroup (Fin n)).subtype

theorem alphabet_sign {n m : ℕ} (ι : Fin n ↪ Fin m)
    (g : alternatingGroup (Fin n)) : alphabetHom ι g ∈ alternatingGroup (Fin m) := by
  classical
  change Equiv.Perm.sign (g.val.viaEmbedding ι) = 1
  rw [Equiv.Perm.viaEmbedding,Equiv.Perm.sign_extendDomain]
  exact g.property

theorem alphabet_support_subset {n m : ℕ} (ι : Fin n ↪ Fin m)
    (g : alternatingGroup (Fin n)) :
    (alphabetHom ι g).support ⊆ Finset.univ.map ι := by
  classical
  intro i hi
  by_contra hn
  have hn' : i ∉ Set.range ι := by simpa using hn
  exact (Equiv.Perm.mem_support.mp hi)
    (Equiv.Perm.viaEmbedding_apply_of_notMem g.val ι i hn')

theorem alphabet_support_card {n m : ℕ} (ι : Fin n ↪ Fin m)
    (g : alternatingGroup (Fin n)) : (alphabetHom ι g).support.card = g.val.support.card := by
  classical
  exact @Equiv.Perm.card_support_extend_domain (Fin n) _ _ (Fin m) _ _
    (Set.range ι.toFun) (Classical.decPred _) (Equiv.ofInjective ι.toFun ι.injective) g.val

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m) {n : ℕ}

theorem alphabet_initial_aligned (ι : Fin n ↪ Fin (m+1)) (j : Fin 5) :
    ConditionalAvailable (alphabetHom ι)
      (polygonAlignedGroup a r m hm (Finset.univ.map ι)) (initialTest a r j) := by
  let f := (conditionalHom (initialTest a r j)).comp (alphabetHom ι)
  have hh : Subgroup.closure {g : alternatingGroup (Fin n) |
      Equiv.Perm.IsThreeCycle g.val} ≤
      (polygonAlignedGroup a r m hm (Finset.univ.map ι)).comap f := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    have hc : (alphabetHom ι g).support.card ≤ 5 := by
      rw [alphabet_support_card, hg.card_support]
      omega
    exact alignedGroup_input _ _ _
      ((j,⟨alphabetHom ι g,alphabet_sign ι g,hc⟩) : SmallConditional m)
      (alphabet_support_subset ι g)
  rw [alternatingGroup.closure_isThreeCycles_eq_top] at hh
  exact fun g => hh (Subgroup.mem_top g)

theorem alphabet_translate_aligned (ι : Fin n ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ Set.range ι) (U : polygonAlgebra a)
    (hU : ConditionalAvailable (alphabetHom ι)
      (polygonAlignedGroup a r m hm (Finset.univ.map ι)) U)
    (u : CutRing × CutRing) :
    ConditionalAvailable (alphabetHom ι)
      (polygonAlignedGroup a r m hm (Finset.univ.map ι))
      ⟨translate a u ⁻¹' U.val,polygon_preimage_translate u U.property⟩ := by
  classical
  obtain ⟨k,d,hk,hd⟩ := sourceLatticeFullMap_prescribed a r m hm
    (Finset.univ.map ι) b (by simpa using hb) (fun _ => -u)
  intro g
  have hd' : ∀ i, alphabetHom ι g i ≠ i → d i = -u := by
    intro i hi
    exact hd i (alphabet_support_subset ι g (Equiv.Perm.mem_support.mpr hi))
  have he := conditional_translation_conjugate U (alphabetHom ι g) d (-u) hd'
  simp only [neg_neg] at he
  rw [he,← hk]
  exact alignedGroup_conjugate _ _ _ k (hU g)

variable [Group.IsPerfect (alternatingGroup (Fin n))]

noncomputable def alphabetAlignedBoolean (ι : Fin n ↪ Fin (m+1)) :
    BooleanSubalgebra (Set (GenericSquare a)) :=
  conditionalBoolean (alphabetHom ι) (polygonAlignedGroup a r m hm (Finset.univ.map ι))
    (alphabet_initial_aligned a r m hm ι 0)

theorem alphabetAlignedBoolean_initial (ι : Fin n ↪ Fin (m+1)) (j : Fin 5) :
    (initialTest a r j).val ∈ alphabetAlignedBoolean a r m hm ι :=
  ⟨(initialTest a r j).property,alphabet_initial_aligned a r m hm ι j⟩

theorem alphabetAlignedBoolean_translate (ι : Fin n ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ Set.range ι) (u : CutRing × CutRing)
    {U : Set (GenericSquare a)} (hU : U ∈ alphabetAlignedBoolean a r m hm ι) :
    translate a u ⁻¹' U ∈ alphabetAlignedBoolean a r m hm ι := by
  obtain ⟨hU,hU'⟩ := hU
  exact ⟨polygon_preimage_translate u hU,
    alphabet_translate_aligned a r m hm ι b hb ⟨U,hU⟩ hU' u⟩

theorem alphabetAlignedBoolean_coordinate (ι : Fin n ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ Set.range ι) (j : Fin 2) (z : CutRing) :
    halfPlane a (Fin.castLE (by omega) j) z ∈ alphabetAlignedBoolean a r m hm ι := by
  apply coordinate_cuts_generated _ j
    (fun u _ hU => alphabetAlignedBoolean_translate a r m hm ι b hb u hU)
  fin_cases j
  · exact alphabetAlignedBoolean_initial a r m hm ι 1
  · exact alphabetAlignedBoolean_initial a r m hm ι 2

theorem alphabet_polygon_aligned (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (ι : Fin n ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (U : polygonAlgebra a) : ConditionalAvailable (alphabetHom ι)
      (polygonAlignedGroup a r m hm (Finset.univ.map ι)) U := by
  let B := alphabetAlignedBoolean a r m hm ι
  have hcoord := alphabetAlignedBoolean_coordinate a r m hm ι b hb
  have htrans := fun u U hU => alphabetAlignedBoolean_translate a r m hm ι b hb u (U := U) hU
  have hv : U.val ∈ B := by
    apply polygon_induction (P := fun U => U ∈ B) ?_ BooleanSubalgebra.bot_mem
      (fun _ _ hU hV => BooleanSubalgebra.sup_mem hU hV)
      (fun _ hU => BooleanSubalgebra.compl_mem hU) U.property
    intro j z
    fin_cases j
    · exact hcoord 0 z
    · exact hcoord 1 z
    · exact slope_cuts_generated r hr B htrans hcoord 2 (Or.inl rfl)
        (alphabetAlignedBoolean_initial a r m hm ι 3) z
    · exact slope_cuts_generated r hr B htrans hcoord 3 (Or.inr rfl)
        (alphabetAlignedBoolean_initial a r m hm ι 4) z
  exact hv.choose_spec

end AlphabetAlignedGeneration

section CentralLaws

variable {D M H : Type*} [Group D] [Group M] [Group H]

def HasCentralLaw (v : D →* M) (f : D →* H) : Prop :=
  v.ker ≤ ((QuotientGroup.mk' (Subgroup.center H)).comp f).ker

theorem hasCentralLaw_iff (v : D →* M) (f : D →* H) :
    HasCentralLaw v f ↔ ∀ w, v w = 1 → f w ∈ Subgroup.center H := by
  constructor
  · intro h w hw
    have hh : f w ∈ (QuotientGroup.mk' (Subgroup.center H)).ker := h hw
    rwa [QuotientGroup.ker_mk'] at hh
  · intro h w hw
    change f w ∈ (QuotientGroup.mk' (Subgroup.center H)).ker
    rw [QuotientGroup.ker_mk']
    exact h w hw

theorem hasCentralLaw_iff_modelMap (v : D →* M) (f : D →* H)
    (hv : Function.Surjective v) : HasCentralLaw v f ↔
    ∃ φ : M →* H ⧸ Subgroup.center H,
      φ.comp v = (QuotientGroup.mk' (Subgroup.center H)).comp f := by
  constructor
  · intro h
    exact ⟨v.liftOfSurjective hv ⟨_,h⟩, v.liftOfRightInverse_comp _ _ _⟩
  · rintro ⟨φ,hφ⟩ w hw
    change QuotientGroup.mk' (Subgroup.center H) (f w) = 1
    have hh := DFunLike.congr_fun hφ w
    change φ (v w) = _ at hh
    rw [show v w = 1 from hw, map_one] at hh
    exact hh.symm

theorem centralLaw_modelMap_surjective (v : D →* M) (f : D →* H)
    (hf : Function.Surjective f) (φ : M →* H ⧸ Subgroup.center H)
    (hφ : φ.comp v = (QuotientGroup.mk' (Subgroup.center H)).comp f) :
    Function.Surjective φ := by
  intro x
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) x
  obtain ⟨w,rfl⟩ := hf y
  exact ⟨v w, DFunLike.congr_fun hφ w⟩

theorem HasCentralLaw.map {Q : Type*} [Group Q] {v : D →* M} {f : D →* H}
    (h : HasCentralLaw v f) (q : H →* Q) (hq : Function.Surjective q) :
    HasCentralLaw v (q.comp f) := by
  rw [hasCentralLaw_iff] at h ⊢
  intro w hw
  apply Subgroup.mem_center_iff.mpr
  intro x
  obtain ⟨y,rfl⟩ := hq x
  simpa only [map_mul, MonoidHom.comp_apply] using
    congrArg q (Subgroup.mem_center_iff.mp (h w hw) y)

theorem centralLaw_of_quotient [Group.IsPerfect H] (v : D →* M) (f : D →* H)
    (h : HasCentralLaw v ((QuotientGroup.mk' (Subgroup.center H)).comp f)) :
    HasCentralLaw v f := by
  rw [hasCentralLaw_iff] at h ⊢
  intro w hw
  have hh := h w hw
  rw [perfect_center_quotient] at hh
  have hh' : f w ∈ (QuotientGroup.mk' (Subgroup.center H)).ker := hh
  rwa [QuotientGroup.ker_mk'] at hh'

end CentralLaws

end SimpleAmenable
end
end

end OAI
