import Mathlib

namespace OAI

namespace CubeShuffle.FiniteCharacters
open scoped BigOperators Classical

section Group
variable {G : Type*} [Group G] [Fintype G]

noncomputable def classRep (c : ConjClasses G) : G := (ConjClasses.exists_rep c).choose
omit [Fintype G] in
lemma classRep_spec (c : ConjClasses G) : ConjClasses.mk (classRep c) = c :=
  (ConjClasses.exists_rep c).choose_spec

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

noncomputable def characterClass (ρ : Representation ℂ G V) : ConjClasses G → ℂ :=
  fun c => ρ.character (classRep c)

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma characterClass_mk (ρ : Representation ℂ G V) (g : G) :
    characterClass ρ (ConjClasses.mk g) = ρ.character g := by
  have h := ConjClasses.mk_eq_mk_iff_isConj.mp (classRep_spec (ConjClasses.mk g))
  obtain ⟨p,hp⟩ := isConj_iff.mp h
  change ρ.character (classRep (ConjClasses.mk g)) = ρ.character g
  exact (Representation.char_conj ρ _ p).symm.trans (congrArg ρ.character hp)

noncomputable def characterDual (ρ : Representation ℂ G V) :
    (ConjClasses G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (Nat.card G : ℂ)⁻¹ * ∑ g, f (ConjClasses.mk g) * ρ.character g⁻¹
  map_add' f h := by simp [Finset.sum_add_distrib,add_mul,mul_add]
  map_smul' a f := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_assoc]
    rw [←Finset.mul_sum]
    ring

lemma characterDual_characterClass (ρ : Representation ℂ G V)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ] :
    characterDual ρ (characterClass σ) = if Nonempty (Representation.Equiv ρ σ) then 1 else 0 := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  change (Nat.card G : ℂ)⁻¹ * ∑ g, characterClass σ (ConjClasses.mk g) * ρ.character g⁻¹ = _
  simp only [characterClass_mk]
  exact Representation.char_orthonormal σ ρ

end Group

/-- A finite family of pairwise inequivalent irreducibles whose size is at
least the number of conjugacy classes is complete. This avoids assuming any
symmetric-group classification theorem. -/
theorem complete_of_card_conjugacy_le
    {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
    (hneq : ∀ i j, i ≠ j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
    (hcard : Nat.card (ConjClasses G) ≤ Fintype.card ι)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [Representation.IsIrreducible σ] :
    ∃ i, Nonempty (Representation.Equiv (ρ i) σ) := by
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  have horth (i j : ι) : characterDual (ρ i) (characterClass (ρ j)) = if i=j then 1 else 0 := by
    rw [characterDual_characterClass]
    by_cases hij : i=j
    · subst j
      simp only [ite_true]
      exact ite_eq_left ⟨Representation.Equiv.refl _⟩
    · rw [ite_eq_right hij,ite_eq_right (hneq i j hij)]
  have hLI : LinearIndependent ℂ (fun i => characterClass (ρ i)) := by
    apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun i => characterDual (ρ i))
    · intro i j hij
      exact (horth i j).trans (ite_eq_right hij)
    · intro i
      simpa using horth i i
  have heq : Fintype.card ι = Module.finrank ℂ (ConjClasses G → ℂ) := by
    apply Nat.le_antisymm hLI.fintype_card_le_finrank
    simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
      smul_eq_mul,mul_one,Nat.card_eq_fintype_card] using hcard
  have hspan := hLI.span_eq_top_of_card_eq_finrank' heq
  by_contra h
  push Not at h
  have hker : Submodule.span ℂ (Set.range (fun i => characterClass (ρ i))) ≤
      (characterDual σ).ker := by
    apply Submodule.span_le.mpr
    rintro f ⟨i,rfl⟩
    change characterDual σ (characterClass (ρ i)) = 0
    rw [characterDual_characterClass,ite_eq_right]
    rintro ⟨T⟩
    exact (h i).false T.symm
  rw [hspan] at hker
  have hz : characterDual σ (characterClass σ) = 0 := hker (show characterClass σ ∈ ⊤ from trivial)
  rw [characterDual_characterClass,ite_eq_left ⟨Representation.Equiv.refl σ⟩] at hz
  exact one_ne_zero hz

end CubeShuffle.FiniteCharacters

namespace CubeShuffle.FiniteCharacters
open Module
open scoped BigOperators Classical

variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
variable (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
variable (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
variable (hneq : ∀ i j, i≠j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
  (hcard : Nat.card (ConjClasses G)≤Fintype.card ι)
include hneq hcard

lemma character_expansion (f : ConjClasses G → ℂ) :
    f=∑ i, characterDual (ρ i) f • characterClass (ρ i) := by
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  have horth (i j : ι) : characterDual (ρ i) (characterClass (ρ j))=if i=j then 1 else 0 := by
    rw [characterDual_characterClass]
    by_cases h : i=j
    · subst j; rw [ite_eq_left ⟨Representation.Equiv.refl _⟩,ite_eq_left rfl]
    · rw [ite_eq_right h,ite_eq_right (hneq i j h)]
  have hLI : LinearIndependent ℂ (fun i => characterClass (ρ i)) := by
    apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun i => characterDual (ρ i))
    · intro i j hij; exact (horth i j).trans (ite_eq_right hij)
    · intro i; simpa using horth i i
  have heq : Fintype.card ι=Module.finrank ℂ (ConjClasses G → ℂ) := by
    apply Nat.le_antisymm hLI.fintype_card_le_finrank
    simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
      smul_eq_mul,mul_one,Nat.card_eq_fintype_card] using hcard
  let b := Basis.mk hLI (by rw [hLI.span_eq_top_of_card_eq_finrank' heq])
  have hb (i : ι) : b i=characterClass (ρ i) := Basis.mk_apply _ _ _
  have hd (i : ι) : b.coord i=characterDual (ρ i) := by
    apply b.ext
    intro j
    rw [hb,horth]
    simp only [←hb,Basis.coord_apply,Basis.repr_self,Finsupp.single_apply]
    split_ifs <;> simp_all
  have h := b.sum_repr f
  simpa only [hb,show ∀ i,b.repr f i=characterDual (ρ i) f from fun i => congrArg (fun l => l f) (hd i)] using h.symm

/-- The sum of squared dimensions is derived from the actual character basis,
without a regular-module decomposition assumption. -/
theorem sum_dimension_sq : ∑ i, (Module.finrank ℂ (V i))^2=Fintype.card G := by
  let f : ConjClasses G → ℂ := fun c => if c=ConjClasses.mk (1:G) then 1 else 0
  have hf (g : G) : f (ConjClasses.mk g)=if g=1 then 1 else 0 := by
    simp only [f,ConjClasses.mk_eq_mk_iff_isConj,isConj_one_left]
  have hd (i : ι) : characterDual (ρ i) f=(Fintype.card G:ℂ)⁻¹*(Module.finrank ℂ (V i):ℂ) := by
    change (Nat.card G:ℂ)⁻¹ * ∑ g, f (ConjClasses.mk g)*(ρ i).character g⁻¹=_
    simp only [hf,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,inv_one,
      Representation.char_one,Nat.card_eq_fintype_card]
  have he := congrFun (character_expansion V ρ hneq hcard f) (ConjClasses.mk (1:G))
  rw [hf,ite_eq_left rfl] at he
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hd,characterClass_mk,Representation.char_one] at he
  have hN : (Fintype.card G:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ i,(Module.finrank ℂ (V i):ℂ)^2)=(Fintype.card G:ℂ) := by
    calc
      _ = (Fintype.card G:ℂ) * ∑ i,(Fintype.card G:ℂ)⁻¹ *
          (Module.finrank ℂ (V i):ℂ)*(Module.finrank ℂ (V i):ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
      _ = _ := by rw [←he,mul_one]
  exact_mod_cast hs

end CubeShuffle.FiniteCharacters

end OAI
