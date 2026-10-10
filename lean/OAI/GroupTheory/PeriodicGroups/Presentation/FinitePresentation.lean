import Mathlib
import OAI.GroupTheory.PeriodicGroups.Matrices.ElementaryGenerators

namespace OAI

section
noncomputable section
open Classical Matrix
namespace SourceBurnside.Stability.LinearAlgebra

lemma extend_independent_map {F W κ : Type*} [Field F] [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] {v w : κ → W}
    (hv : LinearIndependent F v) (hw : LinearIndependent F w) :
    ∃ T : W ≃ₗ[F] W, ∀ k, T (v k) = w k := by
  let f := hv.linearCombinationEquiv.symm.trans hw.linearCombinationEquiv
  obtain ⟨T, hT⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨T, fun k => ?_⟩
  have hh := hT (hv.linearCombinationEquiv (Finsupp.single k 1))
  simpa [f] using hh.symm

variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
include hI

theorem complete_columns {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (j : κ ↪ ι) (v : κ → ι → R)
    (hv : LinearIndependent (ZMod 2) (fun k i => ε (v k i))) :
    ∃ U : (Matrix ι ι R)ˣ, ∀ k i, U.val i (j k) = v k i := by
  have he : LinearIndependent (ZMod 2) (fun k => (Pi.basisFun (ZMod 2) ι) (j k)) :=
    (Pi.basisFun (ZMod 2) ι).linearIndependent.comp j j.injective
  obtain ⟨T, hT⟩ := extend_independent_map he hv
  let N : (Matrix ι ι (ZMod 2))ˣ :=
    Units.map LinearMap.toMatrixAlgEquiv'.toMonoidHom
      (LinearMap.GeneralLinearGroup.ofLinearEquiv T)
  have hN : ∀ k i, N.val i (j k) = ε (v k i) := by
    intro k i
    change (LinearMap.toMatrix' T.toLinearMap) i (j k) = _
    rw [LinearMap.toMatrix'_apply]
    have hh := congrFun (hT k) i
    simpa using hh
  let A : Matrix ι ι R := Matrix.of (fun i l =>
    if h : ∃k, j k = l then v h.choose i else algebraMap (ZMod 2) R (N.val i l))
  have hA : ε.toRingHom.mapMatrix A = N.val := by
    ext i l
    change ε (if h : ∃ k, j k = l then v h.choose i else _) = _
    split_ifs with h
    · rw [← hN, h.choose_spec]
    · simp
  have hu : IsUnit A := (isUnit_matrix_iff ε hI A).mpr (by rw [hA]; exact N.isUnit)
  obtain ⟨U, hU⟩ := hu
  refine ⟨U, fun k i => ?_⟩
  rw [hU]
  change (if h : ∃k', j k' = j k then v h.choose i else _) = _
  split_ifs with h
  · rw [j.injective h.choose_spec]
  · exact (h ⟨k, rfl⟩).elim

end SourceBurnside.Stability.LinearAlgebra

end

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
open Classical MatrixGenerators
variable {R : Type*} [Ring R]

inductive Generator (ι : Type*) (R : Type*) [Ring R] where
  | root (i j : ι) (h : i ≠ j) (a : R)
  | diag (i : ι) (u : Rˣ)

namespace Generator
variable {ι κ : Type*}
def support [DecidableEq ι] : Generator ι R → Finset ι
  | .root i j _ _ => {i,j}
  | .diag i _ => {i}

def map (e : ι ↪ κ) : Generator ι R → Generator κ R
  | .root i j h a => .root (e i) (e j) (e.injective.ne h) a
  | .diag i u => .diag (e i) u

variable [Fintype ι] [DecidableEq ι]
def matrix : Generator ι R → (Matrix ι ι R)ˣ
  | .root i j h a => elementary i j h a
  | .diag i u => singleDiagonal i u
end Generator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixWord : FreeGroup (Generator ι R) →* (Matrix ι ι R)ˣ :=
  FreeGroup.lift Generator.matrix

def supported (S : Finset ι) : Subgroup (FreeGroup (Generator ι R)) :=
  Subgroup.closure (FreeGroup.of '' {g | g.support ⊆ S})

def relations : Set (FreeGroup (Generator ι R)) :=
  {w | matrixWord w = 1 ∧ ∃S : Finset ι, S.card ≤ 5 ∧ w ∈ supported S}

abbrev Group := PresentedGroup (relations (ι := ι) (R := R))

def evaluate : Group (ι := ι) (R := R) →* (Matrix ι ι R)ˣ :=
  PresentedGroup.toGroup (fun _ h => h.1)

def gen (g : Generator ι R) : Group (ι := ι) (R := R) := PresentedGroup.of g

@[simp] lemma evaluate_gen (g : Generator ι R) : evaluate (gen g) = g.matrix :=
  PresentedGroup.toGroup.of _

lemma evaluate_surjective [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) : Function.Surjective (evaluate (ι := ι) (R := R)) := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  intro U _
  have hU := LinearAlgebra.all_matrix_generated ε hI U
  apply (show generated ≤ evaluate.range from ?_) hU
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨i,j,h,a,rfl⟩ | ⟨i,u,rfl⟩)
  · exact ⟨gen (.root i j h a), evaluate_gen _⟩
  · exact ⟨gen (.diag i u), evaluate_gen _⟩

lemma supported_univ : supported (R := R) (Finset.univ : Finset ι) = ⊤ := by
  unfold supported
  simp only [Finset.subset_univ, Set.ofPred_true, Set.image_univ, FreeGroup.closure_range_of]

theorem evaluate_injective_small (hι : Fintype.card ι ≤ 5) :
    Function.Injective (evaluate (ι := ι) (R := R)) := by
  apply (MonoidHom.ker_eq_bot_iff evaluate).mp
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective relations g
  change PresentedGroup.mk relations w = 1
  have hm : matrixWord w = 1 := hg
  apply PresentedGroup.one_of_mem
  exact ⟨hm, Finset.univ, by simpa using hι, by rw [supported_univ]; trivial⟩

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.MatrixGenerators
noncomputable section
open Classical Matrix
variable {R ι κ : Type*} [Ring R] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def embeddingEquiv (e : ι ↪ κ) : ι ⊕ {k // k ∉ Set.range e} ≃ κ :=
  (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

omit [Fintype κ] [DecidableEq ι] in
@[simp] lemma embeddingEquiv_inl (e : ι ↪ κ) (i : ι) : embeddingEquiv e (Sum.inl i) = e i := rfl
omit [Fintype κ] [DecidableEq ι] in
@[simp] lemma embeddingEquiv_inr (e : ι ↪ κ) (i : {k // k ∉ Set.range e}) :
    embeddingEquiv e (Sum.inr i) = i.val := rfl

def embed (e : ι ↪ κ) : (Matrix ι ι R)ˣ →* (Matrix κ κ R)ˣ :=
  (relabel (embeddingEquiv e)).comp (blockInclusion (κ := {k // k ∉ Set.range e}))

@[simp] lemma embed_elementary (e : ι ↪ κ) (i j : ι) (h : i ≠ j) (a : R) :
    embed e (elementary i j h a) = elementary (e i) (e j) (e.injective.ne h) a := by
  simp only [embed,MonoidHom.comp_apply,blockInclusion_elementary,relabel_elementary,
    embeddingEquiv_inl]

lemma blockInclusion_singleDiagonal (i : ι) (u : Rˣ) :
    blockInclusion (κ := κ) (singleDiagonal i u) = singleDiagonal (Sum.inl i) u := by
  rw [singleDiagonal,blockInclusion_diagonal,singleDiagonal]
  congr 1
  funext j
  cases j <;> simp

@[simp] lemma embed_singleDiagonal (e : ι ↪ κ) (i : ι) (u : Rˣ) :
    embed e (singleDiagonal i u) = singleDiagonal (e i) u := by
  simp only [embed,MonoidHom.comp_apply,blockInclusion_singleDiagonal,relabel_singleDiagonal,
    embeddingEquiv_inl]

lemma embed_entry (e : ι ↪ κ) (U : (Matrix ι ι R)ˣ) (i j : ι) :
    (embed e U).val (e i) (e j) = U.val i j := by
  change (Matrix.fromBlocks U.val 0 0 (1 : Matrix {k // k ∉ Set.range e} _ R))
    ((embeddingEquiv e).symm (e i)) ((embeddingEquiv e).symm (e j)) = _
  rw [← embeddingEquiv_inl e i,← embeddingEquiv_inl e j,
    Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rfl

lemma embed_injective (e : ι ↪ κ) : Function.Injective (embed (R := R) e) := by
  intro U V hh
  apply Units.ext
  ext i j
  simpa only [embed_entry] using congrArg (fun B : (Matrix κ κ R)ˣ => B.val (e i) (e j)) hh

lemma embed_off_column (e : ι ↪ κ) (U : (Matrix ι ι R)ˣ) (j : κ) (hj : j ∉ Set.range e)
    (i : κ) : (embed e U).val i j = (1 : Matrix κ κ R) i j := by
  let j' : {k // k ∉ Set.range e} := ⟨j,hj⟩
  obtain ⟨i',rfl⟩ := (embeddingEquiv e).surjective i
  change (Matrix.fromBlocks U.val 0 0 (1 : Matrix {k // k ∉ Set.range e} _ R))
    ((embeddingEquiv e).symm (embeddingEquiv e i'))
    ((embeddingEquiv e).symm (embeddingEquiv e (Sum.inr j'))) =
      if embeddingEquiv e i' = embeddingEquiv e (Sum.inr j') then 1 else 0
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rcases i' with i' | i'
  · change 0 = if _ then (1 : R) else 0
    exact (ite_eq_right ((embeddingEquiv e).injective.ne (Sum.inl_ne_inr))).symm
  · change (if i' = j' then (1 : R) else 0) = if _ then 1 else 0
    congr 1
    exact propext (((embeddingEquiv e).injective.eq_iff.trans Sum.inr_injective.eq_iff).symm)

lemma embed_off_row (e : ι ↪ κ) (U : (Matrix ι ι R)ˣ) (i : κ) (hi : i ∉ Set.range e)
    (j : κ) : (embed e U).val i j = (1 : Matrix κ κ R) i j := by
  let i' : {k // k ∉ Set.range e} := ⟨i,hi⟩
  obtain ⟨j',rfl⟩ := (embeddingEquiv e).surjective j
  change (Matrix.fromBlocks U.val 0 0 (1 : Matrix {k // k ∉ Set.range e} _ R))
    ((embeddingEquiv e).symm (embeddingEquiv e (Sum.inr i')))
    ((embeddingEquiv e).symm (embeddingEquiv e j')) =
      if embeddingEquiv e (Sum.inr i') = embeddingEquiv e j' then 1 else 0
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rcases j' with j' | j'
  · change 0 = if _ then (1 : R) else 0
    exact (ite_eq_right ((embeddingEquiv e).injective.ne (Sum.inr_ne_inl))).symm
  · change (if i' = j' then (1 : R) else 0) = if _ then 1 else 0
    congr 1
    exact propext (((embeddingEquiv e).injective.eq_iff.trans Sum.inr_injective.eq_iff).symm)

end
end SourceBurnside.Stability.MatrixGenerators

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma generator_map_matrix (e : ι ↪ κ) (g : Generator ι R) :
    (g.map e).matrix = embed e g.matrix := by
  cases g <;> simp [Generator.map,Generator.matrix]

lemma matrixWord_map (e : ι ↪ κ) :
    matrixWord.comp (FreeGroup.map (Generator.map e)) = (embed e).comp (matrixWord (R := R)) := by
  apply FreeGroup.ext_hom
  intro g
  simpa [matrixWord] using generator_map_matrix e g

omit [Fintype ι] [Fintype κ] in
lemma supported_map (e : ι ↪ κ) (S : Finset ι) :
    supported (R := R) S ≤ (supported (S.image e)).comap (FreeGroup.map (Generator.map e)) := by
  apply (Subgroup.closure_le _).mpr
  rintro w ⟨g,hg,rfl⟩
  change FreeGroup.map (Generator.map e) (FreeGroup.of g) ∈ supported _
  rw [FreeGroup.map.of]
  apply Subgroup.subset_closure
  refine ⟨g.map e,?_,rfl⟩
  cases g with
  | root i j h a =>
    change ({i,j} : Finset ι) ⊆ S at hg
    change ({e i,e j} : Finset κ) ⊆ S.image e
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff] at hg ⊢
    exact ⟨Finset.mem_image.mpr ⟨i,hg.1,rfl⟩,Finset.mem_image.mpr ⟨j,hg.2,rfl⟩⟩
  | diag i u =>
    change ({i} : Finset ι) ⊆ S at hg
    change ({e i} : Finset κ) ⊆ S.image e
    simp only [Finset.singleton_subset_iff] at hg ⊢
    exact Finset.mem_image.mpr ⟨i,hg,rfl⟩

def inclusion (e : ι ↪ κ) : Group (ι := ι) (R := R) →* Group (ι := κ) (R := R) :=
  PresentedGroup.map (FreeGroup.map (Generator.map e)) (by
    intro w hw
    refine ⟨?_,?_⟩
    · change matrixWord (FreeGroup.map (Generator.map e) w) = 1
      rw [← MonoidHom.comp_apply,matrixWord_map,MonoidHom.comp_apply,hw.1,map_one]
    · obtain ⟨S,hS,hwS⟩ := hw.2
      exact ⟨S.image e,Finset.card_image_le.trans hS,supported_map e S hwS⟩)

@[simp] lemma inclusion_gen (e : ι ↪ κ) (g : Generator ι R) :
    inclusion e (gen g) = gen (g.map e) := by
  change PresentedGroup.mk _ (FreeGroup.map (Generator.map e) (FreeGroup.of g)) = _
  rw [FreeGroup.map.of]
  rfl

lemma evaluate_inclusion (e : ι ↪ κ) : (evaluate (R := R)).comp (inclusion e) = (embed e).comp evaluate := by
  apply PresentedGroup.ext
  intro g
  change evaluate (inclusion e (gen g)) = embed e (evaluate (gen g))
  rw [inclusion_gen,evaluate_gen,evaluate_gen,generator_map_matrix]

@[simp] lemma evaluate_inclusion_apply (e : ι ↪ κ) (g : Group (ι := ι) (R := R)) :
    evaluate (inclusion e g) = embed e (evaluate g) := DFunLike.congr_fun (evaluate_inclusion e) g

omit [Fintype ι] in
lemma supported_letter (S : Finset ι) (g : Generator ι R) (h : g.support ⊆ S) :
    FreeGroup.of g ∈ supported S := Subgroup.subset_closure ⟨g,h,rfl⟩

lemma local_equality (S : Finset ι) (hS : S.card ≤ 5)
    (w w' : FreeGroup (Generator ι R)) (hw : w ∈ supported S) (hw' : w' ∈ supported S)
    (he : matrixWord w = matrixWord w') :
    PresentedGroup.mk relations w = PresentedGroup.mk relations w' := by
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact ⟨by simp only [map_mul,map_inv,he,mul_inv_cancel],S,hS,(supported S).mul_mem hw ((supported S).inv_mem hw')⟩

lemma small_eval_injective (S : Finset ι) (hS : S.card ≤ 5)
    {g h : Group (ι := {i // i ∈ S}) (R := R)}
    (he : evaluate (inclusion (Function.Embedding.subtype _) g) =
      evaluate (inclusion (Function.Embedding.subtype _) h)) : g = h := by
  apply evaluate_injective_small (by simpa using hS)
  apply embed_injective (Function.Embedding.subtype _)
  simpa only [evaluate_inclusion_apply] using he

end
end SourceBurnside.Stability.SmallPresentation

end
section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort

namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def localGroup (S : Finset ι) : Subgroup (Group (ι := ι) (R := R)) :=
  (supported S).map (PresentedGroup.mk relations)

lemma gen_mem_local (S : Finset ι) (g : Generator ι R) (h : g.support ⊆ S) :
    gen g ∈ localGroup S := ⟨FreeGroup.of g,supported_letter S g h,rfl⟩

lemma localGroup_mono {S T : Finset ι} (h : S ⊆ T) :
    localGroup (R := R) S ≤ localGroup T := by
  apply Subgroup.map_mono
  apply Subgroup.closure_mono
  rintro w ⟨g,hg,rfl⟩
  exact ⟨g,hg.trans h,rfl⟩

lemma evaluate_mk (w : FreeGroup (Generator ι R)) :
    evaluate (PresentedGroup.mk relations w) = matrixWord w := rfl

lemma local_faithful (S : Finset ι) (hS : S.card ≤ 5)
    {g h : Group (ι := ι) (R := R)} (hg : g ∈ localGroup S) (hh : h ∈ localGroup S)
    (he : evaluate g = evaluate h) : g = h := by
  obtain ⟨w,hw,rfl⟩ := hg
  obtain ⟨v,hv,rfl⟩ := hh
  exact local_equality S hS w v hw hv he

lemma localGroup_eq_closure (S : Finset ι) : localGroup (R := R) S =
    Subgroup.closure (gen '' {g | g.support ⊆ S}) := by
  rw [localGroup,supported,MonoidHom.map_closure]
  congr 1
  rw [Set.image_image]
  rfl

lemma range_inclusion (S : Finset ι) :
    (inclusion (R := R) (Function.Embedding.subtype (· ∈ S))).range = localGroup S := by
  apply le_antisymm
  · rintro x ⟨g,rfl⟩
    have hh : (⊤ : Subgroup (Group (ι := {i // i ∈ S}) (R := R))) ≤
        (localGroup S).comap (inclusion (Function.Embedding.subtype _)) := by
      rw [← PresentedGroup.closure_range_of (relations (ι := {i // i ∈ S}) (R := R))]
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨g,rfl⟩
      change inclusion _ (gen g) ∈ localGroup S
      rw [inclusion_gen]
      apply gen_mem_local
      cases g with
      | root i j h a => exact Finset.insert_subset_iff.mpr ⟨i.property,Finset.singleton_subset_iff.mpr j.property⟩
      | diag i u => exact Finset.singleton_subset_iff.mpr i.property
    exact hh (Subgroup.mem_top g)
  · rw [localGroup_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨g,hg,rfl⟩
    cases g with
    | root i j h a =>
      obtain ⟨hi,hj⟩ := Finset.insert_subset_iff.mp hg
      have hj := Finset.singleton_subset_iff.mp hj
      refine ⟨gen (.root ⟨i,hi⟩ ⟨j,hj⟩ (fun he => h (congrArg Subtype.val he)) a),?_⟩
      rw [inclusion_gen]; rfl
    | diag i u =>
      refine ⟨gen (.diag ⟨i,Finset.singleton_subset_iff.mp hg⟩ u),?_⟩
      rw [inclusion_gen]; rfl

lemma supported_gen_all : Subgroup.closure (Set.range (gen (ι := ι) (R := R))) = ⊤ :=
  PresentedGroup.closure_range_of _

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def root (i j : ι) (h : i ≠ j) (a : R) : Group (ι := ι) (R := R) := gen (.root i j h a)
def diag (i : ι) (u : Rˣ) : Group (ι := ι) (R := R) := gen (.diag i u)

@[simp] lemma evaluate_root (i j : ι) (h : i≠j) (a : R) :
    evaluate (root i j h a) = elementary i j h a := evaluate_gen _
@[simp] lemma evaluate_diag (i : ι) (u : Rˣ) :
    evaluate (diag i u) = singleDiagonal i u := evaluate_gen _

lemma root_mem_local (S : Finset ι) (i j : ι) (h : i≠j) (a : R)
    (hi : i∈S) (hj : j∈S) : root i j h a ∈ localGroup S :=
  gen_mem_local S _ (Finset.insert_subset_iff.mpr ⟨hi,Finset.singleton_subset_iff.mpr hj⟩)
lemma diag_mem_local (S : Finset ι) (i : ι) (u : Rˣ) (hi : i∈S) : diag i u ∈ localGroup S :=
  gen_mem_local S _ (Finset.singleton_subset_iff.mpr hi)

@[simp] lemma root_add (i j : ι) (h : i≠j) (a b : R) :
    root i j h (a+b) = root i j h a * root i j h b := by
  apply local_faithful {i,j} (by have := Finset.card_insert_le i ({j} : Finset ι); simp only [Finset.card_singleton] at this; omega)
    (root_mem_local _ _ _ _ _ (by simp) (by simp))
    ((localGroup _).mul_mem (root_mem_local _ _ _ _ _ (by simp) (by simp))
      (root_mem_local _ _ _ _ _ (by simp) (by simp)))
  apply Units.ext
  simp [elementary,add_mul,mul_add,h.symm,Matrix.single_add,add_assoc]

@[simp] lemma root_zero (i j : ι) (h : i≠j) : root i j h (0:R) = 1 := by
  have hh := root_add i j h (0:R) 0
  simp only [zero_add] at hh
  exact mul_left_cancel (hh.symm.trans (mul_one _).symm)

@[simp] lemma root_neg (i j : ι) (h : i≠j) (a : R) : root i j h (-a) = (root i j h a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [←root_add,add_neg_cancel,root_zero]

lemma root_commute (i j k l : ι) (hij : i≠j) (hkl : k≠l)
    (hjk : j≠k) (hil : i≠l) (a b : R) : Commute (root i j hij a) (root k l hkl b) := by
  change root i j hij a * root k l hkl b = root k l hkl b * root i j hij a
  let S : Finset ι := {i,j,k,l}
  have hs : S.card ≤ 5 := by
    have h1 := Finset.card_insert_le i ({j,k,l} : Finset ι)
    have h2 := Finset.card_insert_le j ({k,l} : Finset ι)
    have h3 := Finset.card_insert_le k ({l} : Finset ι)
    simp only [Finset.card_singleton] at h3
    dsimp [S]; omega
  have hi := root_mem_local S i j hij a (by simp [S]) (by simp [S])
  have hk := root_mem_local S k l hkl b (by simp [S]) (by simp [S])
  apply local_faithful S hs ((localGroup S).mul_mem hi hk) ((localGroup S).mul_mem hk hi)
  simp only [map_mul,evaluate_root]
  apply Units.ext
  simp only [Units.val_mul,elementary_val,add_mul,mul_add,one_mul,mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk,
    Matrix.single_mul_single_of_ne _ _ _ _ hil.symm]
  abel

@[simp] lemma diag_inv (i : ι) (u : Rˣ) : diag i u⁻¹ = (diag i u)⁻¹ := by
  apply local_faithful {i} (by simp)
    (diag_mem_local _ _ _ (by simp)) ((localGroup _).inv_mem (diag_mem_local _ _ _ (by simp)))
  simp only [evaluate_diag,map_inv]
  apply Units.ext
  ext k l
  by_cases hk : k=i <;> simp [singleDiagonal,diagonal,Matrix.diagonal_apply,hk]

def rowHom (t : ι) : ({j : ι // j≠t} → Multiplicative R) →* Group (ι := ι) (R := R) :=
  MonoidHom.noncommPiCoprod
    (fun j => {toFun := fun a => root t j.val j.property.symm a.toAdd
               map_one' := root_zero _ _ _
               map_mul' := fun _left _right => root_add _ _ _ _ _})
    (fun i j _ _left _right => root_commute _ _ _ _ i.property.symm j.property.symm i.property j.property.symm _ _)

@[simp] lemma rowHom_single (t : ι) (j : {j : ι // j≠t}) (a : R) :
    rowHom t (Pi.mulSingle j (Multiplicative.ofAdd a)) = root t j.val j.property.symm a :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

def rowGroup (t : ι) : Subgroup (Group (ι := ι) (R := R)) := (rowHom t).range

lemma root_mem_row (t j : ι) (h : t≠j) (a : R) : root t j h a ∈ rowGroup t :=
  ⟨Pi.mulSingle ⟨j,h.symm⟩ (Multiplicative.ofAdd a), rowHom_single _ _ _⟩

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma row_mem {t : ι} {P : Subgroup (Group (ι := ι) (R := R))}
    (hP : ∀ j (h : t≠j) a, root t j h a ∈ P)
    (A : {j : ι // j≠t} → Multiplicative R) : rowHom t A ∈ P := by
  change A ∈ P.comap (rowHom t)
  apply Subgroup.pi_mem_of_mulSingle_mem
  intro j
  change rowHom t (Pi.mulSingle j (Multiplicative.ofAdd (A j).toAdd)) ∈ P
  rw [rowHom_single]
  exact hP _ _ _

lemma rowGroup_le {t : ι} {P : Subgroup (Group (ι := ι) (R := R))}
    (hP : ∀ j (h : t≠j) a, root t j h a ∈ P) : rowGroup t ≤ P := by
  rintro x ⟨A,rfl⟩
  exact row_mem hP A

def rowMatrix (t : ι) (A : {j : ι // j≠t} → Multiplicative R) : Matrix ι ι R :=
  fun i j => if i=t then if hj : j≠t then (A ⟨j,hj⟩).toAdd else 0 else 0

omit [Fintype ι] in
@[simp] lemma rowMatrix_entry (t : ι) (A : {j : ι // j≠t} → Multiplicative R)
    (j : {j : ι // j≠t}) : rowMatrix t A t j.val = (A j).toAdd := by
  simp [rowMatrix,j.property]

lemma rowMatrix_product (t : ι) (A B : {j : ι // j≠t} → Multiplicative R) :
    rowMatrix t A * rowMatrix t B = 0 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k=t <;> simp [rowMatrix,hk]

omit [Fintype ι] in
@[simp] lemma rowMatrix_one (t : ι) : rowMatrix t (1 : {j : ι // j≠t} → Multiplicative R) = 0 := by
  ext i j; simp [rowMatrix]

omit [Fintype ι] in
@[simp] lemma rowMatrix_mul (t : ι) (A B : {j : ι // j≠t} → Multiplicative R) :
    rowMatrix t (A*B) = rowMatrix t A + rowMatrix t B := by
  ext i j
  simp only [rowMatrix,Matrix.add_apply]
  split_ifs <;> simp_all

def rowUnits (t : ι) : ({j : ι // j≠t} → Multiplicative R) →* (Matrix ι ι R)ˣ where
  toFun A :=
    { val := 1+rowMatrix t A
      inv := 1-rowMatrix t A
      val_inv := by simp [add_mul,mul_sub,rowMatrix_product]
      inv_val := by simp [sub_mul,mul_add,rowMatrix_product] }
  map_one' := by apply Units.ext; simp
  map_mul' A B := by
    apply Units.ext
    simp only [Units.val_mul,rowMatrix_mul]
    simp [add_mul,mul_add,rowMatrix_product,add_assoc]

omit [Fintype ι] in
lemma rowMatrix_single (t : ι) (j : {j : ι // j≠t}) (a : R) :
    rowMatrix t (Pi.mulSingle j (Multiplicative.ofAdd a)) = Matrix.single t j.val a := by
  ext i k
  by_cases hi : i=t
  · subst i
    by_cases hk : k=t
    · subst k; simp [rowMatrix,j.property]
    · simp only [rowMatrix,dite_eq_left hk,Matrix.single_apply,true_and]
      by_cases he : j.val=k
      · have hh : j=⟨k,hk⟩ := Subtype.ext he
        subst j; simp
      · have hh : j≠⟨k,hk⟩ := fun h => he (congrArg Subtype.val h)
        simp [he,hh]
  · simp [rowMatrix,hi,Ne.symm hi]

@[simp] lemma rowUnits_single (t : ι) (j : {j : ι // j≠t}) (a : R) :
    rowUnits t (Pi.mulSingle j (Multiplicative.ofAdd a)) = elementary t j.val j.property.symm a := by
  apply Units.ext
  change 1+rowMatrix t _ = 1+Matrix.single _ _ _
  rw [rowMatrix_single]

lemma evaluate_rowHom (t : ι) : evaluate.comp (rowHom (R := R) t) = rowUnits t := by
  apply MonoidHom.pi_ext
  intro j a
  change evaluate (rowHom t (Pi.mulSingle j (Multiplicative.ofAdd a.toAdd))) =
    rowUnits t (Pi.mulSingle j (Multiplicative.ofAdd a.toAdd))
  rw [rowHom_single,rowUnits_single,evaluate_root]

@[simp] lemma evaluate_rowHom_apply (t : ι) (A : {j : ι // j≠t} → Multiplicative R) :
    evaluate (rowHom t A) = rowUnits t A := DFunLike.congr_fun (evaluate_rowHom t) A

lemma rowUnits_injective (t : ι) : Function.Injective (rowUnits (R := R) t) := by
  intro A B h
  have hh : rowMatrix t A = rowMatrix t B := add_left_cancel (congrArg Units.val h)
  funext j
  apply Multiplicative.toAdd.injective
  simpa using congrArg (fun M : Matrix ι ι R => M t j.val) hh

lemma row_faithful (t : ι) {g h : Group (ι := ι) (R := R)}
    (hg : g∈rowGroup t) (hh : h∈rowGroup t) (he : evaluate g=evaluate h) : g=h := by
  obtain ⟨A,rfl⟩ := hg
  obtain ⟨B,rfl⟩ := hh
  simp only [evaluate_rowHom_apply] at he
  rw [rowUnits_injective t he]

end
end SourceBurnside.Stability.SmallPresentation

end
section
end

end OAI
