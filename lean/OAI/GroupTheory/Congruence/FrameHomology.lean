import OAI.GroupTheory.Congruence.CongruenceFrames
import OAI.GroupTheory.Congruence.Resolution
import OAI.GroupTheory.Congruence.HomologyEdge

namespace OAI

noncomputable section

/-!
Shapiro comparison, frame resolution homology, augmentation ranges, and triviality of conjugation.
-/

namespace CoboundaryExpanders.ActualShapiro
open CategoryTheory CategoryTheory.Limits Representation Rep Finsupp MonoidalCategory TensorProduct

variable {k G H : Type} [CommRing k] [Group G] [Group H]
variable [DecidableEq G] [DecidableEq H]

def barF (f : H →* G) (n : ℕ) :
    (Rep.barComplex k H).X n ⟶ Rep.res f ((Rep.barComplex k G).X n) :=
  Rep.freeLift k H _ (fun x : Fin n → H =>
    single (f ∘ x) (.single (1 : G) (1 : k)))

omit [DecidableEq G] [DecidableEq H] in
@[simp] lemma barF_single (f : H →* G) (n : ℕ) (x : Fin n → H) (h : H) (r : k) :
    (barF (k := k) f n).hom (single x (.single h r)) =
      single (f ∘ x) (.single (f h) r) := by
  change (Representation.freeLift
    ((Representation.free k G (Fin n → G)).comp f)
    (fun x : Fin n → H => single (f ∘ x) (.single (1 : G) (1 : k))))
    (single x (.single h r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free k G (Fin n → G) (f h) _ = _
  rw [Representation.free_single_single]
  simp

def barMap (f : H →* G) : Rep.barComplex k H ⟶
    ((Rep.resFunctor f).mapHomologicalComplex _).obj (Rep.barComplex k G) where
  f n := barF f n
  comm' i j hij := by
    cases hij
    apply Rep.free_ext
    intro x
    change ((Rep.barComplex k G).d (j+1) j).hom
      ((barF f (j+1)).hom (single x (.single 1 1))) =
      (barF f j).hom (((Rep.barComplex k H).d (j+1) j).hom (single x (.single 1 1)))
    rw [Rep.barComplex.d_def, Rep.barComplex.d_def, barF_single]
    simp only [map_one]
    rw [Rep.barComplex.d_single, Rep.barComplex.d_single]
    have hq : ∀ (n : ℕ) (x : Fin n → H) (h : H) (r : k),
        (barF f n).hom (single x (.single h r)) = single (f ∘ x) (.single (f h) r) := barF_single f
    simp only [map_add, map_sum, hq, map_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    exact (Fin.comp_contractNth (· * ·) (· * ·) (fun a b : H => map_mul f a b) i x).symm

variable (S : Subgroup G)
abbrev restrictedResolution : ProjectiveResolution (Rep.trivial k S k) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution k G)

omit [DecidableEq G] in
lemma bar_augmentation : barMap (k := k) S.subtype ≫ (restrictedResolution (k := k) S).π =
    (Rep.barResolution k S).π := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    apply Rep.free_ext
    intro x
    change ((Rep.barResolution k G).π.f 0).hom
      ((barF S.subtype 0).hom (single x (.single 1 1))) =
      ((Rep.barResolution k S).π.f 0).hom (single x (.single 1 1))
    rw [barF_single, QuotientBarAugmentation.bar_augmentation_single,
      QuotientBarAugmentation.bar_augmentation_single]
  | succ n =>
    apply IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_single_obj_X (V := Rep k S)
      (ComplexShape.down ℕ) 0 (Rep.trivial k S k) (n+1) (by omega)

def barHomotopy : Homotopy (barMap (k := k) S.subtype)
    ((Rep.barResolution k S).homotopyEquiv (restrictedResolution (k := k) S)).hom :=
  ProjectiveResolution.liftHomotopy (P := Rep.barResolution k S)
    (Q := restrictedResolution (k := k) S) (𝟙 _) _ _
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact bar_augmentation S)
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact ProjectiveResolution.homotopyEquiv_hom_π _ _)

def barEquiv : HomotopyEquiv (Rep.barComplex k S)
    ((restrictedResolution (k := k) S).complex) where
  hom := barMap S.subtype
  inv := ((Rep.barResolution k S).homotopyEquiv (restrictedResolution (k := k) S)).inv
  homotopyHomInvId := ((barHomotopy S).compRight _).trans
    ((Rep.barResolution k S).homotopyEquiv (restrictedResolution (k := k) S)).homotopyHomInvId
  homotopyInvHomId := ((barHomotopy S).compLeft _).trans
    ((Rep.barResolution k S).homotopyEquiv (restrictedResolution (k := k) S)).homotopyInvHomId

variable (A : Rep k S)
def indBase : A ⟶ Rep.res S.subtype (Rep.ind S.subtype A) :=
  Rep.indResHomEquiv S.subtype A (Rep.ind S.subtype A) (𝟙 _)

omit [DecidableEq G] in
@[simp] lemma indBase_apply (x : A) : (indBase S A).hom x = IndV.mk S.subtype A.ρ 1 x := rfl

def inducedChainMap : (Rep.barComplex k S).coinvariantsTensorObj A ⟶
    (Rep.barComplex k G).coinvariantsTensorObj (Rep.ind S.subtype A) :=
  (((Rep.coinvariantsTensor k S).obj A).mapHomologicalComplex _).map (barMap S.subtype) ≫
    (groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (Rep.barResolution k G)).hom

lemma chain_factorization :
    (groupHomology.inhomogeneousChainsIso A).hom ≫ inducedChainMap S A =
      groupHomology.chainsMap S.subtype (indBase S A) ≫
        (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x a
  change Rep.coinvariantsTensorIndInv S.subtype A (Rep.free k G (Fin n → G))
    (((Rep.coinvariantsTensor k S).obj A).map (barF S.subtype n)
      (Rep.finsuppToCoinvariantsTensorFree A (Fin n → S) (single x a))) =
    Rep.finsuppToCoinvariantsTensorFree (Rep.ind S.subtype A) (Fin n → G)
      ((groupHomology.chainsMap S.subtype (indBase S A)).f n (single x a))
  rw [Rep.finsuppToCoinvariantsTensorFree_single, groupHomology.chainsMap_f_single,
    Rep.finsuppToCoinvariantsTensorFree_single]
  change Rep.coinvariantsTensorIndInv S.subtype A (Rep.free k G (Fin n → G))
    (Coinvariants.mk _ (a ⊗ₜ (barF S.subtype n).hom (single x (.single 1 1)))) = _
  rw [barF_single, map_one]
  exact Rep.coinvariantsTensorIndInv_mk_tmul_indMk (A := A) (B := Rep.free k G (Fin n → G)) S.subtype a
    (single (S.subtype ∘ x) (MonoidAlgebra.single (1 : G) (1 : k)))

def inducedChainEquiv : HomotopyEquiv ((Rep.barComplex k S).coinvariantsTensorObj A)
    ((Rep.barComplex k G).coinvariantsTensorObj (Rep.ind S.subtype A)) :=
  (((Rep.coinvariantsTensor k S).obj A).mapHomotopyEquiv (barEquiv S)).trans
    (HomotopyEquiv.ofIso
      (groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (Rep.barResolution k G)))

theorem indBase_isIso (j : ℕ) : IsIso (groupHomology.map S.subtype (indBase S A) j) := by
  change IsIso (HomologicalComplex.homologyMap
    (groupHomology.chainsMap S.subtype (indBase S A)) j)
  have hf := congrArg (fun f => HomologicalComplex.homologyMap f j) (chain_factorization S A)
  simp only [HomologicalComplex.homologyMap_comp] at hf
  have he : IsIso (HomologicalComplex.homologyMap (inducedChainMap S A) j) := by
    change IsIso (HomologicalComplex.homologyMap (inducedChainEquiv S A).hom j)
    refine ⟨⟨HomologicalComplex.homologyMap (inducedChainEquiv S A).inv j, ?_, ?_⟩⟩
    · rw [← HomologicalComplex.homologyMap_comp,
        (inducedChainEquiv S A).homotopyHomInvId.homologyMap_eq j, HomologicalComplex.homologyMap_id]
    · rw [← HomologicalComplex.homologyMap_comp,
        (inducedChainEquiv S A).homotopyInvHomId.homologyMap_eq j, HomologicalComplex.homologyMap_id]
  have hi : IsIso (HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso A).hom j ≫
      HomologicalComplex.homologyMap (inducedChainMap S A) j) := inferInstance
  rw [hf] at hi
  exact IsIso.of_isIso_comp_right _
    (HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).hom j)

end CoboundaryExpanders.ActualShapiro


section
open CategoryTheory CategoryTheory.Limits Rep Representation Finsupp

namespace CoboundaryExpanders.CosetModules
variable {k G : Type} [Field k] [Group G] [DecidableEq G] (S : Subgroup G)

omit [DecidableEq G] in
lemma hom_ext_base {A : Rep k G} {f g : permutation (k := k) S ⟶ A}
    (h : base S ≫ (resFunctor S.subtype).map f = base S ≫ (resFunctor S.subtype).map g) : f = g := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro q
  apply LinearMap.ext
  intro r
  induction q using Quotient.inductionOn with | h a =>
    have hh := congrArg (fun f => f.hom r) h
    have hf := Rep.hom_comm_apply f a (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) r)
    have hg := Rep.hom_comm_apply g a (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) r)
    rw [Representation.ofMulAction_single] at hf hg
    change f.hom (MonoidAlgebra.single (QuotientGroup.mk (a*1)) r) = _ at hf
    change g.hom (MonoidAlgebra.single (QuotientGroup.mk (a*1)) r) = _ at hg
    simp only [mul_one] at hf hg
    change f.hom (MonoidAlgebra.single (QuotientGroup.mk a) r) =
      g.hom (MonoidAlgebra.single (QuotientGroup.mk a) r)
    rw [hf, hg]
    exact congrArg (A.ρ a) hh

def indToCoset : Rep.ind S.subtype (Rep.trivial k S k) ⟶ permutation (k := k) S :=
  (Rep.indResHomEquiv S.subtype _ _).symm (base S)

omit [DecidableEq G] in
lemma indBase_comp_toCoset :
    ActualShapiro.indBase S (Rep.trivial k S k) ≫ (resFunctor S.subtype).map (indToCoset S) = base S :=
  (Rep.indResHomEquiv S.subtype _ _).apply_symm_apply (base S)

omit [DecidableEq G] in
lemma indBase_fixed (h : S) :
    (Rep.ind S.subtype (Rep.trivial k S k)).ρ h
      ((ActualShapiro.indBase S (Rep.trivial k S k)).hom (1 : k)) =
      (ActualShapiro.indBase S (Rep.trivial k S k)).hom (1 : k) := by
  have hh := Rep.hom_comm_apply (ActualShapiro.indBase S (Rep.trivial k S k)) h (1 : k)
  exact hh.symm

def cosetToInd : permutation (k := k) S ⟶ Rep.ind S.subtype (Rep.trivial k S k) :=
  extend S _ ((ActualShapiro.indBase S (Rep.trivial k S k)).hom 1) (indBase_fixed S)

omit [DecidableEq G] in
lemma base_comp_toInd : base S ≫ (resFunctor S.subtype).map (cosetToInd (k := k) S) =
    ActualShapiro.indBase S (Rep.trivial k S k) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro r
  change extend S _ _ _ (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) r) = _
  rw [extend_single]
  simp only [map_one, Module.End.one_apply]
  change r • ((ActualShapiro.indBase S (Rep.trivial k S k)).hom 1) =
    (ActualShapiro.indBase S (Rep.trivial k S k)).hom r
  rw [← map_smul]
  simp

def indCosetIso : Rep.ind S.subtype (Rep.trivial k S k) ≅ permutation (k := k) S where
  hom := indToCoset S
  inv := cosetToInd S
  hom_inv_id := by
    apply (Rep.indResHomEquiv S.subtype _ _).injective
    change ActualShapiro.indBase S (Rep.trivial k S k) ≫
      (resFunctor S.subtype).map (indToCoset S ≫ cosetToInd S) = _
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, indBase_comp_toCoset, base_comp_toInd]
    rfl
  inv_hom_id := by
    apply hom_ext_base S
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, base_comp_toInd, indBase_comp_toCoset,
      CategoryTheory.Functor.map_id, Category.comp_id]

theorem base_isIso (j : ℕ) : IsIso (groupHomology.map S.subtype (base (k := k) S) j) := by
  have ht := groupHomology.map_comp (C := permutation (k := k) S) S.subtype (MonoidHom.id G)
    (ActualShapiro.indBase S (Rep.trivial k S k)) (indCosetIso (k := k) S).hom j
  have hc : ActualShapiro.indBase S (Rep.trivial k S k) ≫
      (resFunctor S.subtype).map (indCosetIso (k := k) S).hom = base S := indBase_comp_toCoset S
  change groupHomology.map S.subtype (ActualShapiro.indBase S (Rep.trivial k S k) ≫
    (resFunctor S.subtype).map (indCosetIso (k := k) S).hom) j = _ at ht
  rw [hc] at ht
  rw [ht]
  let f : groupHomology (Rep.trivial k S k) j ⟶
      (groupHomology.functor k G j).obj (Rep.ind S.subtype (Rep.trivial k S k)) :=
    groupHomology.map S.subtype (ActualShapiro.indBase S (Rep.trivial k S k)) j
  have : IsIso f := ActualShapiro.indBase_isIso S (Rep.trivial k S k) j
  change IsIso (f ≫ (groupHomology.functor k G j).map (indCosetIso (k := k) S).hom)
  infer_instance

end CoboundaryExpanders.CosetModules

open CategoryTheory CategoryTheory.Limits Rep Representation Finsupp
open scoped BigOperators
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.CosetSums
variable {k G I : Type} [Field k] [Group G] (H : I → Subgroup G)

def projection (i : I) : permutation (k := k) H ⟶ CosetModules.permutation (k := k) (H i) :=
  Rep.ofHom ⟨(MonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap.comp
    ((Finsupp.lcomapDomain (fun q : G ⧸ H i => (⟨i,q⟩ : Basis H)) (by intro a b h; exact eq_of_heq (Sigma.mk.inj h).2)).comp
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap), by
    intro g
    apply LinearMap.ext
    intro f
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro q
    change ((Representation.ofMulAction k G (Basis H)) g f).coeff ⟨i,q⟩ =
      ((Representation.ofMulAction k G (G ⧸ H i)) g _).coeff q
    rw [Representation.coeff_ofMulAction, Representation.coeff_ofMulAction]
    rfl⟩

@[simp] lemma projection_coeff (i : I) (f : permutation (k := k) H) (q : G ⧸ H i) :
    (projection H i f).coeff q = f.coeff ⟨i,q⟩ := rfl

lemma inclusion_coeff (i : I) (f : CosetModules.permutation (k := k) (H i)) :
    (inclusion H i f).coeff = Finsupp.mapDomain (fun q => (⟨i,q⟩ : Basis H)) f.coeff := by
  have he : (MonoidAlgebra.coeffLinearEquiv k).toLinearMap.comp (inclusion H i).hom.toLinearMap =
      (Finsupp.lmapDomain k k (fun q : G ⧸ H i => (⟨i,q⟩ : Basis H))).comp
        (MonoidAlgebra.coeffLinearEquiv k).toLinearMap := by
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro r
    change (inclusion H i (MonoidAlgebra.single q r)).coeff =
      Finsupp.mapDomain _ (Finsupp.single q r)
    rw [inclusion_single, Finsupp.mapDomain_single]
    rfl
  exact LinearMap.congr_fun he f

lemma sum_inclusion_projection (f : permutation (k := k) H) (F : Finset I)
    (hF : ∀ x ∈ f.coeff.support, x.1 ∈ F) :
    ∑ i ∈ F, inclusion H i (projection H i f) = f := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro x
  have hi (i : I) : (inclusion H i (projection H i f)).coeff x =
      if h : x.1 = i then f.coeff x else 0 := by
    rw [inclusion_coeff]
    split_ifs with h
    · rcases x with ⟨j,q⟩
      dsimp at h
      subst j
      rw [Finsupp.mapDomain_apply_of_injective
        (by intro left right equality; exact eq_of_heq (Sigma.mk.inj equality).2), projection_coeff]
    · apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨q,hq⟩
      exact h (congrArg Sigma.fst hq).symm
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, hi]
  by_cases hx : x.1 ∈ F
  · simp [hx]
  · have hz : f.coeff x = 0 := by
      by_contra hz
      exact hx (hF x (Finsupp.mem_support_iff.mpr hz))
    simp [hz]

open groupHomology

lemma chainsMap_eval {A B : Rep k G} (f : A ⟶ B) (n : ℕ)
    (c : (Fin n → G) →₀ A) (g : Fin n → G) :
    ((chainsMap (MonoidHom.id G) f).f n c) g = f.hom (c g) := by
  change (((chainsMap (MonoidHom.id G) f).f n).hom c) g = _
  rw [chainsMap_id_f_hom_eq_mapRange]
  rfl

theorem homology_generated (n : ℕ) (x : groupHomology (permutation (k := k) H) n) :
    ∃ F : Finset I, ∃ y : ∀ i, groupHomology (CosetModules.permutation (k := k) (H i)) n,
      ∑ i ∈ F, (groupHomology.functor k G n).map (inclusion H i) (y i) = x := by
  induction x using groupHomology_induction_on with | h c =>
    let cc := iCycles (permutation (k := k) H) n c
    let F : Finset I := cc.support.biUnion (fun g => (cc g).coeff.support.image Sigma.fst)
    have hF (g : Fin n → G) (z : Basis H) (hz : z ∈ (cc g).coeff.support) : z.1 ∈ F := by
      have hg : g ∈ cc.support := by
        rw [Finsupp.mem_support_iff]
        intro he
        simp [he] at hz
      exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
    have chain_eq : ∑ i ∈ F,
        (chainsMap (MonoidHom.id G) (inclusion (k := k) H i)).f n
          ((chainsMap (MonoidHom.id G) (projection (k := k) H i)).f n cc) = cc := by
      apply Finsupp.ext
      intro g
      simp only [Finsupp.finsetSum_apply]
      trans ∑ i ∈ F, inclusion H i (projection H i (cc g))
      · apply Finset.sum_congr rfl
        intro i hi
        exact (chainsMap_eval (inclusion H i) n _ g).trans
          (congrArg (fun z => inclusion H i z) (chainsMap_eval (projection H i) n cc g))
      · exact sum_inclusion_projection H (cc g) F (hF g)
    have cyc_eq : ∑ i ∈ F,
        cyclesMap (MonoidHom.id G) (inclusion (k := k) H i) n
          (cyclesMap (MonoidHom.id G) (projection (k := k) H i) n c) = c := by
      apply (ModuleCat.mono_iff_injective (iCycles (permutation (k := k) H) n)).mp inferInstance
      simp only [map_sum]
      have hn {A B : Rep k G} (f : A ⟶ B) (y : cycles A n) :
          iCycles B n (cyclesMap (MonoidHom.id G) f n y) =
            (chainsMap (MonoidHom.id G) f).f n (iCycles A n y) := by
        exact congrArg (fun z => z y) (HomologicalComplex.cyclesMap_i (chainsMap (MonoidHom.id G) f) n)
      simp only [hn]
      exact chain_eq
    refine ⟨F,fun i => (groupHomology.functor k G n).map (projection H i) (π _ n c),?_⟩
    have hn {A B : Rep k G} (f : A ⟶ B) (y : cycles A n) :
        (groupHomology.functor k G n).map f (π A n y) =
          π B n (cyclesMap (MonoidHom.id G) f n y) := by
      exact congrArg (fun z => z y) (π_map (MonoidHom.id G) f n)
    simp only [hn]
    exact (map_sum (π (permutation (k := k) H) n).hom _ F).symm.trans
      (congrArg (fun z => π (permutation (k := k) H) n z) cyc_eq)

theorem homology_isZero (n : ℕ)
    (hz : ∀ i, CategoryTheory.Limits.IsZero (groupHomology (Rep.trivial k (H i) k) n)) :
    CategoryTheory.Limits.IsZero (groupHomology (permutation (k := k) H) n) := by
  have hi (i : I) : CategoryTheory.Limits.IsZero
      (groupHomology (CosetModules.permutation (k := k) (H i)) n) := by
    have := CosetModules.base_isIso (k := k) (H i) n
    exact CategoryTheory.Limits.IsZero.of_epi
      (groupHomology.map (H i).subtype (CosetModules.base (H i)) n) (hz i)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  suffices hh : ∀ x : groupHomology (permutation (k := k) H) n, x = 0 from
    ⟨fun x y => (hh x).trans (hh y).symm⟩
  intro x
  obtain ⟨F,y,rfl⟩ := homology_generated H n x
  apply Finset.sum_eq_zero
  intro i hiF
  have := (ModuleCat.isZero_iff_subsingleton).mp (hi i)
  have he : y i = 0 := Subsingleton.elim _ _
  rw [he]
  exact map_zero _

theorem map_range_le (n : ℕ) {A : Rep k G} (f : permutation (k := k) H ⟶ A)
    (P : Submodule k (groupHomology A n))
    (hP : ∀ i, ∀ y : groupHomology (Rep.trivial k (H i) k) n,
      groupHomology.map (H i).subtype
        (CosetModules.base (H i) ≫ (Rep.resFunctor (H i).subtype).map (inclusion H i ≫ f)) n y ∈ P)
    (x : groupHomology (permutation (k := k) H) n) :
    (groupHomology.functor k G n).map f x ∈ P := by
  obtain ⟨F,y,rfl⟩ := homology_generated H n x
  simp only [map_sum]
  apply Submodule.sum_mem
  intro i hiF
  have := CosetModules.base_isIso (k := k) (H i) n
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective
    (groupHomology.map (H i).subtype (CosetModules.base (H i)) n)).mp inferInstance (y i)
  have hc := groupHomology.map_comp (H i).subtype (MonoidHom.id G)
    (CosetModules.base (H i)) (inclusion H i ≫ f) n
  change groupHomology.map (H i).subtype
    (CosetModules.base (H i) ≫ (Rep.resFunctor (H i).subtype).map (inclusion H i ≫ f)) n =
    groupHomology.map (H i).subtype (CosetModules.base (H i)) n ≫
      (groupHomology.functor k G n).map (inclusion H i ≫ f) at hc
  have hp := hP i z
  rw [hc, CategoryTheory.Functor.map_comp] at hp
  change (groupHomology.functor k G n).map f
    ((groupHomology.functor k G n).map (inclusion H i)
      (groupHomology.map (H i).subtype (CosetModules.base (H i)) n z)) ∈ P at hp
  rw [hz] at hp
  exact hp

end CoboundaryExpanders.CosetSums

namespace CoboundaryExpanders.PermutationProjectivity
variable {k G X : Type} [Field k] [Group G] [MulAction G X]
theorem homology_isZero (n : ℕ)
    (hz : ∀ x : X, CategoryTheory.Limits.IsZero
      (groupHomology (Rep.trivial k (MulAction.stabilizer G x) k) n)) :
    CategoryTheory.Limits.IsZero (groupHomology (FinsuppPermutation.rep k G X) n) := by
  have hh := CosetSums.homology_isZero (k := k)
    (orbitStabilizer (G := G) (X := X)) n (fun q => hz q.out)
  exact hh.of_iso ((groupHomology.functor k G n).mapIso (chainsIso (k := k) (G := G) (X := X))).symm
end CoboundaryExpanders.PermutationProjectivity

end

section
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.RowFrames
variable {A : Type} [CommRing A] {a b : ℕ}
lemma normalization_fixed (P g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A) :
    P*g*P⁻¹ ∈ RowParabolic.fixed A a b ↔
      ∀ i : Fin b, g • P (Sum.inr i) = P (Sum.inr i) := by
  rw [← standard_fixed_iff]
  constructor
  · intro h i
    have hh := congrArg (fun v : Fin a ⊕ Fin b → A => P⁻¹ • v) (h i)
    simpa only [mul_smul,inv_smul_smul,inverse_smul_standard] using hh
  · intro h i
    simp only [mul_smul,inverse_smul_standard,h i]
    rw [← inverse_smul_standard,smul_inv_smul]
end CoboundaryExpanders.RowFrames

namespace CoboundaryExpanders.CongruenceFrames
open Construction Unimodular InfiniteChains RowFrames
variable (p n m : ℕ) [Fact p.Prime]

lemma face_fixed_iff (hm : 1 ≤ m) {b : ℕ} (s : (source p n).Face b) (g : Gamma p n m) :
    g • s = s ↔ ∀ v : s.val, g • v.val = v.val := by
  constructor
  · intro h v
    have hval := congrArg Subtype.val h
    have hv : g • v.val ∈ s.val := by
      have ht : g • v.val ∈ (g • s).val := Finset.mem_map.mpr ⟨v.val,v.property,rfl⟩
      simpa only [hval] using ht
    exact reduce_injOn p n m hm s.val s.property.1 hv v.property (reduce_smul p n m g v.val)
  · intro h
    apply Subtype.ext
    exact FiniteImage.image_eq_of_matching s.val s.val (Equiv.refl _) g h

def completion {b : ℕ} (s : (source p n).Face b) (hb : b < n) :
    Matrix.SpecialLinearGroup (Fin (n-b) ⊕ Fin b) (R p) :=
  (row_completion (show 0 < n-b by omega)
    (fun i j => (FiniteImage.enumeration s.val s.property.2 i).val (splitCoordinates n b hb.le j))
    ((frame_coordinates (splitCoordinates n b hb.le) _).mpr
      ((frame_equiv (R := R p) (f := fun v : s.val => v.val)
        (FiniteImage.enumeration s.val s.property.2)).mpr s.property.1))).choose
lemma completion_row {b : ℕ} (s : (source p n).Face b) (hb : b < n) (i : Fin b) (j) :
    completion p n s hb (Sum.inr i) j =
      (FiniteImage.enumeration s.val s.property.2 i).val (splitCoordinates n b hb.le j) :=
  (row_completion (show 0 < n-b by omega)
    (fun i j => (FiniteImage.enumeration s.val s.property.2 i).val (splitCoordinates n b hb.le j))
    ((frame_coordinates (splitCoordinates n b hb.le) _).mpr
      ((frame_equiv (R := R p) (f := fun v : s.val => v.val)
        (FiniteImage.enumeration s.val s.property.2)).mpr s.property.1))).choose_spec i j

local instance kernelNormal {A B ι : Type} [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]
    (φ : A →+* B) : (Matrix.SpecialLinearGroup.map (n := ι) φ).ker.Normal := inferInstance

def normalize {b : ℕ} (s : (source p n).Face b) (hb : b < n) :
    Gamma p n m ≃* (Matrix.SpecialLinearGroup.map (n := Fin (n-b) ⊕ Fin b)
      (Ideal.Quotient.mk (powerIdeal p m))).ker :=
  (kernelReindex (Ideal.Quotient.mk (powerIdeal p m)) (splitCoordinates n b hb.le).symm).trans
    (MulAut.conjNormal (completion p n s hb))

lemma normalize_fixed_iff (hm : 1 ≤ m) {b : ℕ} (s : (source p n).Face b) (hb : b < n)
    (g : Gamma p n m) :
    (normalize p n m s hb g).val ∈ RowParabolic.fixed (R p) (n-b) b ↔ g • s = s := by
  change completion p n s hb * (kernelReindex (Ideal.Quotient.mk (powerIdeal p m))
    (splitCoordinates n b hb.le).symm g).val * (completion p n s hb)⁻¹ ∈ _ ↔ _
  rw [normalization_fixed,face_fixed_iff p n m hm]
  let e := splitCoordinates n b hb.le
  let q := FiniteImage.enumeration s.val s.property.2
  have hh (i : Fin b) :
      (kernelReindex (Ideal.Quotient.mk (powerIdeal p m)) e.symm g).val •
        completion p n s hb (Sum.inr i) = completion p n s hb (Sum.inr i) ↔
      g • (q i).val = (q i).val := by
    have row : completion p n s hb (Sum.inr i) = fun j => (q i).val (e j) := by
      funext j; exact completion_row p n s hb i j
    rw [row]
    constructor
    · intro h
      change g.val • (q i).val = (q i).val
      funext j
      have hx := congrFun (reindex_smul e.symm g.val (fun j => (q i).val (e j))) j
      have hh := congrFun h (e.symm j)
      have he : (fun i_1 => (q i).val (e (e.symm i_1))) = (q i).val := by funext z; rw [e.apply_symm_apply]
      rw [he] at hx
      exact hx.symm.trans (hh.trans (congrArg (q i).val (e.apply_symm_apply j)))
    · intro h
      funext j
      have hx := congrFun (reindex_smul e.symm g.val (fun j => (q i).val (e j))) (e j)
      have he : (fun i_1 => (q i).val (e (e.symm i_1))) = (q i).val := by funext z; rw [e.apply_symm_apply]
      rw [he,e.symm_apply_apply] at hx
      exact hx.trans (congrFun h (e j))
  constructor
  · intro h v
    obtain ⟨i,rfl⟩ := q.surjective v
    exact (hh i).mp (h i)
  · intro h i; exact (hh i).mpr (h (q i))

def stabilizerEquiv (hm : 1 ≤ m) {b : ℕ} (s : (source p n).Face b) (hb : b < n) :
    MulAction.stabilizer (Gamma p n m) s ≃* MultiParabolic.group p (n-b) b m where
  toFun g := ⟨(normalize p n m s hb g.val).val,
    (normalize_fixed_iff p n m hm s hb g.val).mpr g.property,
    (normalize p n m s hb g.val).property⟩
  invFun g := ⟨(normalize p n m s hb).symm ⟨g.val,g.property.2⟩, by
    apply (normalize_fixed_iff p n m hm s hb _).mp
    rw [MulEquiv.apply_symm_apply]
    exact g.property.1⟩
  left_inv g := by
    apply Subtype.ext
    exact (normalize p n m s hb).symm_apply_apply g.val
  right_inv g := by
    apply Subtype.ext
    change ((normalize p n m s hb) ((normalize p n m s hb).symm ⟨g.val,g.property.2⟩)).val = g.val
    exact congrArg Subtype.val ((normalize p n m s hb).apply_symm_apply ⟨g.val,g.property.2⟩)
  map_mul' g h := by
    apply Subtype.ext
    change (normalize p n m s hb (g.val*h.val)).val =
      (normalize p n m s hb g.val).val * (normalize p n m s hb h.val).val
    exact congrArg Subtype.val ((normalize p n m s hb).map_mul g.val h.val)

lemma stabilizer_homology_isZero (hm : 1 ≤ m) (hp : Odd p) {b : ℕ}
    (s : (source p n).Face b) (hb : b < n) (j : ℕ)
    (hz : IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (n-b) m) (ZMod 2)) j)) :
    IsZero (groupHomology (Rep.trivial (ZMod 2) (MulAction.stabilizer (Gamma p n m) s) (ZMod 2)) j) := by
  have hz' := MultiParabolic.homology_isZero p (n-b) b m hp j hz
  have := F2Stability.hom_equiv_isIso (stabilizerEquiv p n m hm s hb) j
  exact hz'.of_mono (F2Stability.hom (stabilizerEquiv p n m hm s hb).toMonoidHom j)

lemma chains_homology_isZero (hm : 1 ≤ m) (hp : Odd p) (b : ℕ) (hb : b < n) (j : ℕ)
    (hz : IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (n-b) m) (ZMod 2)) j)) :
    IsZero (groupHomology ((source p n).chainsRep (G := Gamma p n m) b) j) :=
  PermutationProjectivity.homology_isZero j (fun s =>
    stabilizer_homology_isZero p n m hm hp s hb j hz)
end CoboundaryExpanders.CongruenceFrames

end

section
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders.MultiParabolic
open Construction F2Stability RowFrames
variable (p a b m : ℕ)
def sectionHom : Gamma p a m →* group p a b m where
  toFun := sectionValue p a b m
  map_one' := by
    apply Subtype.ext
    change (RowParabolic.sectionHom (R p) a b 1).val = 1
    exact congrArg Subtype.val (map_one (RowParabolic.sectionHom (R p) a b))
  map_mul' A B := by
    apply Subtype.ext
    change (RowParabolic.sectionHom (R p) a b (A.val*B.val)).val =
      (RowParabolic.sectionHom (R p) a b A.val).val * (RowParabolic.sectionHom (R p) a b B.val).val
    exact congrArg Subtype.val (map_mul (RowParabolic.sectionHom (R p) a b) A.val B.val)

lemma project_section : (project p a b m).comp (sectionHom p a b m) = MonoidHom.id _ := by
  ext A; rfl

lemma section_homology_isIso [Fact p.Prime] (hp : Odd p) (j : ℕ) :
    IsIso (hom (sectionHom p a b m) j) := by
  have : IsIso (hom (project p a b m) j) := project_homology_isIso p a b m hp j
  have he : hom (sectionHom p a b m) j ≫ hom (project p a b m) j = 𝟙 _ := by
    rw [← F2Stability.hom_comp,project_section,F2Stability.hom_id]
  have : IsIso (hom (sectionHom p a b m) j ≫ hom (project p a b m) j) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_right (hom (sectionHom p a b m) j) (hom (project p a b m) j)

def inclusion : group p a b m →* Gamma p (a+b) m where
  toFun A := ⟨Blocks.reindexSL finSumFinEquiv A.val, by
    change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) _ = 1
    rw [Blocks.reindexSL_map,A.property.2,map_one]⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' A B := by apply Subtype.ext; exact map_mul _ _ _

lemma inclusion_section : (inclusion p a b m).comp (sectionHom p a b m) =
    Blocks.gammaStabilization p a b m := by
  ext A i j
  rfl

lemma inclusion_hom_range [Fact p.Prime] (hp : Odd p) (j : ℕ)
    (y : groupHomology (Rep.trivial (ZMod 2) (group p a b m) (ZMod 2)) j) :
    ∃ x, hom (Blocks.gammaStabilization p a b m) j x = hom (inclusion p a b m) j y := by
  have := section_homology_isIso p a b m hp j
  obtain ⟨x,hx⟩ := (ModuleCat.epi_iff_surjective (hom (sectionHom p a b m) j)).mp inferInstance y
  refine ⟨x,?_⟩
  rw [← inclusion_section,F2Stability.hom_comp]
  change hom (inclusion p a b m) j (hom (sectionHom p a b m) j x) = _
  rw [hx]
end CoboundaryExpanders.MultiParabolic

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.CongruenceFrames
open Construction RowFrames F2Stability
variable (p a m : ℕ) [Fact p.Prime]
local instance gammaNormal : (Gamma p (a+1) m).Normal := by unfold Gamma; infer_instance

def vertexCompletion (s : (source p (a+1)).Face 1) (ha : 0 < a) :
    Matrix.SpecialLinearGroup (Fin (a+1)) (R p) :=
  Blocks.reindexSL finSumFinEquiv (completion p (a+1) s (by omega))

lemma vertex_normalization_map (hm : 1 ≤ m) (s : (source p (a+1)).Face 1) (ha : 0 < a) :
    (MultiParabolic.inclusion p a 1 m).comp (stabilizerEquiv p (a+1) m hm s (by omega)).toMonoidHom =
    ((MulAut.conjNormal (vertexCompletion p a s ha) : MulAut (Gamma p (a+1) m)).toMonoidHom).comp
      (MulAction.stabilizer (Gamma p (a+1) m) s).subtype := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  change Blocks.reindexSL finSumFinEquiv
    (completion p (a+1) s (by omega) *
      (kernelReindex (Ideal.Quotient.mk (powerIdeal p m))
        (splitCoordinates (a+1) 1 (by omega)).symm g.val).val *
      (completion p (a+1) s (by omega))⁻¹) =
    vertexCompletion p a s ha * g.val.val * (vertexCompletion p a s ha)⁻¹
  have he : splitCoordinates (a+1) 1 (by omega) = (finSumFinEquiv : Fin a ⊕ Fin 1 ≃ Fin (a+1)) := by
    ext i; rfl
  rw [he,map_mul,map_mul,map_inv]
  change vertexCompletion p a s ha *
    (Blocks.reindexSL finSumFinEquiv (Blocks.reindexSL finSumFinEquiv.symm g.val.val)) * _ = _
  have hi : Blocks.reindexSL finSumFinEquiv (Blocks.reindexSL finSumFinEquiv.symm g.val.val) = g.val.val := by
    exact (Blocks.reindexSL finSumFinEquiv).apply_symm_apply g.val.val
  rw [hi]
  rfl

theorem vertex_image_stable (hm : 1 ≤ m) (hp : Odd p) (ha : 0 < a)
    (s : (source p (a+1)).Face 1) (j : ℕ)
    (y : groupHomology (Rep.trivial (ZMod 2) (MulAction.stabilizer (Gamma p (a+1) m) s) (ZMod 2)) j) :
    ∃ x, hom (Blocks.gammaStabilization p a 1 m) j x =
      hom (MulAction.stabilizer (Gamma p (a+1) m) s).subtype j y := by
  let E := stabilizerEquiv p (a+1) m hm s (by omega)
  obtain ⟨x,hx⟩ := MultiParabolic.inclusion_hom_range p a 1 m hp j (hom E.toMonoidHom j y)
  have hc := congrArg (fun f => hom f j) (vertex_normalization_map p a m hm s ha)
  rw [F2Stability.hom_comp,F2Stability.hom_comp] at hc
  have hy := congrArg (fun f => f y) hc
  change hom (MultiParabolic.inclusion p a 1 m) j (hom E.toMonoidHom j y) =
    hom (MulAut.conjNormal (vertexCompletion p a s ha) : MulAut (Gamma p (a+1) m)).toMonoidHom j
      (hom (MulAction.stabilizer (Gamma p (a+1) m) s).subtype j y) at hy
  refine ⟨x,?_⟩
  have hf := ActualParabolic.polynomial_fixes_stable_image p a m hp j (vertexCompletion p a s ha)
  have hfx := congrArg (fun f => f x) hf
  have := hom_equiv_isIso (MulAut.conjNormal (vertexCompletion p a s ha) : MulAut (Gamma p (a+1) m)) j
  apply (ModuleCat.mono_iff_injective
    (hom (MulAut.conjNormal (vertexCompletion p a s ha) : MulAut (Gamma p (a+1) m)).toMonoidHom j)).mp inferInstance
  exact hfx.trans (hx.trans hy)
end CoboundaryExpanders.CongruenceFrames

namespace CoboundaryExpanders.InfiniteChains.Complex
variable {V G : Type} [DecidableEq V] [Group G] [MulAction G V]
    (X : CoboundaryExpanders.InfiniteChains.Complex V) [Fact (X.Invariant (G := G))]

def augmentedData : HomologyEdge.AugmentedData (k := k) (G := G) where
  D | 0 => Rep.trivial k G k
    | s+1 => X.chainsRep (G := G) (s+1)
  d | 0 => X.augmentationRep
    | s+1 => X.boundaryRep (s+1)
  square s := by
    cases s with
    | zero => exact X.augmentationRep_boundary
    | succ s => exact X.boundaryRep_squared (s+1)

lemma augmentation_exact_of_exactIn (he : Attachment.ExactIn X.faces 1) :
    Function.Exact (X.boundary 1) (X.sumCoefficients 1) := by
  intro c
  have hh := (Attachment.exactIn_iff_boundary_exact X 0).mp he c
  rw [← X.augmentation_boundary_zero]
  change X.sumCoefficients 0 (X.boundary 0 c) = 0 ↔ _
  rw [← map_zero (X.sumCoefficients 0), X.sumCoefficients_zero_injective.eq_iff]
  exact hh

lemma augmentedData_exact (s : ℕ) (he : Attachment.ExactIn X.faces (s+1)) :
    (ShortComplex.mk ((X.augmentedData (G := G)).d (s+1))
      (X.augmentedData.d s) (X.augmentedData.square s)).Exact := by
  cases s with
  | zero => exact X.augmentationRep_exact (X.augmentation_exact_of_exactIn he)
  | succ s =>
    apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k))).mp
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    exact fun c hc => ((Attachment.exactIn_iff_boundary_exact X (s+1)).mp he c).mp hc
end CoboundaryExpanders.InfiniteChains.Complex

namespace CoboundaryExpanders.Unimodular
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
lemma singleton_mem (v : M) (φ : M →ₗ[R] R) (hv : φ v = 1) :
    {v} ∈ (complex R (id : M → M)).faces := by
  refine ⟨LinearMap.pi (fun _ => φ), ?_⟩
  intro x
  ext y
  have hx : x.val = v := Finset.mem_singleton.mp x.property
  have hy : x = y := Subtype.ext (hx.trans (Finset.mem_singleton.mp y.property).symm)
  simp [hv, hy, Finset.mem_singleton.mp y.property]
end CoboundaryExpanders.Unimodular

namespace CoboundaryExpanders.CongruenceFrames
open Construction Unimodular InfiniteChains HomologyEdge
variable (p n m : ℕ) [Fact p.Prime]
lemma source_vertex (hn : 0 < n) : Nonempty ((source p n).Face 1) := by
  let i : Fin n := ⟨0,hn⟩
  let v : Fin n → R p := Pi.single i 1
  exact ⟨⟨{v}, singleton_mem v (LinearMap.proj i) (by simp [v]), by simp⟩⟩

lemma H0_boundary (hm : 1 ≤ m) (b : ℕ) (hb : b+1 < n)
    (x : groupHomology ((source p n).chainsRep (G := Gamma p n m) (b+1)) 0) :
    (orbitParam p n m hm b (by omega)).H0Equiv
      ((groupHomology.functor (ZMod 2) (Gamma p n m) 0).map ((source p n).boundaryRep b) x) =
    (target p n m hm).boundary b ((orbitParam p n m hm (b+1) hb).H0Equiv x) := by
  apply FinsuppPermutation.OrbitParam.H0_naturality
  exact (reduction p n m hm).boundary b

lemma H0_exact (hm : 1 ≤ m) (b : ℕ) (hb : b+2 < n)
    (x : groupHomology ((source p n).chainsRep (G := Gamma p n m) (b+1)) 0)
    (hx : (groupHomology.functor (ZMod 2) (Gamma p n m) 0).map ((source p n).boundaryRep b) x = 0) :
    ∃ y : groupHomology ((source p n).chainsRep (G := Gamma p n m) (b+2)) 0,
      (groupHomology.functor (ZMod 2) (Gamma p n m) 0).map ((source p n).boundaryRep (b+1)) y = x := by
  let E := (orbitParam p n m hm (b+1) (by omega)).H0Equiv (k := ZMod 2)
  have hz : (target p n m hm).boundary b (E x) = 0 := by
    rw [← H0_boundary p n m hm b (by omega) x,hx]
    exact (orbitParam p n m hm b (by omega)).H0Equiv.map_zero
  obtain ⟨c,hc⟩ := ((Attachment.exactIn_iff_boundary_exact (target p n m hm) b).mp
    (target_exact p n m hm (b+1) (by omega)) (E x)).mp hz
  let F := (orbitParam p n m hm (b+2) hb).H0Equiv (k := ZMod 2)
  refine ⟨F.symm c, E.injective ?_⟩
  change (orbitParam p n m hm (b+1) _).H0Equiv _ = E x
  rw [H0_boundary p n m hm (b+1) (by omega)]
  simpa only [F,LinearEquiv.apply_symm_apply] using hc

theorem augmentation_homology_epi (hm : 1 ≤ m) (hp : Odd p) (q : ℕ) (hn : 2*(q+1)+2 ≤ n)
    (hz : ∀ t, 1 ≤ t → t ≤ q →
      IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (n-(t+1)) m) (ZMod 2)) (q+1-t))) :
    Epi ((groupHomology.functor (ZMod 2) (Gamma p n m) (q+1)).map
      ((source p n).augmentationRep)) := by
  have := source_vertex p n (by omega)
  apply ((source p n).augmentedData (G := Gamma p n m)).epi_edge q
  · exact (source p n).augmentationRep_epi
  · intro s hs
    exact (source p n).augmentedData_exact s (source_exact p n (s+1) (by omega))
  · intro t ht htq
    exact chains_homology_isZero p n m hm hp (t+1) (by omega) (q+1-t) (hz t ht htq)
  · exact H0_exact p n m hm (q+1) (by omega)
end CoboundaryExpanders.CongruenceFrames

end

section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.PermutationProjectivity
variable {k G X : Type} [Field k] [Group G] [MulAction G X]
lemma chainsIso_single (x : CosetSums.Basis (orbitStabilizer (G := G) (X := X))) (r : k) :
    (chainsIso (k := k)).hom (MonoidAlgebra.single x r) = Finsupp.single (orbitBasis x) r := by
  change (Finsupp.domLCongr orbitBasis : _ ≃ₗ[k] _) (Finsupp.single x r) = _
  exact Finsupp.domLCongr_single _ _ _
end CoboundaryExpanders.PermutationProjectivity

namespace CoboundaryExpanders.InfiniteChains.Complex
open PermutationProjectivity F2Stability
variable {V G : Type} [Group G] [MulAction G V]
  (X : CoboundaryExpanders.InfiniteChains.Complex V) [Fact (X.Invariant (G := G))]

lemma orbitBase_augmentation (q : Orbit (G := G) (X := X.Face 1)) :
    CosetModules.base (orbitStabilizer q) ≫
      (Rep.resFunctor (orbitStabilizer q).subtype).map
        (CosetSums.inclusion orbitStabilizer q ≫ (chainsIso (k := ZMod 2)).hom ≫ X.augmentationRep) =
      QuotientCoinvariants.trivialMap (orbitStabilizer q).subtype := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro r
  change X.sumCoefficients 1 ((chainsIso (k := ZMod 2)).hom
    (CosetSums.inclusion orbitStabilizer q (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) r))) = r
  rw [CosetSums.inclusion_single,chainsIso_single,X.sumCoefficients_single]

theorem augmentation_range_le (j : ℕ)
    (P : Submodule (ZMod 2) (groupHomology (Rep.trivial (ZMod 2) G (ZMod 2)) j))
    (hP : ∀ s : X.Face 1, ∀ y : groupHomology (Rep.trivial (ZMod 2)
      (MulAction.stabilizer G s) (ZMod 2)) j,
      hom (MulAction.stabilizer G s).subtype j y ∈ P)
    (x : groupHomology (X.chainsRep (G := G) 1) j) :
    (groupHomology.functor (ZMod 2) G j).map X.augmentationRep x ∈ P := by
  let E := (groupHomology.functor (ZMod 2) G j).mapIso (chainsIso (k := ZMod 2) (G := G) (X := X.Face 1))
  have h := CosetSums.map_range_le (k := ZMod 2) (orbitStabilizer (G := G) (X := X.Face 1)) j
    ((chainsIso (k := ZMod 2)).hom ≫ X.augmentationRep) P (fun q y => ?_) (E.inv x)
  · rw [CategoryTheory.Functor.map_comp] at h
    change (groupHomology.functor (ZMod 2) G j).map X.augmentationRep (E.hom (E.inv x)) ∈ P at h
    have he : E.hom (E.inv x) = x := E.toLinearEquiv.apply_symm_apply x
    rwa [he] at h
  · rw [orbitBase_augmentation]
    exact hP q.out y
end CoboundaryExpanders.InfiniteChains.Complex

end

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.CongruenceFrames
open Construction RowFrames F2Stability
variable (p a m : ℕ) [Fact p.Prime]
attribute [local instance] gammaNormal

theorem stabilization_surjective (hm : 1 ≤ m) (hp : Odd p) (q : ℕ) (hn : 2*(q+1)+2 ≤ a+1)
    (hz : ∀ t, 1 ≤ t → t ≤ q →
      IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (a+1-(t+1)) m) (ZMod 2)) (q+1-t))) :
    Function.Surjective (hom (Blocks.gammaStabilization p a 1 m) (q+1)) := by
  have : Epi ((groupHomology.functor (ZMod 2) (Gamma p (a+1) m) (q+1)).map
    ((source p (a+1)).augmentationRep)) := augmentation_homology_epi p (a+1) m hm hp q hn hz
  intro y
  obtain ⟨x,rfl⟩ := (ModuleCat.epi_iff_surjective ((groupHomology.functor (ZMod 2)
    (Gamma p (a+1) m) (q+1)).map ((source p (a+1)).augmentationRep))).mp inferInstance y
  exact (source p (a+1)).augmentation_range_le (q+1)
    (LinearMap.range (hom (Blocks.gammaStabilization p a 1 m) (q+1)).hom)
    (fun s z => vertex_image_stable p a m hm hp (by omega) s (q+1) z) x

theorem conjugation_trivial (hm : 1 ≤ m) (hp : Odd p) (q : ℕ) (hn : 2*(q+1)+2 ≤ a+1)
    (hz : ∀ t, 1 ≤ t → t ≤ q →
      IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (a+1-(t+1)) m) (ZMod 2)) (q+1-t)))
    (g : Matrix.SpecialLinearGroup (Fin (a+1)) (R p)) :
    hom (MulAut.conjNormal g : MulAut (Gamma p (a+1) m)).toMonoidHom (q+1) = 𝟙 _ := by
  have : Epi (hom (Blocks.gammaStabilization p a 1 m) (q+1)) :=
    (ModuleCat.epi_iff_surjective _).mpr (stabilization_surjective p a m hm hp q hn hz)
  apply (cancel_epi (hom (Blocks.gammaStabilization p a 1 m) (q+1))).mp
  rw [Category.comp_id]
  exact ActualParabolic.polynomial_fixes_stable_image p a m hp (q+1) g
end CoboundaryExpanders.CongruenceFrames

end

end OAI
