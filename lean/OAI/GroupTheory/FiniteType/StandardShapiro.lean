import Mathlib
import OAI.GroupTheory.FiniteType.ProductCoefficientAffineShift

namespace OAI

noncomputable section
open CategoryTheory
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
namespace StandardShapiro
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G)

abbrev restrictedResolution : ProjectiveResolution (Rep.trivial R S R) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.standardResolution R G)

def inclusion : (Rep.standardResolution R S).complex ⟶ (restrictedResolution (R := R) S).complex :=
  StandardVertex.chainMap S.subtype S.subtype (by intro g x; rfl)

lemma inclusion_π : inclusion (R := R) S ≫ (restrictedResolution S).π =
    (Rep.standardResolution R S).π := by
  apply HomologicalComplex.to_single_hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change (Rep.standardComplex.ε R G).hom
      (MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin 1 → S => S.subtype ∘ s)
        (MonoidAlgebra.single s 1)) =
    (Rep.standardComplex.ε R S).hom (MonoidAlgebra.single s 1)
  simp [Rep.standardComplex.ε]
  rfl

def comparisonEquiv : HomotopyEquiv (Rep.standardResolution R S).complex
    (restrictedResolution (R := R) S).complex :=
  (ProjectiveResolution.homotopyEquiv (Rep.standardResolution R S) (restrictedResolution S)).copy
    (ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial R S R)) _ (inclusion S)
      (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact
        ProjectiveResolution.homotopyEquiv_hom_π (Rep.standardResolution R S) (restrictedResolution S))
      (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact inclusion_π S))

def indEquiv (A : Rep R S) :
    HomotopyEquiv ((Rep.standardComplex R S).coinvariantsTensorObj A)
      ((Rep.standardComplex R G).coinvariantsTensorObj (Rep.ind S.subtype A)) :=
  (((Rep.coinvariantsTensor R S).obj A).mapHomotopyEquiv (comparisonEquiv S)).trans
    (HomotopyEquiv.ofIso
      (groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (Rep.standardResolution R G)))

lemma indEquiv_hom_f_mk_tmul (A : Rep R S) (n : ℕ) (a : A)
    (z : MonoidAlgebra R (Fin (n+1) → S)) :
    (indEquiv S A).hom.f n (Coinvariants.mk _ (a ⊗ₜ[R] z)) =
      Coinvariants.mk _ (IndV.mk S.subtype A.ρ 1 a ⊗ₜ[R]
        StandardVertex.map S.subtype S.subtype (by intro g x; rfl) n z) := by
  change Rep.coinvariantsTensorIndInv S.subtype A ((Rep.standardComplex R G).X n)
    (Coinvariants.mk _ (a ⊗ₜ[R]
      StandardVertex.map S.subtype S.subtype (by intro g x; rfl) n z)) = _
  exact Rep.coinvariantsTensorIndInv_mk_tmul_indMk _ _ _

end StandardShapiro

namespace FunctionalTree
section

variable {R V M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def parentMap (p : V → V) : (V →₀ M) →ₗ[R] (V →₀ M) :=
  Finsupp.lmapDomain M R p

def boundary (p : V → V) : (V →₀ M) →ₗ[R] (V →₀ M) :=
  LinearMap.id - parentMap p

def augmentation : (V →₀ M) →ₗ[R] M :=
  Finsupp.lsum R (fun _ => LinearMap.id)

@[simp] lemma parentMap_single (p : V → V) (v : V) (a : M) :
    parentMap (R := R) p (Finsupp.single v a) = Finsupp.single (p v) a := by
  simp [parentMap]

@[simp] lemma augmentation_single (v : V) (a : M) :
    augmentation (R := R) (Finsupp.single v a) = a := by
  simp [augmentation]

lemma augmentation_parentMap (p : V → V) (a : V →₀ M) :
    augmentation (R := R) (parentMap (R := R) p a) = augmentation (R := R) a := by
  have h : (augmentation (R := R) (V := V) (M := M)).comp (parentMap p) = augmentation := by
    apply Finsupp.lhom_ext
    intro v a
    simp
  exact LinearMap.congr_fun h a

@[simp] lemma augmentation_boundary (p : V → V) (a : V →₀ M) :
    augmentation (R := R) (boundary (R := R) p a) = 0 := by
  simp [boundary,augmentation_parentMap]

def path (p : V → V) (n : ℕ) (v : V) (a : M) : V →₀ M :=
  ∑ k ∈ Finset.range n, Finsupp.single (p^[k] v) a

lemma boundary_path (p : V → V) (n : ℕ) (v : V) (a : M) :
    boundary (R := R) p (path p n v a) =
      Finsupp.single v a - Finsupp.single (p^[n] v) a := by
  induction n with
  | zero => simp [path]
  | succ n ih =>
    rw [path,Finset.sum_range_succ]
    change boundary p (path p n v a + Finsupp.single (p^[n] v) a) = _
    rw [map_add,ih]
    simp only [boundary,LinearMap.sub_apply,LinearMap.id_apply,parentMap_single,
      Function.iterate_succ_apply']
    abel

lemma single_sub_single_mem_range (p : V → V)
    (merge : ∀ v w, ∃ n m : ℕ, p^[n] v = p^[m] w) (v w : V) (a : M) :
    Finsupp.single v a - Finsupp.single w a ∈ LinearMap.range (boundary (R := R) p) := by
  obtain ⟨n,m,h⟩ := merge v w
  refine ⟨path p n v a - path p m w a,?_⟩
  rw [map_sub,boundary_path,boundary_path,h]
  abel

lemma range_boundary_eq_ker_augmentation [Nonempty V] (p : V → V)
    (merge : ∀ v w, ∃ n m : ℕ, p^[n] v = p^[m] w) :
    LinearMap.range (boundary (R := R) (M := M) p) = LinearMap.ker augmentation := by
  classical
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    exact augmentation_boundary p a
  · intro a ha
    let w : V := Classical.choice inferInstance
    have hmem : (∑ v ∈ a.support, (Finsupp.single v (a v) - Finsupp.single w (a v))) ∈
        LinearMap.range (boundary (R := R) p) := by
      exact Submodule.sum_mem _ (fun v _ => single_sub_single_mem_range p merge v w (a v))
    rw [Finset.sum_sub_distrib] at hmem
    change (a.sum Finsupp.single - _) ∈ _ at hmem
    rw [Finsupp.sum_single] at hmem
    have hs : (∑ v ∈ a.support, Finsupp.single w (a v)) =
        Finsupp.single w (augmentation (R := R) a) := by
      rw [← Finsupp.single_finsetSum]
      rfl
    rw [hs,show augmentation (R := R) a = 0 from ha,Finsupp.single_zero,sub_zero] at hmem
    exact hmem

lemma boundary_injective (p : V → V) (height : V → ℤ)
    (raise : ∀ v, height (p v) = height v + 1) :
    Function.Injective (boundary (R := R) (M := M) p) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_contra hne
  have hs : a.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image a.support height hs
  have he : a = parentMap (R := R) p a := sub_eq_zero.mp ha
  have hv' : v ∈ (parentMap (R := R) p a).support := by rwa [← he]
  have him : v ∈ a.support.image p := Finsupp.mapDomain_support hv'
  obtain ⟨w,hw,hwv⟩ := Finset.mem_image.mp him
  have h := hmin w hw
  rw [← hwv,raise] at h
  omega

lemma augmentation_surjective [Nonempty V] :
    Function.Surjective (augmentation (R := R) (V := V) (M := M)) := by
  intro a
  exact ⟨Finsupp.single (Classical.choice inferInstance) a,augmentation_single _ _⟩

end

open CategoryTheory
variable {R G V : Type*} [CommRing R] [Group G] [MulAction G V]
variable (A : Rep R G)

def diagonalAction (g : G) : (V →₀ A) →ₗ[R] (V →₀ A) :=
  Finsupp.lsum R (fun v => (Finsupp.lsingle (g • v)).comp (A.ρ g))

@[simp] lemma diagonalAction_single (g : G) (v : V) (a : A) :
    diagonalAction A g (Finsupp.single v a) = Finsupp.single (g • v) (A.ρ g a) := by
  simp [diagonalAction]

def diagonalRep : Rep R G := Rep.of {
  toFun := diagonalAction (V := V) A
  map_one' := by
    apply Finsupp.lhom_ext
    intro v a
    simp
  map_mul' := by
    intro g h
    apply Finsupp.lhom_ext
    intro v a
    simp [mul_smul] }

@[simp] lemma diagonalRep_single (g : G) (v : V) (a : A) :
    (diagonalRep (V := V) A).ρ g (Finsupp.single v a) =
      Finsupp.single (g • v) (A.ρ g a) := diagonalAction_single A g v a

variable (p : V → V) (peq : ∀ (g : G) (v : V), p (g • v) = g • p v)

def parentHom : diagonalRep (V := V) A ⟶ diagonalRep (V := V) A :=
  Rep.ofHom ⟨parentMap (R := R) p,by
    intro g
    apply Finsupp.lhom_ext
    intro v a
    simp [peq]⟩

def boundaryHom : diagonalRep (V := V) A ⟶ diagonalRep (V := V) A :=
  𝟙 _ - parentHom A p peq

@[simp] lemma boundaryHom_apply (z : V →₀ A) :
    boundaryHom A p peq z = boundary (R := R) p z := rfl

def augmentationHom : diagonalRep (V := V) A ⟶ A :=
  Rep.ofHom ⟨augmentation (R := R),by
    intro g
    apply Finsupp.lhom_ext
    intro v a
    simp⟩

@[simp] lemma augmentationHom_apply (z : V →₀ A) :
    augmentationHom A z = augmentation (R := R) z := rfl

def equivariantComplex : ShortComplex (Rep R G) :=
  ShortComplex.mk (boundaryHom A p peq) (augmentationHom A) (by
    ext z
    exact augmentation_boundary p z)

lemma equivariantComplex_shortExact [Nonempty V]
    (merge : ∀ v w, ∃ n m : ℕ, p^[n] v = p^[m] w)
    (height : V → ℤ) (raise : ∀ v, height (p v) = height v + 1) :
    (equivariantComplex A p peq).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (CategoryTheory.ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep R G) (ModuleCat R))).mp
    rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact range_boundary_eq_ker_augmentation p merge
  · rw [Rep.mono_iff_injective]
    exact boundary_injective p height raise
  · rw [Rep.epi_iff_surjective]
    exact augmentation_surjective

end FunctionalTree

end

end OAI
