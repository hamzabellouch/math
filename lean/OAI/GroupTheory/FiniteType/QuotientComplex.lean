import Mathlib
import OAI.GroupTheory.FiniteType.SingularSubdivisionIterateApplyComm

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace QuotientComplex
section
open CategoryTheory
variable {R : Type} [Ring R] {I : Type} {c : ComplexShape I}
  (C : HomologicalComplex (ModuleCat R) c) (S : ∀ i, Submodule R (C.X i))
  (hS : ∀ i j, S i ≤ (S j).comap (C.d i j).hom)

def obj (i : I) : ModuleCat R := ModuleCat.of R ((C.X i) ⧸ S i)

def differential (i j : I) : obj C S i ⟶ obj C S j :=
  ModuleCat.ofHom ((S i).mapQ (S j) (C.d i j).hom (hS i j))

@[simp] lemma differential_mk (i j : I) (x : C.X i) :
    differential C S hS i j ((S i).mkQ x) = (S j).mkQ (C.d i j x) := rfl

lemma differential_shape (i j : I) (h : ¬ c.Rel i j) : differential C S hS i j = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (S i).mkQ_surjective x
  rw [differential_mk,C.shape _ _ h]
  simp
  rfl

lemma differential_comp (i j k : I) :
    differential C S hS i j ≫ differential C S hS j k = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (S i).mkQ_surjective x
  change differential C S hS j k (differential C S hS i j ((S i).mkQ x)) = 0
  rw [differential_mk,differential_mk]
  have h := congrArg (fun f : C.X i ⟶ C.X k => f x) (C.d_comp_d i j k)
  change C.d j k (C.d i j x) = 0 at h
  rw [h,map_zero]
  rfl

def complex : HomologicalComplex (ModuleCat R) c where
  X := obj C S
  d := differential C S hS
  shape := differential_shape C S hS
  d_comp_d' i j k _ _ := differential_comp C S hS i j k

def projection : C ⟶ complex C S hS where
  f i := ModuleCat.ofHom (S i).mkQ
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x : 1
    rfl

@[simp] lemma projection_apply (i : I) (x : C.X i) : (projection C S hS).f i x = (S i).mkQ x := rfl

lemma projection_surjective (i : I) : Function.Surjective ((projection C S hS).f i) :=
  (S i).mkQ_surjective

lemma projection_zero_iff (i : I) (x : C.X i) : (projection C S hS).f i x = 0 ↔ x ∈ S i := by
  change (S i).mkQ x = 0 ↔ _
  change x ∈ LinearMap.ker (S i).mkQ ↔ _
  rw [Submodule.ker_mkQ]

end

open CategoryTheory
variable {R : Type} [Ring R] {I : Type} {c : ComplexShape I}
  {C D : HomologicalComplex (ModuleCat R) c}
  {S : ∀ i, Submodule R (C.X i)} {T : ∀ i, Submodule R (D.X i)}
  (hS : ∀ i j, S i ≤ (S j).comap (C.d i j).hom)
  (hT : ∀ i j, T i ≤ (T j).comap (D.d i j).hom)
  (f : C ⟶ D) (hf : ∀ i, S i ≤ (T i).comap (f.f i).hom)

def map : complex C S hS ⟶ complex D T hT where
  f i := ModuleCat.ofHom ((S i).mapQ (T i) (f.f i).hom (hf i))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x : 1
    obtain ⟨x,rfl⟩ := (S i).mkQ_surjective x
    change (T j).mkQ (D.d i j (f.f i x)) = (T j).mkQ (f.f j (C.d i j x))
    exact congrArg (T j).mkQ (congrArg (fun h : C.X i ⟶ D.X j => h x) (f.comm i j))

@[simp] lemma map_projection (i : I) (x : C.X i) :
    (map hS hT f hf).f i ((projection C S hS).f i x) =
      (projection D T hT).f i (f.f i x) := rfl

end QuotientComplex

namespace SingularSupport
open Classical CategoryTheory SingularChains
variable {X : Type} [TopologicalSpace X] {n : ℕ}

lemma sub_cut_mem {P Q : C(Std n,X) → Prop} {c : (chains X).X n}
    (hc : c ∈ span (fun f => P f ∨ Q f)) : c - cut P c ∈ span Q := by
  change (𝟙 ((chains X).X n) - cut P : (chains X).X n ⟶ (chains X).X n) c ∈ span Q
  apply map_mem _ _ hc
  intro f hf
  change gen f - cut P (gen f) ∈ span Q
  rw [cut_gen]
  by_cases hp : P f
  · rw [ite_eq_left hp,sub_self]; exact Submodule.zero_mem _
  · rw [ite_eq_right hp,sub_zero]; exact gen_mem f (hf.resolve_left hp)

end SingularSupport

namespace SingularSubspace
open Classical Set CategoryTheory SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

lemma group_mono {A B : Set X} (h : A ⊆ B) (n : ℕ) : group A n ≤ group B n :=
  SingularSupport.span_mono fun _ hf => hf.trans h

lemma group_eq_small (A : Set X) (n : ℕ) : group A n = SmallChains.group (fun _ : Unit => A) n := by
  unfold group SmallChains.group
  congr 1
  funext f
  exact propext ⟨fun hf => ⟨(),hf⟩,fun ⟨_,hf⟩ => hf⟩

lemma boundary_mem (A : Set X) {n m : ℕ} {c : (chains X).X n} (hc : c ∈ group A n) :
    (chains X).d n m c ∈ group A m := by
  by_cases h : m+1 = n
  · subst n
    rw [group_eq_small] at hc ⊢
    exact SmallChains.boundary_mem _ hc
  · rw [(chains X).shape n m h]
    exact Submodule.zero_mem _

lemma iterate_mem (A : Set X) {n : ℕ} {c : (chains X).X n} (hc : c ∈ group A n) (k : ℕ) :
    SingularSubdivision.iterate X n k c ∈ group A n := by
  rw [group_eq_small] at hc ⊢
  exact SmallChains.iterate_mem _ hc k

lemma sumPrism_mem (A : Set X) {n : ℕ} {c : (chains X).X n} (hc : c ∈ group A n) (k : ℕ) :
    SingularSubdivision.sumPrism X n k c ∈ group A (n+1) := by
  rw [group_eq_small] at hc ⊢
  exact SmallChains.sumPrism_mem _ hc k

lemma map_mem (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : MapsTo f A B)
    {n : ℕ} {c : (chains X).X n} (hc : c ∈ group A n) : (map f).f n c ∈ group B n := by
  apply SingularSupport.map_mem _ _ hc
  intro g hg
  rw [SingularSupport.map_gen]
  apply SingularSupport.gen_mem
  rintro _ ⟨s,rfl⟩
  exact hf (hg (mem_range_self s))

lemma lift_mem (A B : Set X) {n : ℕ} {c : (chains X).X n} (hc : c ∈ group A n) :
    lift B n c ∈ group ((inclusionMap B) ⁻¹' A) n := by
  apply SingularSupport.map_mem _ _ hc
  intro f hf
  change (generator f ≫ lift B n) 1 ∈ _
  rw [generator_lift]
  split_ifs with hb
  · apply SingularSupport.gen_mem
    rintro _ ⟨s,rfl⟩
    exact hf (mem_range_self s)
  · exact Submodule.zero_mem _

lemma lift_inclusion_apply (B : Set X) {n : ℕ} {c : (chains X).X n} (hc : c ∈ group B n) :
    (map (inclusionMap B)).f n (lift B n c) = c := by
  change (lift B n ≫ (map (inclusionMap B)).f n) c = c
  rw [liftChain_inclusion]
  exact SingularSupport.cut_eq hc

lemma inclusion_lift_apply (B : Set X) {n : ℕ} (c : (chains B).X n) :
    lift B n ((map (inclusionMap B)).f n c) = c := by
  exact congrArg (fun h : (chains B).X n ⟶ (chains B).X n => h c) (inclusion_liftChain B n)

lemma inclusion_mem_iff (A B : Set X) {n : ℕ} (c : (chains B).X n) :
    (map (inclusionMap B)).f n c ∈ group A n ↔ c ∈ group ((inclusionMap B) ⁻¹' A) n := by
  constructor
  · intro hc
    simpa only [inclusion_lift_apply] using lift_mem A B hc
  · exact map_mem _ _ _ (fun _ h => h)

lemma lift_boundary (B : Set X) {n m : ℕ} {c : (chains X).X n} (hc : c ∈ group B n) :
    (chains B).d n m (lift B n c) = lift B m ((chains X).d n m c) := by
  apply inclusion_injective B m
  have h := congrArg (fun h : (chains B).X n ⟶ (chains X).X m => h (lift B n c))
    ((map (inclusionMap B)).comm n m)
  change (chains X).d n m ((map (inclusionMap B)).f n (lift B n c)) =
    (map (inclusionMap B)).f m ((chains B).d n m (lift B n c)) at h
  rw [lift_inclusion_apply B hc] at h
  rw [lift_inclusion_apply B (boundary_mem B hc)]
  exact h.symm

end SingularSubspace

namespace RelativeChains
section
open Set CategoryTheory SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def complex (A : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  QuotientComplex.complex (chains X) (SingularSubspace.group A)
    (fun _ _ _ hc => SingularSubspace.boundary_mem A hc)

def projection (A : Set X) : chains X ⟶ complex A :=
  QuotientComplex.projection (chains X) (SingularSubspace.group A)
    (fun _ _ _ hc => SingularSubspace.boundary_mem A hc)

lemma projection_surjective (A : Set X) (n : ℕ) : Function.Surjective ((projection A).f n) :=
  QuotientComplex.projection_surjective _ _ _ n

lemma projection_zero_iff (A : Set X) (n : ℕ) (c : (chains X).X n) :
    (projection A).f n c = 0 ↔ c ∈ SingularSubspace.group A n :=
  QuotientComplex.projection_zero_iff _ _ _ n c

@[simp] lemma differential_projection (A : Set X) (n m : ℕ) (c : (chains X).X n) :
    (complex A).d n m ((projection A).f n c) = (projection A).f m ((chains X).d n m c) := rfl

def map (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : MapsTo f A B) : complex A ⟶ complex B :=
  QuotientComplex.map _ _ (SingularChains.map f) (fun _ _ hc => SingularSubspace.map_mem A B f hf hc)

@[simp] lemma map_projection (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : MapsTo f A B)
    (n : ℕ) (c : (chains X).X n) :
    (map A B f hf).f n ((projection A).f n c) = (projection B).f n ((SingularChains.map f).f n c) := rfl

def inclusion (A B : Set X) : complex ((SingularSubspace.inclusionMap B) ⁻¹' A) ⟶ complex A :=
  map _ _ (SingularSubspace.inclusionMap B) (fun _ h => h)

end

open Set CategoryTheory SingularChains SingularSubdivision
variable {X : Type} [TopologicalSpace X]

lemma projection_eq_iff (A : Set X) (n : ℕ) (c d : (chains X).X n) :
    (projection A).f n c = (projection A).f n d ↔ c - d ∈ SingularSubspace.group A n := by
  rw [← sub_eq_zero,← map_sub,projection_zero_iff]

lemma inclusion_projection (A B : Set X) (n : ℕ) (c : (chains B).X n) :
    (inclusion A B).f n ((projection ((SingularSubspace.inclusionMap B) ⁻¹' A)).f n c) =
      (projection A).f n ((SingularChains.map (SingularSubspace.inclusionMap B)).f n c) := rfl

lemma inclusion_injective (A B : Set X) (n : ℕ) : Function.Injective ((inclusion A B).f n) := by
  intro c d h
  obtain ⟨c,rfl⟩ := projection_surjective _ n c
  obtain ⟨d,rfl⟩ := projection_surjective _ n d
  rw [inclusion_projection,inclusion_projection,projection_eq_iff,← map_sub,
    SingularSubspace.inclusion_mem_iff] at h
  exact (projection_eq_iff _ n c d).mpr h

lemma cycle_difference (A : Set X) (n k : ℕ) (c : (chains X).X n)
    (hc : (chains X).d n (n-1) c ∈ SingularSubspace.group A (n-1)) :
    (complex A).d (n+1) n ((projection A).f (n+1) (sumPrism X n k c)) =
      (projection A).f n c - (projection A).f n (iterate X n k c) := by
  rw [differential_projection]
  cases n with
  | zero => simp [sumPrism_zero,iterate_zero]
  | succ n =>
    have h := congrArg (fun h : (chains X).X (n+1) ⟶ (chains X).X (n+1) => h c)
      (sumPrism_boundary n k)
    change (chains X).d (n+2) (n+1) (sumPrism X (n+1) k c) =
      c - iterate X (n+1) k c - sumPrism X n k ((chains X).d (n+1) n c) at h
    rw [h,map_sub,map_sub]
    have hz : (projection A).f (n+1) (sumPrism X n k ((chains X).d (n+1) n c)) = 0 :=
      (projection_zero_iff A _ _).mpr (SingularSubspace.sumPrism_mem A hc k)
    rw [hz,sub_zero]

lemma iterate_projection_eq (A : Set X) (n k : ℕ) {c d : (chains X).X n}
    (h : (projection A).f n c = (projection A).f n d) :
    (projection A).f n (iterate X n k c) = (projection A).f n (iterate X n k d) := by
  apply (projection_eq_iff A n _ _).mpr
  rw [← map_sub]
  exact SingularSubspace.iterate_mem A ((projection_eq_iff A n _ _).mp h) k

end RelativeChains

end

end OAI
