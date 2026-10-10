import Mathlib
import OAI.GroupTheory.FiniteType.SingularSubdivisionIterate

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularSubdivision
open CategoryTheory SingularChains
variable {X : Type} [TopologicalSpace X]

lemma iterate_apply_comm (n m k : ℕ) (c : (chains X).X n) :
    (chains X).d n m (iterate X n k c) = iterate X m k ((chains X).d n m c) :=
  congrArg (fun h : (chains X).X n ⟶ (chains X).X m => h c) (iterate_comm n m k)

lemma cycle_difference (n k : ℕ) (c : (chains X).X n) (hc : (chains X).d n (n-1) c = 0) :
    (chains X).d (n+1) n (sumPrism X n k c) = c - iterate X n k c := by
  cases n with
  | zero => simp [sumPrism_zero,iterate_zero]
  | succ n =>
    have h := congrArg (fun h : (chains X).X (n+1) ⟶ (chains X).X (n+1) => h c)
      (sumPrism_boundary n k)
    change (chains X).d (n+2) (n+1) (sumPrism X (n+1) k c) =
      c - iterate X (n+1) k c - sumPrism X n k ((chains X).d (n+1) n c) at h
    have hc' : (chains X).d (n+1) n c = 0 := by
      change (chains X).d (n+1) n c = 0 at hc
      exact hc
    simpa only [hc',map_zero,sub_zero] using h

end SingularSubdivision

namespace SmallChains
open CategoryTheory SingularChains SingularSubdivision HomologicalComplex
variable {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Set X)

lemma d_val (n m : ℕ) (c : (complex U).X n) :
    ((complex U).d n m c).1 = (chains X).d n m c.1 := by
  exact (congrArg (fun h : (complex U).X n ⟶ (chains X).X m => h c) ((inclusion U).comm n m)).symm

abbrev scInclusion (n : ℕ) : (complex U).sc' (n+1) n (n-1) ⟶ (chains X).sc' (n+1) n (n-1) :=
  (shortComplexFunctor' (ModuleCat ℤ) (ComplexShape.down ℕ) (n+1) n (n-1)).map (inclusion U)

lemma scInclusion_surjective (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    Function.Surjective (ShortComplex.homologyMap (scInclusion U n)) := by
  apply ModuleHomology.homologyMap_surjective
  intro c
  obtain ⟨k,hk⟩ := (eventually_small U hU hcover c.1).exists
  have hc : (chains X).d n (n-1) c.1 = 0 := c.2
  let d : ModuleHomology.Cycles ((complex U).sc' (n+1) n (n-1)) := ⟨⟨iterate X n k c.1,hk⟩,by
    apply Subtype.ext
    change ((complex U).d n (n-1) ⟨iterate X n k c.1,hk⟩).1 = 0
    erw [d_val,iterate_apply_comm,hc,map_zero]⟩
  refine ⟨d,sumPrism X n k c.1,?_⟩
  exact cycle_difference n k c.1 hc

lemma scInclusion_injective (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    Function.Injective (ShortComplex.homologyMap (scInclusion U n)) := by
  apply ModuleHomology.homologyMap_injective
  intro c hb
  obtain ⟨b,hb⟩ := hb
  obtain ⟨k,hk⟩ := (eventually_small U hU hcover b).exists
  have hc : (chains X).d n (n-1) c.1.1 = 0 := by
    have h := congrArg Subtype.val c.2
    change ((complex U).d n (n-1) c.1).1 = 0 at h
    erw [d_val] at h
    exact h
  let b' : (complex U).X (n+1) := ⟨iterate X (n+1) k b + sumPrism X n k c.1.1,
    (group U (n+1)).add_mem hk (sumPrism_mem U c.1.2 k)⟩
  refine ⟨b',Subtype.ext ?_⟩
  change ((complex U).d (n+1) n b').1 = c.1.1
  rw [d_val]
  change (chains X).d (n+1) n (iterate X (n+1) k b + sumPrism X n k c.1.1) = c.1.1
  erw [map_add,iterate_apply_comm,cycle_difference n k _ hc]
  change (chains X).d (n+1) n b = c.1.1 at hb
  erw [hb]
  abel

theorem inclusion_quasiIsoAt (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (n : ℕ) : QuasiIsoAt (inclusion U) n := by
  have hp : (ComplexShape.down ℕ).prev n = n+1 :=
    ComplexShape.prev_eq' _ (by rfl)
  have hn : (ComplexShape.down ℕ).next n = n-1 := by
    cases n with
    | zero => exact ComplexShape.next_eq_self' _ _ (by intro k; change ¬ k+1 = 0; omega)
    | succ n => exact ComplexShape.next_eq' _ (by change n+1 = n+1; rfl)
  rw [quasiIsoAt_iff' (inclusion U) _ _ _ hp hn,ShortComplex.quasiIso_iff]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨scInclusion_injective U hU hcover n,scInclusion_surjective U hU hcover n⟩

theorem inclusion_quasiIso (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) : QuasiIso (inclusion U) := by
  constructor
  exact inclusion_quasiIsoAt U hU hcover

end SmallChains

namespace SingularSupport
open Classical
open Set CategoryTheory AlgebraicTopology Limits SingularChains
variable {X : Type} [TopologicalSpace X] {n : ℕ}

def cut (P : C(Std n,X) → Prop) : (chains X).X n ⟶ (chains X).X n :=
  desc (fun f => if P f then generator f else 0)

@[simp] lemma cut_gen (P : C(Std n,X) → Prop) (f : C(Std n,X)) :
    cut P (gen f) = if P f then gen f else 0 := by
  change (generator f ≫ cut P) 1 = _
  rw [cut,generator_desc]
  split_ifs <;> rfl

lemma cut_mem (P : C(Std n,X) → Prop) (c : (chains X).X n) : cut P c ∈ span P := by
  apply induction_on ((span P).comap (cut P).hom) _ c
  intro f
  change cut P (gen f) ∈ span P
  rw [cut_gen]
  split_ifs with hf
  · exact gen_mem f hf
  · exact Submodule.zero_mem _

lemma cut_eq {P : C(Std n,X) → Prop} {c : (chains X).X n} (hc : c ∈ span P) : cut P c = c := by
  induction hc using Submodule.span_induction with
  | mem c hc => obtain ⟨f,hf,rfl⟩ := hc; simp [hf]
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd]
  | smul a c hc ih =>
    simpa only [ih] using (cut P).hom.map_smul a c

lemma cut_mem_and {P Q : C(Std n,X) → Prop} {c : (chains X).X n} (hc : c ∈ span Q) :
    cut P c ∈ span (fun f => P f ∧ Q f) := by
  apply map_mem _ _ hc
  intro f hf
  rw [cut_gen]
  split_ifs with hp
  · exact gen_mem f ⟨hp,hf⟩
  · exact Submodule.zero_mem _

lemma span_and (P Q : C(Std n,X) → Prop) : span (fun f => P f ∧ Q f) = span P ⊓ span Q := by
  apply le_antisymm
  · exact le_inf (span_mono fun _ h => h.1) (span_mono fun _ h => h.2)
  · intro c hc
    rw [← cut_eq hc.1]
    exact cut_mem_and hc.2

lemma span_or (P Q : C(Std n,X) → Prop) : span (fun f => P f ∨ Q f) = span P ⊔ span Q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨f,hf,rfl⟩
    rcases hf with hp|hq
    · exact (show span P ≤ span P ⊔ span Q from le_sup_left) (gen_mem f hp)
    · exact (show span Q ≤ span P ⊔ span Q from le_sup_right) (gen_mem f hq)
  · exact sup_le (span_mono fun _ h => Or.inl h) (span_mono fun _ h => Or.inr h)

end SingularSupport

namespace SingularSubspace
open Classical
open Set CategoryTheory AlgebraicTopology Limits SingularChains
variable {X : Type} [TopologicalSpace X] (A : Set X)

def inclusionMap : C(A,X) := ⟨Subtype.val,continuous_subtype_val⟩

abbrev Within {n : ℕ} (f : C(Std n,X)) : Prop := range f ⊆ A

def group (n : ℕ) : Submodule ℤ ((chains X).X n) := SingularSupport.span (Within A)

lemma group_inf (B : Set X) (n : ℕ) : group (A ∩ B) n = group A n ⊓ group B n := by
  change SingularSupport.span (fun f => range f ⊆ A ∩ B) = _
  simp only [subset_inter_iff]
  exact SingularSupport.span_and (Within A) (Within B)

def liftSimplex {n : ℕ} (f : C(Std n,X)) (hf : Within A f) : C(Std n,A) :=
  ⟨fun s => ⟨f s,hf (mem_range_self s)⟩,f.continuous.subtype_mk _⟩

@[simp] lemma inclusion_lift {n : ℕ} (f : C(Std n,X)) (hf : Within A f) :
    (inclusionMap A).comp (liftSimplex A f hf) = f := rfl

lemma within_inclusion {n : ℕ} (f : C(Std n,A)) : Within A ((inclusionMap A).comp f) := by
  rintro _ ⟨s,rfl⟩
  exact (f s).2

@[simp] lemma lift_inclusion {n : ℕ} (f : C(Std n,A)) :
    liftSimplex A ((inclusionMap A).comp f) (within_inclusion A f) = f := rfl

def lift (n : ℕ) : (chains X).X n ⟶ (chains A).X n :=
  desc (fun f => if hf : Within A f then generator (liftSimplex A f hf) else 0)

@[reassoc] lemma generator_lift {n : ℕ} (f : C(Std n,X)) :
    generator f ≫ lift A n = if hf : Within A f then generator (liftSimplex A f hf) else 0 :=
  generator_desc _ _

lemma inclusion_liftChain (n : ℕ) : (map (inclusionMap A)).f n ≫ lift A n = 𝟙 _ := by
  apply SingularChains.hom_ext
  intro f
  rw [generator_map_assoc,generator_lift,dite_eq_left (within_inclusion A f),lift_inclusion,Category.comp_id]

lemma liftChain_inclusion (n : ℕ) : lift A n ≫ (map (inclusionMap A)).f n = SingularSupport.cut (Within A) := by
  apply SingularChains.hom_ext
  intro f
  rw [generator_lift_assoc]
  by_cases hf : Within A f
  · rw [dite_eq_left hf,generator_map,inclusion_lift,SingularSupport.cut,generator_desc,ite_eq_left hf]
  · rw [dite_eq_right hf,zero_comp,SingularSupport.cut,generator_desc,ite_eq_right hf]

lemma inclusion_injective (n : ℕ) : Function.Injective ((map (inclusionMap A)).f n) := by
  apply Function.HasLeftInverse.injective
  refine ⟨lift A n,?_⟩
  intro c
  exact congrArg (fun h : (chains A).X n ⟶ (chains A).X n => h c) (inclusion_liftChain A n)

lemma inclusion_mem (n : ℕ) (c : (chains A).X n) : (map (inclusionMap A)).f n c ∈ group A n := by
  apply SingularSupport.induction_on ((group A n).comap ((map (inclusionMap A)).f n).hom) _ c
  intro f
  change (map (inclusionMap A)).f n (SingularSupport.gen f) ∈ group A n
  rw [SingularSupport.map_gen]
  exact SingularSupport.gen_mem _ (within_inclusion A f)

lemma group_eq_range (n : ℕ) : group A n = LinearMap.range ((map (inclusionMap A)).f n).hom := by
  apply le_antisymm
  · intro c hc
    refine ⟨lift A n c,?_⟩
    change (lift A n ≫ (map (inclusionMap A)).f n) c = c
    rw [liftChain_inclusion]
    exact SingularSupport.cut_eq hc
  · rintro _ ⟨c,rfl⟩; exact inclusion_mem A n c

end SingularSubspace
end

end OAI
