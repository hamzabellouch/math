import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.Reindexing

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology


namespace KirchbergRordam.GenericRW.SeparableReduction
section
open Set Topology TopologicalSpace
variable {A : Type*} [CStarAlgebra A]


def stage (s : Set A) : ℕ → Set A
  | 0 => s ∪ Set.range (algebraMap ℂ A)
  | n+1 => stage s n ∪ (fun p : A×A=>p.1+p.2) '' (stage s n ×ˢ stage s n) ∪
      (fun p : A×A=>p.1*p.2) '' (stage s n ×ˢ stage s n) ∪ star '' stage s n
lemma stage_step (s : Set A) (n : ℕ) : stage s n ⊆ stage s (n+1) :=
  fun _ hx => Or.inl (Or.inl (Or.inl hx))
lemma stage_mono (s : Set A) : Monotone (stage s) := monotone_nat_of_le_succ (stage_step s)
lemma stage_separable {s : Set A} (hs : IsSeparable s) (n : ℕ) : IsSeparable (stage s n) := by
  induction n with
  | zero => exact hs.union (isSeparable_range (continuous_algebraMap ℂ A))
  | succ n ih => exact ((ih.union ((ih.prod ih).image (continuous_fst.add continuous_snd))).union
      ((ih.prod ih).image (continuous_fst.mul continuous_snd))).union (ih.image continuous_star)
def termAlgebra (s : Set A) : StarSubalgebra ℂ A where
  carrier := ⋃ n, stage s n
  zero_mem' := mem_iUnion.mpr ⟨0,Or.inr ⟨0,map_zero _⟩⟩
  one_mem' := mem_iUnion.mpr ⟨0,Or.inr ⟨1,map_one _⟩⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    obtain ⟨m,hm⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max n m + 1,Or.inl (Or.inl (Or.inr
      ⟨(a,b),⟨stage_mono s (le_max_left _ _) hn,stage_mono s (le_max_right _ _) hm⟩,rfl⟩))⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    obtain ⟨m,hm⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max n m + 1,Or.inl (Or.inr
      ⟨(a,b),⟨stage_mono s (le_max_left _ _) hn,stage_mono s (le_max_right _ _) hm⟩,rfl⟩)⟩
  algebraMap_mem' z := mem_iUnion.mpr ⟨0,Or.inr ⟨z,rfl⟩⟩
  star_mem' := by
    intro a ha
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨n+1,Or.inr ⟨a,hn,rfl⟩⟩
lemma adjoin_separable {s : Set A} (hs : IsSeparable s) :
    IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  have ht : StarAlgebra.adjoin ℂ s ≤ termAlgebra s := StarAlgebra.adjoin_le
    (fun a ha=>mem_iUnion.mpr ⟨0,Or.inl ha⟩)
  exact (IsSeparable.iUnion (stage_separable hs)).mono ht


lemma closedAdjoin_separable {s : Set A} (hs : IsSeparable s) :
    IsSeparable ((StarAlgebra.adjoin ℂ s).topologicalClosure : Set A) :=
  (adjoin_separable hs).closure
end

open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
abbrev Term (A : Type*) := A×A×A×A
def term {R : Type*} [Ring R] (t : Term R) : R := t.1*(t.2.1*t.2.2.1-t.2.2.1*t.2.1)*t.2.2.2
lemma span_commutator_list {x : A} (hx : x∈DetectingSpace.commutatorIdeal (D:=A)) :
    ∃ l : List (Term A), (l.map term).sum=x := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨a,b,rfl⟩ := hx
    exact ⟨[(1,(a:A),(b:A),1)],by simp [term]⟩
  | zero => exact ⟨[],by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨l,hl⟩ := ihx
    obtain ⟨m,hm⟩ := ihy
    exact ⟨l++m,by simp [hl,hm]⟩
  | neg x hx ih =>
    obtain ⟨l,hl⟩ := ih
    refine ⟨l.map (fun t=>(-t.1,t.2)),?_⟩
    simp only [List.map_map,Function.comp_def]
    have he : (fun t : Term A=>term (-t.1,t.2))=fun t=> -(term t) := by funext t; simp [term]
    rw [he]
    have hn := congrArg (fun a : A=> -a) hl
    rw [List.sum_neg,List.map_map] at hn
    exact hn
  | left_absorb a x hx ih =>
    obtain ⟨l,hl⟩ := ih
    refine ⟨l.map (fun t=>(a*t.1,t.2)),?_⟩
    simp only [List.map_map,Function.comp_def]
    have he : (fun t : Term A=>term (a*t.1,t.2))=fun t=>a*term t := by funext t; simp [term,mul_assoc]
    rw [he,List.sum_map_mul_left,hl]
  | right_absorb b x hx ih =>
    obtain ⟨l,hl⟩ := ih
    refine ⟨l.map (fun t=>(t.1,t.2.1,t.2.2.1,t.2.2.2*b)),?_⟩
    simp only [List.map_map,Function.comp_def]
    have he : (fun t : Term A=>term (t.1,t.2.1,t.2.2.1,t.2.2.2*b))=fun t=>term t*b := by
      funext t; simp [term,mul_assoc]
    rw [he,List.sum_map_mul_right,hl]
end KirchbergRordam.GenericRW.SeparableReduction

namespace KirchbergRordam.GenericRW
open SeparableReduction
open TopologicalSpace Topology


theorem separable_characterless_subalgebra (D : Type*) [CStarAlgebra D] [Nontrivial D]
    (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ S : StarSubalgebra ℂ D, IsClosed (S : Set D) ∧
      TopologicalSpace.IsSeparable (S : Set D) ∧ IsEmpty (S →⋆ₐ[ℂ] ℂ) := by
  classical
  have h1 : (1:D)∈DetectingSpace.commutatorIdeal := by
    rw [DetectingSpace.commutatorIdeal_eq_top hD]
    trivial
  obtain ⟨l,hl⟩ := span_commutator_list h1
  let entries : Term D→List D := fun t=>[t.1,t.2.1,t.2.2.1,t.2.2.2]
  let f : Finset D := (l.flatMap entries).toFinset
  let S := (StarAlgebra.adjoin ℂ (f:Set D)).topologicalClosure
  have hm (t : Term D) (ht : t∈l) {a : D} (ha : a∈entries t) : a∈S := by
    apply StarSubalgebra.le_topologicalClosure
    apply StarAlgebra.subset_adjoin
    exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨t,ht,ha⟩)
  let liftTerm : {t // t∈l}→Term S := fun t =>
    (⟨t.1.1,hm t.1 t.2 (by simp [entries])⟩,
     ⟨t.1.2.1,hm t.1 t.2 (by simp [entries])⟩,
     ⟨t.1.2.2.1,hm t.1 t.2 (by simp [entries])⟩,
     ⟨t.1.2.2.2,hm t.1 t.2 (by simp [entries])⟩)
  have hh : (l.attach.map (fun t=>term (liftTerm t))).sum=(1:S) := by
    apply Subtype.ext
    change S.subtype ((l.attach.map (fun t=>term (liftTerm t))).sum)=1
    rw [map_list_sum,List.map_map]
    change (l.attach.map (fun t=>term t.1)).sum=1
    rw [List.attach_map_val,hl]
  refine ⟨S,StarSubalgebra.isClosed_topologicalClosure _,
    closedAdjoin_separable f.finite_toSet.isSeparable,⟨?_⟩⟩
  intro χ
  have hk (t : Term S) : χ (term t)=0 := by
    simp only [term,map_mul,map_sub]
    rw [mul_comm (χ t.2.1) (χ t.2.2.1),sub_self,mul_zero,zero_mul]
  have hz : χ ((l.attach.map (fun t=>term (liftTerm t))).sum)=0 := by
    rw [map_list_sum,List.map_map]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx
    exact hk _
  rw [hh,map_one] at hz
  exact one_ne_zero hz
end KirchbergRordam.GenericRW


namespace KirchbergRordam.GenericRW.MaxTensor
open Topology TopologicalSpace
open scoped CStarAlgebra
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]


theorem separable_maxTensor [SeparableSpace A] [SeparableSpace B] :
    SeparableSpace (Algebra A B) := by
  let s : Set (Algebra A B) := Set.range (includeLeft (A := A) (B := B)) ∪
    Set.range (includeRight (A := A) (B := B))
  let T := (StarAlgebra.adjoin ℂ s).topologicalClosure
  have hsep : IsSeparable (T : Set (Algebra A B)) :=
    SeparableReduction.closedAdjoin_separable ((isSeparable_range (map_continuous includeLeft)).union
      (isSeparable_range (map_continuous includeRight)))
  have hinc : s ⊆ T := (StarAlgebra.subset_adjoin ℂ s).trans
    (StarSubalgebra.le_topologicalClosure _)
  have hall (x : Algebra A B) : x ∈ T := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact StarSubalgebra.isClosed_topologicalClosure _
    | ih x =>
      suffices ∀ tensor : A ⊗[ℂ] B, of (rawEquiv tensor) ∈ T from this x
      intro tensor
      induction tensor using TensorProduct.inductionOn with
      | tmul a b =>
        change of (a ⊗ₜ[ℂ] b) ∈ T
        rw [of_tmul]
        exact T.mul_mem (hinc (Or.inl ⟨a,rfl⟩)) (hinc (Or.inr ⟨b,rfl⟩))
      | add x y hx hy => rw [map_add, map_add]; exact T.add_mem hx hy
  exact isSeparable_univ_iff.mp (hsep.mono (fun x _ => hall x))

instance powerPack_separable (D : Type*) [CStarAlgebra D] [SeparableSpace D] (n : ℕ) :
    SeparableSpace (powerPack D n) := by
  induction n with
  | zero => exact inferInstanceAs (SeparableSpace D)
  | succ n ih =>
    let := ih
    exact separable_maxTensor (A := D) (B := powerPack D n)
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.PrimeDimensionDrop
open MatrixTensor
open scoped Matrix Kronecker ComplexOrder CStarAlgebra


@[simp] lemma eval_apply (p q : ℕ) (t : unitInterval) (f : C(unitInterval, Fiber p q)) :
    eval p q t f = f t := rfl


instance (p q : ℕ) [NeZero p] [NeZero q] : Nontrivial (Algebra p q) := inferInstance

instance (p q : ℕ) : TopologicalSpace.SeparableSpace (Algebra p q) := inferInstance

def inclusion (p q : ℕ) : Algebra p q →⋆ₐ[ℂ] C(unitInterval, Fiber p q) :=
  (subalgebra p q).subtype

def evaluation (p q : ℕ) (t : unitInterval) : Algebra p q →⋆ₐ[ℂ] Fiber p q :=
  (eval p q t).comp (inclusion p q)

@[simp] lemma evaluation_apply (p q : ℕ) (t : unitInterval) (f : Algebra p q) :
    evaluation p q t f = f.val t := rfl

lemma mem_iff {p q : ℕ} (f : C(unitInterval, Fiber p q)) :
    f ∈ subalgebra p q ↔
      (∃ a : Mat (Fin p), leftMatrix a = f 0) ∧
      (∃ b : Mat (Fin q), rightMatrix b = f 1) := Iff.rfl


lemma norm_le_iff {p q : ℕ} (f : Algebra p q) {r : ℝ} (hr : 0 ≤ r) :
    ‖f‖ ≤ r ↔ ∀ t, ‖evaluation p q t f‖ ≤ r :=
  (ContinuousMap.norm_le f.val hr)


def scalar (p q : ℕ) : C(unitInterval, ℂ) →⋆ₐ[ℂ] Algebra p q where
  toFun f := ⟨⟨fun t => (f t) • (1 : Fiber p q), by fun_prop⟩, by
    constructor
    · exact ⟨(f 0) • 1, by simp⟩
    · exact ⟨(f 1) • 1, by simp⟩⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' f g := by ext; simp [add_smul]
  map_mul' f g := by ext; simp [mul_smul, mul_left_comm]
  commutes' z := by ext; simp [Algebra.algebraMap_eq_smul_one]
  map_star' f := by ext; simp


def reparam {p q : ℕ} (ξ : C(unitInterval, unitInterval)) (h0 : ξ 0 = 0)
    (h1 : ξ 1 = 1) : Algebra p q →⋆ₐ[ℂ] Algebra p q where
  toFun f := ⟨f.val.comp ξ, by
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := f.property
    exact ⟨⟨a, by simpa [h0] using ha⟩,⟨b, by simpa [h1] using hb⟩⟩⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

end KirchbergRordam.PrimeDimensionDrop

namespace KirchbergRordam.NormUltrapower
open TopologicalSpace


theorem generic_maximal_power_to_central {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
    [SeparableSpace A] [SeparableSpace D] (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (φ : D →⋆ₐ[ℂ] CentralAlgebra A ω) (n : ℕ) :
    Nonempty (GenericRW.MaxTensor.powerPack D n →⋆ₐ[ℂ] CentralAlgebra A ω) := by
  induction n with
  | zero => exact ⟨φ⟩
  | succ n ih =>
    obtain ⟨ψ⟩ := ih
    obtain ⟨θ,hθ⟩ := relative_commuting_copy ω hω φ ψ
    exact ⟨GenericRW.MaxTensor.lift θ ψ hθ⟩
end KirchbergRordam.NormUltrapower

namespace KirchbergRordam
open TopologicalSpace
omit [GenericRW.Size] [GenericRW.PauliData] in


theorem central_prime_power_drop (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [SeparableSpace A] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hF : IsEmpty (NormUltrapower.CentralAlgebra A ω →⋆ₐ[ℂ] ℂ)) (k : ℕ) :
    Nonempty (PrimeDimensionDrop.Algebra (2^(k+1)) (2^(k+1)+1) →⋆ₐ[ℂ]
      NormUltrapower.CentralAlgebra A ω) := by
  let : GenericRW.Size := GenericRW.powerSize k
  let : GenericRW.PauliData := GenericRW.powerPauliData k
  obtain ⟨S,hclosed,hsep,hS⟩ := GenericRW.separable_characterless_subalgebra
    (NormUltrapower.CentralAlgebra A ω) hF
  let : IsClosed (S : Set (NormUltrapower.CentralAlgebra A ω)) := hclosed
  let : CStarAlgebra S := StarSubalgebra.cstarAlgebra S
  let : SeparableSpace S := hsep.separableSpace
  obtain ⟨m,⟨φ⟩⟩ := GenericRW.finite_prime_power_drop S hS k
  obtain ⟨ψ⟩ := NormUltrapower.generic_maximal_power_to_central ω hω S.subtype m
  exact ⟨ψ.comp φ⟩
end KirchbergRordam
end

end OAI
