import Mathlib
import OAI.GroupTheory.FiniteType.HomStabilizer

namespace OAI

noncomputable section
open scoped Pointwise
namespace BinaryAlgebraPresentation
abbrev Integral (A : Type*) := FreeAbelianGroup (FreeMonoid A)
abbrev Binary (A : Type*) := FreeAlgebra (ZMod 2) A
variable (A : Type*)

def reduction : Integral A →+* Binary A :=
  FreeAbelianGroup.liftMonoid (FreeMonoid.lift (FreeAlgebra.ι (ZMod 2)))

@[simp] lemma reduction_gen (a : A) :
    reduction A (FreeAbelianGroup.of (FreeMonoid.of a)) = FreeAlgebra.ι (ZMod 2) a := by
  simp [reduction]

lemma reduction_surjective : Function.Surjective (reduction A) := by
  intro x
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    refine ⟨(c.val : Integral A),?_⟩
    simp only [map_natCast]
    simpa only [map_natCast] using
      congrArg (algebraMap (ZMod 2) (Binary A)) (ZMod.natCast_zmod_val c)
  | grade1 a => exact ⟨FreeAbelianGroup.of (FreeMonoid.of a),reduction_gen A a⟩
  | mul x y hx hy =>
    obtain ⟨u,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    exact ⟨u*v,map_mul _ _ _⟩
  | add x y hx hy =>
    obtain ⟨u,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    exact ⟨u+v,map_add _ _ _⟩

lemma reduction_kernel : TwoSidedIdeal.ker (reduction A) = TwoSidedIdeal.span {2} := by
  let I : TwoSidedIdeal (Integral A) := TwoSidedIdeal.span {2}
  have hI : I ≤ TwoSidedIdeal.ker (reduction A) := by
    apply TwoSidedIdeal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change reduction A 2=0
    simp only [map_ofNat]
    exact CharP.ofNat_eq_zero (Binary A) 2
  let Q := I.ringCon.Quotient
  let q : Integral A →+* Q := I.ringCon.mk'
  have hq (x : Integral A) : q x=0 ↔ x∈I := by
    change x∈TwoSidedIdeal.ker q ↔ x∈I
    rw [TwoSidedIdeal.ker_ringCon_mk']
  let : Nontrivial Q := ⟨⟨0,1,by
    intro h
    have hi : (1 : Integral A)∈I := (hq 1).mp (by simpa using h.symm)
    have hk : reduction A 1=0 := hI hi
    simp at hk⟩⟩
  let : CharP Q 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by
    have : q 2=0 := (hq 2).mpr (TwoSidedIdeal.subset_span (by simp))
    simpa only [map_ofNat,Nat.cast_ofNat] using this)
  let : Algebra (ZMod 2) Q := ZMod.algebra Q 2
  let r : Binary A →ₐ[ZMod 2] Q :=
    FreeAlgebra.lift (ZMod 2) (fun a => q (FreeAbelianGroup.of (FreeMonoid.of a)))
  have gen : ∀ w : FreeMonoid A, r (reduction A (FreeAbelianGroup.of w)) =
      q (FreeAbelianGroup.of w) := by
    have hm : (r.toRingHom.comp (reduction A)).toMonoidHom.comp FreeAbelianGroup.ofMulHom =
        q.toMonoidHom.comp FreeAbelianGroup.ofMulHom := by
      apply FreeMonoid.hom_eq
      intro a
      simp [r]
    intro w
    exact congrArg (fun f : FreeMonoid A →* Q => f w) hm
  have all (x : Integral A) : r (reduction A x)=q x := by
    induction x using FreeAbelianGroup.induction_on with
    | zero => simp
    | of w => exact gen w
    | neg x hx => simpa only [map_neg] using congrArg Neg.neg hx
    | add x y hx hy => simp only [map_add,hx,hy]
  apply le_antisymm _ hI
  intro x hx
  apply (hq x).mp
  change reduction A x=0 at hx
  rw [← all x,hx,map_zero]
variable {R S T : Type*} [Ring R] [Ring S] [Ring T]

lemma kernel_composition (f : R →+* S) (hf : Function.Surjective f)
    (g : S →+* T) (s : Set R) (t : Set S)
    (hfs : TwoSidedIdeal.ker f=TwoSidedIdeal.span s)
    (hgt : TwoSidedIdeal.ker g=TwoSidedIdeal.span t) :
    TwoSidedIdeal.ker (g.comp f)=
      TwoSidedIdeal.span (s ∪ (Function.surjInv hf '' t)) := by
  classical
  let v : S → R := Function.surjInv hf
  have hv : ∀ y, f (v y)=y := Function.surjInv_eq hf
  let J : TwoSidedIdeal R := TwoSidedIdeal.span (s ∪ (v '' t))
  have hsJ : TwoSidedIdeal.span s ≤ J := TwoSidedIdeal.span_mono Set.subset_union_left
  have hlift : ∀ y, y∈TwoSidedIdeal.span t → ∃ x∈J, f x=y := by
    intro y hy
    induction hy using TwoSidedIdeal.span_induction with
    | mem y hy =>
      exact ⟨v y,TwoSidedIdeal.subset_span (Or.inr ⟨y,hy,rfl⟩),hv y⟩
    | zero => exact ⟨0,J.zero_mem,map_zero f⟩
    | add x y _ _ hx hy =>
      obtain ⟨x',hx',hfx⟩ := hx
      obtain ⟨y',hy',hfy⟩ := hy
      exact ⟨x'+y',J.add_mem hx' hy',by rw [map_add,hfx,hfy]⟩
    | neg x _ hx =>
      obtain ⟨x',hx',hfx⟩ := hx
      exact ⟨-x',J.neg_mem hx',by rw [map_neg,hfx]⟩
    | left_absorb a x _ hx =>
      obtain ⟨x',hx',hfx⟩ := hx
      exact ⟨v a*x',J.mul_mem_left _ _ hx',by rw [map_mul,hv,hfx]⟩
    | right_absorb b x _ hx =>
      obtain ⟨x',hx',hfx⟩ := hx
      exact ⟨x'*v b,J.mul_mem_right _ _ hx',by rw [map_mul,hv,hfx]⟩
  apply le_antisymm
  · intro x hx
    have hx : g (f x)=0 := (TwoSidedIdeal.mem_ker (g.comp f)).mp hx
    have hfx : f x∈TwoSidedIdeal.span t := hgt ▸ (TwoSidedIdeal.mem_ker g).mpr hx
    obtain ⟨y,hy,hfy⟩ := hlift (f x) hfx
    have hsub : x-y∈TwoSidedIdeal.ker f := by
      apply (TwoSidedIdeal.mem_ker f).mpr
      rw [map_sub,hfy,sub_self]
    have hm := J.add_mem (hsJ (hfs ▸ hsub)) hy
    simpa only [sub_add_cancel] using hm
  · apply TwoSidedIdeal.span_le.mpr
    intro x hx
    apply (TwoSidedIdeal.mem_ker (g.comp f)).mpr
    change g (f x)=0
    rcases hx with hx | ⟨y,hy,rfl⟩
    · have hz : f x=0 := (TwoSidedIdeal.mem_ker f).mp
        (hfs.symm ▸ TwoSidedIdeal.subset_span hx)
      rw [hz,map_zero]
    · rw [hv]
      exact (TwoSidedIdeal.mem_ker g).mp (hgt.symm ▸ TwoSidedIdeal.subset_span hy)

theorem integral_presentation
    (π : Binary A →+* R) (hπ : Function.Surjective π)
    (rel : Set (Binary A)) (hrel : rel.Finite)
    (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel) :
    ∃ (q : Integral A →ₙ+* R) (s : Set (Integral A)),
      Function.Surjective q ∧ s.Finite ∧
      {x | q x=0}=(TwoSidedIdeal.span s : Set (Integral A)) := by
  let v := Function.surjInv (reduction_surjective A)
  refine ⟨(π.comp (reduction A)).toNonUnitalRingHom,{2} ∪ (v '' rel),
    hπ.comp (reduction_surjective A),
    (Set.finite_singleton 2).union (hrel.image v),?_⟩
  have hk := kernel_composition (reduction A) (reduction_surjective A)
    π {2} rel (reduction_kernel A) hker
  ext x
  change (π.comp (reduction A)) x=0 ↔ x∈TwoSidedIdeal.span ({2} ∪ (v '' rel))
  rw [←TwoSidedIdeal.mem_ker (π.comp (reduction A)),hk]

theorem rank_six_of_binary_presentation [Finite A]
    (π : Binary A →+* R) (hπ : Function.Surjective π)
    (rel : Set (Binary A)) (hrel : rel.Finite)
    (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel) :
    Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R) := by
  obtain ⟨q,s,hq,hs,hks⟩ := integral_presentation A π hπ rel hrel hker
  exact SteinbergFinitePresentation.rank_six_finitelyPresented A q hq s hs hks

end BinaryAlgebraPresentation

open scoped Pointwise
namespace StageGeometry
open StageConstruction
variable {R Y W G : Type} [Ring R] [Nontrivial R] [Group W] [MulAction W Y]
  [DecidableEq Y] [Group G]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y y', T y*S y'=if y=y' then e else 0) (hSe : ∀ y, S y*e=S y)
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point) (he : e≠0)
variable (F₂ : PairDiagrams (ZMod 2) ι point) (F₃ : PairDiagrams (ZMod 3) ι point)

include hTS hSe hTρ hpt he F₂ F₃ in

theorem action_of_binary_ring_data
    (A : Type) [Finite A] (π : FreeAlgebra (ZMod 2) A →+* R)
    (hπ : Function.Surjective π) (rel : Set (FreeAlgebra (ZMod 2) A))
    (hrel : rel.Finite) (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel)
    (g : G →* Rˣ) (hg : Function.Injective g) :
    letI := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
    Countable (LimitPoints φ S point) ∧ Infinite (LimitPoints φ S point) ∧
      FaithfulSMul (LimitGroup φ D ρ ι hφ hρ hι) (LimitPoints φ S point) ∧
      (∃ ν : G →* LimitGroup φ D ρ ι hφ hρ hι, Function.Injective ν) ∧
      (∀ n (x y : Fin n → LimitPoints φ S point),
        Function.Injective x → Function.Injective y →
        ∃ q : LimitGroup φ D ρ ι hφ hρ hι, ∀ j, q • x j=y j) ∧
      SimpleFInftyOvergroups.HasTypeFInfty (LimitGroup φ D ρ ι hφ hρ hι) ∧
      (∀ n (x : Fin n → LimitPoints φ S point), Function.Injective x →
        SimpleFInftyOvergroups.HasTypeFInfty
          (HomStabilizer.fixedTuple
            (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι) x)) ∧
      (∀ s : Set (LimitPoints φ S point), s.Finite →
        SimpleFInftyOvergroups.HasTypeFInfty (fixingSubgroup (LimitGroup φ D ρ ι hφ hρ hι) s) ∧
        SimpleFInftyOvergroups.HasTypeFInfty
          (MulAction.stabilizer (LimitGroup φ D ρ ι hφ hρ hι) s)) := by
  let := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
  obtain ⟨q,s,hq,hs,hks⟩ := BinaryAlgebraPresentation.integral_presentation A π hπ rel hrel hker
  let : Countable R := hq.countable
  let := SteinbergFinitePresentation.rank_six_finitelyPresented A q hq s hs hks
  have hf := delta_injective φ D ρ ι hφ hρ hι
  have hm := limitRepresentation_injective φ D e S T hTS ρ ι point hρS hpoint hφ hρ hι hpt he
  refine ⟨limitPoints_countable φ S point,
    limitPoints_infinite φ e S T hTS point hφ hpt he,⟨?_⟩,?_,?_,?_,?_,?_⟩
  · intro a b hab
    apply hm
    exact Equiv.ext hab
  · refine ⟨(AscendingHNN.embed (delta φ D ρ ι) hf).comp ((transitionUnits φ D).comp g),?_⟩
    exact (AscendingHNN.embed_injective _ _).comp
      ((transitionUnits_injective φ D hφ).comp hg)
  · intro n x y hx hy
    exact limit_tuple_transitivity φ D e S T hTS hSe ρ ι point hρS hpoint hφ hρ hι hpt n x y hx hy
  · exact limit_geometric φ D e S T hTS hSe ρ ι point hρS hTρ hpoint hφ hρ hι hpt he F₂ F₃
  · intro n x hx
    exact finite_tuple_geometric φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
      hφ hρ hι hpt he F₂ F₃ n x hx
  · intro s hs
    exact ⟨finite_pointwise_geometric φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
      hφ hρ hι hpt he F₂ F₃ s hs,
      finite_setwise_geometric φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
      hφ hρ hι hpt he F₂ F₃ s hs⟩
end StageGeometry

end

end OAI
