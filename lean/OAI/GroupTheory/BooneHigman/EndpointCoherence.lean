import OAI.GroupTheory.BooneHigman.BinaryCategory
import OAI.GroupTheory.BooneHigman.DecoratedPresentation

namespace OAI

noncomputable section

/-!
Associators, symmetries, coordinate invariance, and coherence of endpoint quotient data.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
open CategoryTheory
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X] (s : Finset (Seed (Γ:=Γ) x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

/-- Every algebraic field comes from the finite structural quotient's proved
relations. No new relation is postulated in order to invoke coherence. -/
def structuralBinaryData : BinaryGroupCategory.Data (StructuralQuotient (Γ:=Γ) x s) where
  tensor := structuralTensor x s hs
  a := structuralAssociator x s
  naturality := structuralTensor_associativity x s hs
  pentagon := by
    simpa only [structuralTensor_apply,map_one,mul_one,one_mul] using
      structuralTensor_pentagon x s hs

/-- The actual finite quotient is the positive-object automorphism group of a
monoidal category. Its empty object is separate, with trivial automorphism group. -/
@[instance_reducible] def structuralMonoidal :
    MonoidalCategory (BinaryGroupCategory.Object (StructuralQuotient (Γ:=Γ) x s)) :=
  BinaryGroupCategory.monoidal (structuralBinaryData x s hs)

def structuralExpansion : FreeMonoidalCategory PUnit ⥤
    BinaryGroupCategory.Object (StructuralQuotient (Γ:=Γ) x s) := by
  letI := structuralMonoidal x s hs
  exact FreeMonoidalCategory.project (fun _=>.positive)

/-- All parallel associator/unitor routes agree internally in the finite
presentation. This reuses pinned Mathlib's proved monoidal-coherence theorem,
not the semantic action's equality or any unproved presentation theorem. -/
lemma coherent_structural_routes {A B : FreeMonoidalCategory PUnit} (f g : A ⟶ B) :
    ((structuralExpansion x s hs).map f).val=((structuralExpansion x s hs).map g).val := by
  exact congrArg (fun h : A ⟶ B=>((structuralExpansion x s hs).map h).val)
    (Subsingleton.elim f g)

lemma structuralExpansion_associator :
    ((structuralExpansion (Γ:=Γ) x s hs).map
      (CategoryTheory.MonoidalCategory.associator
        (FreeMonoidalCategory.of PUnit.unit) (FreeMonoidalCategory.of PUnit.unit)
          (FreeMonoidalCategory.of PUnit.unit)).hom).val=(structuralAssociator x s)⁻¹ := rfl

end Generators
end

section
universe u v
open CategoryTheory
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X] (s : Finset (Seed (Γ:=Γ) x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

def structuralSymmetryData : BinaryGroupCategory.SymmetryData (structuralBinaryData (Γ:=Γ) x s hs) where
  c := structuralSymmetry x s
  square := structuralSymmetry_square x s
  naturality := structuralTensor_symmetry x s hs
  hexagon := by
    change structuralSymmetry x s = structuralAssociator x s *
      structuralTensor x s hs (1,structuralSymmetry x s) * (structuralAssociator x s)⁻¹ *
        structuralTensor x s hs (structuralSymmetry x s,1) * structuralAssociator x s
    simpa only [structuralTensor_apply,map_one,mul_one,one_mul] using structuralTensor_hexagon x s hs

@[instance_reducible] def structuralSymmetric : letI := structuralMonoidal (Γ:=Γ) x s hs;
    SymmetricCategory (BinaryGroupCategory.Object (StructuralQuotient x s)) :=
  BinaryGroupCategory.symmetric (structuralBinaryData x s hs) (structuralSymmetryData x s hs)

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

lemma structuralProject_middleSwapWord :
    structuralProject x s (middleSwapWord x)=
      BinaryGroupCategory.middleSwap (structuralBinaryData x s hs) (structuralSymmetryData x s hs) := by
  simp only [BinaryGroupCategory.middleSwap,structuralBinaryData,structuralSymmetryData,
    structuralTensor_apply,map_one,one_mul,mul_one,structuralAssociator,structuralSymmetry,
    structuralLocalization_project,structuralRightLocalization_project,middleSwapWord,
    map_mul,map_inv]

lemma structuralMiddleSwap_naturality (g : StructuralQuotient (Γ:=Γ) x s) :
    Commute (structuralProject x s (middleSwapWord x))
      (structuralTensor x s hs (structuralTensor x s hs (g,g),structuralTensor x s hs (g,g))) := by
  rw [structuralProject_middleSwapWord x s hs]
  exact BinaryGroupCategory.middleSwap_naturality (structuralBinaryData x s hs)
    (structuralSymmetryData x s hs) g

lemma decoratedMiddleSwap_naturality (g : DecoratedQuotient (Γ:=Γ) x s t) :
    Commute (decoratedProject x s t (middleSwapWord x))
      (decoratedTensor x s t hs (decoratedTensor x s t hs (g,g),decoratedTensor x s t hs (g,g))) := by
  obtain ⟨g,rfl⟩ := structuralToDecorated_surjective x s t g
  have h := (structuralMiddleSwap_naturality x s hs g).map (structuralToDecorated x s t)
  simpa only [structuralToDecorated_tensor,structuralToDecorated_project] using h

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes
universe u v w
variable {Γ : Type u} {X : Type v} {H : Type w} [Group Γ] [MulAction Γ X] [Group H]

/-- A grid relation propagates along ordered-pair orbits, because the middle
transposition commutes with four identical leaf labels. -/
theorem covariant_interchange (R D : Γ → H) (E : X → X → H) (M : H)
    (hc : ∀ g a b,R g*E a b=E (g • a) (g • b)*D g)
    (hm : ∀ g,Commute M (D g))
    {a b c d : X} (g : Γ) (hga : g • a=c) (hgb : g • b=d)
    (hab : E a b=E b a*M) : E c d=E d c*M := by
  apply mul_right_cancel (b:=D g)
  calc
    E c d*D g=R g*E a b := by rw [hc,hga,hgb]
    _=R g*(E b a*M) := by rw [hab]
    _=(E d c*D g)*M := by rw [← mul_assoc,hc,hga,hgb]
    _=(E d c*M)*D g := by rw [mul_assoc,← (hm g).eq,← mul_assoc]

end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)
variable (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)
variable (y : X) (hxy : x≠y)
variable (htwo : ∀ x₁ x₂ y₁ y₂ : X,x₁≠x₂ → y₁≠y₂ →
  ∃ g : Γ,g • x₁=y₁ ∧ g • x₂=y₂)
include hs ht hxy htwo

/-- Every distinct-colour elementary interchange follows inside the explicit
finite endpoint quotient, from its one pair representative and finite label
and structural laws. This is not a completeness theorem for arbitrary tables. -/
lemma endpoint_interchange_all (a b : X) (hab : a≠b) :
    endpointProject x s t y (gridWord x a b)=
      endpointProject x s t y (gridWord x b a)*endpointProject x s t y (middleSwapWord x) := by
  let F := decoratedToEndpoint x s t y
  let E := fun a b=>F (decoratedGrid x s t hs a b)
  let R := fun g=>F (decoratedRoot x s t g)
  let D := fun g=>F (decoratedTensor x s t hs
    (decoratedDiagonal x s t hs g,decoratedDiagonal x s t hs g))
  let M := endpointProject x s t y (middleSwapWord x)
  have hc (g : Γ) (a b : X) : R g*E a b=E (g • a) (g • b)*D g := by
    simpa only [map_mul] using congrArg F (decoratedGrid_covariance x s t hs ht g a b)
  have hm (g : Γ) : Commute M (D g) := by
    have h := decoratedMiddleSwap_naturality x s t hs (decoratedRoot x s t g)
    rw [← decoratedDiagonal_tensor x s t hs g] at h
    exact h.map F
  have he (a b : X) : E a b=endpointProject x s t y (gridWord x a b) := by
    dsimp only [E,F]
    rw [← decoratedProject_gridWord x s t hs,decoratedToEndpoint_project]
  have hr : E x y=E y x*M := by
    rw [he,he]
    exact endpoint_interchange x s t y
  obtain ⟨g,hga,hgb⟩ := htwo x y a b hxy hab
  have h := covariant_interchange R D E M hc hm g hga hgb hr
  rwa [he,he] at h

/-- The infinite family of pair-colour kernel words is killed by this one
finite presentation candidate. No kernel injectivity is used. -/
lemma endpointProject_interchange_all (a b : X) (hab : a≠b) :
    endpointProject x s t y (interchangeWord x a b)=1 := by
  simp only [interchangeWord,map_mul,map_inv]
  rw [endpoint_interchange_all x s t hs ht y hxy htwo a b hab]
  group

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

lemma structuralMiddleSwap_interchange (a b c d : StructuralQuotient (Γ:=Γ) x s) :
    structuralProject x s (middleSwapWord x)*
      structuralTensor x s hs (structuralTensor x s hs (a,b),structuralTensor x s hs (c,d))*
        (structuralProject x s (middleSwapWord x))⁻¹=
      structuralTensor x s hs (structuralTensor x s hs (a,c),structuralTensor x s hs (b,d)) := by
  rw [structuralProject_middleSwapWord x s hs]
  exact BinaryGroupCategory.middleSwap_interchange (structuralBinaryData x s hs)
    (structuralSymmetryData x s hs) a b c d

lemma decoratedMiddleSwap_interchange (a b c d : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedProject x s t (middleSwapWord x)*
      decoratedTensor x s t hs (decoratedTensor x s t hs (a,b),decoratedTensor x s t hs (c,d))*
        (decoratedProject x s t (middleSwapWord x))⁻¹=
      decoratedTensor x s t hs (decoratedTensor x s t hs (a,c),decoratedTensor x s t hs (b,d)) := by
  obtain ⟨a,rfl⟩ := structuralToDecorated_surjective x s t a
  obtain ⟨b,rfl⟩ := structuralToDecorated_surjective x s t b
  obtain ⟨c,rfl⟩ := structuralToDecorated_surjective x s t c
  obtain ⟨d,rfl⟩ := structuralToDecorated_surjective x s t d
  have h := congrArg (structuralToDecorated x s t) (structuralMiddleSwap_interchange x s hs a b c d)
  simpa only [map_mul,map_inv,structuralToDecorated_tensor,structuralToDecorated_project] using h

lemma decoratedColourTensor_double (y z : X) (a b c d : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedColourTensor x s t hs y
      (decoratedColourTensor x s t hs z (a,b),decoratedColourTensor x s t hs z (c,d))=
      decoratedGrid x s t hs y z *
        decoratedTensor x s t hs (decoratedTensor x s t hs (a,b),decoratedTensor x s t hs (c,d))*
          (decoratedGrid x s t hs y z)⁻¹ := by
  let T := decoratedTensor x s t hs
  let B := decoratedBaker x s t hs
  have hT : T (B z*T (a,b)*(B z)⁻¹,B z*T (c,d)*(B z)⁻¹)=
      T (B z,B z)*T (T (a,b),T (c,d))*(T (B z,B z))⁻¹ := by
    change T (((B z,B z)*(T (a,b),T (c,d)))*(B z,B z)⁻¹)=_
    rw [map_mul,map_mul,map_inv]
  simp only [decoratedColourTensor_apply,decoratedGrid]
  change B y*T (B z*T (a,b)*(B z)⁻¹,B z*T (c,d)*(B z)⁻¹)*(B y)⁻¹=_
  rw [hT]
  change _=(B y*T (B z,B z))*T (T (a,b),T (c,d))*(B y*T (B z,B z))⁻¹
  group

variable (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)
variable (y₀ : X) (hxy : x≠y₀)
variable (htwo : ∀ x₁ x₂ y₁ y₂ : X,x₁≠x₂ → y₁≠y₂ →
  ∃ g : Γ,g • x₁=y₁ ∧ g • x₂=y₂)
include ht hxy htwo

/-- Arbitrary four decorated subtrees obey the colour interchange in the finite
endpoint quotient. This is the local contextual law, not only the empty grid law. -/
lemma endpoint_decorated_interchange (y z : X) (hyz : y≠z)
    (a b c d : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedToEndpoint x s t y₀ (decoratedColourTensor x s t hs y
      (decoratedColourTensor x s t hs z (a,b),decoratedColourTensor x s t hs z (c,d)))=
    decoratedToEndpoint x s t y₀ (decoratedColourTensor x s t hs z
      (decoratedColourTensor x s t hs y (a,c),decoratedColourTensor x s t hs y (b,d))) := by
  let F := decoratedToEndpoint x s t y₀
  let T := decoratedTensor x s t hs
  let M := decoratedProject x s t (middleSwapWord x)
  have hg : F (decoratedGrid x s t hs y z)=F (decoratedGrid x s t hs z y)*F M := by
    simp only [F,M,← decoratedProject_gridWord x s t hs,decoratedToEndpoint_project]
    exact endpoint_interchange_all x s t hs ht y₀ hxy htwo y z hyz
  have hm : F M*F (T (T (a,b),T (c,d)))*(F M)⁻¹=F (T (T (a,c),T (b,d))) := by
    simpa only [map_mul,map_inv] using congrArg F (decoratedMiddleSwap_interchange x s t hs a b c d)
  rw [decoratedColourTensor_double,decoratedColourTensor_double]
  change F (_*T (T (a,b),T (c,d))*_⁻¹)=F (_*T (T (a,c),T (b,d))*_⁻¹)
  simp only [map_mul,map_inv]
  rw [hg]
  calc
    _=F (decoratedGrid x s t hs z y)*(F M*F (T (T (a,b),T (c,d)))*(F M)⁻¹)*
      (F (decoratedGrid x s t hs z y))⁻¹ := by group
    _=_ := by rw [hm]

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x)) (y₀ : X)
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

lemma decoratedToEndpoint_surjective : Function.Surjective (decoratedToEndpoint (Γ:=Γ) x s t y₀) :=
  FiniteLocalizationClosure.quotientMap_surjective _ _ _ _

def endpointLocalization : EndpointQuotient x s t y₀ →* EndpointQuotient x s t y₀ :=
  FiniteLocalizationClosure.localization _ _ _ _ hs

def endpointRightLocalization : EndpointQuotient x s t y₀ →* EndpointQuotient x s t y₀ :=
  (MulAut.conj (endpointProject x s t y₀ (flipWord x))).toMonoidHom.comp
    (endpointLocalization x s t y₀ hs)

lemma decoratedToEndpoint_localization (g : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedToEndpoint x s t y₀ (decoratedLocalization x s t hs g)=
      endpointLocalization x s t y₀ hs (decoratedToEndpoint x s t y₀ g) :=
  FiniteLocalizationClosure.quotientMap_localization _ _ _ _ hs g

lemma decoratedToEndpoint_rightLocalization (g : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedToEndpoint x s t y₀ (decoratedRightLocalization x s t hs g)=
      endpointRightLocalization x s t y₀ hs (decoratedToEndpoint x s t y₀ g) := by
  change decoratedToEndpoint x s t y₀ (decoratedProject x s t (flipWord x)*
    decoratedLocalization x s t hs g*(decoratedProject x s t (flipWord x))⁻¹)=_
  rw [map_mul,map_mul,map_inv,decoratedToEndpoint_localization]
  rfl

lemma endpointLocalizations_commute (g h : EndpointQuotient (Γ:=Γ) x s t y₀) :
    Commute (endpointLocalization x s t y₀ hs g) (endpointRightLocalization x s t y₀ hs h) := by
  obtain ⟨g,rfl⟩ := decoratedToEndpoint_surjective x s t y₀ g
  obtain ⟨h,rfl⟩ := decoratedToEndpoint_surjective x s t y₀ h
  simpa only [decoratedToEndpoint_localization,decoratedToEndpoint_rightLocalization] using
    (decoratedLocalizations_commute x s t hs g h).map (decoratedToEndpoint x s t y₀)

def endpointTensor : EndpointQuotient (Γ:=Γ) x s t y₀ × EndpointQuotient x s t y₀ →*
    EndpointQuotient x s t y₀ :=
  (endpointLocalization x s t y₀ hs).noncommCoprod (endpointRightLocalization x s t y₀ hs)
    (endpointLocalizations_commute x s t y₀ hs)

lemma endpointTensor_apply (g h : EndpointQuotient (Γ:=Γ) x s t y₀) :
    endpointTensor x s t y₀ hs (g,h)=endpointLocalization x s t y₀ hs g *
      endpointRightLocalization x s t y₀ hs h := rfl

lemma decoratedToEndpoint_tensor (g h : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedToEndpoint x s t y₀ (decoratedTensor x s t hs (g,h))=
      endpointTensor x s t y₀ hs (decoratedToEndpoint x s t y₀ g,decoratedToEndpoint x s t y₀ h) := by
  simp only [decoratedTensor_apply,endpointTensor_apply,map_mul,
    decoratedToEndpoint_localization,decoratedToEndpoint_rightLocalization]

def endpointBaker (y : X) : EndpointQuotient x s t y₀ :=
  decoratedToEndpoint x s t y₀ (decoratedBaker x s t hs y)

def endpointColourTensor (y : X) : EndpointQuotient (Γ:=Γ) x s t y₀ × EndpointQuotient x s t y₀ →*
    EndpointQuotient x s t y₀ :=
  (MulAut.conj (endpointBaker x s t y₀ hs y)).toMonoidHom.comp (endpointTensor x s t y₀ hs)

lemma endpointColourTensor_apply (y : X) (g h : EndpointQuotient (Γ:=Γ) x s t y₀) :
    endpointColourTensor x s t y₀ hs y (g,h)=endpointBaker x s t y₀ hs y *
      endpointTensor x s t y₀ hs (g,h)*(endpointBaker x s t y₀ hs y)⁻¹ := rfl

lemma decoratedToEndpoint_colourTensor (y : X) (g h : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedToEndpoint x s t y₀ (decoratedColourTensor x s t hs y (g,h))=
      endpointColourTensor x s t y₀ hs y (decoratedToEndpoint x s t y₀ g,decoratedToEndpoint x s t y₀ h) := by
  simp only [decoratedColourTensor_apply,endpointColourTensor_apply,map_mul,map_inv,
    decoratedToEndpoint_tensor,endpointBaker]

variable (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤) (hxy : x≠y₀)
variable (htwo : ∀ x₁ x₂ y₁ y₂ : X,x₁≠x₂ → y₁≠y₂ →
  ∃ g : Γ,g • x₁=y₁ ∧ g • x₂=y₂)
include ht hxy htwo

lemma endpointColourTensor_interchange (y z : X) (hyz : y≠z)
    (a b c d : EndpointQuotient (Γ:=Γ) x s t y₀) :
    endpointColourTensor x s t y₀ hs y
      (endpointColourTensor x s t y₀ hs z (a,b),endpointColourTensor x s t y₀ hs z (c,d))=
    endpointColourTensor x s t y₀ hs z
      (endpointColourTensor x s t y₀ hs y (a,c),endpointColourTensor x s t y₀ hs y (b,d)) := by
  obtain ⟨a,rfl⟩ := decoratedToEndpoint_surjective x s t y₀ a
  obtain ⟨b,rfl⟩ := decoratedToEndpoint_surjective x s t y₀ b
  obtain ⟨c,rfl⟩ := decoratedToEndpoint_surjective x s t y₀ c
  obtain ⟨d,rfl⟩ := decoratedToEndpoint_surjective x s t y₀ d
  simpa only [decoratedToEndpoint_colourTensor] using
    endpoint_decorated_interchange x s t hs ht y₀ hxy htwo y z hyz a b c d

end Generators
end

section
universe u v w
attribute [local instance] Classical.propDecidable
namespace Tree
variable {X : Type v} {H : Type w}

def prefixShift (F : Prefix X → H) (p : Prefix X) : Prefix X → H := fun q=>F (p.comp q)

lemma prefixShift_comp (F : Prefix X → H) (p q : Prefix X) :
    prefixShift (prefixShift F p) q=prefixShift F (p.comp q) := by
  funext r
  exact congrArg F (Prefix.comp_assoc p q r).symm

/-- Interpretation of leaf decorations by coordinate-local binary tensor.
Decorations are indexed by literal bricks, not by an arbitrary ordering. -/
def labelledFold (T : X → H × H → H) : Tree X → (Prefix X → H) → H
  | .leaf,F => F Prefix.empty
  | .split x a b,F => T x (labelledFold T a (prefixShift F (Prefix.oneBit x false)),
      labelledFold T b (prefixShift F (Prefix.oneBit x true)))

lemma labelledFold_congr (T : X → H × H → H) (t : Tree X) (F K : Prefix X → H)
    (h : ∀ i,F (t.brick i)=K (t.brick i)) : labelledFold T t F=labelledFold T t K := by
  induction t generalizing F K with
  | leaf => exact h PUnit.unit
  | split x a b ha hb =>
    change T x (_,_) = T x (_, _)
    congr 1
    apply Prod.ext
    · exact ha _ _ (fun i=>h (Sum.inl i))
    · exact hb _ _ (fun i=>h (Sum.inr i))

variable (T : X → H × H → H)
variable (hT : ∀ x y : X,x≠y → ∀ a b c d : H,
  T x (T y (a,b),T y (c,d))=T y (T x (a,c),T x (b,d)))
include hT

lemma Coherent.labelledFold_eq {a b : Tree X} (h : Coherent a b) (F : Prefix X → H) :
    labelledFold T a F=labelledFold T b F := by
  induction h generalizing F with
  | refl => rfl
  | symm _ ih => exact (ih F).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ F).trans (ih₂ F)
  | split x _ _ ih₁ ih₂ => simp only [labelledFold,ih₁,ih₂]
  | @interchange x y hxy a b c d =>
    simp only [labelledFold,prefixShift_comp]
    rw [hT x y hxy]
    rw [Prefix.oneBit_comp_comm hxy false false,
      Prefix.oneBit_comp_comm hxy false true,
      Prefix.oneBit_comp_comm hxy true false,
      Prefix.oneBit_comp_comm hxy true true]

/-- Coordinate-tree invariance for arbitrary leaf group decorations. -/

lemma labelledFold_eq_of_brickSet_eq (a b : Tree X) (hab : brickSet a=brickSet b)
    (F : Prefix X → H) : labelledFold T a F=labelledFold T b F :=
  (coherent_of_brickSet_eq a b hab).labelledFold_eq T hT F
end Tree

namespace Generators
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x)) (y₀ : X)
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)
variable (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤) (hxy : x≠y₀)
variable (htwo : ∀ x₁ x₂ y₁ y₂ : X,x₁≠x₂ → y₁≠y₂ →
  ∃ g : Γ,g • x₁=y₁ ∧ g • x₂=y₂)
include ht hxy htwo

lemma endpoint_labelledFold_eq (a b : Tree X) (hab : a.brickSet=b.brickSet)
    (F : Prefix X → EndpointQuotient (Γ:=Γ) x s t y₀) :
    Tree.labelledFold (fun y=>endpointColourTensor x s t y₀ hs y) a F=
      Tree.labelledFold (fun y=>endpointColourTensor x s t y₀ hs y) b F := by
  apply Tree.labelledFold_eq_of_brickSet_eq _ _ a b hab F
  exact endpointColourTensor_interchange x s t y₀ hs ht hxy htwo

end Generators
end

universe u v w
attribute [local instance] Classical.propDecidable
namespace Tree
variable {X : Type v} {H : Type w}

/-- Naturality under a coordinate relabelling, stated independently of a
particular quotient. It applies to every finite coloured tree, not just grids. -/
lemma labelledFold_naturality (T : X → H × H → H) (f : X → X)
    (P : Prefix X → Prefix X) (C : H → H) (hP₀ : P Prefix.empty=Prefix.empty)
    (hP : ∀ y b p,P ((Prefix.oneBit (f y) b).comp p)=(Prefix.oneBit y b).comp (P p))
    (hC : ∀ y a b,C (T y (a,b))=T (f y) (C a,C b))
    (a : Tree X) (F : Prefix X → H) :
    C (labelledFold T a F)=labelledFold T (mapColors f a) (fun p=>C (F (P p))) := by
  induction a generalizing F with
  | leaf => simp only [labelledFold,mapColors,hP₀]
  | split y a b ha hb =>
    simp only [labelledFold,mapColors,hC,ha,hb]
    congr 1
    apply Prod.ext
    · apply congrArg (labelledFold T (mapColors f a))
      funext p
      dsimp only [prefixShift]
      rw [hP]
    · apply congrArg (labelledFold T (mapColors f b))
      funext p
      dsimp only [prefixShift]
      rw [hP]
end Tree

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma twistPrefix_comp (g : Γ) (p q : Prefix X) :
    twistPrefix g (p.comp q)=(twistPrefix g p).comp (twistPrefix g q) := by
  ext x; rfl

@[simp] lemma twistPrefix_empty (g : Γ) : twistPrefix g (Prefix.empty : Prefix X)=Prefix.empty := by
  ext x; rfl

namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x)) (y₀ : X)
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)
variable (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)

def endpointRoot : Γ →* EndpointQuotient x s t y₀ :=
  (endpointProject x s t y₀).comp (rootWord x)

lemma decoratedToEndpoint_root (g : Γ) :
    decoratedToEndpoint x s t y₀ (decoratedRoot x s t g)=endpointRoot x s t y₀ g :=
  decoratedToEndpoint_project x s t y₀ (rootWord x g)

include ht
lemma endpointColourTensor_covariance (g : Γ) (y : X) (a b : EndpointQuotient (Γ:=Γ) x s t y₀) :
    endpointRoot x s t y₀ g * endpointColourTensor x s t y₀ hs y (a,b) *
      (endpointRoot x s t y₀ g)⁻¹=endpointColourTensor x s t y₀ hs (g • y)
        (endpointRoot x s t y₀ g*a*(endpointRoot x s t y₀ g)⁻¹,
         endpointRoot x s t y₀ g*b*(endpointRoot x s t y₀ g)⁻¹) := by
  obtain ⟨a,rfl⟩ := decoratedToEndpoint_surjective x s t y₀ a
  obtain ⟨b,rfl⟩ := decoratedToEndpoint_surjective x s t y₀ b
  have h := congrArg (decoratedToEndpoint x s t y₀)
    (decoratedColourTensor_covariance x s t hs ht g y a b)
  simpa only [map_mul,map_inv,decoratedToEndpoint_colourTensor,decoratedToEndpoint_root] using h

lemma endpoint_labelledFold_covariance (g : Γ) (a : Tree X)
    (F : Prefix X → EndpointQuotient (Γ:=Γ) x s t y₀) :
    endpointRoot x s t y₀ g * Tree.labelledFold (fun y=>endpointColourTensor x s t y₀ hs y) a F *
        (endpointRoot x s t y₀ g)⁻¹=
      Tree.labelledFold (fun y=>endpointColourTensor x s t y₀ hs y)
        (Tree.mapColors (fun y=>g • y) a)
        (fun p=>endpointRoot x s t y₀ g*F (twistPrefix g⁻¹ p)*(endpointRoot x s t y₀ g)⁻¹) := by
  refine Tree.labelledFold_naturality (fun y=>endpointColourTensor x s t y₀ hs y)
    (fun y=>g • y) (twistPrefix g⁻¹)
    (fun z=>endpointRoot x s t y₀ g*z*(endpointRoot x s t y₀ g)⁻¹) ?_ ?_ ?_ a F
  · exact twistPrefix_empty g⁻¹
  · intro y b p
    rw [twistPrefix_comp,twistPrefix_oneBit,inv_smul_smul]
  · exact endpointColourTensor_covariance x s t y₀ hs ht g

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
