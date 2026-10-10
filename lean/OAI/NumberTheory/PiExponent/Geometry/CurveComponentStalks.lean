import Mathlib

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

theorem generic_iff_no_proper_generalization {T : Type*} [TopologicalSpace T] [QuasiSober T]
    (x : T) : x ∈ genericPoints T ↔ ∀ y : T, y ⤳ x → x ⤳ y := by
  constructor
  · intro hx y hy
    apply specializes_iff_closure_subset.mpr
    exact hx.2 isIrreducible_singleton.closure hy.closure_subset
  · intro hx
    let C : irreducibleComponents T :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    let y := (genericPoints.ofComponent C).val
    have hy : y ⤳ x := (genericPoints.isGenericPoint_ofComponent C).specializes
      mem_irreducibleComponent
    have he : closure ({x} : Set T) = C.val := by
      apply Set.Subset.antisymm
      · exact closure_minimal (Set.singleton_subset_iff.mpr mem_irreducibleComponent)
          (isClosed_of_mem_irreducibleComponents C.val C.property)
      · rw [← (genericPoints.isGenericPoint_ofComponent C).def]
        exact (hx y hy).closure_subset
    change closure ({x} : Set T) ∈ irreducibleComponents T
    rw [he]
    exact C.property

theorem generic_embedding_iff {T S : Type*} [TopologicalSpace T] [QuasiSober T]
    [TopologicalSpace S] [QuasiSober S] {f : S → T} (hf : IsEmbedding f)
    (hstable : ∀ y : S, ∀ x : T, x ⤳ f y → x ∈ Set.range f) (y : S) :
    y ∈ genericPoints S ↔ f y ∈ genericPoints T := by
  rw [generic_iff_no_proper_generalization, generic_iff_no_proper_generalization]
  constructor
  · intro hy x hx
    obtain ⟨z,rfl⟩ := hstable y x hx
    exact (hy z (hf.isInducing.specializes_iff.mp hx)).map hf.continuous
  · intro hy z hz
    exact hf.isInducing.specializes_iff.mp (hy (f z) (hz.map hf.continuous))

def genericPointsEmbeddingEquiv {T S : Type*} [TopologicalSpace T] [QuasiSober T]
    [TopologicalSpace S] [QuasiSober S] {f : S → T} (hf : IsEmbedding f)
    (hstable : ∀ y : S, ∀ x : T, x ⤳ f y → x ∈ Set.range f) :
    genericPoints S ≃ {x : genericPoints T // x.val ∈ Set.range f} := by
  let g : genericPoints S → {x : genericPoints T // x.val ∈ Set.range f} := fun y =>
    ⟨⟨f y.val, (generic_embedding_iff hf hstable y.val).mp y.property⟩, ⟨y.val,rfl⟩⟩
  apply Equiv.ofBijective g
  constructor
  · intro x y h
    exact Subtype.ext (hf.injective (congrArg (fun z => z.val.val) h))
  · intro x
    obtain ⟨y,hy⟩ := x.property
    have hgen : y ∈ genericPoints S :=
      (generic_embedding_iff hf hstable y).mpr (hy ▸ x.val.property)
    exact ⟨⟨y,hgen⟩, Subtype.ext (Subtype.ext hy)⟩

def minimalPrimesGenericEquiv (A : CommRingCat) :
    minimalPrimes A ≃ genericPoints (Spec A) where
  toFun P := ⟨⟨P.val,P.property.1.1⟩, by
    change closure ({⟨P.val,P.property.1.1⟩} : Set (PrimeSpectrum A)) ∈
      irreducibleComponents (PrimeSpectrum A)
    rw [← PrimeSpectrum.vanishingIdeal_mem_minimalPrimes,
      PrimeSpectrum.vanishingIdeal_singleton]
    exact P.property⟩
  invFun y := ⟨y.val.asIdeal, by
    rw [← PrimeSpectrum.vanishingIdeal_singleton y.val]
    exact PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr y.property⟩
  left_inv P := rfl
  right_inv y := by rfl

theorem fromSpecStalk_generizing (X : Scheme.{0}) (x : X)
    (y : Spec (X.presheaf.stalk x)) (z : X) (hz : z ⤳ X.fromSpecStalk x y) :
    z ∈ Set.range (X.fromSpecStalk x) := by
  rw [Scheme.range_fromSpecStalk]
  have hy : X.fromSpecStalk x y ⤳ x := by
    have hmem : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y,rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem
    exact hmem
  exact hz.trans hy

def genericPointsThroughEquiv (X : Scheme.{0}) (x : X) :
    {y : genericPoints X // y.val ∈ Set.range (X.fromSpecStalk x)} ≃
      {C : irreducibleComponents X // x ∈ C.val} where
  toFun y := ⟨genericPoints.component y.val, by
    have hmem : y.val.val ⤳ x :=
      (congrArg (fun S : Set X => y.val.val ∈ S)
        (Scheme.range_fromSpecStalk (X := X) (x := x))).mp y.property
    exact hmem.mem_closure⟩
  invFun C := ⟨genericPoints.ofComponent C.val, by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoints.isGenericPoint_ofComponent C.val).specializes C.property⟩
  left_inv y := by
    apply Subtype.ext
    exact genericPoints.ofComponent_component y.val
  right_inv C := by
    apply Subtype.ext
    exact genericPoints.component_ofComponent C.val

def stalkMinimalPrimesEquivComponentsThrough (X : Scheme.{0}) (x : X) :
    minimalPrimes (X.presheaf.stalk x) ≃
      {C : irreducibleComponents X // x ∈ C.val} :=
  (minimalPrimesGenericEquiv (X.presheaf.stalk x)).trans
    ((genericPointsEmbeddingEquiv (X.fromSpecStalk x).isEmbedding
      (fromSpecStalk_generizing X x)).trans (genericPointsThroughEquiv X x))

theorem stalkMinimalPrimesEquivComponentsThrough_point (X : Scheme.{0}) (x : X)
    (P : minimalPrimes (X.presheaf.stalk x)) :
    X.fromSpecStalk x (⟨P.val,P.property.1.1⟩ : Spec (X.presheaf.stalk x)) =
      (genericPoints.ofComponent
        (stalkMinimalPrimesEquivComponentsThrough X x P).val).val := by
  symm
  exact congrArg Subtype.val (genericPoints.ofComponent_component
    ((genericPointsEmbeddingEquiv (X.fromSpecStalk x).isEmbedding
      (fromSpecStalk_generizing X x))
        (minimalPrimesGenericEquiv (X.presheaf.stalk x) P)).val)

end
end PiExponent.CurveCycle

end OAI
