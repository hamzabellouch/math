import OAI.Analysis.Naimark.Omission

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder

structure ChronologicalHistory (X : TracialStage) (δ : Ordinal.{0}) where
  generator : Ordinal.{0} → X
  active : Set Ordinal.{0}
  active_lt : active ⊆ Set.Iio δ
  dependency : Ordinal.{0} → Set Ordinal.{0}
  lower : ∀ k < δ, dependency k ⊆ Set.Iio k
  countable : ∀ k < δ, (dependency k).Countable
  pair : Ordinal.{0} → PeakingPairData X
  trace : ∀ k a, (pair k).trace a = X.trace a
  leftPeak : ∀ k n, (pair k).peak false n = X.base (carPeak n)
  supported : ∀ k < δ, k ∈ active → ∀ i n,
    (pair k).peak i n ∈ generatedFamily (Set.range X.base) generator (dependency k)
  peak_mem : ∀ k ∈ active, ∀ i n,
    (pair k).peak i n ∈ generatedFamily (Set.range X.base) generator (Set.Iio k)
  chronological : ∀ k < δ, ∀ hk : k ∈ active,
    (pair k).AmbientPresentation (generatedFamily (Set.range X.base) generator (Set.Iio k))
      (peak_mem k hk) (generator k)
      (generatedFamily (Set.range X.base) generator (Set.Iio (k+1)))
  inactive : ∀ k, k ∉ active → generator k = 1
  inequivalent : ∀ k < δ, ∀ hk : k ∈ active,
    (pair k).PairDistinctOn (generatedFamily (Set.range X.base) generator (Set.Iio k))
      (peak_mem k hk)

structure ChronologicalData (X : TracialStage) (δ : Ordinal.{0}) extends ChronologicalHistory X δ where
  generated : generatedFamily (Set.range X.base) generator (Set.Iio δ) = ⊤

namespace TracialStage
variable (X : TracialStage)

def dummyPair : PeakingPairData X :=
  homogeneousCARPeakPair (StarAlgHom.id ℂ CAR) X.base X.base_injective
    X.reference X.reference X.reference_peaks
    (by simpa only [X.reference_spec.2] using carVector_isPure)
    X.reference_spec.1.1 X.baseUEP (StarAlgEquiv.refl ℂ CAR) rfl
    X.positiveTrace X.tracial X.positiveTrace_normalized X.positiveTrace_faithful

lemma dummyPair_trace (a : X) : X.dummyPair.trace a = X.trace a := rfl
lemma dummyPair_leftPeak (n : ℕ) : X.dummyPair.peak false n = X.base (carPeak n) := rfl
lemma base_isClosed : IsClosed (Set.range X.base) :=
  (NonUnitalStarAlgHom.isometry X.base X.base_injective).isClosedEmbedding.isClosed_range

lemma generatedFamily_zero (z : Ordinal.{0} → X) :
    generatedFamily (Set.range X.base) z (Set.Iio 0) = X.base.range := by
  rw [generatedFamily,show Set.Iio (0:Ordinal.{0}) = ∅ by ext k; simp,
    Set.image_empty,Set.union_empty]
  change (StarAlgebra.adjoin ℂ (X.base.range : Set X)).topologicalClosure = _
  rw [StarAlgebra.adjoin_eq]
  apply SetLike.coe_injective
  exact X.base_isClosed.closure_eq

lemma base_simple (z : Ordinal.{0} → X) :
    IsSimpleCStar (generatedFamily (Set.range X.base) z (Set.Iio 0)) := by
  let e : CAR ≃⋆ₐ[ℂ] generatedFamily (Set.range X.base) z (Set.Iio 0) :=
    StarAlgEquiv.ofBijective (X.base.codRestrict _ (fun a =>
      generatedFamily_contains_base (Set.range X.base) z (Set.Iio 0) ⟨a,rfl⟩))
      ⟨fun a b h => X.base_injective (congrArg Subtype.val h),by
        rintro ⟨a,ha⟩
        rw [X.generatedFamily_zero] at ha
        obtain ⟨b,hb⟩ := ha
        exact ⟨b,Subtype.ext hb⟩⟩
  exact carSimple.of_equiv e

lemma base_separable : TopologicalSpace.IsSeparable (Set.range X.base) :=
  TopologicalSpace.isSeparable_range
    (NonUnitalStarAlgHom.isometry X.base X.base_injective).continuous
end TracialStage

namespace ChronologicalData
variable {X : TracialStage} {δ : Ordinal.{0}} (D : ChronologicalData X δ)

abbrev algebra (S : Set Ordinal.{0}) := generatedFamily (Set.range X.base) D.generator S

lemma pureUEP (S : Set Ordinal.{0}) (hS : S ⊆ Set.Iio δ)
    (hclosed : DependencyClosed D.dependency S) : PureUEP (D.algebra S).subtype :=
  PeakingPairData.literal_dependency_closed_ambientUEP (Set.range X.base) D.generator
    D.pair D.active D.dependency δ D.lower D.supported D.peak_mem D.chronological
    (fun k _ => D.inactive k) D.inequivalent (X.base_simple D.generator)
    (fun j _ k _ a => (D.trace j a).trans (D.trace k a).symm) D.generated S hS hclosed

lemma countable_determination (f : X →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ S : Set Ordinal.{0}, S.Countable ∧ S ⊆ Set.Iio δ ∧ DependencyClosed D.dependency S ∧
      TopologicalSpace.IsSeparable (D.algebra S : Set X) ∧ IsSimpleCStar (D.algebra S) ∧
      IsPureState (restrictState (D.algebra S).subtype f) ∧
      StateExtensionUnique (D.algebra S).subtype (restrictState (D.algebra S).subtype f) :=
  PeakingPairData.literal_countable_determination (Set.range X.base) D.generator
    D.pair D.active D.dependency δ D.lower D.supported D.peak_mem D.chronological
    (fun k _ => D.inactive k) D.inequivalent (X.base_simple D.generator)
    (fun j _ k _ a => (D.trace j a).trans (D.trace k a).symm)
    D.countable X.base_separable D.generated f hf

include D in
lemma state_count (hδ : δ.card ≤ Cardinal.continuum) :
    Cardinal.mk {f : X →L[ℂ] ℂ // IsPureState f} ≤ Cardinal.continuum :=
  PeakingPairData.literal_pureStates_le_continuum (Set.range X.base) D.generator
    D.pair D.active D.dependency δ D.lower D.supported D.peak_mem D.chronological
    (fun k _ => D.inactive k) D.inequivalent (X.base_simple D.generator)
    (fun j _ k _ a => (D.trace j a).trans (D.trace k a).symm)
    D.countable X.base_separable D.generated hδ

end ChronologicalData
end

section
open CategoryTheory
attribute [local instance] generatedFamily_isClosed

structure ChronologicalStage where
  stage : TracialStage
  height : Ordinal.{0}
  history : ChronologicalData stage height

namespace ChronologicalStage

@[ext] structure Hom (X Y : ChronologicalStage) where
  embedding : TracialStage.Hom X.stage Y.stage
  height_le : X.height ≤ Y.height
  generator : ∀ k < X.height,
    embedding.map (X.history.generator k) = Y.history.generator k
  active : ∀ k < X.height, k ∈ X.history.active ↔ k ∈ Y.history.active
  dependency : ∀ k < X.height, X.history.dependency k = Y.history.dependency k
  peak : ∀ k < X.height, ∀ i n,
    embedding.map ((X.history.pair k).peak i n) = (Y.history.pair k).peak i n

namespace Hom
variable {X Y Z : ChronologicalStage}

def id (X : ChronologicalStage) : Hom X X where
  embedding := TracialStage.Hom.id X.stage
  height_le := le_rfl
  generator _ _ := rfl
  active _ _ := Iff.rfl
  dependency _ _ := rfl
  peak _ _ _ _ := rfl

def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  embedding := g.embedding.comp f.embedding
  height_le := f.height_le.trans g.height_le
  generator k hk := by
    change g.embedding.map (f.embedding.map (X.history.generator k)) = _
    rw [f.generator k hk,g.generator k (hk.trans_le f.height_le)]
  active k hk := (f.active k hk).trans (g.active k (hk.trans_le f.height_le))
  dependency k hk := (f.dependency k hk).trans (g.dependency k (hk.trans_le f.height_le))
  peak k hk i n := by
    change g.embedding.map (f.embedding.map ((X.history.pair k).peak i n)) = _
    rw [f.peak k hk,g.peak k (hk.trans_le f.height_le)]

@[simp] lemma comp_embedding (g : Hom Y Z) (f : Hom X Y) :
    (g.comp f).embedding = g.embedding.comp f.embedding := rfl
end Hom

instance : Category ChronologicalStage where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp f := by ext a; rfl
  comp_id f := by ext a; rfl
  assoc f g h := by ext a; rfl

def forget : ChronologicalStage ⥤ TracialStage where
  obj := ChronologicalStage.stage
  map f := f.embedding
  map_id _ := rfl
  map_comp _ _ := rfl

def initialHistory : ChronologicalData TracialStage.initial 0 where
  generator _ := 1
  active := ∅
  active_lt := Set.empty_subset _
  dependency _ := ∅
  lower _ _ := Set.empty_subset _
  countable _ _ := Set.countable_empty
  pair _ := TracialStage.initial.dummyPair
  trace _ _ := rfl
  leftPeak _ _ := rfl
  supported _ _ h := False.elim h
  peak_mem _ h := False.elim h
  chronological _ _ h := False.elim h
  inactive _ _ := rfl
  inequivalent _ _ h := False.elim h
  generated := by
    rw [TracialStage.generatedFamily_zero]
    ext a
    constructor
    · intro _; trivial
    · intro _; exact ⟨a,rfl⟩

def initial : ChronologicalStage := ⟨TracialStage.initial,0,initialHistory⟩

end ChronologicalStage
end

namespace PeakingPairData
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A S T R U : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra T] [partialOrderT : PartialOrder T] [starOrderedRingT : StarOrderedRing T]
  [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  [CStarAlgebra U] [PartialOrder U] [StarOrderedRing U]

omit partialOrderT starOrderedRingT in
lemma hnnAmbient_of_data [PartialOrder T] [StarOrderedRing T] (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (D : PeakingPairData S)
    (hp : ∀ i n, b (D.peak i n) = G.peak i n)
    (ht : ∀ a, D.trace a = G.trace (b a))
    (e : D.HNNAlgebra ≃⋆ₐ[ℂ] T)
    (heb : ∀ a, t (e (D.hnnBase a)) = b a)
    (hew : ∀ i, t (e (D.hnnLetter i)) = z i)
    (het : ∀ a, G.trace (t (e a)) = D.hnnTrace a) :
    G.HNNAmbientPresentation b t z :=
  ⟨D,hp,ht,e,heb,hew,het⟩

variable {B : Type} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma exists_reparam_pair (D : PeakingPairData S) (e : S ≃⋆ₐ[ℂ] R) :
    ∃ D' : PeakingPairData R,
      (∀ i n, e.symm (D'.peak i n) = D.peak i n) ∧
      (∀ a, D.trace (e.symm a) = D'.trace a) := by
  exact ⟨D.pullback e.symm.toStarAlgHom e.symm.injective
    (fun i n => e (D.peak i n)) (fun _ _ => e.symm_apply_apply _),
    (fun _ _ => e.symm_apply_apply _),fun _ => rfl⟩

omit partialOrderT starOrderedRingT in
lemma HNNAmbientPresentation.transport [PartialOrder T] [StarOrderedRing T] (G : PeakingPairData A) (G' : PeakingPairData B)
    (φ : A →⋆ₐ[ℂ] B) (hp : ∀ i n, φ (G.peak i n) = G'.peak i n)
    (ht : ∀ a, G'.trace (φ a) = G.trace a)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (b' : R →⋆ₐ[ℂ] B) (t' : U →⋆ₐ[ℂ] B)
    (s : S ≃⋆ₐ[ℂ] R) (r : T ≃⋆ₐ[ℂ] U)
    (hs : ∀ a, b' (s a) = φ (b a)) (hr : ∀ a, t' (r a) = φ (t a))
    (H : G.HNNAmbientPresentation b t z) :
    G'.HNNAmbientPresentation b' t' (φ ∘ z) := by
  obtain ⟨D,hDp,hDt,e,heb,hew,het⟩ := H
  obtain ⟨D',hdp,hdt⟩ := exists_reparam_pair D s
  obtain ⟨E,hEb,hEw,hEt,_⟩ := D'.hnn_equiv_of_peaks D s.symm hdp hdt
  have hs' (a : R) : b' a = φ (b (s.symm a)) := by
    simpa only [s.apply_symm_apply] using hs (s.symm a)
  refine hnnAmbient_of_data G' b' t' (φ ∘ z) D' ?_ ?_ (E.trans (e.trans r)) ?_ ?_ ?_
  · intro i n
    rw [hs',hdp,hDp,hp]
  · intro a
    rw [hs',ht,← hdt,hDt]
  · intro a
    change t' (r (e (E (D'.hnnBase a)))) = b' a
    rw [hr,hEb,heb,hs']
  · intro i
    change t' (r (e (E (D'.hnnLetter i)))) = φ (z i)
    rw [hr,hEw,hew]
  · intro a
    change G'.trace (t' (r (e (E a)))) = D'.hnnTrace a
    rw [hr,ht,het,hEt]

lemma HNNAmbientPresentation.same_data (G G' : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (hp : ∀ i n, G.peak i n = G'.peak i n)
    (ht : ∀ a, G.trace a = G'.trace a)
    (H : G.HNNAmbientPresentation b t z) : G'.HNNAmbientPresentation b t z := by
  obtain ⟨D,hDp,hDt,e,heb,hew,het⟩ := H
  exact hnnAmbient_of_data G' b t z D (fun i n => (hDp i n).trans (hp i n))
    (fun a => (hDt a).trans (ht _)) e heb hew (fun a => (ht _).symm.trans (het a))

end PeakingPairData

open Topology
section
variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

lemma generatedFamily_congr_on {ι : Type*} (b : Set A) (x y : ι → A) (S : Set ι)
    (h : ∀ k ∈ S, x k = y k) : generatedFamily b x S = generatedFamily b y S := by
  unfold generatedFamily
  congr 2
  exact congrArg (b ∪ ·) (Set.image_congr h)

lemma closed_map_isClosed (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) : IsClosed (S.map φ : Set B) :=
  (NonUnitalStarAlgHom.isometry φ.toNonUnitalStarAlgHom hφ).isClosedEmbedding.isClosedMap _
    (show IsClosed (S : Set A) from inferInstance)

def closedMapEquiv (S : StarSubalgebra ℂ A) (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) : S ≃⋆ₐ[ℂ] S.map φ :=
  StarAlgEquiv.ofBijective
    ((φ.comp S.subtype).codRestrict (S.map φ) (fun a => ⟨a,a.property,rfl⟩))
    ⟨fun a b h => Subtype.ext (hφ (congrArg Subtype.val h)), by
      rintro ⟨b,a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩⟩

@[simp] lemma closedMapEquiv_apply (S : StarSubalgebra ℂ A) (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) (a : S) : (closedMapEquiv S φ hφ a : B) = φ a := rfl

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
attribute [local irreducible] HNNAlgebra hnnCStar hnnOrder
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (P : PeakingPairData A) (Q : PeakingPairData B) (φ : A →⋆ₐ[ℂ] B)
  (hφ : Function.Injective φ)
  (hp : ∀ i n, φ (P.peak i n) = Q.peak i n)
  (ht : ∀ a, Q.trace (φ a) = P.trace a)

include hp in
lemma states_restrict_of_peaks (i : Bool) : restrictState φ (Q.state i) = P.state i := by
  apply (P.peaks i).2.2.2.2 _ (isState_restrict φ _ (Q.peaks i).2.2.1)
  intro n
  change Q.state i (φ (P.peak i n)) = 1
  rw [hp]
  exact (Q.peaks i).2.2.2.1 n

include ht in
lemma mapped_presentation_data
    (S T : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    [IsClosed (S.map φ : Set B)] [IsClosed (T.map φ : Set B)]
    (D : PeakingPairData S) (D' : PeakingPairData (S.map φ))
    (z : A) (e : D.HNNAlgebra ≃⋆ₐ[ℂ] T)
    (E : D'.HNNAlgebra ≃⋆ₐ[ℂ] D.HNNAlgebra)
    (heb : ∀ a, (e (D.hnnBase a) : A) = (a:A))
    (hew : ∀ i, (e (D.hnnLetter i) : A) = starPair z i)
    (het : ∀ a, P.trace (e a) = D.hnnTrace a)
    (hEb : ∀ a, E (D'.hnnBase a) = D.hnnBase ((closedMapEquiv S φ hφ).symm a))
    (hEw : ∀ i, E (D'.hnnLetter i) = D.hnnLetter i)
    (hEt : ∀ a, D.hnnTrace (E a) = D'.hnnTrace a) :
    let ε := E.trans (e.trans (closedMapEquiv T φ hφ))
    (∀ a, (ε (D'.hnnBase a) : B) = (a:B)) ∧
    (∀ i, (ε (D'.hnnLetter i) : B) = starPair (φ z) i) ∧
    (∀ a, Q.trace (ε a) = D'.hnnTrace a) := by
  refine ⟨?_,?_,?_⟩
  · intro a
    change φ (e (E (D'.hnnBase a))) = (a:B)
    exact (congrArg (fun b => φ (e b)) (hEb a)).trans
      ((congrArg φ (heb _)).trans
        (congrArg Subtype.val ((closedMapEquiv S φ hφ).apply_symm_apply a)))
  · intro i
    change φ (e (E (D'.hnnLetter i))) = starPair (φ z) i
    calc
      _ = φ (starPair z i) := (congrArg (fun b => φ (e b)) (hEw i)).trans
        (congrArg φ (hew i))
      _ = _ := by cases i; rfl; exact map_star φ z
  · intro a
    change Q.trace (φ (e (E a))) = D'.hnnTrace a
    exact (ht _).trans ((het _).trans (hEt a))

include hp ht in
lemma exists_mapped_peaking_data
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    [IsClosed (S.map φ : Set B)] (D : PeakingPairData S)
    (hDp : ∀ i n, (D.peak i n : A) = P.peak i n)
    (hDt : ∀ a, D.trace a = P.trace (a:A)) :
    ∃ D' : PeakingPairData (S.map φ),
      (∀ i n, (D'.peak i n : B) = Q.peak i n) ∧
      (∀ a, D'.trace a = Q.trace (a:B)) ∧
      (∀ i n, (closedMapEquiv S φ hφ).symm (D'.peak i n) = D.peak i n) ∧
      (∀ a, D.trace ((closedMapEquiv S φ hφ).symm a) = D'.trace a) := by
  let s := closedMapEquiv S φ hφ
  let D' := D.pullback s.symm.toStarAlgHom s.symm.injective
    (fun i n => s (D.peak i n)) (fun i n => s.symm_apply_apply _)
  refine ⟨D',?_,?_,fun i n => s.symm_apply_apply _,fun _ => rfl⟩
  · intro i n
    change φ (D.peak i n) = Q.peak i n
    exact (congrArg φ (hDp i n)).trans (hp i n)
  · intro a
    change D.trace (s.symm a) = Q.trace (a:B)
    rw [hDt,← ht]
    exact congrArg Q.trace (congrArg Subtype.val (s.apply_symm_apply a))

include ht in
lemma mapped_ambient_from_data
    (S T : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    [IsClosed (S.map φ : Set B)] [IsClosed (T.map φ : Set B)]
    (pQ : ∀ i n, Q.peak i n ∈ S.map φ)
    (D : PeakingPairData S) (D' : PeakingPairData (S.map φ))
    (hp' : ∀ i n, (D'.peak i n : B) = Q.peak i n)
    (ht' : ∀ a, D'.trace a = Q.trace (a:B))
    (z : A) (e : D.HNNAlgebra ≃⋆ₐ[ℂ] T)
    (E : D'.HNNAlgebra ≃⋆ₐ[ℂ] D.HNNAlgebra)
    (heb : ∀ a, (e (D.hnnBase a) : A) = (a:A))
    (hew : ∀ i, (e (D.hnnLetter i) : A) = starPair z i)
    (het : ∀ a, P.trace (e a) = D.hnnTrace a)
    (hEb : ∀ a, E (D'.hnnBase a) = D.hnnBase ((closedMapEquiv S φ hφ).symm a))
    (hEw : ∀ i, E (D'.hnnLetter i) = D.hnnLetter i)
    (hEt : ∀ a, D.hnnTrace (E a) = D'.hnnTrace a) :
    Q.AmbientPresentation (S.map φ) pQ (φ z) (T.map φ) := by
  have h := mapped_presentation_data P Q φ hφ ht S T D D' z e E heb hew het hEb hEw hEt
  exact hnnAmbient_of_data Q (S.map φ).subtype (T.map φ).subtype (starPair (φ z))
    D' hp' ht' (E.trans (e.trans (closedMapEquiv T φ hφ))) h.1 h.2.1 h.2.2

include hp ht hφ in
lemma AmbientPresentation.map
    (S T : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    [IsClosed (S.map φ : Set B)] [IsClosed (T.map φ : Set B)]
    (pS : ∀ i n, P.peak i n ∈ S) (z : A)
    (H : P.AmbientPresentation S pS z T) :
    Q.AmbientPresentation (S.map φ)
      (fun i n => hp i n ▸ (show φ (P.peak i n) ∈ S.map φ from ⟨_,pS i n,rfl⟩))
      (φ z) (T.map φ) := by
  have hz : (φ ∘ starPair z) = starPair (φ z) := by
    funext i
    cases i
    · rfl
    · exact map_star φ z
  have H' := HNNAmbientPresentation.transport P Q φ hp ht S.subtype T.subtype
    (starPair z) (S.map φ).subtype (T.map φ).subtype
    (closedMapEquiv S φ hφ) (closedMapEquiv T φ hφ) (fun _ => rfl) (fun _ => rfl) H
  rw [hz] at H'
  exact H'

include hp in
lemma PairDistinctOn.map
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (pS : ∀ i n, P.peak i n ∈ S) (H : P.PairDistinctOn S pS) :
    letI := closed_map_isClosed S φ hφ
    Q.PairDistinctOn (S.map φ)
      (fun i n => hp i n ▸ (show φ (P.peak i n) ∈ S.map φ from ⟨_,pS i n,rfl⟩)) := by
  let := closed_map_isClosed S φ hφ
  let pQ : ∀ i n, Q.peak i n ∈ S.map φ :=
    fun i n => hp i n ▸ ⟨_,pS i n,rfl⟩
  let e := closedMapEquiv S φ hφ
  have hstate (i : Bool) : restrictState e.toStarAlgHom ((Q.onSubalgebra (S.map φ) pQ).state i) =
      (P.onSubalgebra S pS).state i := by
    ext a
    exact congrArg (fun f : A →L[ℂ] ℂ => f a) (states_restrict_of_peaks P Q φ hp i)
  intro he
  have hh := pureStateEquivalent_restrict_equiv e _ _
    ((Q.onSubalgebra (S.map φ) pQ).peaks false).isPureState
    ((Q.onSubalgebra (S.map φ) pQ).peaks true).isPureState he
  exact H (by simpa only [hstate] using hh)

end PeakingPairData
end

open Topology
section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder

namespace TracialStage.Hom
variable {X Y : TracialStage} (φ : TracialStage.Hom X Y)

def pushPair (P : PeakingPairData X) (ht : ∀ a, P.trace a = X.trace a) : PeakingPairData Y :=
  P.push φ.map φ.injective Y.positiveTrace Y.tracial Y.positiveTrace_normalized
    Y.positiveTrace_faithful (fun a => (φ.trace_map a).trans (ht a).symm)
    (fun i => φ.uep _ (P.peaks i).isPureState)

@[simp] lemma pushPair_peak (P : PeakingPairData X) (ht : ∀ a, P.trace a = X.trace a)
    (i : Bool) (n : ℕ) : (φ.pushPair P ht).peak i n = φ.map (P.peak i n) := rfl
@[simp] lemma pushPair_trace (P : PeakingPairData X) (ht : ∀ a, P.trace a = X.trace a)
    (a : Y) : (φ.pushPair P ht).trace a = Y.trace a := rfl

lemma image_base : φ.map '' Set.range X.base = Set.range Y.base := by
  rw [← Set.range_comp]
  congr 1
  funext a
  exact φ.base_map a

lemma generatedFamily_map (z : Ordinal.{0} → X) (S : Set Ordinal.{0}) :
    (generatedFamily (Set.range X.base) z S).map φ.map =
      generatedFamily (Set.range Y.base) (φ.map ∘ z) S := by
  rw [NaimarkZFC.generatedFamily_map _ _ _ φ.map φ.injective,φ.image_base]

lemma mapped_mem (z : Ordinal.{0} → X) (S : Set Ordinal.{0})
    {a : X} (ha : a ∈ generatedFamily (Set.range X.base) z S) :
    φ.map a ∈ generatedFamily (Set.range Y.base) (φ.map ∘ z) S := by
  rw [← φ.generatedFamily_map]
  exact ⟨a,ha,rfl⟩
end TracialStage.Hom

namespace ChronologicalHistory
variable {X Y : TracialStage} {δ : Ordinal.{0}} (D : ChronologicalHistory X δ)
  (φ : TracialStage.Hom X Y)

lemma mapped_presentation (k : Ordinal.{0}) (hk : k < δ) (ha : k ∈ D.active) :
    (φ.pushPair (D.pair k) (D.trace k)).AmbientPresentation
      (generatedFamily (Set.range Y.base) (φ.map ∘ D.generator) (Set.Iio k))
      (fun i n => φ.mapped_mem D.generator (Set.Iio k) (D.peak_mem k ha i n))
      (φ.map (D.generator k))
      (generatedFamily (Set.range Y.base) (φ.map ∘ D.generator) (Set.Iio (k+1))) := by
  let S := generatedFamily (Set.range X.base) D.generator (Set.Iio k)
  let T := generatedFamily (Set.range X.base) D.generator (Set.Iio (k+1))
  let := closed_map_isClosed S φ.map φ.injective
  let := closed_map_isClosed T φ.map φ.injective
  have h := PeakingPairData.AmbientPresentation.map (D.pair k)
    (φ.pushPair (D.pair k) (D.trace k)) φ.map φ.injective
    (fun _ _ => rfl) (fun a => (φ.trace_map a).trans (D.trace k a).symm)
    S T (D.peak_mem k ha) (D.generator k) (D.chronological k hk ha)
  exact PeakingPairData.AmbientPresentation.congr _ _ _ _ _ _ _ _
    (φ.generatedFamily_map D.generator (Set.Iio k))
    (φ.generatedFamily_map D.generator (Set.Iio (k+1))) h

lemma mapped_inequivalent (k : Ordinal.{0}) (hk : k < δ) (ha : k ∈ D.active) :
    (φ.pushPair (D.pair k) (D.trace k)).PairDistinctOn
      (generatedFamily (Set.range Y.base) (φ.map ∘ D.generator) (Set.Iio k))
      (fun i n => φ.mapped_mem D.generator (Set.Iio k) (D.peak_mem k ha i n)) := by
  let S := generatedFamily (Set.range X.base) D.generator (Set.Iio k)
  let := closed_map_isClosed S φ.map φ.injective
  have h := PeakingPairData.PairDistinctOn.map (D.pair k)
    (φ.pushPair (D.pair k) (D.trace k)) φ.map φ.injective (fun _ _ => rfl)
    S (D.peak_mem k ha) (D.inequivalent k hk ha)
  exact PeakingPairData.PairDistinctOn.congr _ _ _ _ _
    (φ.generatedFamily_map D.generator (Set.Iio k)) h

def push : ChronologicalHistory Y δ where
  generator := φ.map ∘ D.generator
  active := D.active
  active_lt := D.active_lt
  dependency := D.dependency
  lower := D.lower
  countable := D.countable
  pair k := φ.pushPair (D.pair k) (D.trace k)
  trace _ _ := rfl
  leftPeak k n := by
    change φ.map ((D.pair k).peak false n) = _
    rw [D.leftPeak,φ.base_map]
  supported k hk ha i n := φ.mapped_mem D.generator _ (D.supported k hk ha i n)
  peak_mem k ha i n := φ.mapped_mem D.generator _ (D.peak_mem k ha i n)
  chronological := D.mapped_presentation φ
  inactive k hk := by change φ.map (D.generator k) = 1; rw [D.inactive k hk,map_one]
  inequivalent := D.mapped_inequivalent φ

end ChronologicalHistory

namespace ChronologicalStage.Hom
variable {X Y : ChronologicalStage} (φ : ChronologicalStage.Hom X Y)

lemma algebra_map (S : Set Ordinal.{0}) (hS : S ⊆ Set.Iio X.height) :
    (X.history.algebra S).map φ.embedding.map = Y.history.algebra S := by
  rw [ChronologicalData.algebra,φ.embedding.generatedFamily_map]
  exact generatedFamily_congr_on _ _ _ _ (fun k hk => φ.generator k (hS hk))

end ChronologicalStage.Hom
end

open Topology
section
attribute [local instance] generatedFamily_isClosed
local instance : DecidableEq Ordinal.{0} := Classical.decEq _
namespace ChronologicalData
variable {X Y : TracialStage} {δ : Ordinal.{0}} (D : ChronologicalData X δ)
  (φ : TracialStage.Hom X Y)

lemma image_generated_range :
    generatedFamily (Set.range Y.base) (φ.map ∘ D.generator) (Set.Iio δ) = φ.map.range := by
  rw [← φ.generatedFamily_map,D.generated]
  ext a
  constructor
  · rintro ⟨x,_,rfl⟩; exact ⟨x,rfl⟩
  · rintro ⟨x,rfl⟩; exact ⟨x,trivial,rfl⟩

lemma image_mem (a : X) :
    φ.map a ∈ generatedFamily (Set.range Y.base) (φ.map ∘ D.generator) (Set.Iio δ) := by
  rw [D.image_generated_range φ]
  exact ⟨a,rfl⟩

lemma updated_generated (z : Y)
    (hd : Dense (StarAlgebra.adjoin ℂ (Set.range φ.map ∪ Set.range (starPair z)) : Set Y)) :
    generatedFamily (Set.range Y.base) (Function.update (φ.map ∘ D.generator) δ z)
      (Set.Iio (δ+1)) = ⊤ := by
  let T := generatedFamily (Set.range Y.base)
    (Function.update (φ.map ∘ D.generator) δ z) (Set.Iio (δ+1))
  have hz : z ∈ T := by
    have h := generatedFamily_contains (Set.range Y.base)
      (Function.update (φ.map ∘ D.generator) δ z) (show δ ∈ Set.Iio (δ+1) from lt_add_one δ)
    simpa only [Function.update_self] using h
  have hr : Set.range φ.map ⊆ (T : Set Y) := by
    rintro _ ⟨a,rfl⟩
    have h := D.image_mem φ a
    apply (StarSubalgebra.topologicalClosure_mono ?_) h
    apply StarAlgebra.adjoin_mono
    apply Set.union_subset_union Set.Subset.rfl
    rintro _ ⟨k,hk,rfl⟩
    exact ⟨k,(show k < δ+1 from hk.trans (lt_add_one δ)),Function.update_of_ne hk.ne _ _⟩
  have hg : StarAlgebra.adjoin ℂ (Set.range φ.map ∪ Set.range (starPair z)) ≤ T := by
    apply StarAlgebra.adjoin_le
    rintro a (ha|⟨b,rfl⟩)
    · exact hr ha
    · cases b
      · exact hz
      · exact star_mem hz
  apply top_unique
  intro a _
  exact (show IsClosed (T : Set Y) from inferInstance).closure_subset_iff.mpr hg (hd a)

end ChronologicalData
end

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (P Q : PeakingPairData A) (hp : ∀ i n, P.peak i n = Q.peak i n)

include hp in
lemma AmbientPresentation.same_data
    (ht : ∀ a,P.trace a = Q.trace a)
    (S T : StarSubalgebra ℂ A) [IsClosed (S:Set A)] [IsClosed (T:Set A)]
    (pS : ∀ i n,P.peak i n ∈ S) (qS : ∀ i n,Q.peak i n ∈ S) (z : A)
    (H : P.AmbientPresentation S pS z T) : Q.AmbientPresentation S qS z T :=
  HNNAmbientPresentation.same_data P Q S.subtype T.subtype (starPair z) hp ht H

include hp in
lemma PairDistinctOn.same_peaks
    (S : StarSubalgebra ℂ A) [IsClosed (S:Set A)]
    (pS : ∀ i n,P.peak i n ∈ S) (qS : ∀ i n,Q.peak i n ∈ S)
    (H : P.PairDistinctOn S pS) : Q.PairDistinctOn S qS := by
  have hs (i : Bool) : (Q.onSubalgebra S qS).state i = (P.onSubalgebra S pS).state i := by
    have h := states_restrict_of_peaks (P.onSubalgebra S pS) (Q.onSubalgebra S qS)
      (StarAlgHom.id ℂ S) (fun i n => Subtype.ext (hp i n)) i
    exact h
  unfold PairDistinctOn at H ⊢
  simpa only [hs] using H

end PeakingPairData

section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder
local instance : DecidableEq Ordinal.{0} := Classical.decEq _

lemma generatedFamily_update_before {A : Type} [CStarAlgebra A] (b : Set A)
    (x : Ordinal.{0} → A) (δ : Ordinal.{0}) (z : A) (S : Set Ordinal.{0})
    (hS : S ⊆ Set.Iio δ) :
    generatedFamily b (Function.update x δ z) S = generatedFamily b x S := by
  exact generatedFamily_congr_on _ _ _ _ (fun k hk => Function.update_of_ne (hS hk).ne _ _)

namespace ChronologicalHistory
variable {X : TracialStage} {δ : Ordinal.{0}} (D : ChronologicalHistory X δ)
  (Q : PeakingPairData X) (htrace : ∀ a,Q.trace a = X.trace a)
  (hleft : ∀ n,Q.peak false n = X.base (carPeak n))
  (S : Set Ordinal.{0}) (hS : S ⊆ Set.Iio δ) (hSc : S.Countable)
  (hsupport : ∀ i n,Q.peak i n ∈ generatedFamily (Set.range X.base) D.generator S)
  (z : X)

include hS hsupport in
lemma inserted_peak_mem (i : Bool) (n : ℕ) :
    Q.peak i n ∈ generatedFamily (Set.range X.base) D.generator (Set.Iio δ) :=
  generatedFamily_mono _ _ hS (hsupport i n)

variable (HP : Q.AmbientPresentation (generatedFamily (Set.range X.base) D.generator (Set.Iio δ))
    (D.inserted_peak_mem Q S hS hsupport) z
    (generatedFamily (Set.range X.base) (Function.update D.generator δ z) (Set.Iio (δ+1))))
  (HD : Q.PairDistinctOn (generatedFamily (Set.range X.base) D.generator (Set.Iio δ))
    (D.inserted_peak_mem Q S hS hsupport))

def insertActive : ChronologicalHistory X (δ+1) where
  generator := Function.update D.generator δ z
  active := insert δ D.active
  active_lt := by
    intro k hk
    rcases hk with rfl | hk
    · exact (lt_add_one k)
    · exact (show k < δ from D.active_lt hk).trans ((lt_add_one δ))
  dependency := Function.update D.dependency δ S
  lower k hk := by
    by_cases he : k=δ
    · subst k; simpa only [Function.update_self] using hS
    · rw [Function.update_of_ne he]
      exact D.lower k (lt_of_le_of_ne (Order.lt_add_one_iff.mp hk) he)
  countable k hk := by
    by_cases he : k=δ
    · subst k; simpa only [Function.update_self] using hSc
    · rw [Function.update_of_ne he]
      exact D.countable k (lt_of_le_of_ne (Order.lt_add_one_iff.mp hk) he)
  pair := Function.update D.pair δ Q
  trace k a := by
    by_cases he : k=δ
    · subst k; simpa only [Function.update_self] using htrace a
    · simpa only [Function.update_of_ne he] using D.trace k a
  leftPeak k n := by
    by_cases he : k=δ
    · subst k; simpa only [Function.update_self] using hleft n
    · simpa only [Function.update_of_ne he] using D.leftPeak k n
  supported k hk ha i n := by
    by_cases he : k=δ
    · subst k
      rw [Function.update_self,Function.update_self,
        generatedFamily_update_before _ _ _ _ _ hS]
      exact hsupport i n
    · rw [Function.update_of_ne he,Function.update_of_ne he,
        generatedFamily_update_before _ _ _ _ _ ((D.lower k
          (lt_of_le_of_ne (Order.lt_add_one_iff.mp hk) he)).trans
          (Set.Iio_subset_Iio (Order.lt_add_one_iff.mp hk)))]
      exact D.supported k (lt_of_le_of_ne (Order.lt_add_one_iff.mp hk) he)
        ((Set.mem_insert_iff.mp ha).resolve_left he) i n
  peak_mem k ha i n := by
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · rw [Function.update_self,generatedFamily_update_before _ _ _ _ _ (fun _ h => h)]
      exact D.inserted_peak_mem Q S hS hsupport i n
    · have hk := D.active_lt ha
      rw [Function.update_of_ne hk.ne,generatedFamily_update_before _ _ _ _ _
        (Set.Iio_subset_Iio hk.le)]
      exact D.peak_mem k ha i n
  chronological k hk ha := by
    by_cases he : k=δ
    · subst k
      simpa only [Function.update_self,
        generatedFamily_update_before _ _ _ _ (Set.Iio δ) (fun _ h => h)] using HP
    · have hkδ : k < δ := lt_of_le_of_ne (Order.lt_add_one_iff.mp hk) he
      have ha' : k ∈ D.active := (Set.mem_insert_iff.mp ha).resolve_left he
      simp only [Function.update_of_ne he]
      exact PeakingPairData.AmbientPresentation.congr _ _ _ _ _ _ _ _
        (generatedFamily_update_before _ _ _ _ _ (Set.Iio_subset_Iio hkδ.le)).symm
        (generatedFamily_update_before _ _ _ _ _
          (Set.Iio_subset_Iio (Order.add_one_le_iff.mpr hkδ))).symm (D.chronological k hkδ ha')
  inactive k hk := by
    have hne : k≠δ := fun he => hk (he ▸ Set.mem_insert δ D.active)
    rw [Function.update_of_ne hne]
    exact D.inactive k (fun ha => hk (Set.mem_insert_of_mem _ ha))
  inequivalent k hk ha := by
    by_cases he : k=δ
    · subst k
      simpa only [Function.update_self,
        generatedFamily_update_before _ _ _ _ (Set.Iio δ) (fun _ h => h)] using HD
    · have hkδ : k < δ := lt_of_le_of_ne (Order.lt_add_one_iff.mp hk) he
      have ha' : k ∈ D.active := (Set.mem_insert_iff.mp ha).resolve_left he
      simp only [Function.update_of_ne he]
      exact PeakingPairData.PairDistinctOn.congr _ _ _ _ _
        (generatedFamily_update_before _ _ _ _ _ (Set.Iio_subset_Iio hkδ.le)).symm
        (D.inequivalent k hkδ ha')

end ChronologicalHistory
end

section
variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

def fullImageEquiv (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    (S : StarSubalgebra ℂ B) (hS : S = φ.range) : A ≃⋆ₐ[ℂ] S :=
  StarAlgEquiv.ofBijective (φ.codRestrict S (fun a => hS ▸ ⟨a,rfl⟩))
    ⟨fun a b h => hφ (congrArg Subtype.val h),by
      intro a
      have ha : (a:B) ∈ φ.range := hS ▸ a.property
      obtain ⟨b,hb⟩ := ha
      exact ⟨b,Subtype.ext hb⟩⟩

@[simp] lemma fullImageEquiv_apply (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    (S : StarSubalgebra ℂ B) (hS : S = φ.range) (a : A) :
    (fullImageEquiv φ hφ S hS a : B) = φ a := rfl

def fullTopEquiv (T : StarSubalgebra ℂ B) (hT : T = ⊤) : B ≃⋆ₐ[ℂ] T :=
  StarAlgEquiv.ofBijective ((StarAlgHom.id ℂ B).codRestrict T (fun _ => hT ▸ trivial))
    ⟨fun _ _ h => congrArg Subtype.val h,fun a => ⟨a,Subtype.ext rfl⟩⟩

@[simp] lemma fullTopEquiv_apply (T : StarSubalgebra ℂ B) (hT : T = ⊤) (b : B) :
    (fullTopEquiv T hT b : B) = b := rfl

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma HNNAmbientPresentation.fullImage (G : PeakingPairData B)
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) (z : B)
    (S T : StarSubalgebra ℂ B) [IsClosed (S : Set B)] [IsClosed (T : Set B)]
    (hS : S = φ.range) (hT : T = ⊤) (hp : ∀ i n,G.peak i n ∈ S)
    (H : G.HNNAmbientPresentation φ (StarAlgHom.id ℂ B) (starPair z)) :
    G.AmbientPresentation S hp z T := by
  exact HNNAmbientPresentation.transport G G (StarAlgHom.id ℂ B)
    (fun _ _ => rfl) (fun _ => rfl) φ (StarAlgHom.id ℂ B) (starPair z)
    S.subtype T.subtype (fullImageEquiv φ hφ S hS) (fullTopEquiv T hT)
    (fun _ => rfl) (fun _ => rfl) H

lemma PairDistinctOn.fullImage (P : PeakingPairData A) (G : PeakingPairData B)
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    (hp : ∀ i n,φ (P.peak i n) = G.peak i n)
    (S : StarSubalgebra ℂ B) [IsClosed (S : Set B)] (hS : S = φ.range)
    (pS : ∀ i n,G.peak i n ∈ S)
    (H : ¬ PureStateEquivalent (P.state false) (P.peaks false).isPureState
      (P.state true) (P.peaks true).isPureState) : G.PairDistinctOn S pS := by
  let e := fullImageEquiv φ hφ S hS
  have he (i : Bool) (n : ℕ) : e (P.peak i n) = (G.onSubalgebra S pS).peak i n :=
    Subtype.ext (hp i n)
  have hstate := states_restrict_of_peaks P (G.onSubalgebra S pS) e.toStarAlgHom he
  intro hh
  have h := pureStateEquivalent_restrict_equiv e _ _
    ((G.onSubalgebra S pS).peaks false).isPureState
    ((G.onSubalgebra S pS).peaks true).isPureState hh
  exact H (by simpa only [hstate] using h)

end PeakingPairData
end

open Topology
namespace PeakingPairData
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
attribute [local irreducible] HNNAlgebra hnnCStar hnnOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma hnnLetter_starPair (Q : PeakingPairData A) :
    Q.hnnLetter = starPair (Q.hnnLetter false) := by
  funext i
  cases i
  · rfl
  · exact (Q.hnnLetter_star false).symm

lemma hnn_generated_starPair (Q : PeakingPairData A) :
    Dense (StarAlgebra.adjoin ℂ (Set.range Q.hnnBase ∪
      Set.range (starPair (Q.hnnLetter false))) : Set Q.HNNAlgebra) := by
  rw [← Q.hnnLetter_starPair]
  exact Q.hnn_generated

lemma hnn_ambient_literal (Q : PeakingPairData A) (G : PeakingPairData Q.HNNAlgebra)
    (hp : ∀ i n,G.peak i n = Q.hnnBase (Q.peak i n))
    (ht : ∀ a,G.trace a = Q.hnnTrace a) :
    G.HNNAmbientPresentation Q.hnnBase (StarAlgHom.id ℂ Q.HNNAlgebra)
      (starPair (Q.hnnLetter false)) := by
  exact hnnAmbient_of_data G Q.hnnBase (StarAlgHom.id ℂ Q.HNNAlgebra)
    (starPair (Q.hnnLetter false)) Q (fun i n => (hp i n).symm)
    (fun a => (Q.hnnTrace_base a).symm.trans (ht _).symm)
    (StarAlgEquiv.refl _ _) (fun _ => rfl) (fun i => congrFun Q.hnnLetter_starPair i) ht

end PeakingPairData

open Topology
namespace ChronologicalStage
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder
attribute [local instance 2000] PeakingPairData.hnnCStar PeakingPairData.hnnOrder PeakingPairData.hnnStarOrder
local instance : DecidableEq Ordinal.{0} := Classical.decEq _
variable (X : ChronologicalStage) (Q : PeakingPairData X.stage) (hs : Q.Separated)
  (ht : ∀ a,Q.trace a = X.stage.trace a)
  (hl : ∀ n,Q.peak false n = X.stage.base (carPeak n))
  (S : Set Ordinal.{0}) (hS : S ⊆ Set.Iio X.height) (hSc : S.Countable)
  (hp : ∀ i n,Q.peak i n ∈ X.history.algebra S)
  (hne : ¬ PureStateEquivalent (Q.state false) (Q.peaks false).isPureState
    (Q.state true) (Q.peaks true).isPureState)

abbrev hnnEmbedding := TracialStage.hnnHom X.stage Q hs ht
abbrev hnnPriorHistory := X.history.toChronologicalHistory.push (hnnEmbedding X Q hs ht)
abbrev hnnNewPair := (hnnEmbedding X Q hs ht).pushPair Q ht

include hl in
lemma hnn_new_left (n : ℕ) : (hnnNewPair X Q hs ht).peak false n =
    (TracialStage.hnn X.stage Q hs).base (carPeak n) := by
  change Q.hnnBase (Q.peak false n) = Q.hnnBase (X.stage.base (carPeak n))
  rw [hl]

include hp in
lemma hnn_new_supported (i : Bool) (n : ℕ) :
    (hnnNewPair X Q hs ht).peak i n ∈ generatedFamily
      (Set.range (TracialStage.hnn X.stage Q hs).base) (hnnPriorHistory X Q hs ht).generator S :=
  (hnnEmbedding X Q hs ht).mapped_mem X.history.generator S (hp i n)

lemma hnn_before_range : generatedFamily (Set.range (TracialStage.hnn X.stage Q hs).base)
    (hnnPriorHistory X Q hs ht).generator (Set.Iio X.height) = Q.hnnBase.range :=
  X.history.image_generated_range (hnnEmbedding X Q hs ht)

lemma hnn_after_generated : generatedFamily (Set.range (TracialStage.hnn X.stage Q hs).base)
    (Function.update (hnnPriorHistory X Q hs ht).generator X.height (Q.hnnLetter false))
    (Set.Iio (X.height+1)) = ⊤ :=
  X.history.updated_generated (hnnEmbedding X Q hs ht) (Q.hnnLetter false) Q.hnn_generated_starPair

lemma hnn_new_presentation :
    (hnnNewPair X Q hs ht).AmbientPresentation
      (generatedFamily (Set.range (TracialStage.hnn X.stage Q hs).base)
        (hnnPriorHistory X Q hs ht).generator (Set.Iio X.height))
      ((hnnPriorHistory X Q hs ht).inserted_peak_mem (hnnNewPair X Q hs ht) S hS
        (hnn_new_supported X Q hs ht S hp))
      (Q.hnnLetter false)
      (generatedFamily (Set.range (TracialStage.hnn X.stage Q hs).base)
        (Function.update (hnnPriorHistory X Q hs ht).generator X.height (Q.hnnLetter false))
        (Set.Iio (X.height+1))) := by
  exact PeakingPairData.HNNAmbientPresentation.fullImage (hnnNewPair X Q hs ht)
    Q.hnnBase Q.hnnBase_injective (Q.hnnLetter false) _ _
    (hnn_before_range X Q hs ht) (hnn_after_generated X Q hs ht) _
    (Q.hnn_ambient_literal (hnnNewPair X Q hs ht) (fun _ _ => rfl) (fun _ => rfl))

include hne in
lemma hnn_new_inequivalent :
    (hnnNewPair X Q hs ht).PairDistinctOn
      (generatedFamily (Set.range (TracialStage.hnn X.stage Q hs).base)
        (hnnPriorHistory X Q hs ht).generator (Set.Iio X.height))
      ((hnnPriorHistory X Q hs ht).inserted_peak_mem (hnnNewPair X Q hs ht) S hS
        (hnn_new_supported X Q hs ht S hp)) :=
  PeakingPairData.PairDistinctOn.fullImage Q (hnnNewPair X Q hs ht)
    Q.hnnBase Q.hnnBase_injective (fun _ _ => rfl) _ (hnn_before_range X Q hs ht) _ hne

def hnnHistory : ChronologicalData (TracialStage.hnn X.stage Q hs) (X.height+1) where
  toChronologicalHistory := (hnnPriorHistory X Q hs ht).insertActive
    (hnnNewPair X Q hs ht) (fun _ => rfl) (hnn_new_left X Q hs ht hl)
    S hS hSc (hnn_new_supported X Q hs ht S hp) (Q.hnnLetter false)
    (hnn_new_presentation X Q hs ht S hS hp) (hnn_new_inequivalent X Q hs ht S hS hp hne)
  generated := hnn_after_generated X Q hs ht

abbrev hnnSuccessor : ChronologicalStage :=
  ⟨TracialStage.hnn X.stage Q hs,X.height+1,hnnHistory X Q hs ht hl S hS hSc hp hne⟩

def hnnHom : Hom X (hnnSuccessor X Q hs ht hl S hS hSc hp hne) where
  embedding := hnnEmbedding X Q hs ht
  height_le := (lt_add_one X.height).le
  generator k hk := by
    exact (Function.update_of_ne hk.ne (Q.hnnLetter false)
      (hnnPriorHistory X Q hs ht).generator).symm
  active k hk := by
    change k ∈ X.history.active ↔ k ∈ insert X.height X.history.active
    simp only [Set.mem_insert_iff,hk.ne,false_or]
  dependency k hk := by
    dsimp only [hnnSuccessor,hnnHistory,ChronologicalHistory.insertActive]
    rw [Function.update_of_ne hk.ne]
    rfl
  peak k hk i n := by
    dsimp only [hnnSuccessor,hnnHistory,ChronologicalHistory.insertActive]
    rw [Function.update_of_ne hk.ne]
    rfl

end ChronologicalStage

section
attribute [local instance] generatedFamily_isClosed
namespace ChronologicalData
variable {X : TracialStage} {δ : Ordinal.{0}} (D : ChronologicalData X δ)

def advanceInactive : ChronologicalData X (δ+1) where
  generator := D.generator
  active := D.active
  active_lt := D.active_lt.trans (Set.Iio_subset_Iio (le_add_right (le_rfl : δ ≤ δ)))
  dependency k := if k < δ then D.dependency k else ∅
  lower k _ := by
    split_ifs with h
    · exact D.lower k h
    · exact Set.empty_subset _
  countable k _ := by
    split_ifs with h
    · exact D.countable k h
    · exact Set.countable_empty
  pair := D.pair
  trace := D.trace
  leftPeak := D.leftPeak
  supported k _ ha i n := by
    rw [ite_eq_left (show k < δ from D.active_lt ha)]
    exact D.supported k (D.active_lt ha) ha i n
  peak_mem := D.peak_mem
  chronological k _ ha := D.chronological k (D.active_lt ha) ha
  inactive := D.inactive
  inequivalent k _ ha := D.inequivalent k (D.active_lt ha) ha
  generated := by
    apply top_unique
    rw [← D.generated]
    exact generatedFamily_mono _ _ (Set.Iio_subset_Iio (le_add_right (le_rfl : δ ≤ δ)))
end ChronologicalData
namespace ChronologicalStage
variable (X : ChronologicalStage)
def inactiveSuccessor : ChronologicalStage :=
  ⟨X.stage,X.height+1,X.history.advanceInactive⟩

def inactiveHom : Hom X X.inactiveSuccessor where
  embedding := TracialStage.Hom.id X.stage
  height_le := le_add_right (le_rfl : X.height ≤ X.height)
  generator _ _ := rfl
  active _ _ := Iff.rfl
  dependency k hk := by change _ = if k < X.height then _ else _; rw [ite_eq_left hk]
  peak _ _ _ _ := rfl

end ChronologicalStage
end

section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder

namespace KOS

def SimpleSeparableRows : Prop :=
  ∀ (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A], IsSimpleCStar A →
      ¬ FiniteDimensional ℂ A → ApproxNearCentralRows (A := A)
end KOS

namespace ChronologicalStage
variable (X : ChronologicalStage)

def coreBase (S : Set Ordinal.{0}) : CAR →⋆ₐ[ℂ] X.history.algebra S :=
  X.stage.base.codRestrict _ (fun a => generatedFamily_contains_base _ _ _ ⟨a,rfl⟩)

lemma exists_supported_pair (H : KOS.SimpleSeparableRows)
    (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ S : Set Ordinal.{0}, S.Countable ∧ S ⊆ Set.Iio X.height ∧
      ∃ Q : PeakingPairData X.stage,
        (∀ a,Q.trace a = X.stage.trace a) ∧ Q.state false = X.stage.reference ∧
        Q.state true = f ∧ (∀ n,Q.peak false n = X.stage.base (carPeak n)) ∧
        (∀ i n,Q.peak i n ∈ X.history.algebra S) := by
  obtain ⟨S,hSc,hS,hclosed,hsep,hsimple,hfr,_⟩ := X.history.countable_determination f hf
  let : TopologicalSpace.SeparableSpace (X.history.algebra S) := hsep.separableSpace
  let ψ := X.coreBase S
  let φ := (X.history.algebra S).subtype
  have hbase : ∀ a,φ (ψ a) = X.stage.base a := fun _ => rfl
  have hinf := TracialStage.core_infinite X.stage ψ φ hbase
  obtain ⟨Q,ht,h0,h1,hl,hp⟩ := TracialStage.exists_supported_peak_pair X.stage
    hsimple ψ φ Subtype.val_injective hbase (X.history.pureUEP S hS hclosed) f hf hfr
    (H _ hsimple hinf)
  refine ⟨S,hSc,hS,Q,ht,h0,h1,hl,?_⟩
  intro i n
  obtain ⟨a,ha⟩ := hp i n
  exact ha ▸ a.property

theorem exists_joining_successor (H : KOS.SimpleSeparableRows)
    (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ Y : ChronologicalStage, ∃ j : Hom X Y,
      Y.height = X.height+1 ∧
      ∃ F : Y.stage →L[ℂ] ℂ, ∃ hF : IsPureState F,
        restrictState j.embedding.map F = f ∧
        PureStateEquivalent Y.stage.reference Y.stage.reference_spec.1 F hF := by
  by_cases he : PureStateEquivalent X.stage.reference X.stage.reference_spec.1 f hf
  · exact ⟨X.inactiveSuccessor,X.inactiveHom,rfl,f,hf,rfl,he⟩
  · obtain ⟨S,hSc,hS,Q,ht,h0,h1,hl,hp⟩ := X.exists_supported_pair H f hf
    have hne : ¬ PureStateEquivalent (Q.state false) (Q.peaks false).isPureState
        (Q.state true) (Q.peaks true).isPureState := by
      simpa only [h0,h1] using he
    let hs := Q.separated_of_inequivalent hne
    obtain ⟨F,hF,hr,hjoin⟩ := TracialStage.hnn_reference_join X.stage Q hs ht f hf h0 h1
    exact ⟨X.hnnSuccessor Q hs ht hl S hS hSc hp hne,
      X.hnnHom Q hs ht hl S hS hSc hp hne,rfl,F,hF,hr,hjoin⟩

end ChronologicalStage
end

open CategoryTheory
namespace TracialStage

variable {J : Type} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  (D : J ⥤ TracialStage)

def bond (i j : J) (h : i ≤ j) : D.obj i →⋆ₐ[ℂ] D.obj j :=
  (D.map (homOfLE h)).map

instance bond_directed : DirectedSystem (fun i => D.obj i) (bond D · · ·) where
  map_self i a := by
    change (D.map (𝟙 i)).map a = a
    rw [D.map_id]
    rfl
  map_map k j i hij hjk a := by
    change (D.map (homOfLE hjk)).map ((D.map (homOfLE hij)).map a) =
      (D.map (homOfLE (hij.trans hjk))).map a
    have h := D.map_comp (homOfLE hij) (homOfLE hjk)
    exact congrArg (fun f : Hom (D.obj i) (D.obj k) => f.map a) h.symm

instance bond_isometric : IsometricStarSystem (fun i => D.obj i) (bond D) where
  isometry _ _ h := NonUnitalStarAlgHom.isometry (D.map (homOfLE h)).map.toNonUnitalStarAlgHom
    (D.map (homOfLE h)).injective

abbrev LimitCarrier := CStarDirectLimit (fun i => D.obj i) (bond D)

def limitIncl (i : J) : D.obj i →⋆ₐ[ℂ] LimitCarrier D :=
  cstarDirectLimitInclude (fun i => D.obj i) (bond D) i

lemma limitIncl_injective (i : J) : Function.Injective (limitIncl D i) :=
  (cstarDirectLimitInclude_isometry (fun i => D.obj i) (bond D) i).injective

@[simp] lemma limitIncl_compatible (i j : J) (h : i ≤ j) (a : D.obj i) :
    limitIncl D j ((D.map (homOfLE h)).map a) = limitIncl D i a :=
  cstarDirectLimitInclude_compatible (fun i => D.obj i) (bond D) i j h a

lemma limitIncl_base_eq (i j : J) (a : CAR) :
    limitIncl D i ((D.obj i).base a) = limitIncl D j ((D.obj j).base a) := by
  obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
  rw [← limitIncl_compatible D i k hik,← limitIncl_compatible D j k hjk]
  rw [(D.map (homOfLE hik)).base_map,(D.map (homOfLE hjk)).base_map]

def limitTrace : LimitCarrier D →L[ℂ] ℂ :=
  cstarDirectLimitState (fun i => D.obj i) (bond D) (fun i => (D.obj i).trace)
    (fun i => (D.obj i).traceState) (fun _ _ h a => (D.map (homOfLE h)).trace_map a)

lemma limitTrace_state : IsState (limitTrace D) :=
  cstarDirectLimitState_isState _ _ _ _ _

lemma limitTrace_tracial (a b : LimitCarrier D) :
    limitTrace D (a*b) = limitTrace D (b*a) :=
  cstarDirectLimitState_tracial _ _ _ _ _ (fun i => (D.obj i).tracial) a b

@[simp] lemma limitTrace_stage (i : J) (a : D.obj i) :
    limitTrace D (limitIncl D i a) = (D.obj i).trace a :=
  cstarDirectLimitState_stage (fun i => D.obj i) (bond D)
    (fun i => (D.obj i).trace) (fun i => (D.obj i).traceState)
    (fun _ _ h a => (D.map (homOfLE h)).trace_map a) i a

lemma limitIncl_uep (i : J) : PureUEP (limitIncl D i) :=
  cstarDirectLimit_pureUEP (fun i => D.obj i) (bond D) (fun _ _ h => (D.map (homOfLE h)).uep) i

def directLimit : TracialStage where
  carrier := LimitCarrier D
  cstar := inferInstance
  order := CStarAlgebra.spectralOrder _
  starOrder := CStarAlgebra.spectralOrderedRing _
  simple := cstarDirectLimit_simple _ _ (fun i => (D.obj i).simple)
  trace := limitTrace D
  traceState := limitTrace_state D
  tracial := limitTrace_tracial D
  base := (limitIncl D (Classical.arbitrary J)).comp (D.obj (Classical.arbitrary J)).base
  base_injective := (limitIncl_injective D _).comp (D.obj _).base_injective
  baseUEP := (D.obj _).baseUEP.comp (limitIncl_uep D _)

def directLimitHom (i : J) : Hom (D.obj i) (directLimit D) where
  map := limitIncl D i
  injective := limitIncl_injective D i
  trace_map := limitTrace_stage D i
  base_map a := limitIncl_base_eq D i (Classical.arbitrary J) a
  uep := limitIncl_uep D i

@[simp] lemma directLimitHom_compatible (i j : J) (h : i ≤ j) :
    Hom.comp (directLimitHom D j) (D.map (homOfLE h)) = directLimitHom D i := by
  ext a
  exact limitIncl_compatible D i j h a

lemma directLimitHom_dense :
    Dense (⋃ i, Set.range (directLimitHom D i).map) :=
  cstarDirectLimitInclude_dense _ _

end TracialStage

open CategoryTheory
namespace ChronologicalStage
attribute [local instance] generatedFamily_isClosed
variable {J : Type} [Preorder J] [isDirectedOrderJ : IsDirectedOrder J] [nonemptyJ : Nonempty J]
  (F : J ⥤ ChronologicalStage)

def limitStage : TracialStage := TracialStage.directLimit (F ⋙ forget)
def limitEmbedding (i : J) : TracialStage.Hom (F.obj i).stage (limitStage F) :=
  TracialStage.directLimitHom (F ⋙ forget) i

def limitHeight : Ordinal.{0} := ⨆ i, (F.obj i).height
omit isDirectedOrderJ nonemptyJ in
lemma height_le_limit [IsDirectedOrder J] [Nonempty J] (i : J) : (F.obj i).height ≤ limitHeight F :=
  Ordinal.le_iSup _ i

def limitIndex (k : Ordinal.{0}) (hk : k < limitHeight F) : J :=
  Classical.choose (Ordinal.lt_iSup_iff.mp hk)
omit isDirectedOrderJ nonemptyJ in
lemma limitIndex_spec [IsDirectedOrder J] [Nonempty J] (k : Ordinal.{0}) (hk : k < limitHeight F) :
    k < (F.obj (limitIndex F k hk)).height :=
  Classical.choose_spec (Ordinal.lt_iSup_iff.mp hk)

lemma limit_embedding_compatible (i j : J) (h : i ≤ j) (a : (F.obj i).stage) :
    (limitEmbedding F j).map ((F.map (homOfLE h)).embedding.map a) =
      (limitEmbedding F i).map a :=
  TracialStage.limitIncl_compatible (F ⋙ forget) i j h a

lemma limit_generator_agree (i j : J) (k : Ordinal.{0})
    (hi : k < (F.obj i).height) (hj : k < (F.obj j).height) :
    (limitEmbedding F i).map ((F.obj i).history.generator k) =
      (limitEmbedding F j).map ((F.obj j).history.generator k) := by
  obtain ⟨m,him,hjm⟩ := exists_ge_ge i j
  rw [← limit_embedding_compatible F i m him,← limit_embedding_compatible F j m hjm,
    (F.map (homOfLE him)).generator k hi,(F.map (homOfLE hjm)).generator k hj]

lemma limit_peak_agree (i j : J) (k : Ordinal.{0})
    (hi : k < (F.obj i).height) (hj : k < (F.obj j).height) (b : Bool) (n : ℕ) :
    (limitEmbedding F i).map (((F.obj i).history.pair k).peak b n) =
      (limitEmbedding F j).map (((F.obj j).history.pair k).peak b n) := by
  obtain ⟨m,him,hjm⟩ := exists_ge_ge i j
  rw [← limit_embedding_compatible F i m him,← limit_embedding_compatible F j m hjm,
    (F.map (homOfLE him)).peak k hi,(F.map (homOfLE hjm)).peak k hj]

omit nonemptyJ in
lemma limit_active_agree [Nonempty J] (i j : J) (k : Ordinal.{0})
    (hi : k < (F.obj i).height) (hj : k < (F.obj j).height) :
    k ∈ (F.obj i).history.active ↔ k ∈ (F.obj j).history.active := by
  obtain ⟨m,him,hjm⟩ := exists_ge_ge i j
  exact ((F.map (homOfLE him)).active k hi).trans ((F.map (homOfLE hjm)).active k hj).symm

omit nonemptyJ in
lemma limit_dependency_agree [Nonempty J] (i j : J) (k : Ordinal.{0})
    (hi : k < (F.obj i).height) (hj : k < (F.obj j).height) :
    (F.obj i).history.dependency k = (F.obj j).history.dependency k := by
  obtain ⟨m,him,hjm⟩ := exists_ge_ge i j
  exact ((F.map (homOfLE him)).dependency k hi).trans
    ((F.map (homOfLE hjm)).dependency k hj).symm

def limitGenerator (k : Ordinal.{0}) : limitStage F :=
  if hk : k < limitHeight F then
    (limitEmbedding F (limitIndex F k hk)).map
      ((F.obj (limitIndex F k hk)).history.generator k) else 1

def limitActive : Set Ordinal.{0} :=
  {k | ∃ hk : k < limitHeight F, k ∈ (F.obj (limitIndex F k hk)).history.active}

def limitDependency (k : Ordinal.{0}) : Set Ordinal.{0} :=
  if hk : k < limitHeight F then (F.obj (limitIndex F k hk)).history.dependency k else ∅

def limitPair (k : Ordinal.{0}) : PeakingPairData (limitStage F) :=
  if hk : k < limitHeight F then
    (limitEmbedding F (limitIndex F k hk)).pushPair
      ((F.obj (limitIndex F k hk)).history.pair k)
      ((F.obj (limitIndex F k hk)).history.trace k)
  else (limitStage F).dummyPair

lemma limitGenerator_stage (i : J) (k : Ordinal.{0}) (hk : k < (F.obj i).height) :
    limitGenerator F k = (limitEmbedding F i).map ((F.obj i).history.generator k) := by
  have hl := hk.trans_le (height_le_limit F i)
  rw [limitGenerator,dite_eq_left hl]
  exact limit_generator_agree F _ i k (limitIndex_spec F k hl) hk

lemma limitActive_stage (i : J) (k : Ordinal.{0}) (hk : k < (F.obj i).height) :
    k ∈ limitActive F ↔ k ∈ (F.obj i).history.active := by
  constructor
  · rintro ⟨hl,ha⟩
    exact (limit_active_agree F _ i k (limitIndex_spec F k hl) hk).mp ha
  · intro ha
    have hl := hk.trans_le (height_le_limit F i)
    exact ⟨hl,(limit_active_agree F _ i k (limitIndex_spec F k hl) hk).mpr ha⟩

lemma limitDependency_stage (i : J) (k : Ordinal.{0}) (hk : k < (F.obj i).height) :
    limitDependency F k = (F.obj i).history.dependency k := by
  have hl := hk.trans_le (height_le_limit F i)
  rw [limitDependency,dite_eq_left hl]
  exact limit_dependency_agree F _ i k (limitIndex_spec F k hl) hk

lemma limitPair_peak_stage (i : J) (k : Ordinal.{0}) (hk : k < (F.obj i).height)
    (b : Bool) (n : ℕ) :
    (limitPair F k).peak b n = (limitEmbedding F i).map (((F.obj i).history.pair k).peak b n) := by
  have hl := hk.trans_le (height_le_limit F i)
  rw [limitPair,dite_eq_left hl,TracialStage.Hom.pushPair_peak]
  exact limit_peak_agree F _ i k (limitIndex_spec F k hl) hk b n

lemma limitPair_trace (k : Ordinal.{0}) (a : limitStage F) :
    (limitPair F k).trace a = (limitStage F).trace a := by
  unfold limitPair
  split <;> rfl

lemma limitPair_leftPeak (k : Ordinal.{0}) (n : ℕ) :
    (limitPair F k).peak false n = (limitStage F).base (carPeak n) := by
  unfold limitPair
  split
  · simp only [TracialStage.Hom.pushPair_peak,ChronologicalHistory.leftPeak,
      TracialStage.Hom.base_map]
  · rfl

lemma limit_algebra_map (i : J) (S : Set Ordinal.{0}) (hS : S ⊆ Set.Iio (F.obj i).height) :
    ((F.obj i).history.algebra S).map (limitEmbedding F i).map =
      generatedFamily (Set.range (limitStage F).base) (limitGenerator F) S := by
  rw [ChronologicalData.algebra,TracialStage.Hom.generatedFamily_map]
  exact generatedFamily_congr_on _ _ _ _ (fun k hk => (limitGenerator_stage F i k (hS hk)).symm)

end ChronologicalStage

open CategoryTheory Topology
namespace ChronologicalStage
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder
variable {J : Type} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  (F : J ⥤ ChronologicalStage)

lemma limit_generated_eq (i : J) (S : Set Ordinal.{0}) (hS : S ⊆ Set.Iio (F.obj i).height) :
    generatedFamily (Set.range (limitStage F).base)
      ((limitEmbedding F i).map ∘ (F.obj i).history.generator) S =
      generatedFamily (Set.range (limitStage F).base) (limitGenerator F) S :=
  generatedFamily_congr_on _ _ _ _ (fun k hk => (limitGenerator_stage F i k (hS hk)).symm)

lemma limit_peak_mem (k : Ordinal.{0}) (ha : k ∈ limitActive F) (b : Bool) (n : ℕ) :
    (limitPair F k).peak b n ∈
      generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio k) := by
  obtain ⟨hk,ha⟩ := ha
  let i := limitIndex F k hk
  have hi : k < (F.obj i).height := limitIndex_spec F k hk
  rw [limitPair_peak_stage F i k hi,← limit_generated_eq F i _ (Set.Iio_subset_Iio hi.le)]
  exact (limitEmbedding F i).mapped_mem _ _ ((F.obj i).history.peak_mem k ha b n)

lemma limit_supported (k : Ordinal.{0}) (hk : k < limitHeight F)
    (ha : k ∈ limitActive F) (b : Bool) (n : ℕ) :
    (limitPair F k).peak b n ∈ generatedFamily (Set.range (limitStage F).base)
      (limitGenerator F) (limitDependency F k) := by
  let i := limitIndex F k hk
  have hi : k < (F.obj i).height := limitIndex_spec F k hk
  have hai := (limitActive_stage F i k hi).mp ha
  rw [limitPair_peak_stage F i k hi,limitDependency_stage F i k hi,
    ← limit_generated_eq F i _ (((F.obj i).history.lower k hi).trans (Set.Iio_subset_Iio hi.le))]
  exact (limitEmbedding F i).mapped_mem _ _ ((F.obj i).history.supported k hi hai b n)

lemma limit_chronological (k : Ordinal.{0}) (hk : k < limitHeight F)
    (ha : k ∈ limitActive F) :
    (limitPair F k).AmbientPresentation
      (generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio k))
      (limit_peak_mem F k ha) (limitGenerator F k)
      (generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio (k+1))) := by
  let i := limitIndex F k hk
  have hi : k < (F.obj i).height := limitIndex_spec F k hk
  let E := (F.obj i).history.toChronologicalHistory.push (limitEmbedding F i)
  have hai : k ∈ E.active := (limitActive_stage F i k hi).mp ha
  have H := E.chronological k hi hai
  have pS : ∀ b n, (E.pair k).peak b n ∈
      generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio k) := by
    intro b n
    rw [← limit_generated_eq F i _ (Set.Iio_subset_Iio hi.le)]
    exact E.peak_mem k hai b n
  have H' := PeakingPairData.AmbientPresentation.congr _ _ _ _ _ _ pS _
    (limit_generated_eq F i _ (Set.Iio_subset_Iio hi.le))
    (limit_generated_eq F i _ (Set.Iio_subset_Iio (Order.add_one_le_iff.mpr hi))) H
  have hz : E.generator k = limitGenerator F k := (limitGenerator_stage F i k hi).symm
  rw [hz] at H'
  exact PeakingPairData.AmbientPresentation.same_data (E.pair k) (limitPair F k)
    (fun b n => (limitPair_peak_stage F i k hi b n).symm)
    (fun a => (E.trace k a).trans (limitPair_trace F k a).symm) _ _ pS (limit_peak_mem F k ha) _ H'

lemma limit_inequivalent (k : Ordinal.{0}) (hk : k < limitHeight F)
    (ha : k ∈ limitActive F) :
    (limitPair F k).PairDistinctOn
      (generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio k))
      (limit_peak_mem F k ha) := by
  let i := limitIndex F k hk
  have hi : k < (F.obj i).height := limitIndex_spec F k hk
  let E := (F.obj i).history.toChronologicalHistory.push (limitEmbedding F i)
  have hai : k ∈ E.active := (limitActive_stage F i k hi).mp ha
  have pS : ∀ b n, (E.pair k).peak b n ∈
      generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio k) := by
    intro b n
    rw [← limit_generated_eq F i _ (Set.Iio_subset_Iio hi.le)]
    exact E.peak_mem k hai b n
  have H := PeakingPairData.PairDistinctOn.congr _ _ _ _ pS
    (limit_generated_eq F i _ (Set.Iio_subset_Iio hi.le)) (E.inequivalent k hi hai)
  exact PeakingPairData.PairDistinctOn.same_peaks (E.pair k) (limitPair F k)
    (fun b n => (limitPair_peak_stage F i k hi b n).symm) _ pS (limit_peak_mem F k ha) H

lemma limit_inactive (k : Ordinal.{0}) (ha : k ∉ limitActive F) : limitGenerator F k = 1 := by
  by_cases hk : k < limitHeight F
  · let i := limitIndex F k hk
    have hi : k < (F.obj i).height := limitIndex_spec F k hk
    rw [limitGenerator_stage F i k hi,
      (F.obj i).history.inactive k (fun h => ha ((limitActive_stage F i k hi).mpr h)),map_one]
  · exact dite_eq_right hk

lemma limit_generated :
    generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio (limitHeight F)) = ⊤ := by
  apply top_unique
  intro a _
  have hs : (⋃ i,Set.range (limitEmbedding F i).map) ⊆
      (generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio (limitHeight F)) : Set (limitStage F)) := by
    rintro a ⟨_,⟨i,rfl⟩,⟨x,rfl⟩⟩
    have hx : (limitEmbedding F i).map x ∈ ((F.obj i).history.algebra (Set.Iio (F.obj i).height)).map
        (limitEmbedding F i).map := by
      refine ⟨x,?_,rfl⟩
      rw [ChronologicalData.algebra,(F.obj i).history.generated]
      trivial
    rw [limit_algebra_map F i _ (fun _ h => h)] at hx
    exact generatedFamily_mono _ _ (Set.Iio_subset_Iio (height_le_limit F i)) hx
  exact (show IsClosed (generatedFamily (Set.range (limitStage F).base) (limitGenerator F)
    (Set.Iio (limitHeight F)) : Set (limitStage F)) from inferInstance).closure_subset_iff.mpr hs
      (TracialStage.directLimitHom_dense (F ⋙ forget) a)

def limitHistory : ChronologicalData (limitStage F) (limitHeight F) where
  generator := limitGenerator F
  active := limitActive F
  active_lt := fun k hk => hk.choose
  dependency := limitDependency F
  lower k hk := by
    rw [limitDependency_stage F (limitIndex F k hk) k (limitIndex_spec F k hk)]
    exact (F.obj _).history.lower k (limitIndex_spec F k hk)
  countable k hk := by
    rw [limitDependency_stage F (limitIndex F k hk) k (limitIndex_spec F k hk)]
    exact (F.obj _).history.countable k (limitIndex_spec F k hk)
  pair := limitPair F
  trace := limitPair_trace F
  leftPeak := limitPair_leftPeak F
  supported := limit_supported F
  peak_mem := limit_peak_mem F
  chronological := limit_chronological F
  inactive := limit_inactive F
  inequivalent := limit_inequivalent F
  generated := limit_generated F

def directLimit : ChronologicalStage := ⟨limitStage F,limitHeight F,limitHistory F⟩
def directLimitHom (i : J) : Hom (F.obj i) (directLimit F) where
  embedding := limitEmbedding F i
  height_le := height_le_limit F i
  generator k hk := (limitGenerator_stage F i k hk).symm
  active k hk := (limitActive_stage F i k hk).symm
  dependency k hk := (limitDependency_stage F i k hk).symm
  peak k hk b n := (limitPair_peak_stage F i k hk b n).symm

def directLimitCocone : CategoryTheory.Limits.Cocone F where
  pt := directLimit F
  ι := {app := directLimitHom F
        naturality := fun i j h => by
          apply Hom.ext
          apply TracialStage.Hom.ext
          ext a
          exact limit_embedding_compatible F i j (leOfHom h) a}

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable {J : Type} [LinearOrder J] (S : Set J)
  (F : ∀ j : S, Set.Iic (j : J) ⥤ ChronologicalStage)
  (hF : ∀ (i j : S) (h : i ≤ j), restrictionLE (F j) h = F i)

include hF in
lemma prefix_congr_obj (i j : S) (k : J) (hi : k ≤ i) (hj : k ≤ j) :
    (F i).obj ⟨k,hi⟩ = (F j).obj ⟨k,hj⟩ := by
  rcases le_total i j with hij | hji
  · have hh := Functor.congr_obj (hF i j hij) ⟨k,hi⟩
    exact hh.symm
  · exact (Functor.congr_obj (hF j i hji) ⟨k,hj⟩)

include hF in
lemma prefix_congr_arrow (i j : S) {k l : J} (hkl : k ≤ l) (hi : l ≤ i) (hj : l ≤ j) :
    arrowMap (F i) k l hkl hi = arrowMap (F j) k l hkl hj := by
  rcases le_total i j with hij | hji
  · have hh := congrArg (fun D => arrowMap D k l hkl hi) (hF i j hij)
    exact hh.symm
  · exact congrArg (fun D => arrowMap D k l hkl hj) (hF j i hji)

lemma prefix_congr_map (i j : S) {k l : J} (hkl : k ≤ l) (hi : l ≤ i) (hj : l ≤ j) :
    (F i).map (homOfLE hkl : ⟨k,hkl.trans hi⟩ ⟶ ⟨l,hi⟩) =
      eqToHom (prefix_congr_obj S F hF i j k (hkl.trans hi) (hkl.trans hj)) ≫
        (F j).map (homOfLE hkl) ≫
        eqToHom (prefix_congr_obj S F hF i j l hi hj).symm := by
  have hh := (Arrow.mk_eq_mk_iff _ _).mp (prefix_congr_arrow S F hF i j hkl hi hj)
  tauto

def prefixMap (i j : S) (h : i ≤ j) :
    (F i).obj ⟨i,le_rfl⟩ ⟶ (F j).obj ⟨j,le_rfl⟩ :=
  eqToHom (prefix_congr_obj S F hF i j i le_rfl h) ≫ (F j).map (homOfLE h)

@[simp] lemma prefixMap_refl (i : S) : prefixMap S F hF i i le_rfl = 𝟙 _ := by
  simp [prefixMap]

lemma prefixMap_comp (i j k : S) (hij : i ≤ j) (hjk : j ≤ k) :
    prefixMap S F hF i j hij ≫ prefixMap S F hF j k hjk =
      prefixMap S F hF i k (hij.trans hjk) := by
  simp [prefixMap,prefix_congr_map S F hF j k hij le_rfl hjk,← Functor.map_comp]

def gluePrefixes : S ⥤ ChronologicalStage where
  obj i := (F i).obj ⟨i,le_rfl⟩
  map {i j} f := prefixMap S F hF i j (leOfHom f)
  map_id i := prefixMap_refl S F hF i
  map_comp {i j k} f g := (prefixMap_comp S F hF i j k (leOfHom f) (leOfHom g)).symm

lemma gluePrefixes_arrow (i j : S) (hij : i ≤ j) :
    Arrow.mk ((gluePrefixes S F hF).map (homOfLE hij)) =
      arrowMap (F j) i j hij le_rfl := by
  simp [gluePrefixes,prefixMap,arrowMap]

variable {S F hF}

lemma restrictionLE_of_glued_cocone (l : J)
    (F : ∀ j : Set.Iio l, Set.Iic (j : J) ⥤ ChronologicalStage)
    (hF : ∀ (i j : Set.Iio l) (h : i ≤ j), restrictionLE (F j) h = F i)
    (c : Cocone (gluePrefixes (Set.Iio l) F hF)) (i : J) (hi : i < l) :
    restrictionLE (SuccStruct.ofCocone c) hi.le = F ⟨i,hi⟩ := by
  apply Arrow.functor_ext
  intro k m f
  change arrowMap (restrictionLE (SuccStruct.ofCocone c) hi.le) k m
    (leOfHom f) (show (m : J) ≤ i from m.property) = _
  exact (arrowMap_restrictionLE (SuccStruct.ofCocone c) hi.le k m
      (leOfHom f) (show (m : J) ≤ i from m.property)).trans
    ((SuccStruct.arrowMap_ofCocone c k m (leOfHom f) (lt_of_le_of_lt m.property hi)).trans
      ((gluePrefixes_arrow (Set.Iio l) F hF
        ⟨k,lt_of_le_of_lt k.property hi⟩ ⟨m,lt_of_le_of_lt m.property hi⟩ (leOfHom f)).trans
        (prefix_congr_arrow (Set.Iio l) F hF
          ⟨m,lt_of_le_of_lt m.property hi⟩ ⟨i,hi⟩ (leOfHom f) le_rfl m.property)))

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable (J : Type) [LinearOrder J]

def prefixSystem : Jᵒᵖ ⥤ Type 1 where
  obj j := Set.Iic j.unop ⥤ ChronologicalStage
  map {i j} f := ↾fun D => restrictionLE D (leOfHom f.unop)
  map_id i := by
    apply ConcreteCategory.hom_ext
    intro D
    apply Arrow.functor_ext
    intro k l f
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro D
    apply Arrow.functor_ext
    intro k l f
    rfl

variable [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]

omit orderBotJ in
lemma restriction_extendToSucc [OrderBot J] (j : J) (hj : ¬ IsMax j)
    (D : Set.Iic j ⥤ ChronologicalStage) {X : ChronologicalStage}
    (τ : D.obj ⟨j,le_rfl⟩ ⟶ X) :
    restrictionLE (extendToSucc hj D τ) (Order.le_succ j) = D := by
  apply Arrow.functor_ext
  intro k l f
  exact (arrowMap_restrictionLE (extendToSucc hj D τ) (Order.le_succ j) k l
    (leOfHom f) l.property).trans
    (arrowMap_extendToSucc hj D τ k l (leOfHom f) l.property)

abbrev SuccessorRule := ∀ (j : J) (_ : ¬ IsMax j) (D : Set.Iic j ⥤ ChronologicalStage),
  Σ X : ChronologicalStage, (D.obj ⟨j,le_rfl⟩ ⟶ X)

variable (R : SuccessorRule J)

omit succOrderJ orderBotJ in
lemma section_coherent [SuccOrder J] [OrderBot J] (j : J)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ prefixSystem J).sections)
    (i k : Set.Iio j) (h : i ≤ k) :
    restrictionLE (x.val (op k)) h = x.val (op i) :=
  x.property (homOfLE h).op

def recursionData : (prefixSystem J).WellOrderInductionData where
  succ j hj D := extendToSucc hj D (R j hj D).2
  map_succ j hj D := restriction_extendToSucc J j hj D (R j hj D).2
  lift j hj x := by
    letI : Nonempty (Set.Iio j) := ⟨⟨⊥,hj.bot_lt⟩⟩
    exact SuccStruct.ofCocone (directLimitCocone
      (gluePrefixes (Set.Iio j) (fun i => x.val (op i)) (section_coherent J j x)))
  map_lift j hj x i hi := by
    let : Nonempty (Set.Iio j) := ⟨⟨⊥,hj.bot_lt⟩⟩
    exact restrictionLE_of_glued_cocone j (fun i => x.val (op i))
      (section_coherent J j x) (directLimitCocone
        (gluePrefixes (Set.Iio j) (fun i => x.val (op i)) (section_coherent J j x))) i hi

variable [WellFoundedLT J]

def recursivePrefixes : (prefixSystem J).sections :=
  (recursionData J R).sectionsMk ((Functor.const (Set.Iic (⊥ : J))).obj initial)

lemma recursivePrefixes_compatible (i j : J) (h : i ≤ j) :
    restrictionLE ((recursivePrefixes J R).val (op j)) h =
      (recursivePrefixes J R).val (op i) :=
  (recursivePrefixes J R).property (homOfLE h).op

def recursiveTower : J ⥤ ChronologicalStage :=
  (OrderIso.Set.univ : Set.univ ≃o J).symm.monotone.functor ⋙
    gluePrefixes Set.univ (fun j => (recursivePrefixes J R).val (op j.val))
      (fun i j h => recursivePrefixes_compatible J R i j h)

lemma recursivePrefixes_bot :
    (recursivePrefixes J R).val (op ⊥) =
      (Functor.const (Set.Iic (⊥ : J))).obj initial :=
  (recursionData J R).sectionsMk_val_op_bot _

lemma recursivePrefixes_succ (j : J) (hj : ¬ IsMax j) :
    (recursivePrefixes J R).val (op (Order.succ j)) =
      extendToSucc hj ((recursivePrefixes J R).val (op j))
        (R j hj ((recursivePrefixes J R).val (op j))).2 := by
  let e : (recursionData J R).Extension
      ((Functor.const (Set.Iic (⊥ : J))).obj initial) (Order.succ j) :=
    (Functor.WellOrderInductionData.Extension.instUnique (F := prefixSystem J)
      (d := recursionData J R) (val₀ := (Functor.const (Set.Iic (⊥ : J))).obj initial)
      (Order.succ j)).default
  have h := e.map_succ j (Order.lt_succ_of_not_isMax hj)
  change restrictionLE e.val le_rfl =
    extendToSucc hj (restrictionLE e.val (Order.le_succ j))
      (R j hj (restrictionLE e.val (Order.le_succ j))).2 at h
  have hr : restrictionLE e.val (Order.le_succ j) =
      (recursivePrefixes J R).val (op j) :=
    recursivePrefixes_compatible J R _ _ (Order.le_succ j)
  rw [hr] at h
  exact h

lemma recursiveTower_obj (j : J) :
    (recursiveTower J R).obj j = ((recursivePrefixes J R).val (op j)).obj ⟨j,le_rfl⟩ := rfl

lemma recursiveTower_arrow (i j : J) (hij : i ≤ j) :
    Arrow.mk ((recursiveTower J R).map (homOfLE hij)) =
      arrowMap ((recursivePrefixes J R).val (op j)) i j hij le_rfl :=
  gluePrefixes_arrow Set.univ (fun j => (recursivePrefixes J R).val (op j.val))
    (fun i j h => recursivePrefixes_compatible J R i j h) ⟨i,Set.mem_univ i⟩ ⟨j,Set.mem_univ j⟩ hij

lemma recursiveTower_bot : (recursiveTower J R).obj ⊥ = initial := by
  rw [recursiveTower_obj,recursivePrefixes_bot]
  rfl

lemma recursiveTower_succ_arrow (j : J) (hj : ¬ IsMax j) :
    Arrow.mk ((recursiveTower J R).map (homOfLE (Order.le_succ j))) =
      Arrow.mk (R j hj ((recursivePrefixes J R).val (op j))).2 := by
  rw [recursiveTower_arrow,recursivePrefixes_succ J R j hj]
  exact arrowSucc_extendToSucc hj _ _

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable (J : Type) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (R : SuccessorRule J)

def earlierPrefixes (j : J) :
    ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ prefixSystem J).sections where
  val k := (recursivePrefixes J R).val (op k.unop.val)
  property {i k} f := recursivePrefixes_compatible J R k.unop.val i.unop.val (leOfHom f.unop)

lemma recursivePrefixes_limit (j : J) (hj : Order.IsSuccLimit j) :
    (recursivePrefixes J R).val (op j) =
      (recursionData J R).lift j hj (earlierPrefixes J R j) := by
  let e : (recursionData J R).Extension
      ((Functor.const (Set.Iic (⊥ : J))).obj initial) j :=
    (Functor.WellOrderInductionData.Extension.instUnique (F := prefixSystem J)
      (d := recursionData J R) (val₀ := (Functor.const (Set.Iic (⊥ : J))).obj initial)
      j).default
  have h := e.map_limit j hj le_rfl
  change e.val = (recursionData J R).lift j hj _ at h
  change e.val = _
  rw [h]
  congr 1
  ext k
  exact recursivePrefixes_compatible J R k.unop.val j k.unop.property.le

lemma recursiveTower_limit_height (j : J) (hj : Order.IsSuccLimit j) :
    ((recursiveTower J R).obj j).height =
      ⨆ i : Set.Iio j, ((recursiveTower J R).obj i.val).height := by
  let : Nonempty (Set.Iio j) := ⟨⟨⊥,hj.bot_lt⟩⟩
  rw [recursiveTower_obj,recursivePrefixes_limit J R j hj]
  change ((SuccStruct.ofCocone (directLimitCocone
    (gluePrefixes (Set.Iio j) (fun i => (recursivePrefixes J R).val (op i.val))
      (section_coherent J j (earlierPrefixes J R j))))).obj ⟨j,le_rfl⟩).height = _
  rw [SuccStruct.ofCocone_obj_eq_pt]
  rfl

lemma recursiveTower_succ_height
    (hr : ∀ j hj D, (R j hj D).1.height = (D.obj ⟨j,le_rfl⟩).height+1)
    (j : J) (hj : ¬ IsMax j) :
    ((recursiveTower J R).obj (Order.succ j)).height =
      ((recursiveTower J R).obj j).height+1 := by
  have h := congrArg (fun a : Arrow ChronologicalStage => a.right.height)
    (recursiveTower_succ_arrow J R j hj)
  exact h.trans (hr j hj ((recursivePrefixes J R).val (op j)))

theorem recursiveTower_height_le
    (hr : ∀ j hj D, (R j hj D).1.height = (D.obj ⟨j,le_rfl⟩).height+1)
    (o : J → Ordinal.{0}) (h0 : o ⊥ = 0)
    (hs : ∀ j, ¬ IsMax j → o j+1 ≤ o (Order.succ j))
    (hm : Monotone o) (j : J) :
    ((recursiveTower J R).obj j).height ≤ o j := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl : j = ⊥ := by simpa using hj
    rw [recursiveTower_bot,h0]
    exact le_rfl
  | succ j hj ih =>
    rw [recursiveTower_succ_height J R hr j hj]
    have hh : ((recursiveTower J R).obj j).height+1 ≤ o j+1 := by
      simpa using (Ordinal.add_le_add_iff_right 1).mpr ih
    exact hh.trans (hs j hj)
  | isSuccLimit j hj ih =>
    rw [recursiveTower_limit_height J R j hj]
    exact Ordinal.iSup_le fun i => (ih i.val i.property).trans (hm i.property.le)

end ChronologicalStage

open CategoryTheory Cardinal Classical
namespace TracialStage.Hom
variable {X Y : TracialStage} (j : Hom X Y) (f : X →L[ℂ] ℂ) (hf : IsPureState f)

def pureLift : Y →L[ℂ] ℂ :=
  ((j.uep f hf).exists_unique_pure j.injective hf).choose
lemma pureLift_pure : IsPureState (j.pureLift f hf) :=
  ((j.uep f hf).exists_unique_pure j.injective hf).choose_spec.1
lemma pureLift_restrict : restrictState j.map (j.pureLift f hf) = f :=
  ((j.uep f hf).exists_unique_pure j.injective hf).choose_spec.2.1
end TracialStage.Hom

namespace ChronologicalStage
variable (K : Type) (hK : 𝔠 ≤ #K) (X : ChronologicalStage)

def pureList : K → X.stage →L[ℂ] ℂ :=
  if h : #({f : X.stage →L[ℂ] ℂ // IsPureState f}) ≤ 𝔠 then
    (exists_pureState_list K hK h X.stage.reference X.stage.reference_spec.1).choose
  else fun _ => X.stage.reference

lemma pureList_pure (k : K) : IsPureState (pureList K hK X k) := by
  classical
  unfold pureList
  split_ifs with h
  · exact (exists_pureState_list K hK h X.stage.reference X.stage.reference_spec.1).choose_spec.1 k
  · exact X.stage.reference_spec.1

lemma pureList_covers (hheight : X.height.card ≤ 𝔠)
    (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ k, pureList K hK X k = f := by
  classical
  have hc := X.history.state_count hheight
  simp only [pureList,dite_eq_left hc]
  exact (exists_pureState_list K hK hc X.stage.reference X.stage.reference_spec.1).choose_spec.2 f hf

variable (H : KOS.SimpleSeparableRows)

def joiningChoice (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    Σ Y : ChronologicalStage, Hom X Y :=
  ⟨(X.exists_joining_successor H f hf).choose,
    (X.exists_joining_successor H f hf).choose_spec.choose⟩

lemma joiningChoice_height (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    (joiningChoice X H f hf).1.height = X.height+1 :=
  (X.exists_joining_successor H f hf).choose_spec.choose_spec.1

lemma joiningChoice_treated (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ F : (joiningChoice X H f hf).1.stage →L[ℂ] ℂ, ∃ hF : IsPureState F,
      restrictState (joiningChoice X H f hf).2.embedding.map F = f ∧
      PureStateEquivalent (joiningChoice X H f hf).1.stage.reference
        (joiningChoice X H f hf).1.stage.reference_spec.1 F hF :=
  (X.exists_joining_successor H f hf).choose_spec.choose_spec.2

variable {J : Type} [LinearOrder J]
  (σ : J × K → J) (hσ : ∀ p, p.1 ≤ σ p)
  (j : J) (D : Set.Iic j ⥤ ChronologicalStage)

def scheduledTarget : (D.obj ⟨j,le_rfl⟩).stage →L[ℂ] ℂ :=
  if h : ∃ p, σ p = j then
    let p := h.choose
    let hp : p.1 ≤ j := (hσ p).trans_eq h.choose_spec
    let e := (D.map (homOfLE hp : ⟨p.1,hp⟩ ⟶ ⟨j,le_rfl⟩)).embedding
    e.pureLift (pureList K hK (D.obj ⟨p.1,hp⟩) p.2)
      (pureList_pure K hK (D.obj ⟨p.1,hp⟩) p.2)
  else (D.obj ⟨j,le_rfl⟩).stage.reference

lemma scheduledTarget_pure : IsPureState (scheduledTarget K hK σ hσ j D) := by
  classical
  unfold scheduledTarget
  split_ifs
  · exact TracialStage.Hom.pureLift_pure _ _ _
  · exact (D.obj ⟨j,le_rfl⟩).stage.reference_spec.1

lemma scheduledTarget_restrict (hi : Function.Injective σ)
    (p : J × K) (hp : σ p = j) :
    restrictState (D.map (homOfLE ((hσ p).trans_eq hp) :
      ⟨p.1,(hσ p).trans_eq hp⟩ ⟶ ⟨j,le_rfl⟩)).embedding.map
      (scheduledTarget K hK σ hσ j D) =
        pureList K hK (D.obj ⟨p.1,(hσ p).trans_eq hp⟩) p.2 := by
  classical
  have hx : ∃ q,σ q=j := ⟨p,hp⟩
  have he : hx.choose = p := hi (hx.choose_spec.trans hp.symm)
  subst p
  simp only [scheduledTarget,dite_eq_left hx]
  exact TracialStage.Hom.pureLift_restrict _ _ _

variable [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]

def scheduledRule : SuccessorRule J := fun j _ D =>
  joiningChoice (D.obj ⟨j,le_rfl⟩) H (scheduledTarget K hK σ hσ j D)
    (scheduledTarget_pure K hK σ hσ j D)

omit succOrderJ orderBotJ in
lemma scheduledRule_height [SuccOrder J] [OrderBot J] (j : J) (hj : ¬ IsMax j) (D : Set.Iic j ⥤ ChronologicalStage) :
    (scheduledRule K hK H σ hσ j hj D).1.height =
      (D.obj ⟨j,le_rfl⟩).height+1 :=
  joiningChoice_height _ _ _ _

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject Opposite Cardinal
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable {J : Type} [LinearOrder J] [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]

omit orderBotJ in
lemma arrowMap_extendToSucc_through [OrderBot J] (j : J) (hj : ¬ IsMax j)
    (D : Set.Iic j ⥤ ChronologicalStage) {X : ChronologicalStage}
    (τ : D.obj ⟨j,le_rfl⟩ ⟶ X) (i : J) (hij : i ≤ j) :
    arrowMap (extendToSucc hj D τ) i (Order.succ j)
      (hij.trans (Order.le_succ j)) le_rfl =
      Arrow.mk ((D.map (homOfLE hij : ⟨i,hij⟩ ⟶ ⟨j,le_rfl⟩)) ≫ τ) := by
  apply Arrow.ext (extendToSucc_obj_eq hj D τ i hij)
    (extendToSucc_obj_succ_eq hj D τ)
  have hc := (extendToSucc hj D τ).map_comp
    (homOfLE hij : ⟨i,hij.trans (Order.le_succ j)⟩ ⟶ ⟨j,Order.le_succ j⟩)
    (homOfLE (Order.le_succ j) : (⟨j,Order.le_succ j⟩ : Set.Iic (Order.succ j)) ⟶ ⟨Order.succ j,le_rfl⟩)
  simp only [homOfLE_comp] at hc
  change (extendToSucc hj D τ).map
    (homOfLE (hij.trans (Order.le_succ j)) :
      ⟨i, hij.trans (Order.le_succ j)⟩ ⟶ ⟨Order.succ j, le_rfl⟩) = _
  rw [hc, extendToSucc_map hj D τ i j hij le_rfl,
    extendToSucc_map_le_succ, assoc, assoc, Iso.inv_hom_id_assoc]
  simp only [extendToSuccObjIso, extendToSucc.objIso,
    extendToSuccObjSuccIso, extendToSucc.objSuccIso,
    eqToIso.hom, eqToIso.inv, Arrow.mk_hom, assoc]
  rfl

variable (K : Type) (hK : 𝔠 ≤ #K)

def Treated (η : K) (a : Arrow ChronologicalStage) : Prop :=
  ∃ F : a.right.stage →L[ℂ] ℂ, ∃ hF : IsPureState F,
    restrictState a.hom.embedding.map F = pureList K hK a.left η ∧
    PureStateEquivalent a.right.stage.reference a.right.stage.reference_spec.1 F hF

variable (H : KOS.SimpleSeparableRows) (σ : J × K → J)
    (hσ : ∀ p,p.1 ≤ σ p)

omit succOrderJ orderBotJ in
lemma scheduledRule_treated [SuccOrder J] [OrderBot J] (hi : Function.Injective σ) (j : J) (hj : ¬ IsMax j) (D : Set.Iic j ⥤ ChronologicalStage)
    (p : J × K) (hp : σ p = j) :
    Treated K hK p.2 (Arrow.mk
      ((D.map (homOfLE ((hσ p).trans_eq hp) :
        ⟨p.1,(hσ p).trans_eq hp⟩ ⟶ ⟨j,le_rfl⟩)) ≫
          (scheduledRule K hK H σ hσ j hj D).2)) := by
  obtain ⟨F,hF,hr,he⟩ := joiningChoice_treated (D.obj ⟨j,le_rfl⟩) H
    (scheduledTarget K hK σ hσ j D) (scheduledTarget_pure K hK σ hσ j D)
  refine ⟨F,hF,?_,he⟩
  change restrictState ((scheduledRule K hK H σ hσ j hj D).2.embedding.map.comp
    (D.map (homOfLE ((hσ p).trans_eq hp))).embedding.map) F = _
  exact (restrictState_comp _ _ F).symm.trans
    ((congrArg (restrictState (D.map (homOfLE ((hσ p).trans_eq hp) :
      ⟨p.1,(hσ p).trans_eq hp⟩ ⟶ ⟨j,le_rfl⟩)).embedding.map) hr).trans
      (scheduledTarget_restrict K hK σ hσ j D hi p hp))

variable [WellFoundedLT J]

lemma recursiveTower_through_succ_arrow (R : SuccessorRule J)
    (j : J) (hj : ¬ IsMax j) (i : J) (hij : i ≤ j) :
    Arrow.mk ((recursiveTower J R).map (homOfLE (hij.trans (Order.le_succ j)))) =
      Arrow.mk ((((recursivePrefixes J R).val (op j)).map
        (homOfLE hij : ⟨i,hij⟩ ⟶ ⟨j,le_rfl⟩)) ≫
          (R j hj ((recursivePrefixes J R).val (op j))).2) := by
  rw [recursiveTower_arrow,recursivePrefixes_succ J R j hj]
  exact arrowMap_extendToSucc_through j hj _ _ i hij

theorem recursiveTower_treated (hi : Function.Injective σ) (p : J × K) (hj : ¬ IsMax (σ p)) :
    Treated K hK p.2
      (Arrow.mk ((recursiveTower J (scheduledRule K hK H σ hσ)).map
        (homOfLE ((hσ p).trans (Order.le_succ (σ p)))))) := by
  rw [recursiveTower_through_succ_arrow (scheduledRule K hK H σ hσ) (σ p) hj p.1 (hσ p)]
  exact scheduledRule_treated K hK H σ hσ hi (σ p) hj _ p rfl

end ChronologicalStage

open Cardinal Ordinal

abbrev ConstructionIndex := constructionCardinal.{0}.ord.ToType

lemma construction_ordinal_limit : Order.IsSuccLimit constructionCardinal.{0}.ord :=
  Cardinal.isSuccLimit_ord (Cardinal.aleph0_le_continuum.trans (Order.le_succ _))

instance constructionIndex_nonempty : Nonempty ConstructionIndex :=
  ⟨Ordinal.ToType.mk ⟨0,construction_ordinal_limit.bot_lt⟩⟩

instance constructionIndex_orderBot : OrderBot ConstructionIndex :=
  WellFoundedLT.toOrderBot _

instance constructionIndex_noMax : NoMaxOrder ConstructionIndex where
  exists_gt j := by
    refine ⟨Ordinal.ToType.mk ⟨(j:Ordinal)+1,construction_ordinal_limit.add_one_lt j.toOrd.property⟩,?_⟩
    apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
    change (j:Ordinal) < (Ordinal.ToType.mk ⟨(j:Ordinal)+1,_⟩ : Ordinal)
    simpa only [Ordinal.ToType.toOrd,OrderIso.symm_apply_apply] using lt_add_one (j:Ordinal)

lemma constructionIndex_bot : ((⊥ : ConstructionIndex) : Ordinal) = 0 := by
  have h : (⊥ : ConstructionIndex) ≤ Ordinal.ToType.mk ⟨0,construction_ordinal_limit.bot_lt⟩ := bot_le
  have h' := Ordinal.ToType.mk.symm.monotone h
  change (↑(⊥ : ConstructionIndex) : Ordinal) ≤
    (Ordinal.ToType.mk ⟨0,construction_ordinal_limit.bot_lt⟩ : Ordinal) at h'
  simpa only [Ordinal.ToType.toOrd,OrderIso.symm_apply_apply,nonpos_iff_eq_zero] using h'

lemma constructionIndex_monotone : Monotone (fun j : ConstructionIndex => (j:Ordinal)) :=
  fun _ _ h => Ordinal.ToType.mk.symm.monotone h

lemma constructionIndex_succ_bound (j : ConstructionIndex) :
    (j:Ordinal)+1 ≤ ((Order.succ j : ConstructionIndex):Ordinal) := by
  apply Order.add_one_le_iff.mpr
  exact Ordinal.ToType.mk.symm.strictMono (Order.lt_succ j)

lemma constructionIndex_cardinal : Cardinal.continuum ≤ Cardinal.mk ConstructionIndex := by
  rw [Cardinal.mk_ord_toType]
  exact Order.le_succ _

open CategoryTheory Topology
namespace ChronologicalStage
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder
variable (F : constructionCardinal.{0}.ord.ToType ⥤ ChronologicalStage)

lemma limit_countable_support_bounded (S : Set Ordinal.{0}) (hS : S.Countable)
    (hSl : S ⊆ Set.Iio (limitHeight F)) :
    ∃ j : constructionCardinal.{0}.ord.ToType, S ⊆ Set.Iio (F.obj j).height := by
  let e : S → constructionCardinal.{0}.ord.ToType :=
    fun k => limitIndex F k.val (hSl k.property)
  let : Countable S := hS.to_subtype
  obtain ⟨j,hj⟩ := countable_bounded_construction (Set.range e) (Set.countable_range e)
  refine ⟨j,?_⟩
  intro k hk
  have he := hj (e ⟨k,hk⟩) ⟨⟨k,hk⟩,rfl⟩
  exact (limitIndex_spec F k (hSl hk)).trans_le
    (F.map (homOfLE he.le)).height_le

lemma limit_support_le_range (S : Set Ordinal.{0})
    (j : constructionCardinal.{0}.ord.ToType) (hS : S ⊆ Set.Iio (F.obj j).height) :
    (limitHistory F).algebra S ≤ (limitEmbedding F j).map.range := by
  change generatedFamily (Set.range (limitStage F).base) (limitGenerator F) S ≤ _
  rw [← limit_generated_eq F j S hS]
  rw [← (F.obj j).history.image_generated_range (limitEmbedding F j)]
  exact generatedFamily_mono _ _ hS

theorem limit_eventual_pure (f : (limitStage F) →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ j : constructionCardinal.{0}.ord.ToType,
      IsPureState (restrictState (limitEmbedding F j).map f) := by
  obtain ⟨S,hSc,hS,_,_,_,hp,hu⟩ := (limitHistory F).countable_determination f hf
  obtain ⟨j,hSj⟩ := limit_countable_support_bounded F S hSc hS
  let φ := (limitEmbedding F j).map
  have hφ : Function.Injective φ := (limitEmbedding F j).injective
  let : IsClosed (φ.range : Set (limitStage F)) :=
    (NonUnitalStarAlgHom.isometry φ hφ).isClosedEmbedding.isClosed_range
  have hr := pure_restrict_intermediate_subalgebra
    ((limitHistory F).algebra S) φ.range (limit_support_le_range F S j hSj)
    f hf.1 hp hu
  let e : (F.obj j).stage ≃⋆ₐ[ℂ] φ.range :=
    StarAlgEquiv.ofBijective (φ.codRestrict φ.range (fun a => ⟨a,rfl⟩))
      ⟨fun a b h => hφ (congrArg Subtype.val h),by
        rintro ⟨a,⟨b,rfl⟩⟩; exact ⟨b,rfl⟩⟩
  exact ⟨j,isPureState_restrict_equiv e (restrictState φ.range.subtype f) hr⟩

end ChronologicalStage

open CategoryTheory Cardinal
namespace ChronologicalStage

abbrev FullRule (H : KOS.SimpleSeparableRows)
    (σ : ConstructionIndex × ConstructionIndex → ConstructionIndex)
    (hσ : ∀ p,p.1 ≤ σ p) :=
  scheduledRule ConstructionIndex constructionIndex_cardinal H σ hσ

abbrev fullTower (H : KOS.SimpleSeparableRows)
    (σ : ConstructionIndex × ConstructionIndex → ConstructionIndex)
    (hσ : ∀ p,p.1 ≤ σ p) := recursiveTower ConstructionIndex (FullRule H σ hσ)

variable (H : KOS.SimpleSeparableRows)
    (σ : ConstructionIndex × ConstructionIndex → ConstructionIndex)
    (hσ : ∀ p,p.1 ≤ σ p)

lemma fullTower_height (j : ConstructionIndex) :
    ((fullTower H σ hσ).obj j).height ≤ (j:Ordinal) :=
  recursiveTower_height_le _ _ (scheduledRule_height _ _ _ _ _)
    (fun j => (j:Ordinal)) constructionIndex_bot
    (fun j _ => constructionIndex_succ_bound j) constructionIndex_monotone j

lemma fullTower_count (j : ConstructionIndex) :
    ((fullTower H σ hσ).obj j).height.card ≤ 𝔠 :=
  (Ordinal.card_le_card (fullTower_height H σ hσ j)).trans (construction_initial_cardinal_le j)

theorem fullTower_pure_reference (hi : Function.Injective σ)
    (f : limitStage (fullTower H σ hσ) →L[ℂ] ℂ) (hf : IsPureState f) :
    PureStateEquivalent f hf (limitStage (fullTower H σ hσ)).reference
      (limitStage (fullTower H σ hσ)).reference_spec.1 := by
  let F := fullTower H σ hσ
  let X := limitStage F
  let into := fun j => (limitEmbedding F j).map
  let incl := fun {i j : ConstructionIndex} (h : i ≤ j) => (F.map (homOfLE h)).embedding.map
  have hcomp : ∀ {i j} (h : i ≤ j), (into j).comp (incl h) = into i := by
    intro i j h
    ext a
    exact limit_embedding_compatible F i j h a
  have hfp : ∀ j, IsPureState (restrictState (into j) X.reference) := by
    intro j
    rw [(limitEmbedding F j).reference_map]
    exact (F.obj j).stage.reference_spec.1
  apply scheduled_pure_equivalent_to_reference (fun j => (F.obj j).stage)
    into (fun j => (limitEmbedding F j).injective) incl hcomp
    (fun j => (limitEmbedding F j).uep) X.reference X.reference_spec.1 hfp
    (fun j => pureList ConstructionIndex constructionIndex_cardinal (F.obj j))
    (fun j => pureList_pure ConstructionIndex constructionIndex_cardinal (F.obj j))
    (fun j g hg => pureList_covers ConstructionIndex constructionIndex_cardinal (F.obj j)
      (fullTower_count H σ hσ j) g hg)
    σ hσ Order.succ Order.le_succ ?_ f hf (limit_eventual_pure F f hf)
  intro j η
  obtain ⟨G,hG,hr,he⟩ := recursiveTower_treated ConstructionIndex constructionIndex_cardinal
    H σ hσ hi (j,η) (not_isMax _)
  refine ⟨G,hG,hr,?_⟩
  change PureStateEquivalent G hG
    (restrictState (limitEmbedding F _).map (limitStage F).reference) _
  simp only [TracialStage.Hom.reference_map]
  exact he.symm

end ChronologicalStage

section

universe u v
section
variable (A : Type u) [CStarAlgebra A]

instance liftStarRing : StarRing (ULift.{v} A) where
  star a := ⟨star a.down⟩
  star_involutive a := by cases a; simp
  star_mul a b := by cases a; cases b; exact congrArg ULift.up (star_mul _ _)
  star_add a b := by cases a; cases b; exact congrArg ULift.up (star_add _ _)

instance liftStarModule : StarModule ℂ (ULift.{v} A) where
  star_smul c a := by cases a; exact congrArg ULift.up (star_smul c _)

instance liftCStarRing : CStarRing (ULift.{v} A) where
  norm_mul_self_le a := by
    change ‖a.down‖ * ‖a.down‖ ≤ ‖star a.down * a.down‖
    exact CStarRing.norm_mul_self_le a.down

instance liftCStarAlgebra : CStarAlgebra (ULift.{v} A) where

def liftStarAlgEquiv : A ≃⋆ₐ[ℂ] ULift.{v} A where
  toFun := ULift.up
  invFun := ULift.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp] lemma liftStarAlgEquiv_apply (a : A) : liftStarAlgEquiv A a = ULift.up a := rfl

end
end

universe u v w

theorem rankOne_isCompact {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (x y : H) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ x y) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ x)).comp_clm (innerSL ℂ y)

theorem compacts_representation_map_one {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hrange : ∀ T : H →L[ℂ] H, IsCompactOperator T → ∃ a : A, φ a = T) :
    φ 1 = ContinuousLinearMap.id ℂ H := by
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨a, ha⟩ := hrange _ (rankOne_isCompact x x)
    have hmul : φ 1 * InnerProductSpace.rankOne ℂ x x =
        InnerProductSpace.rankOne ℂ x x := by
      rw [← ha, ← map_mul, one_mul]
    have hv := congrArg (fun T : H →L[ℂ] H => T x) hmul
    simp only [mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
      map_smul] at hv
    exact smul_right_injective H (inner_self_ne_zero.mpr hx) hv

theorem not_isIsomorphicToCompacts {A : Type u} [CStarAlgebra A]
    (hA : ¬ FiniteDimensional ℂ A)
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    ¬ IsIsomorphicToCompacts A H := by
  rintro ⟨φ, hinj, hrange⟩
  have hone : φ 1 = ContinuousLinearMap.id ℂ H :=
    compacts_representation_map_one φ (fun T hT => (hrange T).mpr hT)
  have hcompact : IsCompactOperator (ContinuousLinearMap.id ℂ H) := by
    rw [← hone]
    exact (hrange (φ 1)).mp ⟨1, rfl⟩
  have : FiniteDimensional ℂ H :=
    FiniteDimensional.of_isCompactOperator_id (𝕜 := ℂ) hcompact
  let F : A →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun c a => map_smul φ c a }
  exact hA (FiniteDimensional.of_injective F hinj)

lemma pureHomogeneity_of_equiv {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B)
    (h : ∀ (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g),
      PureStateEquivalent f hf g hg)
    (f g : B →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    PureStateEquivalent f hf g hg := by
  have hrf := isPureState_restrict_equiv e f hf
  have hrg := isPureState_restrict_equiv e g hg
  exact pure_lifts_equivalent e.toStarAlgHom _ _ hrf hrg (h _ _ hrf hrg)
    (StateExtensionUnique.of_surjective _ e.surjective _) f g hf hg rfl rfl

theorem main_of_approxNearCentralRows (Hrows : KOS.SimpleSeparableRows) :
    ∃ (A : Type u) (_ : CStarAlgebra A),
      IsSimpleCStar A ∧ ¬ FiniteDimensional ℂ A ∧
      (∃ τ : A →L[ℂ] ℂ, IsFaithfulTracialState τ) ∧
      HasUniqueIrreducibleRepresentation.{u, v, w} A ∧
      ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
        ¬ IsIsomorphicToCompacts A H := by
  obtain ⟨σ,hi,hσ⟩ := exists_pair_schedule constructionCardinal.{0} constructionCardinal_regular
  let X := ChronologicalStage.limitStage (ChronologicalStage.fullTower Hrows σ hσ)
  have hall : ∀ (f g : X →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g),
      PureStateEquivalent f hf g hg := by
    intro f g hf hg
    exact (ChronologicalStage.fullTower_pure_reference Hrows σ hσ hi f hf).trans
      (ChronologicalStage.fullTower_pure_reference Hrows σ hσ hi g hg).symm
  let A := ULift.{u} X
  let e : X ≃⋆ₐ[ℂ] A := liftStarAlgEquiv X
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hinf : ¬ FiniteDimensional ℂ A := by
    intro h
    exact X.infinite (FiniteDimensional.of_injective e.toAlgEquiv.toLinearEquiv.toLinearMap e.injective)
  refine ⟨A,inferInstance,X.simple.of_equiv e,hinf,?_,?_,?_⟩
  · refine ⟨restrictState e.symm.toStarAlgHom X.trace,
      isState_restrict _ _ X.traceState,?_,?_⟩
    · intro a b
      change X.trace (e.symm (a*b)) = X.trace (e.symm (b*a))
      rw [map_mul e.symm a b, map_mul e.symm b a]
      exact X.tracial _ _
    · intro a ha
      change 0 < (X.trace (e.symm (star a*a))).re
      rw [map_mul e.symm (star a) a, map_star e.symm a]
      exact X.traceFaithful _ (fun h => ha (e.symm.injective (h.trans (map_zero e.symm).symm)))
  · intro H _ _ _ K _ _ _ π ρ hπ hρ
    exact all_irreducibles_equivalent_of_pure_states (pureHomogeneity_of_equiv e hall) π hπ ρ hρ
  · intro H _ _ _
    exact not_isIsomorphicToCompacts hinf H

end NaimarkZFC

end

end OAI
