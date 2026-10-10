import OAI.CategoryTheory.Thomason.GlobularComplexes
import OAI.CategoryTheory.Thomason.Gray.SimplicialHomotopyWhiskering
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionAnodyneHorn
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Simplicial.ConstructedExtensionLocalizer
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionWeakLifting
import OAI.CategoryTheory.Thomason.Transfer.FiniteEmptyAttachmentFibers

namespace OAI

section

/-! # From chain-valued vertex labels to a simplicial map

Labels need not be monotone.  It suffices that they send comparable
vertices to comparable vertices: taking the greatest label on each face
then gives a monotone map on the finite-chain poset.
-/

namespace Thomason.Construction.ChainLabelApproximation

open CategoryTheory PartialOrder
open scoped Simplicial

noncomputable section

def greatest {P : Type} [PartialOrder P] (C : NonemptyFiniteChains P) : P :=
  ((ChainOrdinal.choose C).enum (Fin.last (ChainOrdinal.choose C).dim)).val

theorem greatest_mem {P : Type} [PartialOrder P] (C : NonemptyFiniteChains P) :
    greatest C ∈ C.finset :=
  ((ChainOrdinal.choose C).enum (Fin.last (ChainOrdinal.choose C).dim)).property

theorem le_greatest {P : Type} [PartialOrder P] (C : NonemptyFiniteChains P)
    (x : P) (hx : x ∈ C.finset) : x ≤ greatest C := by
  obtain ⟨i, hi⟩ := (ChainOrdinal.choose C).enum.surjective ⟨x, hx⟩
  have h := (ChainOrdinal.choose C).enum.monotone (Fin.le_last i)
  change ((ChainOrdinal.choose C).enum i).val ≤ greatest C at h
  simpa only [hi] using h

theorem greatest_monotone {P : Type} [PartialOrder P] :
    Monotone (greatest (P := P)) := by
  intro C D hCD
  exact le_greatest D _ (hCD (greatest_mem C))

def greatestHom {P : Type} [PartialOrder P] : NonemptyFiniteChains P →o P :=
  ⟨greatest, greatest_monotone⟩

theorem greatest_map {P R : Type} [PartialOrder P] [PartialOrder R]
    (f : P →o R) (C : NonemptyFiniteChains P) :
    greatest (C.map f) = f (greatest C) := by
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := (NonemptyFiniteChains.mem_map_iff C f _).mp
      (greatest_mem (C.map f))
    rw [← he]
    exact f.monotone (le_greatest C x hx)
  · exact le_greatest (C.map f) _ ((NonemptyFiniteChains.mem_map_iff C f _).mpr
      ⟨greatest C, greatest_mem C, rfl⟩)

theorem greatest_eq_chainMaximum {P : Type} [LinearOrder P] (C : NonemptyFiniteChains P) :
    greatest C = chainMaximum C := by
  apply le_antisymm
  · exact Finset.le_max' C.finset _ (greatest_mem C)
  · exact le_greatest C _ (Finset.max'_mem C.finset C.nonempty)

def MapsChains {Q P : Type} [PartialOrder Q] [PartialOrder P] (label : Q → P) : Prop :=
  ∀ ⦃x y⦄, x ≤ y → label x ≤ label y ∨ label y ≤ label x

def labelChain {Q P : Type} [PartialOrder Q] [PartialOrder P]
    (label : Q → P) (hlabel : MapsChains label) (C : NonemptyFiniteChains Q) :
    NonemptyFiniteChains P where
  finset := by classical exact C.finset.image label
  nonempty := by classical exact C.nonempty.image label
  comparable := by
    classical
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    rcases C.comparable ⟨a, ha⟩ ⟨b, hb⟩ with hab | hba
    · exact hlabel hab
    · exact (hlabel hba).symm

theorem labelChain_monotone {Q P : Type} [PartialOrder Q] [PartialOrder P]
    (label : Q → P) (hlabel : MapsChains label) : Monotone (labelChain label hlabel) := by
  classical
  intro C D hCD
  exact Finset.image_subset_image hCD

def greatestLabel {Q P : Type} [PartialOrder Q] [PartialOrder P]
    (label : Q → P) (hlabel : MapsChains label) : NonemptyFiniteChains Q →o P :=
  greatestHom.comp ⟨labelChain label hlabel, labelChain_monotone label hlabel⟩

theorem greatestLabel_mem {Q P : Type} [PartialOrder Q] [PartialOrder P]
    (label : Q → P) (hlabel : MapsChains label) (C : NonemptyFiniteChains Q) :
    ∃ q ∈ C.finset, label q = greatestLabel label hlabel C := by
  classical
  exact Finset.mem_image.mp (greatest_mem (labelChain label hlabel C))

theorem greatestLabel_of_monotone {Q P : Type} [PartialOrder Q] [PartialOrder P]
    (label : Q →o P) (C : NonemptyFiniteChains Q) :
    greatestLabel label (fun _ _ h => Or.inl (label.monotone h)) C = label (greatest C) := by
  have he : labelChain label (fun _ _ h => Or.inl (label.monotone h)) C = C.map label := by
    apply NonemptyFiniteChains.ext
    rfl
  change greatest (labelChain label (fun _ _ h => Or.inl (label.monotone h)) C) = _
  rw [he, greatest_map]

def nerveMapOfLabels {Q P : Type} [PartialOrder Q] [PartialOrder P]
    (label : Q → P) (hlabel : MapsChains label) :
    nerve (NonemptyFiniteChains Q) ⟶ nerve P :=
  nerveMap (greatestLabel label hlabel).monotone.functor

def subdivisionMapOfLabels {Q P : Type} [PartialOrder Q] [PartialOrder P]
    (label : Q → P) (hlabel : MapsChains label) : SSet.sd.obj (nerve Q) ⟶ nerve P :=
  NerveSubdivisionMap.map Q ≫ nerveMapOfLabels label hlabel

/-- All output vertices of a chain simplex are labels of vertices in its
greatest source face.  This is the finite carrier needed for approximation. -/
theorem nerveMapOfLabels_carrier {Q P : Type} [PartialOrder Q] [PartialOrder P]
    (label : Q → P) (hlabel : MapsChains label) (d : SimplexCategoryᵒᵖ)
    (s : (nerve (NonemptyFiniteChains Q)).obj d) (i : Fin (d.unop.len+1)) :
    ∃ q ∈ (s.obj (Fin.last d.unop.len)).finset,
      label q = ((nerveMapOfLabels label hlabel).app d s).obj i := by
  obtain ⟨q, hq, he⟩ := greatestLabel_mem label hlabel (s.obj i)
  refine ⟨q, ?_, he⟩
  exact leOfHom (s.map (homOfLE (Fin.le_last i))) hq

theorem vertices_factor {P : Type} [PartialOrder P] {n : SimplexCategory}
    (f : SSet.stdSimplex.obj n ⟶ nerve P) :
    (simplexNerveIso.app n).inv ≫ f =
      nerveMap (NerveSubdivisionMap.vertices f).monotone.functor := by
  let e : SSet.stdSimplex.obj n ≅ nerve (ULift.{0} (Fin (n.len+1))) := simplexNerveIso.app n
  change e.inv ≫ f = _
  have hf : f = e.hom ≫
      nerveMap (NerveSubdivisionMap.vertices f).monotone.functor := by
    apply SSet.yonedaEquiv.injective
    apply nerve.ext_of_isThin
    funext i
    rfl
  calc
    e.inv ≫ f = e.inv ≫ (e.hom ≫
        nerveMap (NerveSubdivisionMap.vertices f).monotone.functor) :=
      congrArg (e.inv ≫ ·) hf
    _ = _ := e.inv_hom_id_assoc _

theorem piece_greatest {P : Type} [PartialOrder P] {n : SimplexCategory}
    (f : SSet.stdSimplex.obj n ⟶ nerve P) :
    NerveSubdivisionMap.piece f ≫ nerveMap (greatestHom (P := P)).monotone.functor =
      lastVertex.app (SSet.stdSimplex.obj n) ≫ f := by
  let e : SSet.stdSimplex.obj n ≅ nerve (ULift.{0} (Fin (n.len+1))) := simplexNerveIso.app n
  let d : SSet.sd.obj (SSet.stdSimplex.obj n) ≅
      nerve (NonemptyFiniteChains (ULift.{0} (Fin (n.len+1)))) := SSet.stdSimplex.sdIso.app n
  let v := NerveSubdivisionMap.vertices f
  let m : NonemptyFiniteChains (ULift.{0} (Fin (n.len+1))) →o ULift.{0} (Fin (n.len+1)) :=
    chainMaximumHom
  have hp : nerveMap (NonemptyFiniteChains.orderHomMap v).monotone.functor ≫
      nerveMap (greatestHom (P := P)).monotone.functor =
        nerveMap m.monotone.functor ≫ nerveMap v.monotone.functor := by
    rw [← orderNerveMap_comp, ← orderNerveMap_comp]
    apply congrArg (fun g : NonemptyFiniteChains (ULift.{0} (Fin (n.len+1))) →o P =>
      nerveMap g.monotone.functor)
    apply DFunLike.ext
    intro C
    exact (greatest_map v C).trans (congrArg v (greatest_eq_chainMaximum C))
  have hv : e.inv ≫ f = nerveMap v.monotone.functor := vertices_factor f
  have hd : d.hom ≫ nerveMap m.monotone.functor ≫ e.inv =
      lastVertex.app (SSet.stdSimplex.obj n) := lastVertex_standard_formula n
  calc
    _ = d.hom ≫ (nerveMap (NonemptyFiniteChains.orderHomMap v).monotone.functor ≫
        nerveMap (greatestHom (P := P)).monotone.functor) := Category.assoc _ _ _
    _ = d.hom ≫ (nerveMap m.monotone.functor ≫ nerveMap v.monotone.functor) :=
      congrArg (d.hom ≫ ·) hp
    _ = d.hom ≫ (nerveMap m.monotone.functor ≫ (e.inv ≫ f)) :=
      congrArg (fun q => d.hom ≫ (nerveMap m.monotone.functor ≫ q)) hv.symm
    _ = (d.hom ≫ nerveMap m.monotone.functor ≫ e.inv) ≫ f := by
      simp only [Category.assoc]
    _ = _ := congrArg (· ≫ f) hd

/-- The greatest-face map agrees with the last-vertex map on subdivision. -/
theorem subdivision_greatest_eq_lastVertex (P : Type) [PartialOrder P] :
    NerveSubdivisionMap.map P ≫ nerveMap (greatestHom (P := P)).monotone.functor =
      lastVertex.app (nerve P) := by
  apply (SimplicialHomotopyDescent.isColimit SSet.sd (nerve P)).hom_ext
  intro j
  change SSet.sd.map j.hom ≫ (NerveSubdivisionMap.map P ≫
      nerveMap (greatestHom (P := P)).monotone.functor) =
    SSet.sd.map j.hom ≫ lastVertex.app (nerve P)
  rw [← Category.assoc, NerveSubdivisionMap.map_fac, piece_greatest]
  exact (lastVertex.naturality j.hom).symm

theorem greatest_nerveMap_weak (P : Type) [PartialOrder P] [Finite P] :
    realizationWeakEquivalences (nerveMap (greatestHom (P := P)).monotone.functor) := by
  apply realizationWeakEquivalences.of_precomp (NerveSubdivisionMap.iso P).hom _
    (realizationWeakEquivalences.of_isIso _)
  change realizationWeakEquivalences
    (NerveSubdivisionMap.map P ≫ nerveMap (greatestHom (P := P)).monotone.functor)
  rw [subdivision_greatest_eq_lastVertex]
  exact lastVertex_weak _

end

end Thomason.Construction.ChainLabelApproximation

end

section

/-! # Comparing label approximations with a prescribed monotone map

A bound on every label gives a bound on the greatest label of each chain.
The resulting inequality gives a simplicial homotopy on subdivision
through its comparison with the chain nerve.
-/

namespace Thomason.Construction.ChainLabelApproximation

open CategoryTheory PartialOrder
open scoped Simplicial

noncomputable section

variable {Q P : Type} [PartialOrder Q] [PartialOrder P]
    (label : Q → P) (hlabel : MapsChains label)

/-- Every bound on the labels of a face bounds its greatest label. -/
theorem greatestLabel_le (C : NonemptyFiniteChains Q) (b : P)
    (h : ∀ q ∈ C.finset, label q ≤ b) : greatestLabel label hlabel C ≤ b := by
  obtain ⟨q, hq, he⟩ := greatestLabel_mem label hlabel C
  rw [← he]
  exact h q hq

/-- A prescribed monotone carrier upper bound gives the comparison
homotopy without requiring the labels themselves to be monotone. -/
def nerveMapOfLabelsCarrierHomotopy (g : NonemptyFiniteChains Q →o P)
    (h : ∀ C, ∀ q ∈ C.finset, label q ≤ g C) :
    SSet.Homotopy (nerveMapOfLabels label hlabel) (nerveMap g.monotone.functor) :=
  orderNerveHomotopy (greatestLabel label hlabel) g
    (fun C => greatestLabel_le label hlabel C (g C) (h C))

/-- A pointwise comparison propagates to the chain-valued approximation. -/
theorem greatestLabel_le_comp_greatest (g : Q →o P) (h : ∀ q, label q ≤ g q)
    (C : NonemptyFiniteChains Q) : greatestLabel label hlabel C ≤ g (greatest C) := by
  apply greatestLabel_le
  intro q hq
  exact (h q).trans (g.monotone (le_greatest C q hq))

/-- Labels with a common prescribed upper map give a homotopy to that map
composed with the greatest-face comparison. -/
def nerveMapOfLabelsHomotopy (g : Q →o P) (h : ∀ q, label q ≤ g q) :
    SSet.Homotopy (nerveMapOfLabels label hlabel)
      (nerveMap (greatestHom (P := Q)).monotone.functor ≫ nerveMap g.monotone.functor) := by
  simpa only [nerveMapOfLabels, orderNerveMap_comp] using
    (orderNerveHomotopy (greatestLabel label hlabel) (g.comp greatestHom)
      (greatestLabel_le_comp_greatest label hlabel g h))

/-- The comparison on subdivision has the last-vertex map as its endpoint. -/
def subdivisionMapOfLabelsHomotopy (g : Q →o P) (h : ∀ q, label q ≤ g q) :
    SSet.Homotopy (subdivisionMapOfLabels label hlabel)
      (lastVertex.app (nerve Q) ≫ nerveMap g.monotone.functor) := by
  have H := whiskerSimplicialHomotopy (NerveSubdivisionMap.map Q)
    (nerveMapOfLabelsHomotopy label hlabel g h) (𝟙 _)
  simpa only [Category.comp_id, Category.assoc, subdivisionMapOfLabels,
    ← subdivision_greatest_eq_lastVertex] using H

end

end Thomason.Construction.ChainLabelApproximation

end

section

/-! # The sieve and retracting cosieve of face chains

For a subset of faces, old chains are those entirely inside the subset.
The containing cosieve consists of chains meeting it. Intersection gives
the required right adjoint; the empty boundary case is included.
-/

namespace Thomason.Construction.ChainSieve

open PartialOrder

universe u
variable {P : Type u} [PartialOrder P]

def old (S : Set P) : Set (NonemptyFiniteChains P) :=
  {c | ∀ x ∈ c.finset, x ∈ S}

def upper (S : Set P) : Set (NonemptyFiniteChains P) :=
  {c | ∃ x ∈ c.finset, x ∈ S}

theorem old_lower (S : Set P) : IsLowerSet (old S) :=
  fun _ _ h hc => Thomason.Subdivision.oldChains_sieve S h hc

theorem upper_upper (S : Set P) : IsUpperSet (upper S) :=
  fun _ _ h hc => Thomason.Subdivision.meetingChains_cosieve S h hc

theorem old_subset_upper (S : Set P) : old S ⊆ upper S := by
  intro c hc
  obtain ⟨x, hx⟩ := c.nonempty
  exact ⟨x, hx, hc x hx⟩

noncomputable def intersection (S : Set P) (c : upper S) : NonemptyFiniteChains P :=
  (Thomason.Subdivision.chainIntersection S c).val

theorem intersection_old (S : Set P) (c : upper S) : intersection S c ∈ old S :=
  (Thomason.Subdivision.chainIntersection S c).property

theorem intersection_upper (S : Set P) (c : upper S) : intersection S c ∈ upper S :=
  old_subset_upper S (intersection_old S c)

/-- The face-chain inclusion retracts on precisely the chains meeting the
old faces, with the order adjunction. -/
noncomputable def retraction (S : Set P) :
    SieveRetraction {c : upper S | c.val ∈ old S} where
  lower := by
    intro c d hcd hd
    exact old_lower S hcd hd
  rightAdjoint :=
    { toFun := fun c => ⟨⟨intersection S c, intersection_upper S c⟩, intersection_old S c⟩
      monotone' := by
        classical
        intro c d hcd x hx
        exact Finset.mem_filter.mpr ⟨hcd (Finset.mem_filter.mp hx).1,
          (Finset.mem_filter.mp hx).2⟩ }
  adjunction := by
    classical
    intro a c
    constructor
    · intro hac x hx
      exact Finset.mem_filter.mpr ⟨hac hx, a.property x hx⟩
    · intro hac x hx
      exact (Finset.mem_filter.mp (hac hx)).1

end Thomason.Construction.ChainSieve

end

section

/-! # Chains in a subposet and chains supported in it

This identifies the source of the twice-subdivided attaching map with the
sieve of supported chains in the attachment comparison.
-/

namespace Thomason.Construction.ChainSieve

open PartialOrder

variable {P : Type} [PartialOrder P]

noncomputable def chainInclusion (S : Set P) : NonemptyFiniteChains S →o old S :=
  (Thomason.Subdivision.chainsSubtypeOrderIso S).toOrderEmbedding.toOrderHom

noncomputable def restrict (S : Set P) (c : old S) : NonemptyFiniteChains S :=
  (Thomason.Subdivision.chainsSubtypeOrderIso S).symm c

noncomputable def subsetIso (S : Set P) : NonemptyFiniteChains S ≃o old S :=
  Thomason.Subdivision.chainsSubtypeOrderIso S

/-- The identification commutes with the original chain inclusion. -/
theorem subsetIso_inclusion (S : Set P) :
    (subposetInclusion (old S)).comp (subsetIso S).toOrderEmbedding.toOrderHom =
      NonemptyFiniteChains.orderHomMap (subposetInclusion S) := rfl

end Thomason.Construction.ChainSieve

end

section

/-! # Barycentric contraction of the mesh of a finite poset

Comparable face barycenters retain a common original vertex with a
uniform positive mass. The dimension bound gives one contraction factor
which remains valid on every subsequent chain-poset stage.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open PartialOrder Convexity

noncomputable section

def chainDistribution {P : Type} [PartialOrder P] (C : NonemptyFiniteChains P) :
    StdSimplex ℝ P := StdSimplex.subBarycenter C.finset C.nonempty

theorem chainDistribution_weight {P : Type} [PartialOrder P] [DecidableEq P]
    (C : NonemptyFiniteChains P) (i : P) :
    (chainDistribution C).weights i = if i ∈ C.finset then (C.finset.card : ℝ)⁻¹ else 0 := by
  classical
  simp [chainDistribution, StdSimplex.weights_subBarycenter, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply, eq_comm]

theorem chainDistribution_lower {P : Type} [PartialOrder P] {N : ℕ}
    (hP : ChainCardBound P N) (C : NonemptyFiniteChains P) (v : P) (hv : v ∈ C.finset) :
    1 / ((N : ℝ)+1) ≤ (chainDistribution C).weights v := by
  classical
  rw [chainDistribution_weight, ite_eq_left hv, ← one_div]
  apply one_div_le_one_div_of_le
  · exact_mod_cast Finset.card_pos.mpr C.nonempty
  · exact_mod_cast hP C

def chainAverage {P : Type} [PartialOrder P] [Fintype P] {d : ℕ}
    (x : P → Fin d → ℝ) (C : NonemptyFiniteChains P) : Fin d → ℝ :=
  fun j => finiteAffineValue (fun i => x i j) (chainDistribution C)

def ChainMesh {P : Type} [PartialOrder P] {d : ℕ} (x : P → Fin d → ℝ) (D : ℝ) : Prop :=
  ∀ i j, (i ≤ j ∨ j ≤ i) → dist (x i) (x j) ≤ D

theorem chainAverage_dist_of_le {P : Type} [PartialOrder P] [Fintype P]
    {N d : ℕ} (hP : ChainCardBound P N) (x : P → Fin d → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hx : ChainMesh x D)
    (A B : NonemptyFiniteChains P) (hAB : A ≤ B) :
    dist (chainAverage x A) (chainAverage x B) ≤ (1-1/((N : ℝ)+1))*D := by
  classical
  have hρ : 0 ≤ 1-1/((N : ℝ)+1) := by
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity : (0 : ℝ) < (N : ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) N]
  obtain ⟨v, hv⟩ := A.nonempty
  have hvB : v ∈ B.finset := hAB hv
  apply (dist_pi_le_iff (mul_nonneg hρ hD)).mpr
  intro j
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image B.finset (fun i => x i j) B.nonempty
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image B.finset (fun i => x i j) B.nonempty
  have hbounds (i : P) (hi : i ∈ B.finset) : x a j ≤ x i j ∧ x i j ≤ x b j :=
    ⟨hmin i hi, hmax i hi⟩
  have hwidth : x b j-x a j ≤ D := by
    calc
      _ ≤ |x b j-x a j| := le_abs_self _
      _ = dist (x b j) (x a j) := (Real.dist_eq _ _).symm
      _ ≤ dist (x b) (x a) := dist_le_pi_dist (x b) (x a) j
      _ ≤ D := hx b a (B.comparable ⟨b, hb⟩ ⟨a, ha⟩)
  have hsupport (C : NonemptyFiniteChains P) (hCB : C ≤ B)
      (i : P) (hi : (chainDistribution C).weights i ≠ 0) :
      x a j ≤ x i j ∧ x i j ≤ x b j := by
    apply hbounds i
    apply hCB
    by_contra hn
    exact hi (by rw [chainDistribution_weight, ite_eq_right hn])
  change |finiteAffineValue (fun i => x i j) (chainDistribution A) -
    finiteAffineValue (fun i => x i j) (chainDistribution B)| ≤ _
  exact (supported_common_mass_dist (fun i => x i j) (chainDistribution A)
    (chainDistribution B) v (1/((N : ℝ)+1)) (x a j) (x b j)
    (chainDistribution_lower hP A v hv) (chainDistribution_lower hP B v hvB)
    (hbounds v hvB) (hsupport A hAB) (hsupport B le_rfl)).trans
      (mul_le_mul_of_nonneg_left hwidth hρ)

theorem chainMesh_average {P : Type} [PartialOrder P] [Fintype P]
    {N d : ℕ} (hP : ChainCardBound P N) (x : P → Fin d → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hx : ChainMesh x D) :
    ChainMesh (chainAverage x) ((1-1/((N : ℝ)+1))*D) := by
  intro A B hAB
  rcases hAB with hAB | hBA
  · exact chainAverage_dist_of_le hP x D hD hx A B hAB
  · rw [dist_comm]
    exact chainAverage_dist_of_le hP x D hD hx B A hBA

end

end Thomason.Construction.SubdivisionBarycentric

end

end OAI
