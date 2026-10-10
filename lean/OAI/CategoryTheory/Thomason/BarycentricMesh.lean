import Mathlib
import OAI.CategoryTheory.Thomason.Polyhedra

namespace OAI

/-! Barycentric Mesh. -/

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.PolyPoint
variable {P : Type u} [PartialOrder P]
local instance barycentricMeshDecidableEq : DecidableEq P := Classical.decEq P

lemma barycentricLinear_support_eq (g : NonemptyFiniteChains P →₀ ℝ)
    (hg : ∀ s, 0 ≤ g s) :
    (barycentricLinear g).support = g.support.biUnion NonemptyFiniteChains.finset := by
  classical
  apply Finset.Subset.antisymm (barycentricLinear_support g)
  intro p hp
  obtain ⟨s,hs,hps⟩ := Finset.mem_biUnion.mp hp
  rw [Finsupp.mem_support_iff]
  apply ne_of_gt
  rw [barycentricLinear_apply, Finsupp.sum]
  apply (Finset.sum_pos_iff_of_nonneg (fun t ht =>
    mul_nonneg (hg t) ((barycenter t).nonneg p))).mpr
  refine ⟨s,hs,mul_pos ?_ ?_⟩
  · exact lt_of_le_of_ne (hg s) (Ne.symm (Finsupp.mem_support_iff.mp hs))
  · rw [barycenter_apply, ite_eq_left hps]
    exact inv_pos.mpr (by exact_mod_cast Finset.card_pos.mpr s.nonempty)

lemma barycentricLinear_eq_zero_iff (g : NonemptyFiniteChains P →₀ ℝ)
    (hg : ∀ s, 0 ≤ g s) : barycentricLinear g = 0 ↔ g = 0 := by
  classical
  constructor
  · intro he
    by_contra hg0
    obtain ⟨s,hs⟩ := Finsupp.support_nonempty_iff.mpr hg0
    obtain ⟨p,hp⟩ := s.nonempty
    have hmem : p ∈ (barycentricLinear g).support := by
      rw [barycentricLinear_support_eq g hg]
      exact Finset.mem_biUnion.mpr ⟨s,hs,hp⟩
    simp [he] at hmem
  · rintro rfl
    exact map_zero _

lemma flag_has_max (S : Finset (NonemptyFiniteChains P))
    (hc : IsChain (· ≤ ·) (S : Set (NonemptyFiniteChains P))) (hne : S.Nonempty) :
    ∃ s ∈ S, ∀ t ∈ S, t ≤ s := by
  obtain ⟨s,hs,hm⟩ := Finset.exists_max_image S (fun t => t.finset.card) hne
  refine ⟨s,hs,fun t ht => ?_⟩
  rcases hc.total ht hs with h | h
  · exact h
  · exact le_of_eq (NonemptyFiniteChains.ext (Finset.eq_of_subset_of_card_le h (hm t ht))).symm

lemma flag_union_eq_max (S : Finset (NonemptyFiniteChains P))
    (s : NonemptyFiniteChains P) (hs : s ∈ S) (hm : ∀ t ∈ S, t ≤ s) :
    S.biUnion NonemptyFiniteChains.finset = s.finset := by
  classical
  ext p
  constructor
  · rintro hp
    obtain ⟨t,ht,hpt⟩ := Finset.mem_biUnion.mp hp
    exact hm t ht hpt
  · intro hp
    exact Finset.mem_biUnion.mpr ⟨s,hs,hp⟩

lemma flag_max_exclusive_vertex (S : Finset (NonemptyFiniteChains P))
    (hc : IsChain (· ≤ ·) (S : Set (NonemptyFiniteChains P)))
    (s : NonemptyFiniteChains P) (_ : s ∈ S) (hm : ∀ t ∈ S, t ≤ s) :
    ∃ p ∈ s.finset, ∀ t ∈ S, p ∈ t.finset → t = s := by
  classical
  by_cases hne : (S.erase s).Nonempty
  · obtain ⟨t,ht,htm⟩ := flag_has_max (S.erase s) (hc.mono (by simp)) hne
    have hts : t ≤ s := hm t (Finset.mem_of_mem_erase ht)
    have hst : ¬s.finset ⊆ t.finset := by
      intro h
      exact (Finset.mem_erase.mp ht).1 (le_antisymm hts h)
    obtain ⟨p,hps,hpt⟩ := Finset.not_subset.mp hst
    refine ⟨p,hps,fun a ha hpa => ?_⟩
    by_contra has
    exact hpt (htm a (Finset.mem_erase.mpr ⟨has,ha⟩) hpa)
  · obtain ⟨p,hp⟩ := s.nonempty
    refine ⟨p,hp,fun t ht hpt => ?_⟩
    by_contra hts
    exact hne ⟨t,Finset.mem_erase.mpr ⟨hts,ht⟩⟩

lemma barycentric_max_minimum (g : NonemptyFiniteChains P →₀ ℝ)
    (hn : ∀ s, 0 ≤ g s) (hc : IsChain (· ≤ ·) (g.support : Set (NonemptyFiniteChains P)))
    (s : NonemptyFiniteChains P) (hs : s ∈ g.support) (hm : ∀ t ∈ g.support, t ≤ s) :
    (∀ p ∈ s.finset, g s * (s.finset.card : ℝ)⁻¹ ≤ barycentricLinear g p) ∧
    ∃ p ∈ s.finset, barycentricLinear g p = g s * (s.finset.card : ℝ)⁻¹ := by
  classical
  constructor
  · intro p hp
    rw [barycentricLinear_apply, Finsupp.sum]
    have hl := Finset.single_le_sum (f := fun t => g t * (barycenter t).weights p)
      (fun t ht => mul_nonneg (hn t) ((barycenter t).nonneg p)) hs
    simpa only [barycenter_apply, ite_eq_left hp] using hl
  · obtain ⟨p,hps,hex⟩ := flag_max_exclusive_vertex g.support hc s hs hm
    refine ⟨p,hps,?_⟩
    rw [barycentricLinear_apply, Finsupp.sum]
    calc
      ∑ t ∈ g.support, g t * (barycenter t).weights p =
          g s * (barycenter s).weights p := by
        apply Finset.sum_eq_single s
        · intro t ht hts
          have hpnot : p ∉ t.finset := fun h => hts (hex t ht h)
          simp [barycenter_apply, hpnot]
        · exact fun h => (h hs).elim
      _ = _ := by rw [barycenter_apply, ite_eq_left hps]

lemma barycentricLinear_injective_nonneg_flag
    (g h : NonemptyFiniteChains P →₀ ℝ)
    (hgn : ∀ s, 0 ≤ g s) (hhn : ∀ s, 0 ≤ h s)
    (hgc : IsChain (· ≤ ·) (g.support : Set (NonemptyFiniteChains P)))
    (hhc : IsChain (· ≤ ·) (h.support : Set (NonemptyFiniteChains P)))
    (he : barycentricLinear g = barycentricLinear h) : g = h := by
  classical
  suffices ∀ (n : ℕ) (g h : NonemptyFiniteChains P →₀ ℝ), g.support.card = n →
      (∀ s, 0 ≤ g s) → (∀ s, 0 ≤ h s) →
      IsChain (· ≤ ·) (g.support : Set (NonemptyFiniteChains P)) →
      IsChain (· ≤ ·) (h.support : Set (NonemptyFiniteChains P)) →
      barycentricLinear g = barycentricLinear h → g = h by
    exact this _ g h rfl hgn hhn hgc hhc he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro g h hcard hgn hhn hgc hhc he
    by_cases hg0 : g = 0
    · subst g
      have hh0 : h = 0 := (barycentricLinear_eq_zero_iff h hhn).mp (by simpa using he.symm)
      exact hh0.symm
    have hh0 : h ≠ 0 := by
      rintro rfl
      exact hg0 ((barycentricLinear_eq_zero_iff g hgn).mp (by simpa using he))
    obtain ⟨s,hs,hsm⟩ := flag_has_max g.support hgc (Finsupp.support_nonempty_iff.mpr hg0)
    obtain ⟨t,ht,htm⟩ := flag_has_max h.support hhc (Finsupp.support_nonempty_iff.mpr hh0)
    have hst : s = t := by
      apply NonemptyFiniteChains.ext
      calc
        s.finset = (barycentricLinear g).support :=
          ((barycentricLinear_support_eq g hgn).trans (flag_union_eq_max _ s hs hsm)).symm
        _ = (barycentricLinear h).support := congrArg Finsupp.support he
        _ = t.finset := (barycentricLinear_support_eq h hhn).trans (flag_union_eq_max _ t ht htm)
    subst t
    obtain ⟨hgl,p,hp,hpe⟩ := barycentric_max_minimum g hgn hgc s hs hsm
    obtain ⟨hhl,q,hq,hqe⟩ := barycentric_max_minimum h hhn hhc s ht htm
    have hcoef : g s = h s := by
      have hp' := hhl p hp
      have hq' := hgl q hq
      rw [← he, hpe] at hp'
      rw [he, hqe] at hq'
      have hc : (s.finset.card : ℝ)⁻¹ > 0 :=
        inv_pos.mpr (by exact_mod_cast Finset.card_pos.mpr s.nonempty)
      exact (mul_right_cancel₀ hc.ne') (le_antisymm hq' hp')
    have herase : barycentricLinear (g.erase s) = barycentricLinear (h.erase s) := by
      have hg := congrArg barycentricLinear (Finsupp.erase_add_single s g)
      have hh := congrArg barycentricLinear (Finsupp.erase_add_single s h)
      rw [map_add] at hg hh
      rw [hcoef, he] at hg
      exact add_right_cancel (hg.trans hh.symm)
    have heraseeq : g.erase s = h.erase s := by
      apply ih (g.erase s).support.card
      · rw [Finsupp.support_erase, ← hcard]
        exact Finset.card_lt_card (Finset.erase_ssubset hs)
      · rfl
      · intro t
        rw [Finsupp.erase_apply]
        split_ifs
        · exact le_rfl
        · exact hgn t
      · intro t
        rw [Finsupp.erase_apply]
        split_ifs
        · exact le_rfl
        · exact hhn t
      · exact hgc.mono (by simp)
      · exact hhc.mono (by simp)
      · exact herase
    calc
      g = g.erase s + Finsupp.single s (g s) := (Finsupp.erase_add_single s g).symm
      _ = h.erase s + Finsupp.single s (h s) := by rw [heraseeq,hcoef]
      _ = h := Finsupp.erase_add_single s h

lemma subdivide_injective : Function.Injective (@subdivide P _) := by
  intro x y h
  apply PolyPoint.ext
  apply barycentricLinear_injective_nonneg_flag x.weights y.weights
    x.nonneg y.nonneg x.chain y.chain
  exact congrArg PolyPoint.weights h

end Thomason.GeometricRecognition.PolyPoint

end

noncomputable section
universe u v w z


namespace Thomason.GeometricRecognition
namespace PolyPoint
variable {P : Type u} [PartialOrder P]

instance finiteChainIndex [Finite P] : Finite (ChainIndex P) :=
  Finite.of_injective ChainIndex.carrier (by
    intro s t h
    cases s
    cases t
    cases h
    rfl)

lemma isCompact_chainFace (s : ChainIndex P) :
    IsCompact (Set.range (fun x : Face s.carrier => x.val)) := by
  classical
  have he : Set.range (fun x : Face s.carrier => x.val) = Set.range (eval s.vertices) := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨s.coordinates a, s.eval_coordinates a⟩
    · rintro ⟨a,rfl⟩
      refine ⟨⟨eval s.vertices a, ?_⟩,rfl⟩
      intro p hp
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (evalWeights_support s.vertices a hp)
      exact s.vertices_mem i
  rw [he]
  exact isCompact_range (continuous_eval s.vertices)

instance compactSpace [Finite P] : CompactSpace (PolyPoint P) := by
  classical
  have hc : IsCompact (⋃ s : ChainIndex P, Set.range (fun x : Face s.carrier => x.val)) :=
    isCompact_iUnion isCompact_chainFace
  have he : (⋃ s : ChainIndex P, Set.range (fun x : Face s.carrier => x.val)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨supportIndex x, ⟨⟨x,Finset.Subset.refl _⟩,rfl⟩⟩
  exact ⟨he ▸ hc⟩

lemma embedding_weights [Finite P] :
    Topology.IsEmbedding (fun x : PolyPoint P => (fun p => x.weights p)) :=
  ((continuous_pi continuous_weights).isClosedEmbedding
    (by intro x y h; exact PolyPoint.ext (Finsupp.ext (congrFun h)))).isEmbedding

lemma continuous_iff_weights [Finite P] {A : Type*} [TopologicalSpace A]
    (f : A → PolyPoint P) : Continuous f ↔ ∀ p, Continuous (fun a => (f a).weights p) := by
  rw [embedding_weights.isInducing.continuous_iff]
  exact continuous_pi_iff

instance finiteBoundedChainIndex (s : Finset P) :
    Finite {t : ChainIndex P // t.carrier ⊆ s} := by
  classical
  apply Finite.of_injective
    (fun t : {t : ChainIndex P // t.carrier ⊆ s} =>
      (⟨t.val.carrier,Finset.mem_powerset.mpr t.property⟩ : ↥s.powerset))
  intro a b h
  apply Subtype.ext
  have hc : a.val.carrier = b.val.carrier := congrArg Subtype.val h
  obtain ⟨⟨ca,ha,na⟩,pa⟩ := a
  obtain ⟨⟨cb,hb,nb⟩,pb⟩ := b
  cases hc
  rfl

lemma isCompact_carrier (s : Finset P) :
    IsCompact {x : PolyPoint P | x.weights.support ⊆ s} := by
  classical
  have hc : IsCompact (⋃ t : {t : ChainIndex P // t.carrier ⊆ s},
      Set.range (fun x : Face t.val.carrier => x.val)) :=
    isCompact_iUnion (fun t => isCompact_chainFace t.val)
  have he : (⋃ t : {t : ChainIndex P // t.carrier ⊆ s},
      Set.range (fun x : Face t.val.carrier => x.val)) =
        {x : PolyPoint P | x.weights.support ⊆ s} := by
    ext x
    constructor
    · intro hx
      obtain ⟨t,⟨a,rfl⟩⟩ := Set.mem_iUnion.mp hx
      exact a.property.trans t.property
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨supportIndex x,hx⟩,⟨⟨x,Finset.Subset.refl _⟩,rfl⟩⟩
  exact he ▸ hc

lemma isClosed_carrier (s : Finset P) :
    IsClosed {x : PolyPoint P | x.weights.support ⊆ s} := by
  classical
  have he : {x : PolyPoint P | x.weights.support ⊆ s} =
      ⋂ p : {p : P // p ∉ s}, {x : PolyPoint P | x.weights p.val = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hx p
      exact Finsupp.notMem_support_iff.mp (fun h => p.property (hx h))
    · intro hx p hp
      by_contra hps
      exact (Finsupp.mem_support_iff.mp hp) (hx ⟨p,hps⟩)
  rw [he]
  exact isClosed_iInter (fun p => isClosed_eq (continuous_weights p.val) continuous_const)

lemma continuous_face_val (s : Finset P) : Continuous (fun x : Face s => x.val) := by
  let : CompactSpace {x : PolyPoint P | x.weights.support ⊆ s} :=
    isCompact_iff_compactSpace.mp (isCompact_carrier s)
  have hc : Continuous (fun x : {x : PolyPoint P | x.weights.support ⊆ s} =>
      (fun p => x.val.weights p)) :=
    continuous_pi (fun p => (continuous_weights p).comp continuous_subtype_val)
  have he : Topology.IsEmbedding
      (fun x : {x : PolyPoint P | x.weights.support ⊆ s} => (fun p => x.val.weights p)) :=
    (hc.isClosedEmbedding (by
      intro x y h
      exact Subtype.ext (PolyPoint.ext (Finsupp.ext (congrFun h))))).isEmbedding
  have hf : Continuous (fun x : Face s =>
      (⟨x.val,x.property⟩ : {x : PolyPoint P | x.weights.support ⊆ s})) :=
    he.continuous_iff.mpr continuous_induced_dom
  exact continuous_subtype_val.comp hf

lemma continuous_of_finite_carrier {A : Type*} [TopologicalSpace A]
    (f : A → PolyPoint P) (s : Finset P) (h : ∀ a, (f a).weights.support ⊆ s)
    (hf : ∀ p, Continuous (fun a => (f a).weights p)) : Continuous f := by
  let g : A → Face s := fun a => ⟨f a,h a⟩
  have hg : Continuous g := continuous_induced_rng.mpr (continuous_pi hf)
  exact (continuous_face_val s).comp hg

end PolyPoint
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.PolyPoint
variable {P : Type u} [PartialOrder P]
local instance boundedFacesDecidableEq : DecidableEq P := Classical.decEq P

instance finiteBoundedFaces (s : Finset P) :
    Finite {t : NonemptyFiniteChains P // t.finset ⊆ s} := by
  classical
  apply Finite.of_injective
    (fun t : {t : NonemptyFiniteChains P // t.finset ⊆ s} =>
      (⟨t.val.finset,Finset.mem_powerset.mpr t.property⟩ : ↥s.powerset))
  intro a b h
  exact Subtype.ext (NonemptyFiniteChains.ext (congrArg Subtype.val h))

def allFaces (s : Finset P) : Finset (NonemptyFiniteChains P) :=
  letI : Finite ↑{t : NonemptyFiniteChains P | t.finset ⊆ s} := finiteBoundedFaces s
  (Set.toFinite {t : NonemptyFiniteChains P | t.finset ⊆ s}).toFinset

@[simp] lemma mem_allFaces (s : Finset P) (t : NonemptyFiniteChains P) :
    t ∈ allFaces s ↔ t.finset ⊆ s := by simp [allFaces]

lemma subdivide_carrier_iff (x : PolyPoint (NonemptyFiniteChains P)) (s : Finset P) :
    (subdivide x).weights.support ⊆ s ↔ x.weights.support ⊆ allFaces s := by
  classical
  change (barycentricLinear x.weights).support ⊆ s ↔ _
  rw [barycentricLinear_support_eq x.weights x.nonneg]
  constructor
  · intro h t ht
    rw [mem_allFaces]
    exact fun p hp => h (Finset.mem_biUnion.mpr ⟨t,ht,hp⟩)
  · intro h p hp
    obtain ⟨t,ht,hpt⟩ := Finset.mem_biUnion.mp hp
    exact (mem_allFaces s t).mp (h ht) hpt

lemma isClosedMap_subdivide : IsClosedMap (@subdivide P _) := by
  classical
  intro A hA
  rw [isClosed_iff_faces]
  intro s
  let K : Set (PolyPoint (NonemptyFiniteChains P)) :=
    {x | x.weights.support ⊆ allFaces s.carrier}
  have hK : IsCompact K := isCompact_carrier _
  have hAK : IsCompact (A ∩ K) := hK.inter_left hA
  have he : (fun y : Face s.carrier => y.val) ⁻¹' (subdivide '' A) =
      (fun y : Face s.carrier => y.val) ⁻¹' (subdivide '' (A ∩ K)) := by
    ext y
    constructor
    · rintro ⟨x,hx,hxy⟩
      refine ⟨x,⟨hx,?_⟩,hxy⟩
      exact (subdivide_carrier_iff x s.carrier).mp
        (by rw [hxy]; exact y.property)
    · rintro ⟨x,⟨hx,hKx⟩,hxy⟩
      exact ⟨x,hx,hxy⟩
  rw [he]
  exact (hAK.image continuous_subdivide).isClosed.preimage (continuous_chainFace_val s)

def subdivisionHomeomorph : PolyPoint (NonemptyFiniteChains P) ≃ₜ PolyPoint P :=
  (Equiv.ofBijective subdivide ⟨subdivide_injective,subdivide_surjective⟩).toHomeomorphOfContinuousClosed
    continuous_subdivide isClosedMap_subdivide
end Thomason.GeometricRecognition.PolyPoint

end

noncomputable section
universe u v w z


namespace Thomason.GeometricRecognition.Mesh
variable {P : Type u} {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
local instance : DecidableEq P := Classical.decEq P

def average (s : Finset P) (v : P → V) : V := (s.card : ℝ)⁻¹ • ∑ p ∈ s, v p

lemma card_smul_average (s : Finset P) (hs : s.Nonempty) (v : P → V) :
    (s.card : ℝ) • average s v = ∑ p ∈ s, v p := by
  rw [average, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast Finset.card_ne_zero.mpr hs

lemma average_sub (s : Finset P) (hs : s.Nonempty) (v : P → V) (w : V) :
    average s v - w = average s (fun p => v p - w) := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  rw [average, average, Finset.sum_sub_distrib, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul]

lemma norm_average_sub_le (s : Finset P) (hs : s.Nonempty) (v : P → V) (w : V)
    (d : ℝ) (hd : ∀ p ∈ s, ‖v p - w‖ ≤ d) : ‖average s v - w‖ ≤ d := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  rw [average_sub s hs, average, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    (s.card : ℝ)⁻¹ * ‖∑ p ∈ s, (v p - w)‖ ≤
        (s.card : ℝ)⁻¹ * ∑ p ∈ s, d :=
      mul_le_mul_of_nonneg_left (norm_sum_le_of_le s hd) (by positivity)
    _ = d := by rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

lemma sum_average_sub (s : Finset P) (hs : s.Nonempty) (v : P → V) :
    ∑ p ∈ s, (average s v - v p) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    card_smul_average s hs v, sub_self]

lemma average_sub_average (s t : Finset P) (ht : t.Nonempty) (hst : s ⊆ t)
    (hs : s.Nonempty) (v : P → V) :
    average s v - average t v = (t.card : ℝ)⁻¹ •
      ∑ p ∈ t \ s, (average s v - v p) := by
  classical
  have hn : (t.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr ht
  have hsum : ∑ p ∈ t \ s, (average s v - v p) = ∑ p ∈ t, (average s v - v p) := by
    rw [Finset.sum_sdiff_eq_sub hst, sum_average_sub s hs v, sub_zero]
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rfl

lemma norm_average_sub_average_le (s t : Finset P) (ht : t.Nonempty) (hst : s ⊆ t)
    (hs : s.Nonempty) (v : P → V) (d : ℝ)
    (hd : ∀ p ∈ t, ∀ q ∈ t, ‖v p - v q‖ ≤ d) :
    ‖average s v - average t v‖ ≤
      ((t.card : ℝ) - (s.card : ℝ)) / (t.card : ℝ) * d := by
  classical
  rw [average_sub_average s t ht hst hs, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hb (q : P) (hq : q ∈ t \ s) : ‖average s v - v q‖ ≤ d :=
    norm_average_sub_le s hs v (v q) d (fun p hp => hd p (hst hp) q (Finset.mem_sdiff.mp hq).1)
  calc
    (t.card : ℝ)⁻¹ * ‖∑ p ∈ t \ s, (average s v - v p)‖ ≤
        (t.card : ℝ)⁻¹ * ∑ p ∈ t \ s, d :=
      mul_le_mul_of_nonneg_left (norm_sum_le_of_le (t \ s) hb) (by positivity)
    _ = ((t.card : ℝ) - (s.card : ℝ)) / (t.card : ℝ) * d := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff,
        Finset.inter_eq_left.mpr hst, Nat.cast_sub (Finset.card_le_card hst)]
      ring

def ratio (N : ℕ) : ℝ := ((N : ℝ) - 1) / (N : ℝ)

lemma ratio_nonneg {N : ℕ} (hN : 0 < N) : 0 ≤ ratio N := by
  dsimp [ratio]
  exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast Nat.succ_le_iff.mpr hN)) (by positivity)

lemma ratio_lt_one {N : ℕ} (hN : 0 < N) : ratio N < 1 := by
  dsimp [ratio]
  apply (div_lt_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
  linarith

lemma card_ratio_le {s t : Finset P} (hs : s.Nonempty) (ht : t.Nonempty)
    (N : ℕ) (hcard : t.card ≤ N) :
    ((t.card : ℝ) - (s.card : ℝ)) / (t.card : ℝ) ≤ ratio N := by
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast Finset.card_pos.mpr ht
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le htpos (by exact_mod_cast hcard)
  have hspos : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hc : (t.card : ℝ) ≤ N := by exact_mod_cast hcard
  rw [ratio, div_le_div_iff₀ htpos hNpos]
  nlinarith

lemma norm_nested_barycenters_le (s t : Finset P) (ht : t.Nonempty) (hst : s ⊆ t)
    (hs : s.Nonempty) (v : P → V) (d : ℝ) (hd0 : 0 ≤ d)
    (hd : ∀ p ∈ t, ∀ q ∈ t, ‖v p - v q‖ ≤ d)
    (N : ℕ) (hcard : t.card ≤ N) :
    ‖average s v - average t v‖ ≤ ratio N * d :=
  (norm_average_sub_average_le s t ht hst hs v d hd).trans
    (mul_le_mul_of_nonneg_right (card_ratio_le hs ht N hcard) hd0)

end Thomason.GeometricRecognition.Mesh

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Mesh
variable {P : Type u} [PartialOrder P]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

def ChainBound (P : Type u) [PartialOrder P] (N : ℕ) : Prop :=
  ∀ s : NonemptyFiniteChains P, s.finset.card ≤ N

lemma chainBound_subdivision {N : ℕ} (h : ChainBound P N) :
    ChainBound (NonemptyFiniteChains P) N := by
  classical
  intro c
  have hinj : Set.InjOn (fun s : NonemptyFiniteChains P => s.finset.card) c.finset := by
    intro a ha b hb he
    change a.finset.card = b.finset.card at he
    rcases c.comparable ⟨a,ha⟩ ⟨b,hb⟩ with hab | hba
    · exact NonemptyFiniteChains.ext (Finset.eq_of_subset_of_card_le (show a.finset ⊆ b.finset from hab) he.ge)
    · exact (NonemptyFiniteChains.ext (Finset.eq_of_subset_of_card_le (show b.finset ⊆ a.finset from hba) he.le)).symm
  have he : (c.finset.image (fun s => s.finset.card)).card = c.finset.card :=
    Finset.card_image_of_injOn hinj
  have hsub : c.finset.image (fun s => s.finset.card) ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr a.nonempty, h a⟩
  have hn := Finset.card_le_card hsub
  simpa only [he, Nat.card_Icc, Nat.add_sub_cancel] using hn

def Bound (v : P → V) (d : ℝ) : Prop :=
  ∀ p q, (p ≤ q ∨ q ≤ p) → ‖v p - v q‖ ≤ d

lemma bound_subdivision (v : P → V) (d : ℝ) (hd : 0 ≤ d) (hv : Bound v d)
    {N : ℕ} (hN : ChainBound P N) :
    Bound (fun s : NonemptyFiniteChains P => average s.finset v) (ratio N * d) := by
  intro s t hst
  rcases hst with hst | hts
  · exact norm_nested_barycenters_le s.finset t.finset t.nonempty hst s.nonempty
      v d hd (fun p hp q hq => hv p q (t.comparable ⟨p,hp⟩ ⟨q,hq⟩)) N (hN t)
  · rw [norm_sub_rev]
    exact norm_nested_barycenters_le t.finset s.finset s.nonempty hts t.nonempty
      v d hd (fun p hp q hq => hv p q (s.comparable ⟨p,hp⟩ ⟨q,hq⟩)) N (hN s)

def evaluate (v : P → V) (x : PolyPoint P) : V :=
  Finsupp.linearCombination ℝ v x.weights

lemma evaluate_eq_sum (v : P → V) (x : PolyPoint P) :
    evaluate v x = ∑ p ∈ x.weights.support, x.weights p • v p := by
  rfl

lemma norm_evaluate_sub_le (v : P → V) (x : PolyPoint P) (w : V) (d : ℝ)
    (h : ∀ p ∈ x.weights.support, ‖v p - w‖ ≤ d) : ‖evaluate v x - w‖ ≤ d := by
  have ht : ∑ p ∈ x.weights.support, x.weights p = 1 := x.total
  have he : evaluate v x - w =
      ∑ p ∈ x.weights.support, x.weights p • (v p - w) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, ht, one_smul]
    rfl
  rw [he]
  calc
    ‖∑ p ∈ x.weights.support, x.weights p • (v p - w)‖ ≤
        ∑ p ∈ x.weights.support, x.weights p * d := by
      apply norm_sum_le_of_le
      intro p hp
      rw [norm_smul, Real.norm_of_nonneg (x.nonneg p)]
      exact mul_le_mul_of_nonneg_left (h p hp) (x.nonneg p)
    _ = d := by
      rw [← Finset.sum_mul, ht, one_mul]

lemma evaluate_barycenter (v : P → V) (s : NonemptyFiniteChains P) :
    evaluate v (PolyPoint.barycenter s) = average s.finset v := by
  classical
  simp only [evaluate, PolyPoint.barycenter, map_sum, Finsupp.linearCombination_single,
    ← Finset.smul_sum, average]

lemma evaluate_subdivide (v : P → V) (x : PolyPoint (NonemptyFiniteChains P)) :
    evaluate v (PolyPoint.subdivide x) =
      evaluate (fun s : NonemptyFiniteChains P => average s.finset v) x := by
  change Finsupp.linearCombination ℝ v (PolyPoint.barycentricLinear x.weights) = _
  have hi : PolyPoint.barycentricLinear x.weights =
      x.weights.sum (fun s r => r • (PolyPoint.barycenter s).weights) := rfl
  rw [hi, map_finsuppSum]
  simp only [map_smul]
  change x.weights.sum (fun s r => r • evaluate v (PolyPoint.barycenter s)) = _
  simp only [evaluate_barycenter]
  rfl

instance finiteChains [Finite P] : Finite (NonemptyFiniteChains P) :=
  Finite.of_injective NonemptyFiniteChains.finset
    (fun _ _ h => NonemptyFiniteChains.ext h)

@[reducible] def level (P : PartOrd.{u}) : ℕ → PartOrd.{u}
  | 0 => P
  | n + 1 => PartOrd.of (NonemptyFiniteChains (level P n))

instance finiteLevel (P : PartOrd.{u}) [Finite P] (n : ℕ) : Finite (level P n) := by
  induction n with
  | zero => exact ‹Finite P›
  | succ n ih => exact @finiteChains (level P n) _ ih

def levelHomeomorph (P : PartOrd.{u}) : (n : ℕ) → PolyPoint (level P n) ≃ₜ PolyPoint P
  | 0 => Homeomorph.refl _
  | n + 1 => PolyPoint.subdivisionHomeomorph.trans (levelHomeomorph P n)

def levelVertices (P : PartOrd.{u}) (v : P → V) : (n : ℕ) → level P n → V
  | 0 => v
  | n + 1 => fun s => average s.finset (levelVertices P v n)

lemma chainBound_level (P : PartOrd.{u}) {N : ℕ} (h : ChainBound P N) (n : ℕ) :
    ChainBound (level P n) N := by
  induction n with
  | zero => exact h
  | succ n ih => exact chainBound_subdivision ih

lemma bound_level (P : PartOrd.{u}) (v : P → V) (d : ℝ) (hd : 0 ≤ d)
    (hv : Bound v d) {N : ℕ} (hN : 0 < N) (hP : ChainBound P N) (n : ℕ) :
    Bound (levelVertices P v n) ((ratio N) ^ n * d) := by
  induction n with
  | zero => simpa only [levelVertices, pow_zero, one_mul] using hv
  | succ n ih =>
    have h := bound_subdivision (levelVertices P v n) ((ratio N) ^ n * d)
      (mul_nonneg (pow_nonneg (ratio_nonneg hN) n) hd) ih (chainBound_level P hP n)
    simpa only [levelVertices, pow_succ', mul_assoc] using h

lemma evaluate_levelHomeomorph (P : PartOrd.{u}) (v : P → V) (n : ℕ)
    (x : PolyPoint (level P n)) :
    evaluate v (levelHomeomorph P n x) = evaluate (levelVertices P v n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change evaluate v (levelHomeomorph P n (PolyPoint.subdivide x)) = _
    rw [ih]
    exact evaluate_subdivide (levelVertices P v n) x

lemma exists_small_mesh (P : PartOrd.{u}) (v : P → V) (d : ℝ) (hd : 0 ≤ d)
    (hv : Bound v d) {N : ℕ} (hN : 0 < N) (hP : ChainBound P N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ e : ℝ, 0 ≤ e ∧ e < ε ∧ Bound (levelVertices P v n) e := by
  have ht : Filter.Tendsto (fun n : ℕ => ratio N ^ n * d) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (ratio_nonneg hN) (ratio_lt_one hN)).mul_const d
  obtain ⟨n, hn⟩ := Filter.Eventually.exists (ht.eventually (gt_mem_nhds hε))
  exact ⟨n,ratio N ^ n * d, mul_nonneg (pow_nonneg (ratio_nonneg hN) n) hd,
    hn, bound_level P v d hd hv hN hP n⟩

end Mesh
end Thomason.GeometricRecognition

end

end OAI
