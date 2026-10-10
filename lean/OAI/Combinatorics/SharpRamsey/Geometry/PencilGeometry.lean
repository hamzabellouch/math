import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.ActualClassLaw
import OAI.Combinatorics.SharpRamsey.Marking.UniformSupports

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open scoped BigOperators
open Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPencilGeometry_1 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
local instance flat_JoinedPencilGeometry_2 : Fintype (Submodule K V) := Fintype.ofFinite _

def RadialLine (x : Projectivization K V) :=
  {W : Submodule K V // Module.finrank K W = 2 ∧ x.submodule ≤ W}

instance radialLineFintype (x : Projectivization K V) : Fintype (RadialLine x) := by
  unfold RadialLine
  infer_instance

def lines (x : Projectivization K V) (H : Projectivization K (Module.Dual K V)) :
    Finset (RadialLine x) :=
  Finset.univ.filter (fun W => W.1 ≤ LinearMap.ker H.rep)

@[simp] lemma mem_lines (x : Projectivization K V)
    (H : Projectivization K (Module.Dual K V)) (W : RadialLine x) :
    W ∈ lines x H ↔ W.1 ≤ LinearMap.ker H.rep := by simp [lines]

omit [Finite K] [FiniteDimensional K V] in
lemma finrank_join (x y : Projectivization K V) (hne : x ≠ y) :
    Module.finrank K (x.submodule ⊔ y.submodule : Submodule K V) = 2 := by
  have hh := finrank_span_eq_card (Projectivization.linearIndependent_pair_iff_ne.mpr hne)
  have he : Set.range ![x.rep,y.rep] = {x.rep,y.rep} := by
    ext v
    simp [or_comm]
  rw [he, Submodule.span_insert] at hh
  rw [x.submodule_eq, y.submodule_eq]
  exact hh

omit [Finite K] in
lemma radial_unique (x y : Projectivization K V) (hne : x ≠ y)
    (W : RadialLine x) (hy : y.submodule ≤ W.1) :
    x.submodule ⊔ y.submodule = W.1 :=
  Submodule.eq_of_le_of_finrank_eq (sup_le W.2.2 hy) ((finrank_join x y hne).trans W.2.1.symm)

def radialFiber (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (W : RadialLine x) : Finset (Projectivization K V) :=
  S.filter (fun y => y ≠ x ∧ y.submodule ≤ W.1)

omit [Finite K] [FiniteDimensional K V] in
@[simp] lemma mem_radialFiber (S : Finset (Projectivization K V)) (x y : Projectivization K V)
    (W : RadialLine x) : y ∈ radialFiber S x W ↔ y ∈ S ∧ y ≠ x ∧ y.submodule ≤ W.1 := by
  simp [radialFiber]

omit [Finite K] in

lemma radialFiber_disjoint (S : Finset (Projectivization K V)) (x : Projectivization K V)
    {W U : RadialLine x} (hne : W ≠ U) : Disjoint (radialFiber S x W) (radialFiber S x U) := by
  apply Finset.disjoint_left.mpr
  intro y hyW hyU
  obtain ⟨_, hyx, hyW⟩ := (mem_radialFiber S x y W).mp hyW
  have hyU := ((mem_radialFiber S x y U).mp hyU).2.2
  exact hne (Subtype.ext ((radial_unique x y hyx.symm W hyW).symm.trans
    (radial_unique x y hyx.symm U hyU)))

lemma radial_biUnion (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (U : Submodule K V) (hx : x.submodule ≤ U) :
    (Finset.univ.filter (fun W : RadialLine x => W.1 ≤ U)).biUnion (radialFiber S x) =
      S.filter (fun y => y ≠ x ∧ y.submodule ≤ U) := by
  ext y
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_radialFiber]
  constructor
  · rintro ⟨W, hWU, hyS, hyx, hyW⟩
    exact ⟨hyS, hyx, hyW.trans hWU⟩
  · rintro ⟨hyS, hyx, hyU⟩
    refine ⟨⟨x.submodule ⊔ y.submodule, finrank_join x y hyx.symm, le_sup_left⟩,
      sup_le hx hyU, hyS, hyx, le_sup_right⟩

theorem radial_count (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (U : Submodule K V) (hx : x.submodule ≤ U) :
    ∑ W ∈ Finset.univ.filter (fun W : RadialLine x => W.1 ≤ U), (radialFiber S x W).card =
      (S.filter (fun y => y ≠ x ∧ y.submodule ≤ U)).card := by
  rw [← Finset.card_biUnion, radial_biUnion S x U hx]
  intro W _ U _ hne
  exact radialFiber_disjoint S x hne

theorem radial_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (U : Submodule K V) (hx : x.submodule ≤ U) (c : ℝ) :
    ∑ W ∈ Finset.univ.filter (fun W : RadialLine x => W.1 ≤ U), c*(radialFiber S x W).card =
      c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ U)).card := by
  rw [← Finset.mul_sum, ← Nat.cast_sum, radial_count S x U hx]

theorem hyperplane_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (H : Projectivization K (Module.Dual K V)) (hx : x.submodule ≤ LinearMap.ker H.rep) (c : ℝ) :
    ∑ W ∈ lines x H, c*(radialFiber S x W).card =
      c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ LinearMap.ker H.rep)).card :=
  radial_mass S x (LinearMap.ker H.rep) hx c

theorem intersection_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (H J : Projectivization K (Module.Dual K V))
    (hxH : x.submodule ≤ LinearMap.ker H.rep) (hxJ : x.submodule ≤ LinearMap.ker J.rep)
    (c : ℝ) :
    ∑ W ∈ lines x H ∩ lines x J, c*(radialFiber S x W).card =
      c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ LinearMap.ker H.rep ⊓ LinearMap.ker J.rep)).card := by
  have he : lines x H ∩ lines x J =
      Finset.univ.filter (fun W : RadialLine x => W.1 ≤ LinearMap.ker H.rep ⊓ LinearMap.ker J.rep) := by
    ext W
    simp only [Finset.mem_inter, mem_lines, Finset.mem_filter, Finset.mem_univ, true_and, le_inf_iff]
  rw [he]
  exact radial_mass S x _ (le_inf hxH hxJ) c

end
end SharpLogRamsey.PreparedProjectiveGeometry

open Finset Classical
namespace SharpLogRamsey.CertificateGeometry
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
noncomputable section
local instance flat_JoinedPencilGeometry_3 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPencilGeometry_4 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
omit [Finite K] [FiniteDimensional K V] in

lemma through_iff (W : Submodule K V) (H : Projectivization K (Module.Dual K V)) :
    W ≤ LinearMap.ker H.rep ↔ H.submodule ≤ W.dualAnnihilator := by
  rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem,
    Submodule.mem_dualAnnihilator]
  rfl

theorem card_through (W : Submodule K V) :
    Fintype.card {H : Projectivization K (Module.Dual K V) // W ≤ LinearMap.ker H.rep} =
      ∑ i ∈ range (Module.finrank K W.dualAnnihilator), Nat.card K^i := by
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (Equiv.subtypeEquivRight (through_iff W)),
    ← Nat.card_congr (projectiveSubmoduleEquiv W.dualAnnihilator)]
  exact Projectivization.card_of_finrank K W.dualAnnihilator rfl

theorem line_card (hdim : Module.finrank K V = 4) (W : Submodule K V)
    (hW : Module.finrank K W = 2) :
    Fintype.card {H : Projectivization K (Module.Dual K V) // W ≤ LinearMap.ker H.rep} =
      Nat.card K+1 := by
  rw [card_through]
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have H : Module.finrank K W.dualAnnihilator = 2 := by omega
  rw [H]
  simp [sum_range_succ,Nat.add_comm]

end
end SharpLogRamsey.CertificateGeometry

namespace SharpLogRamsey.PreparedProjectiveGeometry
open SharpLogRamsey.CertificateGeometry
open scoped BigOperators
open Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPencilGeometry_5 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
local instance flat_JoinedPencilGeometry_6 : Fintype (Submodule K V) := Fintype.ofFinite _
local instance flat_JoinedPencilGeometry_7 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPencilGeometry_8 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

omit [Finite K] [FiniteDimensional K V] in
lemma point_dualCoannihilator (H : Projectivization K (Module.Dual K V)) :
    H.submodule.dualCoannihilator = LinearMap.ker H.rep := by
  apply SetLike.coe_injective
  rw [H.submodule_eq, Submodule.coe_dualCoannihilator_span]
  ext v
  simp

omit [Finite K] in
lemma intersection_finrank (hdim : Module.finrank K V = 4)
    (H J : Projectivization K (Module.Dual K V)) (hne : H ≠ J) :
    Module.finrank K (LinearMap.ker H.rep ⊓ LinearMap.ker J.rep : Submodule K V) = 2 := by
  have hr := finrank_join H J hne
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (H.submodule ⊔ J.submodule : Submodule K (Module.Dual K V))
  rw [Submodule.dualCoannihilator_sup_eq, point_dualCoannihilator,
    point_dualCoannihilator] at hd
  omega

def strength (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ) (W : RadialLine x) : ℝ := c*(radialFiber S x W).card

def overlap (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ) (H J : Projectivization K (Module.Dual K V)) : ℝ :=
  c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ LinearMap.ker H.rep ⊓ LinearMap.ker J.rep)).card

lemma overlap_is_strength (hdim : Module.finrank K V = 4)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ)
    (H J : Projectivization K (Module.Dual K V)) (hne : H ≠ J)
    (hxH : x.submodule ≤ LinearMap.ker H.rep) (hxJ : x.submodule ≤ LinearMap.ker J.rep) :
    ∃ W : RadialLine x, W ∈ lines x H ∧ W ∈ lines x J ∧
      overlap S x c H J = strength S x c W := by
  refine ⟨⟨_, intersection_finrank hdim H J hne, le_inf hxH hxJ⟩, ?_, ?_, rfl⟩
  · exact (mem_lines _ _ _).mpr inf_le_left
  · exact (mem_lines _ _ _).mpr inf_le_right

lemma hyperplanes_on_line_card_le (hdim : Module.finrank K V = 4)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (W : RadialLine x) :
    (A.filter (fun H => W ∈ lines x H)).card ≤ Nat.card K+1 := by
  calc
    _ ≤ Fintype.card {H : Projectivization K (Module.Dual K V) // W.1 ≤ LinearMap.ker H.rep} := by
      rw [← Fintype.card_coe]
      apply Fintype.card_le_of_injective (fun H : {H // H ∈ A.filter (fun H => W ∈ lines x H)} =>
        (⟨H.1, (mem_lines _ _ _).mp ((Finset.mem_filter.mp H.2).2)⟩ :
          {H : Projectivization K (Module.Dual K V) // W.1 ≤ LinearMap.ker H.rep}))
      intro H J he
      exact Subtype.ext (congrArg (fun U :
        {H : Projectivization K (Module.Dual K V) // W.1 ≤ LinearMap.ker H.rep} => U.1) he)
    _ = _ := line_card hdim W.1 W.2.1

def richRadials (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c a : ℝ) : Finset (RadialLine x) := univ.filter (fun W => a ≤ strength S x c W)

def hyperplanesOn (A : Finset (Projectivization K (Module.Dual K V)))
    (x : Projectivization K V) (W : RadialLine x) :
    Finset (Projectivization K (Module.Dual K V)) := A.filter (fun H => W ∈ lines x H)

def largePairs (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c a : ℝ) (A : Finset (Projectivization K (Module.Dual K V))) :=
  (A ×ˢ A).filter (fun z => z.1 ≠ z.2 ∧ a ≤ overlap S x c z.1 z.2)

theorem largePairs_card (hdim : Module.finrank K V = 4)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c a : ℝ)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hAx : ∀ H ∈ A, x.submodule ≤ LinearMap.ker H.rep) :
    (largePairs S x c a A).card ≤ (richRadials S x c a).card*(Nat.card K+1)^2 := by
  have hsub : largePairs S x c a A ⊆
      (richRadials S x c a).biUnion (fun W => hyperplanesOn A x W ×ˢ hyperplanesOn A x W) := by
    rintro ⟨H,J⟩ hmem
    obtain ⟨hmem,hne,hov⟩ := mem_filter.mp hmem
    obtain ⟨hH,hJ⟩ := mem_product.mp hmem
    obtain ⟨W,hWH,hWJ,he⟩ := overlap_is_strength hdim S x c H J hne (hAx H hH) (hAx J hJ)
    apply mem_biUnion.mpr
    exact ⟨W, by simp [richRadials, ← he, hov],
      mem_product.mpr ⟨mem_filter.mpr ⟨hH,hWH⟩, mem_filter.mpr ⟨hJ,hWJ⟩⟩⟩
  calc
    _ ≤ ((richRadials S x c a).biUnion
        (fun W => hyperplanesOn A x W ×ˢ hyperplanesOn A x W)).card := card_le_card hsub
    _ ≤ ∑ W ∈ richRadials S x c a, (hyperplanesOn A x W ×ˢ hyperplanesOn A x W).card :=
      card_biUnion_le
    _ ≤ ∑ _W ∈ richRadials S x c a, (Nat.card K+1)^2 := by
      apply sum_le_sum
      intro W _
      rw [card_product, ← pow_two]
      exact Nat.pow_le_pow_left (hyperplanes_on_line_card_le hdim A x W) 2
    _ = _ := by simp

def largeNeighbors (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c a : ℝ) (A : Finset (Projectivization K (Module.Dual K V)))
    (H : Projectivization K (Module.Dual K V)) :=
  A.filter (fun J => H ≠ J ∧ a ≤ overlap S x c H J)

lemma neighbors_card (hdim : Module.finrank K V = 4)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c a : ℝ)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hAx : ∀ H ∈ A, x.submodule ≤ LinearMap.ker H.rep)
    (H : Projectivization K (Module.Dual K V)) (hxH : x.submodule ≤ LinearMap.ker H.rep) :
    (largeNeighbors S x c a A H).card ≤
      (richRadials S x c a ∩ lines x H).card*(Nat.card K+1) := by
  have hsub : largeNeighbors S x c a A H ⊆
      (richRadials S x c a ∩ lines x H).biUnion (hyperplanesOn A x) := by
    intro J hJ
    obtain ⟨hJ,hne,hov⟩ := mem_filter.mp hJ
    obtain ⟨W,hWH,hWJ,he⟩ := overlap_is_strength hdim S x c H J hne hxH (hAx J hJ)
    exact mem_biUnion.mpr ⟨W, mem_inter.mpr ⟨by simp [richRadials, ← he, hov], hWH⟩,
      mem_filter.mpr ⟨hJ,hWJ⟩⟩
  calc
    _ ≤ ((richRadials S x c a ∩ lines x H).biUnion (hyperplanesOn A x)).card := card_le_card hsub
    _ ≤ ∑ W ∈ richRadials S x c a ∩ lines x H, (hyperplanesOn A x W).card := card_biUnion_le
    _ ≤ ∑ _W ∈ richRadials S x c a ∩ lines x H, (Nat.card K+1) :=
      sum_le_sum (fun W _ => hyperplanes_on_line_card_le hdim A x W)
    _ = _ := by simp

theorem largeNeighbors_bound (hdim : Module.finrank K V = 4)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c a : ℝ)
    (hc : 0 ≤ c) (ha : 0 < a)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hAx : ∀ H ∈ A, x.submodule ≤ LinearMap.ker H.rep)
    (H : Projectivization K (Module.Dual K V)) (hxH : x.submodule ≤ LinearMap.ker H.rep)
    (hmass : c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ LinearMap.ker H.rep)).card ≤ 2) :
    ((largeNeighbors S x c a A H).card : ℝ) ≤ 2*((Nat.card K : ℝ)+1)/a := by
  have hsum : ∑ W ∈ lines x H, strength S x c W ≤ 2 :=
    (hyperplane_mass S x H hxH c).le.trans hmass
  have hthreshold : ((richRadials S x c a ∩ lines x H).card : ℝ)*a ≤ 2 := by
    calc
      _ = ∑ _W ∈ richRadials S x c a ∩ lines x H, a := by simp
      _ ≤ ∑ W ∈ richRadials S x c a ∩ lines x H, strength S x c W := by
        apply sum_le_sum
        intro W hW
        exact (mem_filter.mp (mem_inter.mp hW).1).2
      _ ≤ ∑ W ∈ lines x H, strength S x c W := by
        apply sum_le_sum_of_subset_of_nonneg inter_subset_right
        intro W _ _
        exact mul_nonneg hc (Nat.cast_nonneg _)
      _ ≤ 2 := hsum
  have hcard : ((largeNeighbors S x c a A H).card : ℝ) ≤
      (richRadials S x c a ∩ lines x H).card*((Nat.card K : ℝ)+1) := by
    exact_mod_cast neighbors_card hdim S x c a A hAx H hxH
  apply (le_div_iff₀ ha).mpr
  have hqa : 0 ≤ (Nat.card K : ℝ)+1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hthreshold hqa
  have hmul' := mul_le_mul_of_nonneg_right hcard ha.le
  nlinarith

omit [Finite K] in
theorem overlap_plane_zero (hdim : Module.finrank K V = 3)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ)
    (H J : Projectivization K (Module.Dual K V)) (hne : H ≠ J)
    (hxH : x.submodule ≤ LinearMap.ker H.rep) (hxJ : x.submodule ≤ LinearMap.ker J.rep) :
    overlap S x c H J = 0 := by
  have hr := finrank_join H J hne
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (H.submodule ⊔ J.submodule : Submodule K (Module.Dual K V))
  rw [Submodule.dualCoannihilator_sup_eq, point_dualCoannihilator,
    point_dualCoannihilator] at hd
  have hdim' : Module.finrank K (LinearMap.ker H.rep ⊓ LinearMap.ker J.rep : Submodule K V) = 1 := by omega
  have he : x.submodule = LinearMap.ker H.rep ⊓ LinearMap.ker J.rep :=
    Submodule.eq_of_le_of_finrank_eq (le_inf hxH hxJ) (x.finrank_submodule.trans hdim'.symm)
  have hfilter : S.filter (fun y => y ≠ x ∧ y.submodule ≤ LinearMap.ker H.rep ⊓ LinearMap.ker J.rep) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro y _ h
    apply h.1
    apply Projectivization.submodule_injective
    apply Submodule.eq_of_le_of_finrank_eq
    · exact h.2.trans he.ge
    · exact y.finrank_submodule.trans x.finrank_submodule.symm
  unfold overlap
  rw [hfilter]
  simp

end
end SharpLogRamsey.PreparedProjectiveGeometry

namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset SharpLogRamsey.CertificateGeometry
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPencilGeometry_9 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPencilGeometry_10 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

theorem one_direction_card (hdim : Module.finrank K V≤4)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (W : RadialLine x) :
    (A.filter (fun H => W∈lines x H)).card≤Nat.card K+1 := by
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W.1
  have hw := W.2.1
  have h2 : Module.finrank K W.1.dualAnnihilator≤2 := by omega
  calc
    _ ≤ Fintype.card {H : Projectivization K (Module.Dual K V) // W.1≤LinearMap.ker H.rep} := by
      rw [←Fintype.card_coe]
      apply Fintype.card_le_of_injective (fun H : {H // H∈A.filter (fun H => W∈lines x H)} =>
        (⟨H.1,(mem_lines _ _ _).mp (mem_filter.mp H.2).2⟩ :
          {H : Projectivization K (Module.Dual K V) // W.1≤LinearMap.ker H.rep}))
      intro H J he
      apply Subtype.ext
      exact congrArg (fun z => z.1) he
    _ = ∑ i∈range (Module.finrank K W.1.dualAnnihilator),Nat.card K^i := card_through _
    _ ≤ ∑ i∈range 2,Nat.card K^i :=
      sum_le_sum_of_subset (range_mono h2)
    _ = _ := by simp [sum_range_succ,Nat.add_comm]

theorem two_directions_card (hdim : Module.finrank K V≤4)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (D E : RadialLine x) (hne : D≠E) :
    (A.filter (fun H => D∈lines x H ∧ E∈lines x H)).card≤1 := by
  apply card_le_one.mpr
  intro H hH J hJ
  by_contra hHJ
  have hr := finrank_join H J hHJ
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (H.submodule⊔J.submodule : Submodule K (Module.Dual K V))
  rw [Submodule.dualCoannihilator_sup_eq,point_dualCoannihilator,point_dualCoannihilator] at hd
  have hdimdual : Module.finrank K (Module.Dual K V)=Module.finrank K V := by simp
  have hi : Module.finrank K (LinearMap.ker H.rep⊓LinearMap.ker J.rep : Submodule K V)≤2 := by omega
  have hD : D.1≤LinearMap.ker H.rep⊓LinearMap.ker J.rep :=
    le_inf ((mem_lines _ _ _).mp (mem_filter.mp hH).2.1)
      ((mem_lines _ _ _).mp (mem_filter.mp hJ).2.1)
  have hE : E.1≤LinearMap.ker H.rep⊓LinearMap.ker J.rep :=
    le_inf ((mem_lines _ _ _).mp (mem_filter.mp hH).2.2)
      ((mem_lines _ _ _).mp (mem_filter.mp hJ).2.2)
  have hi2 : Module.finrank K (LinearMap.ker H.rep⊓LinearMap.ker J.rep : Submodule K V)=2 :=
    le_antisymm hi (D.2.1 ▸ Submodule.finrank_mono hD)
  have heD := Submodule.eq_of_le_of_finrank_eq hD (D.2.1.trans hi2.symm)
  have heE := Submodule.eq_of_le_of_finrank_eq hE (E.2.1.trans hi2.symm)
  exact hne (Subtype.ext (heD.trans heE.symm))

theorem pencil_card (hdim : Module.finrank K V≤4)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (hA : ∀ H∈A,x.submodule≤LinearMap.ker H.rep) :
    A.card≤(Nat.card K)^2+Nat.card K+1 := by
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq x.submodule
  have hx := x.finrank_submodule
  have h3 : Module.finrank K x.submodule.dualAnnihilator≤3 := by omega
  calc
    _ ≤ Fintype.card {H : Projectivization K (Module.Dual K V) // x.submodule≤LinearMap.ker H.rep} := by
      rw [←Fintype.card_coe]
      apply Fintype.card_le_of_injective (fun H : A =>
        (⟨H.1,hA H H.2⟩ : {H : Projectivization K (Module.Dual K V) // x.submodule≤LinearMap.ker H.rep}))
      intro H J he
      apply Subtype.ext
      exact congrArg (fun z => z.1) he
    _ = ∑ i∈range (Module.finrank K x.submodule.dualAnnihilator),Nat.card K^i := card_through _
    _ ≤ ∑ i∈range 3,Nat.card K^i := sum_le_sum_of_subset (range_mono h3)
    _ = _ := by simp [sum_range_succ]; omega

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
