import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceRestriction
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedCoefficient
import Mathlib.Logic.Equiv.Sum

namespace OAI

/-! A common reference lattice collects the uniquely assigned packets
from all tops. Disjointness is imposed on the actual sites, not paid for
by summing bounds over top labels. Profiles and waves are unchanged. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem sigma_site_injective {τ : Type*} {I : τ → Type*}
    (site : ∀ t, I t → ℤ×ℤ) (hinj : ∀ t, Function.Injective (site t))
    (hdisjoint : ∀ s t, s ≠ t → Disjoint (Set.range (site s)) (Set.range (site t))) :
    Function.Injective (fun u : Σ t, I t => site u.1 u.2) := by
  rintro ⟨s,u⟩ ⟨t,v⟩ h
  have hst : s = t := by
    by_contra hn
    exact Set.disjoint_left.mp (hdisjoint s t hn) ⟨u,rfl⟩ ⟨v,h.symm⟩
  subst t
  exact congrArg (Sigma.mk s) (hinj s h)

namespace SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- Retain the common scale/label geometry while supplying actual
packet sites and profiles from a subcollection or disjoint union. -/
def referenceItems (I : ∀ j, Label j → Type) [∀ j l, Fintype (I j l)]
    (site : ∀ j (l : P.labels j), I j l → ℤ×ℤ)
    (hinj : ∀ j l, Function.Injective (site j l))
    (profile : ∀ j (l : P.labels j), I j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hprofile : ∀ j l u k, planarProfileConstant (profile j l u k) (2*P.order) ≤ P.profileBound) :
    SourceLabeledLattice N κ Label I where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := P.carrierBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := P.carrierBound_nonneg
  labels := P.labels
  originX := P.originX
  originZ := P.originZ
  rowSlope := P.rowSlope
  frequency := P.frequency
  site := site
  site_injective := hinj
  profile := profile
  profile_bound := hprofile
  shear_bound := P.shear_bound
  carrier_bound := P.carrier_bound

variable {τ : Type} [Fintype τ]
  (I : τ → ∀ j, Label j → Type) [∀ t j l, Fintype (I t j l)]
  (site : ∀ t j (l : P.labels j), I t j l → ℤ×ℤ)
  (hjoint : ∀ j (l : P.labels j), Function.Injective (fun u : Σ t, I t j l => site u.1 j l u.2))
  (profile : ∀ t j (l : P.labels j), I t j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hprofile : ∀ t j l u k, planarProfileConstant (profile t j l u k) (2*P.order) ≤ P.profileBound)

/-- The common reference collection has the original profile bound.
Its constant contains no factor counting the source tops. -/
def flattenReference : SourceLabeledLattice N κ Label (fun j l => Σ t, I t j l) :=
  P.referenceItems (fun j l => Σ t, I t j l)
    (fun j l u => site u.1 j l u.2) hjoint
    (fun j l u k => profile u.1 j l u.2 k)
    (fun j l u k => hprofile u.1 j l u.2 k)

@[simp] theorem flattenReference_constant :
    (P.flattenReference I site hjoint profile hprofile).constant = P.constant := rfl

@[simp] theorem flattenReference_actualX (j : Fin N) (l : P.labels j) (t : τ) (u : I t j l) :
    (P.flattenReference I site hjoint profile hprofile).actualX j l ⟨t,u⟩ =
      P.originX j l+P.length j*(site t j l u).1 := rfl

@[simp] theorem flattenReference_actualZ (j : Fin N) (l : P.labels j) (t : τ) (u : I t j l) :
    (P.flattenReference I site hjoint profile hprofile).actualZ j l ⟨t,u⟩ =
      P.originZ j l+P.rowSlope j l*P.length j*(site t j l u).1+P.width*(site t j l u).2 := rfl

@[simp] theorem flattenReference_physicalPacket (s : ℝ) (j : Fin N)
    (l : P.labels j) (t : τ) (u : I t j l) (k : κ) :
    (P.flattenReference I site hjoint profile hprofile).physicalPacket s j l ⟨t,u⟩ k =
      physicalPlanarPacket (profile t j l u k)
        (P.originX j l+P.length j*(site t j l u).1)
        ((P.originZ j l+P.rowSlope j l*P.length j*(site t j l u).1+P.width*(site t j l u).2)+
          s*(P.originX j l+P.length j*(site t j l u).1))
        (P.length j) P.width (s+P.rowSlope j l) (P.frequency k)
        (P.length_pos j).ne' P.width_pos.ne' := rfl

/-- Recombination is an exact finite sum, before any norm estimate. -/
theorem flattenReference_sum {E : Type*} [AddCommMonoid E]
    (f : ∀ t j (l : P.labels j), I t j l → E) :
    (∑ j, ∑ l : P.labels j, ∑ u : Σ t, I t j l, f u.1 j l u.2) =
      ∑ t : τ, ∑ j, ∑ l : P.labels j, ∑ u : I t j l, f t j l u := by
  simp_rw [Fintype.sum_sigma]
  calc
    _ = ∑ j, ∑ t : τ, ∑ l : P.labels j, ∑ u : I t j l, f t j l u := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The component top inside the same common reference geometry. -/
def referenceComponent (t : τ) : SourceLabeledLattice N κ Label (I t) :=
  P.referenceItems (I t) (site t)
    (by
      intro j l a b h
      have hs : (⟨t,a⟩ : Σ s, I s j l) = ⟨t,b⟩ := hjoint j l h
      exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2)
    (profile t) (hprofile t)

@[simp] theorem flattenReference_component_raw (t : τ) (i : Fin 3) (j : Fin N)
    (l : P.labels j) (u : I t j l) (k : κ) (y : ℝ) :
    (P.flattenReference I site hjoint profile hprofile).raw i j l ⟨t,u⟩ k y =
      (P.referenceComponent I site hjoint profile hprofile t).raw i j l u k y := rfl

@[simp] theorem flattenReference_component_physicalCoefficient (s : ℝ)
    (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (owner : τ) (j : Fin N) (l : P.labels j) (u : I owner j l) :
    (P.flattenReference I site hjoint profile hprofile).physicalCoefficient s d v g j l ⟨owner,u⟩ =
      (P.referenceComponent I site hjoint profile hprofile owner).physicalCoefficient s d v g j l u := rfl

/-- Recombine source amplitudes before taking a norm or invoking a
reference moment estimate. -/
theorem flattenReference_rawInterval
    (coeff : ∀ t j (l : P.labels j), I t j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    (P.flattenReference I site hjoint profile hprofile).rawInterval
      (fun j l u => coeff u.1 j l u.2) i lower upper x y =
      ∑ t : τ, (P.referenceComponent I site hjoint profile hprofile t).rawInterval
        (coeff t) i lower upper x y := by
  have hband (j : Fin N) (k : κ) (y : ℝ) :
      (∑ t : τ, ∑ p : Σ l : P.labels j, I t j l,
        coeff t j p.1 p.2 k * (P.referenceComponent I site hjoint profile hprofile t).raw i j p.1 p.2 k y x) =
      ∑ p : Σ l : P.labels j, Σ t, I t j l,
        coeff p.2.1 j p.1 p.2.2 k *
          (P.flattenReference I site hjoint profile hprofile).raw i j p.1 p.2 k y x := by
    simp_rw [Fintype.sum_sigma]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    rfl
  have hpartial (n : ℕ) (k : κ) :
      (∑ t : τ, scalarBandPartial (fun j =>
        planarPacketBand (ι := fun j => Σ l : P.labels j, I t j l)
          (fun j p => coeff t j p.1 p.2)
          (fun j p k z a => (P.referenceComponent I site hjoint profile hprofile t).raw i j p.1 p.2 k z a) j k x) n y) =
      scalarBandPartial (fun j =>
        planarPacketBand (ι := fun j => Σ l : P.labels j, Σ t, I t j l)
          (fun j p => coeff p.2.1 j p.1 p.2.2)
          (fun j p k z a => (P.flattenReference I site hjoint profile hprofile).raw i j p.1 p.2 k z a) j k x) n y := by
    unfold scalarBandPartial
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < n
    · simp only [hj,ite_true,planarPacketBand]
      exact hband j k y
    · simp only [hj,ite_false,Finset.sum_const_zero]
  symm
  ext k
  simp only [rawInterval,planarPacketInterval,bandIntervalSignal,
    WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp]
  rw [Finset.sum_sub_distrib]
  exact congrArg₂ (fun a b : ℂ => a-b) (hpartial upper k) (hpartial lower k)

omit [Fintype τ] in
/-- Site injection of a unique packet-to-top assignment is automatic:
forgetting the owner is the natural equivalence of all ownership fibers
with the original packet set. -/
theorem owner_union_site_injective (owner : ∀ j (l : P.labels j), Item j l → τ)
    (j : Fin N) (l : P.labels j) :
    Function.Injective (fun u : Σ t, {i : Item j l // owner j l i = t} => P.site j l u.2.val) :=
  (P.site_injective j l).comp (Equiv.sigmaFiberEquiv (owner j l)).injective

/-- The actual ownership-fiber union, preserving every original profile
and integer site without repetition. -/
def flattenOwnedReference (owner : ∀ j (l : P.labels j), Item j l → τ) :
    SourceLabeledLattice N κ Label
      (fun j l => Σ t, {i : Item j l // ∃ h : l ∈ P.labels j, owner j ⟨l,h⟩ i = t}) :=
  P.referenceItems _
    (fun j l u => P.site j l u.2.val)
    (by
      intro j l a b h
      have huv : a.2.val = b.2.val := P.site_injective j l h
      have ha : owner j l a.2.val = a.1 := by
        obtain ⟨ha,ha'⟩ := a.2.property
        convert ha' using 1
      have hb : owner j l b.2.val = b.1 := by
        obtain ⟨hb,hb'⟩ := b.2.property
        convert hb' using 1
      have howner : a.1 = b.1 := by rw [← ha,← hb,huv]
      cases a with
      | mk ta ua =>
        cases b with
        | mk tb ub =>
          dsimp only at huv howner
          subst tb
          exact congrArg (Sigma.mk ta) (Subtype.ext huv))
    (fun j l u k => P.profile j l u.2.val k)
    (fun j l u k => P.profile_bound j l u.2.val k)

@[simp] theorem flattenOwnedReference_constant (owner : ∀ j (l : P.labels j), Item j l → τ) :
    (P.flattenOwnedReference owner).constant = P.constant := rfl

@[simp] theorem flattenOwnedReference_physicalPacket
    (owner : ∀ j (l : P.labels j), Item j l → τ) (s : ℝ) (j : Fin N) (l : P.labels j)
    (u : Σ t, {i : Item j l // ∃ h : l.val ∈ P.labels j, owner j ⟨l.val,h⟩ i = t}) (k : κ) :
    (P.flattenOwnedReference owner).physicalPacket s j l u k =
      P.physicalPacket s j l u.2.val k := rfl

/-- Forgetting an owner is a bijection, rather than a bounded-multiplicity
map. This is why recombination has no top-count loss. -/
def ownedReferenceEquiv (owner : ∀ j (l : P.labels j), Item j l → τ)
    (j : Fin N) (l : P.labels j) :
    (Σ t, {i : Item j l // ∃ h : l.val ∈ P.labels j, owner j ⟨l.val,h⟩ i = t}) ≃ Item j l :=
  Equiv.ofBijective (fun u => u.2.val) ⟨by
    intro a b h
    apply (P.flattenOwnedReference owner).site_injective j l
    exact congrArg (P.site j l) h,
    fun u => ⟨⟨owner j l u,⟨u,⟨l.property,rfl⟩⟩⟩,rfl⟩⟩

theorem sum_ownedReference {E : Type*} [AddCommMonoid E]
    (owner : ∀ j (l : P.labels j), Item j l → τ) (j : Fin N) (l : P.labels j)
    (f : Item j l → E) :
    (∑ u : Σ t, {i : Item j l // ∃ h : l.val ∈ P.labels j, owner j ⟨l.val,h⟩ i = t}, f u.2.val) =
      ∑ u : Item j l, f u :=
  Equiv.sum_comp (P.ownedReferenceEquiv owner j l) f

@[simp] theorem flattenOwnedReference_physicalCoefficient
    (owner : ∀ j (l : P.labels j), Item j l → τ) (s : ℝ)
    (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j)
    (u : Σ t, {i : Item j l // ∃ h : l.val ∈ P.labels j, owner j ⟨l.val,h⟩ i = t}) :
    (P.flattenOwnedReference owner).physicalCoefficient s d v g j l u =
      P.physicalCoefficient s d v g j l u.2.val := rfl

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
