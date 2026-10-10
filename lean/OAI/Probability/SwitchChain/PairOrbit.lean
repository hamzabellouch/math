import Mathlib

namespace OAI

noncomputable section

namespace Problem315.PairOrbit

variable {α : Type*} [sectionFintypeα : Fintype α] [DecidableEq α]

def membershipColor (S T : Finset α) (a : α) : Bool × Bool :=
  (decide (a ∈ S), decide (a ∈ T))

theorem color_filter (S T : Finset α) (b c : Bool) :
    (Finset.univ.filter fun a => membershipColor S T a = (b,c)) =
      if b then (if c then S ∩ T else S \ T)
      else (if c then T \ S else Finset.univ \ (S ∪ T)) := by
  cases b <;> cases c <;> ext a <;>
    simp [membershipColor, not_or, and_comm]

theorem membershipColor_fiber_card
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) (b : Bool × Bool) :
    Fintype.card {a // membershipColor S T a = b} =
      Fintype.card {a // membershipColor U V a = b} := by
  have hdiff : (S \ T).card = (U \ V).card := by
    have ha := Finset.card_sdiff_add_card_inter S T
    have hb := Finset.card_sdiff_add_card_inter U V
    omega
  have hdiff' : (T \ S).card = (V \ U).card := by
    have ha := Finset.card_sdiff_add_card_inter T S
    have hb := Finset.card_sdiff_add_card_inter V U
    have hI' : (T ∩ S).card = (V ∩ U).card := by simpa [Finset.inter_comm] using hI
    omega
  have hunion : (S ∪ T).card = (U ∪ V).card := by
    have ha := Finset.card_union_add_card_inter S T
    have hb := Finset.card_union_add_card_inter U V
    omega
  have hcompl : (Finset.univ \ (S ∪ T)).card = (Finset.univ \ (U ∪ V)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_sdiff_of_subset (Finset.subset_univ _), hunion]
  rcases b with ⟨b,c⟩
  rw [Fintype.card_subtype, Fintype.card_subtype, color_filter, color_filter]
  cases b <;> cases c <;> simp [hI, hdiff, hdiff', hcompl]

theorem exists_perm_membership
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) :
    ∃ e : Equiv.Perm α,
      (∀ a, a ∈ S ↔ e a ∈ U) ∧ (∀ a, a ∈ T ↔ e a ∈ V) := by
  let ef : ∀ b : Bool × Bool,
      {a // membershipColor S T a = b} ≃ {a // membershipColor U V a = b} :=
    fun b => Fintype.equivOfCardEq (membershipColor_fiber_card S T U V hS hT hI b)
  let e : Equiv.Perm α := Equiv.ofFiberEquiv ef
  have hc (a : α) : membershipColor U V (e a) = membershipColor S T a :=
    Equiv.ofFiberEquiv_map ef a
  refine ⟨e, ?_, ?_⟩
  · intro a
    have hh := congrArg Prod.fst (hc a)
    simpa [membershipColor, eq_comm] using hh
  · intro a
    have hh := congrArg Prod.snd (hc a)
    simpa [membershipColor, eq_comm] using hh

include sectionFintypeα in
theorem image_eq_of_membership (S U : Finset α) (e : Equiv.Perm α)
    (h : ∀ a, a ∈ S ↔ e a ∈ U) : S.image e = U := by
  have retainedsectionFintypeα := sectionFintypeα
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact (h a).mp ha
  · intro hb
    apply Finset.mem_image.mpr
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    apply (h (e.symm b)).mpr
    simpa using hb

theorem exists_perm_image
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) :
    ∃ e : Equiv.Perm α, S.image e = U ∧ T.image e = V := by
  obtain ⟨e, heS, heT⟩ := exists_perm_membership S T U V hS hT hI
  exact ⟨e, image_eq_of_membership S U e heS, image_eq_of_membership T V e heT⟩

theorem invariant_kernel_eq_of_card
    {β : Type*} (K : Finset α → Finset α → β)
    (hinv : ∀ (e : Equiv.Perm α) S T, K (S.image e) (T.image e) = K S T)
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) : K S T = K U V := by
  obtain ⟨e, heS, heT⟩ := exists_perm_image S T U V hS hT hI
  simpa only [heS, heT] using (hinv e S T).symm

theorem invariant_pair_kernel_eq_of_intersection
    {β : Type*} (K : Finset α → Finset α → β)
    (hinv : ∀ (e : Equiv.Perm α) S T, K (S.image e) (T.image e) = K S T)
    (S T U V : Finset α)
    (hS : S.card = 2) (hT : T.card = 2) (hU : U.card = 2) (hV : V.card = 2)
    (hI : (S ∩ T).card = (U ∩ V).card) : K S T = K U V := by
  exact invariant_kernel_eq_of_card K hinv S T U V (hS.trans hU.symm)
    (hT.trans hV.symm) hI

include sectionFintypeα in
theorem gram_invariant
    {Ω : Type*} [Fintype Ω]
    (action : Equiv.Perm α → Equiv.Perm Ω)
    (z : Finset α → Ω → ℝ)
    (hz : ∀ (e : Equiv.Perm α) S ω, z (S.image e) (action e ω) = z S ω)
    (e : Equiv.Perm α) (S T : Finset α) :
    (∑ ω, z (S.image e) ω * z (T.image e) ω) = ∑ ω, z S ω * z T ω := by
  have retainedsectionFintypeα := sectionFintypeα
  rw [← Equiv.sum_comp (action e) (fun ω => z (S.image e) ω * z (T.image e) ω)]
  simp_rw [hz]

theorem gram_eq_of_intersection
    {Ω : Type*} [Fintype Ω]
    (action : Equiv.Perm α → Equiv.Perm Ω)
    (z : Finset α → Ω → ℝ)
    (hz : ∀ (e : Equiv.Perm α) S ω, z (S.image e) (action e ω) = z S ω)
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) :
    (∑ ω, z S ω * z T ω) = ∑ ω, z U ω * z V ω := by
  exact invariant_kernel_eq_of_card (fun S T => ∑ ω, z S ω * z T ω)
    (gram_invariant action z hz) S T U V hS hT hI

end Problem315.PairOrbit

end

end OAI
