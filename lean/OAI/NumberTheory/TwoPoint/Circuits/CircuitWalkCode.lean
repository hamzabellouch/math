import OAI.NumberTheory.TwoPoint.Circuits.CircuitBlockCode
import OAI.NumberTheory.TwoPoint.Circuits.CircuitWalkImage

namespace OAI

/-! Injectivity of the switching encoding. Earlier incompatible terms stay
incompatible, while the first queried term becomes compatible in the image.
The first block and its responses can therefore be decoded and removed. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace DNFQueryBlock

lemma codes_cons {n : ℕ} (b : DNFQueryBlock n) (bs : List (DNFQueryBlock n)) :
    codes (b :: bs) = b.literalCode.map some ++ none :: codes bs := by
  simp [codes, code, List.append_assoc]

lemma codes_eq_nil_iff {n : ℕ} (bs : List (DNFQueryBlock n)) : codes bs = [] ↔ bs = [] := by
  cases bs with
  | nil => simp [codes]
  | cons b bs => simp [codes_cons]

end DNFQueryBlock

namespace CanonicalDNFWalk

lemma codes_length_le {n : ℕ} {F : List (CubeTerm n)} {ρ : PartialAssignment n}
    {bs : List (DNFQueryBlock n)} (h : CanonicalDNFWalk F ρ bs) :
    (DNFQueryBlock.codes bs).length ≤ 2 * DNFQueryBlock.length bs := by
  induction h with
  | nil => simp [DNFQueryBlock.codes, DNFQueryBlock.length]
  | skip _ _ ih => exact ih
  | @step C F ρ bs x _ hne _ ih =>
    have hc : 1 ≤ (C.live ρ).card := card_pos.mpr hne
    simp only [DNFQueryBlock.codes_cons, List.length_append, List.length_map,
      List.length_cons, DNFQueryBlock.literalCode, Finset.length_sort,
      DNFQueryBlock.length]
    omega

lemma code_positions_le {n w : ℕ} {F : List (CubeTerm n)} {ρ : PartialAssignment n}
    {bs : List (DNFQueryBlock n)} (h : CanonicalDNFWalk F ρ bs)
    (hF : ∀ C ∈ F, C.support.card ≤ w) :
    ∀ z ∈ DNFQueryBlock.codes bs, ∀ a b, z = some (a, b) → a ≤ w := by
  induction h with
  | nil => simp [DNFQueryBlock.codes]
  | @skip C F ρ bs _ _ ih =>
    exact ih (fun D hD => hF D (List.mem_cons_of_mem C hD))
  | @step C F ρ bs x _ _ _ ih =>
    intro z hz a b hza
    rw [DNFQueryBlock.codes_cons] at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨q, hq, hqz⟩ := List.mem_map.mp hz
      obtain ⟨i, hi, hiq⟩ := List.mem_map.mp hq
      have hp : (C.slot i, x i) = (a, b) := Option.some.inj
        ((congrArg some hiq).trans (hqz.trans hza))
      have hslot : C.slot i = a := congrArg Prod.fst hp
      rw [← hslot]
      exact (C.slot_le i).trans (hF C (by simp))
    · rcases List.mem_cons.mp hz with hz | hz
      · rw [hz] at hza
        cases hza
      · exact ih (fun D hD => hF D (List.mem_cons_of_mem C hD)) z hz a b hza

theorem image_code_injective {n : ℕ} {F : List (CubeTerm n)}
    {ρ τ : PartialAssignment n} {bs cs : List (DNFQueryBlock n)}
    (hρ : CanonicalDNFWalk F ρ bs) (hτ : CanonicalDNFWalk F τ cs)
    (hi : DNFQueryBlock.image ρ bs = DNFQueryBlock.image τ cs)
    (hc : DNFQueryBlock.codes bs = DNFQueryBlock.codes cs) : ρ = τ := by
  induction F generalizing ρ τ bs cs with
  | nil =>
    cases hρ
    cases hτ
    exact hi
  | cons C F ih =>
    by_cases hb : bs = []
    · subst bs
      have hc' : cs = [] := (DNFQueryBlock.codes_eq_nil_iff cs).mp hc.symm
      subst cs
      exact hi
    by_cases hd : cs = []
    · subst cs
      have hb' : bs = [] := (DNFQueryBlock.codes_eq_nil_iff bs).mp hc
      exact False.elim (hb hb')
    cases hρ with
    | nil => exact False.elim (hb rfl)
    | skip hC hρ =>
      cases hτ with
      | nil => exact False.elim (hd rfl)
      | skip hD hτ => exact ih hρ hτ hi hc
      | step y hD hne hτ =>
        have hbad := C.incompatible_mono hC hρ.image_extends
        apply False.elim
        apply hbad
        rw [hi]
        exact step_image_compatible y hD hτ
    | @step _ _ _ bs x hC hne hρ =>
      cases hτ with
      | nil => exact False.elim (hd rfl)
      | skip hD hτ =>
        have hbad := C.incompatible_mono hD hτ.image_extends
        apply False.elim
        apply hbad
        rw [← hi]
        exact step_image_compatible x hC hρ
      | @step _ _ _ cs y hD hne' hτ =>
        rw [DNFQueryBlock.codes_cons, DNFQueryBlock.codes_cons] at hc
        obtain ⟨hlit, hrest⟩ := separated_option_lists_injective _ _ _ _ hc
        obtain ⟨hS, hxy⟩ := DNFQueryBlock.literalCode_injective C (C.live ρ) (C.live τ)
          (filter_subset _ _) (filter_subset _ _) x y hlit
        have hr := congrArg (fun σ : PartialAssignment n => σ.assign (C.live ρ) x) hi
        rw [step_image_restore x hρ] at hr
        have hright :
            (DNFQueryBlock.image τ (⟨C, C.live τ, y⟩ :: cs)).assign (C.live ρ) x =
              DNFQueryBlock.image (τ.assign (C.live τ) y) cs := by
          rw [PartialAssignment.assign_congr_on _ _ x y hxy, hS]
          exact step_image_restore y hτ
        rw [hright] at hr
        have hnext := ih hρ hτ hr hrest
        apply PartialAssignment.assign_injective_of_free ρ τ (C.live ρ)
          (C.live_subset_free ρ) (by rw [hS]; exact C.live_subset_free τ) x y
        simpa only [hS] using hnext

end CanonicalDNFWalk

end TwoPointCorrelations

end OAI
