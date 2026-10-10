import OAI.Dynamics.EntropyCounterexample.MonotoneItineraries

namespace OAI

namespace Problem340
namespace RegisterEntropyCoding

open Dynamics Set
open scoped SetRel

theorem netMaxcard_le_card_code {X β : Type*} [Finite β]
    (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ)
    (code : X → β)
    (hcode : ∀ x ∈ F, ∀ y ∈ F, code x = code y →
      (x, y) ∈ dynEntourage T U n) :
    netMaxcard T F U n ≤ (Nat.card β : ℕ∞) := by
  classical
  unfold netMaxcard
  refine iSup₂_le fun s hs => ?_
  have hinj : Function.Injective (fun x : s => code x.val) := by
    intro x y hxy
    apply Subtype.ext
    exact Set.PairwiseDisjoint.elim_set hs.2 x.property y.property y.val
      (hcode x.val (hs.1 x.property) y.val (hs.1 y.property) hxy)
      (hcode y.val (hs.1 y.property) y.val (hs.1 y.property) rfl)
  have hcard := Nat.card_le_card_of_injective _ hinj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    (show (Nat.card s : ℕ∞) ≤ Nat.card β by exact_mod_cast hcard)

theorem netMaxcard_le_register_code {X α : Type*} [LinearOrder α]
    {q H K : ℕ} (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ)
    (R : α → α) (b : α → Fin H) (hR : Monotone R) (hb : Monotone b)
    (radius : X → Fin q → α) (angle : X → Fin q → Fin K)
    (hcode : ∀ x ∈ F, ∀ y ∈ F,
      (∀ j, angle x j = angle y j) →
      (∀ j, MonotoneItineraries.itinerary R b n (radius x j) =
        MonotoneItineraries.itinerary R b n (radius y j)) →
      (x, y) ∈ dynEntourage T U n) :
    netMaxcard T F U n ≤ ((K * (1 + n * (H - 1))) ^ q : ℕ) := by
  classical
  let I := Set.range (MonotoneItineraries.itinerary R b n)
  let code : X → Fin q → Fin K × I := fun x j =>
    (angle x j, ⟨MonotoneItineraries.itinerary R b n (radius x j),
      ⟨radius x j, rfl⟩⟩)
  have hbound := netMaxcard_le_card_code T F U n code (by
    intro x hx y hy hxy
    apply hcode x hx y hy
    · intro j
      exact congrArg (fun z => (z j).1) hxy
    · intro j
      exact congrArg (fun z => (z j).2.val) hxy)
  apply hbound.trans
  have hi : Nat.card I ≤ 1 + n * (H - 1) :=
    MonotoneItineraries.card_itinerary_range_le hR hb n
  have hnat : Nat.card (Fin q → Fin K × I) ≤ (K * (1 + n * (H - 1))) ^ q := by
    simp only [Nat.card_fun, Nat.card_prod, Nat.card_fin]
    gcongr
  exact_mod_cast hnat

theorem netMaxcard_le_of_radius_angle {X α : Type*} [LinearOrder α]
    {q H K : ℕ} (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ)
    (R : α → α) (b : α → Fin H) (hR : Monotone R) (hb : Monotone b)
    (radius : X → Fin q → α) (angle : X → Fin q → Fin K)
    (hF : Set.MapsTo T F F)
    (hrad : ∀ j, Function.Semiconj (fun x => radius x j) T R)
    (hang : ∀ x, angle (T x) = angle x)
    (hclose : ∀ x ∈ F, ∀ y ∈ F,
      (∀ j, angle x j = angle y j) →
      (∀ j, b (radius x j) = b (radius y j)) → (x, y) ∈ U) :
    netMaxcard T F U n ≤ ((K * (1 + n * (H - 1))) ^ q : ℕ) := by
  apply netMaxcard_le_register_code T F U n R b hR hb radius angle
  intro x hx y hy hangle hitinerary
  rw [mem_dynEntourage]
  intro k hk
  apply hclose _ (hF.iterate k hx) _ (hF.iterate k hy)
  · have ha : angle ∘ T = angle := funext hang
    have hak := Function.iterate_invariant ha k
    have hax : angle (T^[k] x) = angle x := congrFun hak x
    have hay : angle (T^[k] y) = angle y := congrFun hak y
    intro j
    rw [hax, hay]
    exact hangle j
  · intro j
    have hrx : radius (T^[k] x) j = R^[k] (radius x j) := (hrad j).iterate_right k x
    have hry : radius (T^[k] y) j = R^[k] (radius y j) := (hrad j).iterate_right k y
    rw [hrx, hry]
    exact congrFun (hitinerary j) ⟨k, hk⟩

lemma register_bound_le_polynomial (K H q n : ℕ) :
    (K * (1 + n * (H - 1))) ^ q ≤
      (K * (H + 1)) ^ q * (n + 1) ^ q := by
  have hlinear : 1 + n * (H - 1) ≤ (H + 1) * (n + 1) := by
    nlinarith [Nat.sub_le H 1]
  calc
    (K * (1 + n * (H - 1))) ^ q ≤ (K * ((H + 1) * (n + 1))) ^ q := by
      gcongr
    _ = (K * (H + 1)) ^ q * (n + 1) ^ q := by rw [← mul_assoc, mul_pow]

theorem netMaxcard_le_card_code_after_one {X β : Type*} [Finite β]
    {C : ℕ} (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ)
    (initial : X → Fin C) (code : X → β)
    (hinitial : ∀ x ∈ F, ∀ y ∈ F, initial x = initial y → (x, y) ∈ U)
    (hcode : ∀ x ∈ F, ∀ y ∈ F, code (T x) = code (T y) →
      (T x, T y) ∈ dynEntourage T U n) :
    netMaxcard T F U n ≤ (C * Nat.card β : ℕ) := by
  have hbound := netMaxcard_le_card_code T F U n
    (fun x => (initial x, code (T x))) (by
      intro x hx y hy hxy
      rw [mem_dynEntourage]
      intro k hk
      cases k with
      | zero =>
        simpa using hinitial x hx y hy (congrArg Prod.fst hxy)
      | succ k =>
        have htail := (mem_dynEntourage.mp
          (hcode x hx y hy (congrArg Prod.snd hxy))) k (by omega)
        simpa only [Function.iterate_succ_apply] using htail)
  simpa only [Nat.card_prod, Nat.card_fin] using hbound

end RegisterEntropyCoding
end Problem340

end OAI
