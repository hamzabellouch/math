import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactMediator

namespace OAI

/-! Independent prescribed lengths for the exact nineteen local edges
identified with the actual iterated mediator graph. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator

abbrev ContactEdge := Fin 9 ⊕ (Unit ⊕ Fin 9)

def leftEdge (k : Fin 9) : LocalEdge :=
  ![Sum.inr (Sum.inr (Sum.inr (0, 0), 0)),
    Sum.inr (Sum.inl (Sum.inr (0, 0))),
    Sum.inr (Sum.inr (Sum.inr (0, 0), 1)),
    Sum.inr (Sum.inr (Sum.inl 0, 0)),
    Sum.inr (Sum.inl (Sum.inl 0)),
    Sum.inr (Sum.inr (Sum.inl 0, 1)),
    Sum.inr (Sum.inr (Sum.inr (0, 1), 1)),
    Sum.inr (Sum.inl (Sum.inr (0, 1))),
    Sum.inr (Sum.inr (Sum.inr (0, 1), 0))] k

def rightEdge (k : Fin 9) : LocalEdge :=
  ![Sum.inr (Sum.inr (Sum.inr (1, 1), 0)),
    Sum.inr (Sum.inl (Sum.inr (1, 1))),
    Sum.inr (Sum.inr (Sum.inr (1, 1), 1)),
    Sum.inr (Sum.inr (Sum.inl 1, 1)),
    Sum.inr (Sum.inl (Sum.inl 1)),
    Sum.inr (Sum.inr (Sum.inl 1, 0)),
    Sum.inr (Sum.inr (Sum.inr (1, 0), 1)),
    Sum.inr (Sum.inl (Sum.inr (1, 0))),
    Sum.inr (Sum.inr (Sum.inr (1, 0), 0))] k

def edgeAt : ContactEdge → LocalEdge :=
  Sum.elim leftEdge (Sum.elim (fun _ => Sum.inl ()) rightEdge)

def edgeIndex : LocalEdge → ContactEdge
  | Sum.inl _ => Sum.inr (Sum.inl ())
  | Sum.inr (Sum.inl (Sum.inl s)) =>
      if s = 0 then Sum.inl 4 else Sum.inr (Sum.inr 4)
  | Sum.inr (Sum.inl (Sum.inr (s, u))) =>
      if s = 0 then Sum.inl (if u = 0 then 1 else 7)
      else Sum.inr (Sum.inr (if u = 0 then 7 else 1))
  | Sum.inr (Sum.inr (Sum.inl s, t)) =>
      if s = 0 then Sum.inl (if t = 0 then 3 else 5)
      else Sum.inr (Sum.inr (if t = 0 then 5 else 3))
  | Sum.inr (Sum.inr (Sum.inr (s, u), t)) =>
      if s = 0 then Sum.inl (if u = 0 then (if t = 0 then 0 else 2)
        else (if t = 0 then 8 else 6))
      else Sum.inr (Sum.inr (if u = 0 then (if t = 0 then 8 else 6)
        else (if t = 0 then 0 else 2)))

def contactEdgeEquiv : ContactEdge ≃ LocalEdge where
  toFun := edgeAt
  invFun := edgeIndex
  left_inv := by
    rintro (k | (⟨⟩ | k))
    · fin_cases k <;> rfl
    · rfl
    · fin_cases k <;> rfl
  right_inv := by
    rintro (⟨⟩ | (p | ⟨p, t⟩))
    · rfl
    · cases p with
      | inl s => fin_cases s <;> rfl
      | inr su =>
        rcases su with ⟨s, u⟩
        fin_cases s <;> fin_cases u <;> rfl
    · cases p with
      | inl s => fin_cases s <;> fin_cases t <;> rfl
      | inr su =>
        rcases su with ⟨s, u⟩
        fin_cases s <;> fin_cases u <;> fin_cases t <;> rfl

theorem leftEdge_distance (negative : Bool) (G : ContactGadgetSite → ContactPoint) (k : Fin 9) :
    dist (G (localToContact (localLeft (if negative then 0 else 1) (leftEdge k))))
      (G (localToContact (localRight (leftEdge k)))) =
        dist (G (Sum.inl k.succ)) (G (Sum.inl k.castSucc)) := by
  fin_cases k <;> cases negative <;>
    simp [leftEdge, localToContact, localLeft, localRight, secondEndpoint, firstAttachment,
      localOld, localFirst, localSecond, localThird, dist_comm] <;> first | rfl | exact dist_comm _ _

theorem rightEdge_distance (negative : Bool) (G : ContactGadgetSite → ContactPoint) (k : Fin 9) :
    dist (G (localToContact (localLeft (if negative then 0 else 1) (rightEdge k))))
      (G (localToContact (localRight (rightEdge k)))) =
        dist (G (contactGadgetRightNode negative k.succ))
          (G (contactGadgetRightNode negative k.castSucc)) := by
  fin_cases k <;> cases negative <;>
    simp [rightEdge, localToContact, localLeft, localRight, secondEndpoint, firstAttachment,
      localOld, localFirst, localSecond, localThird, contactGadgetRightNode, contactGadgetSide,
      dist_comm] <;> first | rfl | exact dist_comm _ _

def pathLengths (ℓ : LocalEdge → ℝ) (edge : Fin 9 → LocalEdge) (k : ℕ) : ℝ :=
  if hk : k < 9 then ℓ (edge ⟨k, hk⟩) else 1

theorem exists_local_geometry (negative : Bool) (ℓ : LocalEdge → ℝ)
    (hℓ : ∀ a, ℓ a ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance)) :
    ∃ P : LocalSite → ContactPoint,
      P (localOld 0) = contactPoint 0 0 ∧
      P (localOld 1) = contactPoint 17 0 ∧
      (∀ a, dist (P (localLeft (if negative then 0 else 1) a)) (P (localRight a)) = ℓ a) ∧
      (∀ x y, x ≠ y → ¬contactGadgetLinked negative (localToContact x) (localToContact y) →
        6 / 5 < dist (P x) (P y)) ∧
      (∀ x, dist (P x) (contactBaseGadgetPosition negative (localToContact x)) < 1 / 20) := by
  let central := ℓ (Sum.inl ())
  let ll := pathLengths ℓ leftEdge
  let rr := pathLengths ℓ rightEdge
  have hl (k : ℕ) (hk : k < 9) : ll k ∈
      Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance) := by
    simpa only [ll, pathLengths, dite_eq_left hk] using hℓ (leftEdge ⟨k, hk⟩)
  have hr (k : ℕ) (hk : k < 9) : rr k ∈
      Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance) := by
    simpa only [rr, pathLengths, dite_eq_left hk] using hℓ (rightEdge ⟨k, hk⟩)
  obtain ⟨lh, rh, hlh, hrh, hls, _, hstart, hend⟩ :=
    contactGadget_independent_lengths negative (hℓ (Sum.inl ())).1 (hℓ (Sum.inl ())).2 ll rr
      (fun k hk => (hl k hk).1) (fun k hk => (hl k hk).2)
      (fun k hk => (hr k hk).1) (fun k hk => (hr k hk).2)
  let G := contactGadgetPosition negative central ll rr lh rh
  let P : LocalSite → ContactPoint := G ∘ localToContact
  have hlinks := contactGadget_link_lengths negative (hℓ (Sum.inl ())).1 ll rr
    (fun k hk => (hl k hk).1) (fun k hk => (hr k hk).1) hlh hrh hls
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · exact hstart
  · simpa [P, G, localToContact, localOld, contactGadgetRightNode] using hend
  · intro a
    obtain ⟨b, rfl⟩ := contactEdgeEquiv.surjective a
    rcases b with k | (⟨⟩ | k)
    · change dist (G (localToContact (localLeft _ (leftEdge k))))
        (G (localToContact (localRight (leftEdge k)))) = _
      rw [leftEdge_distance]
      change dist (G (Sum.inl k.succ)) (G (Sum.inl k.castSucc)) = ℓ (leftEdge k)
      simpa only [G, central, ll, pathLengths, dite_eq_left k.isLt] using hlinks.1 k
    · change dist (G (Sum.inl 9)) (G contactGadgetSide) = central
      rw [dist_comm]
      exact hlinks.2.1
    · change dist (G (localToContact (localLeft _ (rightEdge k))))
        (G (localToContact (localRight (rightEdge k)))) = _
      rw [rightEdge_distance]
      change dist (G (contactGadgetRightNode negative k.succ))
        (G (contactGadgetRightNode negative k.castSucc)) = ℓ (rightEdge k)
      simpa only [G, central, rr, pathLengths, dite_eq_left k.isLt] using hlinks.2.2 k
  · intro x y hxy hlink
    exact contactGadget_nonlink_separation negative (hℓ (Sum.inl ())).1
      (hℓ (Sum.inl ())).2 ll rr (fun k hk => (hl k hk).1) (fun k hk => (hl k hk).2)
      (fun k hk => (hr k hk).1) (fun k hk => (hr k hk).2) hlh hrh
      (localToContact x) (localToContact y)
      (fun h => hxy (localContactEquiv.injective h)) hlink
  · exact fun x => contactGadgetPosition_near negative (hℓ (Sum.inl ())).1
      (hℓ (Sum.inl ())).2 ll rr (fun k hk => (hl k hk).1) (fun k hk => (hl k hk).2)
      (fun k hk => (hr k hk).1) (fun k hk => (hr k hk).2) hlh hrh (localToContact x)

end ContinuumCoulomb.ContactMediator

end

end OAI
