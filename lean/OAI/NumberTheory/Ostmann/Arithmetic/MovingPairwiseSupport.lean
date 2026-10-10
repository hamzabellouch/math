import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularSlots

namespace OAI

/-! # Reducing full moving-history coprimality to the new compensation tests -/

namespace Ostmann
open scoped Classical

def MovingSlotData.currentSlots {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℕ) : List ℕ :=
  XL :: XR :: T.regularSlots.map value

def MovingSlotData.CurrentPairwise {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℕ) : Prop :=
  (T.currentSlots value XL XR).Pairwise Nat.Coprime

private theorem parent_current_perm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n) (XL XR : ℕ) :
    ((.node s CL CR U left right : MovingSlotData σ (n + 1)).currentSlots value XL XR).Perm
      ((XL :: CL.map value) ++ (XR :: CR.map value)) := by
  apply List.perm_iff_count.mpr
  intro a
  simp only [MovingSlotData.currentSlots, MovingSlotData.regularSlots,
    List.map_append, List.count_cons, List.count_append]
  omega

private theorem child_current_perm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (U C : List σ) (h : T.regularSlots.Perm (U ++ C))
    (p x : ℕ) : (T.currentSlots value p x).Perm (p :: (U.map value ++ (x :: C.map value))) := by
  have hp := List.perm_iff_count.mp (h.map value)
  apply List.perm_iff_count.mpr
  intro a
  have ha := hp a
  simp only [List.map_append, List.count_append] at ha
  simp only [MovingSlotData.currentSlots, List.count_cons, List.count_append]
  omega

/-- The local equivalence is stated on the actual child states. Slot
coherence is available for every `buildMovingSlotData` by construction. -/
theorem moving_node_pairwise_iff {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n)
    (hcoh : (.node s CL CR U left right : MovingSlotData σ (n + 1)).RegularCoherent)
    (XL XR : ℕ)
    (hold : (.node s CL CR U left right : MovingSlotData σ (n + 1)).CurrentPairwise value XL XR)
    (hv : IsCoprime left.frequency (XL * MovingSlotReversal.naturalProduct value CL : ℤ))
    (hw : IsCoprime right.frequency (XR * MovingSlotReversal.naturalProduct value CR : ℤ))
    (hI : (MovingSlotData.step s CL CR U left right false).IntegralAt value (XL, XR)) :
    let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
    (left.CurrentPairwise value p XL ∧ right.CurrentPairwise value p XR) ↔
      (U.map value).Pairwise Nat.Coprime ∧ p.Coprime (MovingSlotReversal.naturalProduct value U) := by
  dsimp only
  let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
  have hp := (parent_current_perm value s CL CR U left right XL XR).pairwise_iff (R := Nat.Coprime)
    (fun h => h.symm)
  have hleft := (child_current_perm value left U CL hcoh.1 p XL).pairwise_iff (R := Nat.Coprime)
    (fun h => h.symm)
  have hright := (child_current_perm value right U CR hcoh.2.1 p XR).pairwise_iff (R := Nat.Coprime)
    (fun h => h.symm)
  have h := moving_children_pairwise_iff (XL :: CL.map value) (XR :: CR.map value)
    (U.map value) p s left.frequency right.frequency (hp.mp hold)
    (by simpa only [List.prod_cons, MovingSlotReversal.naturalProduct, Nat.cast_mul] using hv)
    (by simpa only [List.prod_cons, MovingSlotReversal.naturalProduct, Nat.cast_mul] using hw)
    (by simpa only [List.prod_cons, MovingSlotReversal.naturalProduct, MovingSlotData.step, p]
      using hI.2)
  exact (and_congr hleft hright).trans h

/-- Cross-branch frequency tests are retained explicitly at every node. -/
def MovingSlotData.CrossFrequencyUnits {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, .leaf _ _, _, _ => True
  | _, .node s CL CR U left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      IsCoprime left.frequency (XL * MovingSlotReversal.naturalProduct value CL : ℤ) ∧
      IsCoprime right.frequency (XR * MovingSlotReversal.naturalProduct value CR : ℤ) ∧
      left.CrossFrequencyUnits value p XL ∧ right.CrossFrequencyUnits value p XR

def MovingSlotData.FullPairwise {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, T@(.leaf _ _), XL, XR => T.CurrentPairwise value XL XR
  | _, T@(.node s CL CR U left right), XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      T.CurrentPairwise value XL XR ∧ left.FullPairwise value p XL ∧ right.FullPairwise value p XR

def MovingSlotData.NewCompensationUnits {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, .leaf _ _, _, _ => True
  | _, .node s CL CR U left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      ((U.map value).Pairwise Nat.Coprime ∧ p.Coprime (MovingSlotReversal.naturalProduct value U)) ∧
      left.NewCompensationUnits value p XL ∧ right.NewCompensationUnits value p XR

/-- Full pairwise coprimality down the original moving tree is equivalent
to top coprimality and the new compensation tests. Integral reconstruction
and all cross-frequency tests remain hypotheses on these exact states. -/
theorem MovingSlotData.fullPairwise_iff {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hcoh : T.RegularCoherent) (XL XR : ℕ)
    (hI : T.Integral value XL XR) (hfreq : T.CrossFrequencyUnits value XL XR) :
    T.FullPairwise value XL XR ↔ T.CurrentPairwise value XL XR ∧ T.NewCompensationUnits value XL XR := by
  induction T generalizing XL XR with
  | leaf => simp only [FullPairwise, NewCompensationUnits, and_true]
  | node s CL CR U left right ihL ihR =>
    have hL := ihL hcoh.2.2.1 _ _ hI.2.1 hfreq.2.2.1
    have hR := ihR hcoh.2.2.2 _ _ hI.2.2 hfreq.2.2.2
    change (_ ∧ _ ∧ _) ↔ _ ∧ (_ ∧ _ ∧ _)
    rw [hL, hR]
    constructor
    · rintro ⟨htop, ⟨hl, hnewL⟩, ⟨hr, hnewR⟩⟩
      exact ⟨htop, (moving_node_pairwise_iff value s CL CR U left right hcoh XL XR htop
        hfreq.1 hfreq.2.1 hI.1).mp ⟨hl, hr⟩, hnewL, hnewR⟩
    · rintro ⟨htop, hnew, hnewL, hnewR⟩
      have hc := (moving_node_pairwise_iff value s CL CR U left right hcoh XL XR htop
        hfreq.1 hfreq.2.1 hI.1).mpr hnew
      exact ⟨htop, ⟨hc.1, hnewL⟩, ⟨hc.2, hnewR⟩⟩

end Ostmann

end OAI
