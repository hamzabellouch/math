import OAI.Computability.UniqueGames.Soundness.RawPrivateTable
import OAI.Computability.UniqueGames.Soundness.RawTargetLawLemmas

namespace OAI

section

/-! Conversion of actual binary linear points to the named projection answers. -/

namespace UniqueGamesTheorem.Soundness.ActualPointAnswers
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open PartnerProjection PartnerMapCoordinates RawPartnerTarget
open RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat}

def sourceTau : ActualHomogeneous.E k →ₗ[F2] F2 := LinearMap.fst F2 F2 _
def partnerTau (J : Finset (Fin k)) : RawPoint J →ₗ[F2] F2 := LinearMap.proj none

theorem tau_projection (rhs : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) : (partnerTau J).comp (rawProjection rhs J slot) = sourceTau := by
  apply LinearMap.ext
  intro x
  change ofBit (toBit x.1) = x.1
  exact ofBit_toBit _

def firstAnswer (rhs : Fin k → Bool) (x : ActualHomogeneous.E k) :
    ActualProjection.FirstAnswer (Fin k) :=
  let p := (PartnerLinear.sourceLinearEquiv rhs).symm x
  (p.homogeneous, fun j => ConcreteExtraction.tripleCoordinates (p.coordinates j))

def secondAnswer (rhs : Fin k → Bool) (J : Finset (Fin k)) (v : RawPoint J) :
    ActualProjection.SecondAnswer (Fin k) :=
  let y := (pointEquiv rhs J).symm v
  (y.homogeneous, (fun j => ConcreteExtraction.tripleCoordinates (y.full j)), y.single)

private theorem triple_eq_of_first_second_parity (a b : PartnerProjection.Triple)
    (h₁ : a.first = b.first) (h₂ : a.second = b.second) (hp : parity a = parity b) : a = b := by
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  dsimp only at h₁ h₂
  subst b₁
  subst b₂
  simp only [parity] at hp
  have h₃ := congrArg (fun z => (a₁ ^^ a₂) ^^ z) hp
  have cancel (c d : Bool) : (c ^^ (c ^^ d)) = d := by
    cases c <;> cases d <;> rfl
  simp only [cancel] at h₃
  cases h₃
  rfl

/-- Inactive occurrences determine every full triple. The active right-hand
sides never enter the partner answer. -/
theorem secondAnswer_projection (rhs rhs' : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (x : ActualHomogeneous.E k)
    (hout : ∀ j, j ∉ J → rhs' j = rhs j) :
    secondAnswer rhs' J (rawProjection rhs J slot x) =
      ActualProjection.project (activeOf J) (fun j => ConcreteExtraction.slotIndex (slot j))
        (firstAnswer rhs x) := by
  let p := (PartnerLinear.sourceLinearEquiv rhs).symm x
  let y := (pointEquiv rhs' J).symm (rawProjection rhs J slot x)
  let z := PartnerLinear.projection rhs (activeOf J) slot p
  have hr : pointEquiv rhs' J y = pointEquiv rhs J z :=
    (pointEquiv rhs' J).apply_symm_apply _
  have hh : y.homogeneous = z.homogeneous := by
    have h := congrArg toBit (congrFun hr none)
    simpa only [pointEquiv_none, toBit_ofBit] using h
  have hfull : y.full = z.full := by
    funext j
    by_cases hj : j ∈ J
    · rw [y.full_zero j (by simp [activeOf, hj]), z.full_zero j (by simp [activeOf, hj])]
    · have h₁ : (y.full j).first = (z.full j).first := by
        have h := congrArg toBit (congrFun hr (some (.inl (⟨j,hj⟩,(0:Fin 2)))))
        simpa only [pointEquiv_full_first, toBit_ofBit] using h
      have h₂ : (y.full j).second = (z.full j).second := by
        have h := congrArg toBit (congrFun hr (some (.inl (⟨j,hj⟩,(1:Fin 2)))))
        simpa only [pointEquiv_full_second, toBit_ofBit] using h
      have hp : parity (y.full j) = parity (z.full j) := by
        rw [y.full_valid j (by simp [activeOf, hj]),
          z.full_valid j (by simp [activeOf, hj]), hout j hj, hh]
      exact triple_eq_of_first_second_parity _ _ h₁ h₂ hp
  have hsingle : y.single = z.single := by
    funext j
    by_cases hj : j ∈ J
    · have h := congrArg toBit (congrFun hr (some (.inr ⟨j,hj⟩)))
      simpa only [pointEquiv_single, toBit_ofBit] using h
    · rw [y.single_zero j (by simp [activeOf, hj]), z.single_zero j (by simp [activeOf, hj])]
  change (y.homogeneous, (fun j => ConcreteExtraction.tripleCoordinates (y.full j)), y.single) = _
  rw [hh, hfull, hsingle]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext j i
      change ConcreteExtraction.tripleCoordinates
          (if decide (j ∈ J) then zeroTriple else p.coordinates j) i =
        (if decide (j ∈ J) then false else ConcreteExtraction.tripleCoordinates (p.coordinates j) i)
      cases decide (j ∈ J) <;> simp [ConcreteExtraction.tripleCoordinates, zeroTriple]
    · funext j
      change (if decide (j ∈ J) then retained (slot j) (p.coordinates j) else false) =
        (if decide (j ∈ J) then ConcreteExtraction.tripleCoordinates (p.coordinates j)
          (ConcreteExtraction.slotIndex (slot j)) else false)
      rw [ConcreteExtraction.retained_coordinates]

def displayedRhs {Id Name : Type} (rhs : Id → Bool) (question : Fin k → Sum Id Name) :
    Fin k → Bool := fun j => match question j with
  | .inl o => rhs o
  | .inr _ => false

theorem displayedRhs_full {Id Name : Type} (rhs : Id → Bool)
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (slot : Fin k → Slot) (j : Fin k) (hj : j ∉ J) :
    displayedRhs rhs (RawPrivateTable.displayed J names occ slot) j = rhs (occ j) := by
  simp [displayedRhs, RawPrivateTable.displayed, hj]

/-- Actual point equality gives acceptance in the named verifier on complete
private inputs, with local answer conversions. -/
theorem actual_accepts {Q Id Name : Type} (J : Finset (Fin k))
    (g : IncidenceExtraction.Incidence Id Name)
    (qa : ZeroInformation.FirstInput (Fin k) Q Id)
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name)
    (slot : Fin k → Slot)
    (hquestion : qb.question = RawPrivateTable.displayed J g.name qa.question slot)
    (x : ActualHomogeneous.E k) (v : RawPoint J)
    (hone : sourceTau x = 1)
    (hprojection : rawProjection (fun j => g.rhs (qa.question j)) J slot x = v) :
    ActualProjection.accepts g (activeOf J) qa qb
      (firstAnswer (fun j => g.rhs (qa.question j)) x)
      (secondAnswer (displayedRhs g.rhs qb.question) J v) := by
  let p := (PartnerLinear.sourceLinearEquiv (fun j => g.rhs (qa.question j))).symm x
  have hp : p.homogeneous = true := by
    change toBit x.1 = true
    change x.1 = 1 at hone
    rw [hone]
    decide
  refine ⟨?_, hp, (fun j => ConcreteExtraction.slotIndex (slot j)), ?_, ?_⟩
  · intro j
    exact (ConcreteExtraction.parity_coordinates _).trans (p.valid j)
  · rw [hquestion]
    funext j
    by_cases hj : j ∈ J <;>
      simp [RawPrivateTable.displayed, ZeroInformation.partnerQuestion, activeOf, hj]
  · rw [← hprojection]
    exact secondAnswer_projection _ _ J slot x (fun j hj => by
      rw [hquestion]
      exact displayedRhs_full g.rhs J g.name qa.question slot j hj)

end
end UniqueGamesTheorem.Soundness.ActualPointAnswers

end

end OAI
