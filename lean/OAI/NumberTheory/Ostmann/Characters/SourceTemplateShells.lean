import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePriors
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorSources

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction Preliminaries HigherBiasSourceWord HigherBiasSourceRoleBounds
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sourcePrimeShells_half {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (E : Fin (sourceHalfSize cfg m) → Finset (PrimeUpTo Q))
    (r : InitialRole k) (a : Fin (sourceWidth cfg m r.role)) (side : Bool) :
    sourcePrimeShells cfg m E ⟨(r,side),a⟩ = E (halfRoleIndexEquiv cfg m ⟨r,a⟩) := by
  cases side
  · change characterDoubleShell E (Fin.natAdd (sourceHalfSize cfg m) (halfRoleIndexEquiv cfg m ⟨r,a⟩)) = _
    exact Fin.append_right _ _ _
  · change characterDoubleShell E (Fin.castAdd (sourceHalfSize cfg m) (halfRoleIndexEquiv cfg m ⟨r,a⟩)) = _
    exact Fin.append_left _ _ _

theorem configurationPrimeShells_anchor {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (j : Fin k) (big side : Bool)
    (a : Fin (sourceWidth cfg m (.anchor j.val big))) :
    configurationPrimeShells cfg m bulk top E ⟨(.anchor j big,side),a⟩ =
      boundedRawLogCell E (cfg.1 (anchorCoordinate j big)) := by
  unfold configurationPrimeShells
  erw [sourcePrimeShells_half]
  change halfRoleShells bulk top m (configurationCells E cfg)
    (Fin.natAdd (m+1) (cellCoordinateEquiv cfg (.inl (anchorCoordinate j big)))) = _
  rw [halfRoleShells, Fin.append_right]
  exact congrArg (boundedRawLogCell E) (cellCoordinateEquiv_anchor cfg _)

theorem configurationPrimeShells_pivot {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (j : Fin k) (side : Bool)
    (a : Fin (cfg.2 j.castSucc).length) :
    configurationPrimeShells cfg m bulk top E
      ⟨(.pivot j,side),Fin.cast (sourceWidth_pivot cfg m j).symm a⟩ =
      boundedRawLogCell E ((cfg.2 j.castSucc).get a) := by
  unfold configurationPrimeShells
  erw [sourcePrimeShells_half]
  change halfRoleShells bulk top m (configurationCells E cfg)
    (Fin.natAdd (m+1) (cellCoordinateEquiv cfg (.inr ⟨j.castSucc,a⟩))) = _
  rw [halfRoleShells, Fin.append_right]
  exact congrArg (boundedRawLogCell E) (cellCoordinateEquiv_list cfg _ _)

theorem configurationPrimeShells_filler {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (side : Bool) (a : Fin (cfg.2 (Fin.last k)).length) :
    configurationPrimeShells cfg m bulk top E ⟨(.filler,side),a⟩ =
      boundedRawLogCell E ((cfg.2 (Fin.last k)).get a) := by
  unfold configurationPrimeShells
  erw [sourcePrimeShells_half]
  change halfRoleShells bulk top m (configurationCells E cfg)
    (Fin.natAdd (m+1) (cellCoordinateEquiv cfg (.inr ⟨Fin.last k,a⟩))) = _
  rw [halfRoleShells, Fin.append_right]
  exact congrArg (boundedRawLogCell E) (cellCoordinateEquiv_list cfg _ _)

theorem scheduledConstituentOrigin_role (k : ℕ) (width : Role → ℕ) (j : ℕ)
    (i : (schedule k j).Constituent width) :
    (schedule k 0).role (scheduledConstituentOrigin k width j i).1 = (schedule k j).role i.1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rcases i with ⟨i,a⟩
    cases i with
    | inl z => exact ih ⟨z.1.val,a⟩
    | inr z => exact ih ⟨z.val,a⟩

theorem scheduledConstituentOrigin_position (k : ℕ) (width : Role → ℕ) (j : ℕ)
    (i : (schedule k j).Constituent width) :
    (scheduledConstituentOrigin k width j i).2.val = i.2.val := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rcases i with ⟨i,a⟩
    cases i with
    | inl z => exact ih ⟨z.1.val,a⟩
    | inr z => exact ih ⟨z.val,a⟩

theorem scheduledPrimeShells_word {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (i : (schedule k j).Slot)
    (hi : (schedule k j).role i = .word) (a : Fin (sourceWidth cfg m ((schedule k j).role i))) :
    scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) j ⟨i,a⟩ =
      roleShells bulk top m ⟨a.val,by simpa only [hi,sourceWidth_word] using a.isLt⟩ := by
  rw [scheduledPrimeShells_eq_origin]
  have hr := scheduledConstituentOrigin_role k (sourceWidth cfg m) j ⟨i,a⟩
  have hp := scheduledConstituentOrigin_position k (sourceWidth cfg m) j ⟨i,a⟩
  rw [hi] at hr
  generalize he : scheduledConstituentOrigin k (sourceWidth cfg m) j ⟨i,a⟩ = x at hr hp ⊢
  rcases x with ⟨⟨r,b⟩,v⟩
  have hw : r = .word := by
    change r.role = .word at hr
    cases r <;> simp_all [InitialRole.role]
  subst r
  erw [configurationPrimeShells_word]
  congr 1
  exact Fin.ext hp

theorem configurationPrimeShells_nonword_mass {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (μ : ℝ)
    (hc : ∀ i, μ ≤ primeShellMass (configurationCells E cfg i))
    (i : SourceConstituent cfg m) (hi : (schedule k 0).role i.1 ≠ .word) :
    μ ≤ primeShellMass (configurationPrimeShells cfg m bulk top E i) := by
  rcases i with ⟨⟨r,b⟩,a⟩
  unfold configurationPrimeShells
  erw [sourcePrimeShells_half]
  cases r with
  | word => exact False.elim (hi rfl)
  | anchor j big =>
    change μ ≤ primeShellMass (halfRoleShells bulk top m (configurationCells E cfg)
      (Fin.natAdd (m+1) (cellCoordinateEquiv cfg (.inl (anchorCoordinate j big)))))
    rw [halfRoleShells, Fin.append_right]
    exact hc _
  | pivot j =>
    change μ ≤ primeShellMass (halfRoleShells bulk top m (configurationCells E cfg)
      (Fin.natAdd (m+1) (cellCoordinateEquiv cfg
        (.inr ⟨j.castSucc,Fin.cast (sourceWidth_pivot cfg m j) a⟩))))
    rw [halfRoleShells, Fin.append_right]
    exact hc _
  | filler =>
    change μ ≤ primeShellMass (halfRoleShells bulk top m (configurationCells E cfg)
      (Fin.natAdd (m+1) (cellCoordinateEquiv cfg (.inr ⟨Fin.last k,a⟩))))
    rw [halfRoleShells, Fin.append_right]
    exact hc _

theorem scheduledPrimeShells_nonword_mass {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (μ : ℝ)
    (hc : ∀ i, μ ≤ primeShellMass (configurationCells E cfg i))
    (i : (schedule k j).Constituent (sourceWidth cfg m))
    (hi : (schedule k j).role i.1 ≠ .word) :
    μ ≤ primeShellMass (scheduledPrimeShells k (sourceWidth cfg m)
      (configurationPrimeShells cfg m bulk top E) j i) := by
  rw [scheduledPrimeShells_eq_origin]
  apply configurationPrimeShells_nonword_mass cfg m bulk top E μ hc
  rw [scheduledConstituentOrigin_role]
  exact hi

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
