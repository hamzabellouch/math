import OAI.NumberTheory.Ostmann.Characters.SourceTemplateIndices

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction Preliminaries HigherBiasSourceWord HigherBiasSourceRoleBounds
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sourceSample {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (w : Fin (sourceHalfSize cfg m + sourceHalfSize cfg m) → PrimeUpTo Q) :
    SourceConstituent cfg m → PrimeUpTo Q := fun i => w (sourceIndexEquiv cfg m i)

def sourceSampleEquiv {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    (Fin (sourceHalfSize cfg m + sourceHalfSize cfg m) → PrimeUpTo Q) ≃
      (SourceConstituent cfg m → PrimeUpTo Q) where
  toFun := sourceSample cfg m
  invFun x := fun i => x ((sourceIndexEquiv cfg m).symm i)
  left_inv x := by funext i; simp only [sourceSample, Equiv.apply_symm_apply]
  right_inv x := by funext i; simp only [sourceSample, Equiv.symm_apply_apply]

def sourcePrimeShells {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (E : Fin (sourceHalfSize cfg m) → Finset (PrimeUpTo Q)) :
    SourceConstituent cfg m → Finset (PrimeUpTo Q) :=
  fun i => characterDoubleShell E (sourceIndexEquiv cfg m i)

theorem sourcePrimeShells_positive {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (E : Fin (sourceHalfSize cfg m) → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i)) :
    ∀ i, 0 < primeShellMass (sourcePrimeShells cfg m E i) :=
  fun i => characterDoubleShell_positive E hE (sourceIndexEquiv cfg m i)

def configurationPrimeShells {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) : SourceConstituent cfg m → Finset (PrimeUpTo Q) :=
  sourcePrimeShells cfg m (halfRoleShells bulk top m (configurationCells E cfg))

theorem sourceSample_prior_mass {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (E : Fin (sourceHalfSize cfg m) → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i))
    (w : Fin (sourceHalfSize cfg m + sourceHalfSize cfg m) → PrimeUpTo Q) :
    (constituentPrimePrior (schedule k 0) (sourceWidth cfg m)
      (sourcePrimeShells cfg m E) (sourcePrimeShells_positive cfg m E hE)).mass
      (sourceSample cfg m w) =
    (characterTuplePrior (characterDoubleShell E) (characterDoubleShell_positive E hE)).mass w := by
  change (∏ i, (primeShellPrior (characterDoubleShell E (sourceIndexEquiv cfg m i))
    (characterDoubleShell_positive E hE (sourceIndexEquiv cfg m i))).mass
      (w (sourceIndexEquiv cfg m i))) =
    ∏ i, (primeShellPrior (characterDoubleShell E i) (characterDoubleShell_positive E hE i)).mass (w i)
  exact (sourceIndexEquiv cfg m).prod_comp
    (fun i => (primeShellPrior (characterDoubleShell E i) (characterDoubleShell_positive E hE i)).mass (w i))

theorem sourceSample_cmean {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (E : Fin (sourceHalfSize cfg m) → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i))
    (F : (SourceConstituent cfg m → PrimeUpTo Q) → ℂ) :
    (characterTuplePrior (characterDoubleShell E) (characterDoubleShell_positive E hE)).cmean
      (fun w => F (sourceSample cfg m w)) =
    (constituentPrimePrior (schedule k 0) (sourceWidth cfg m)
      (sourcePrimeShells cfg m E) (sourcePrimeShells_positive cfg m E hE)).cmean F := by
  unfold FinitePrior.cmean
  rw [← (sourceSampleEquiv cfg m).sum_comp (fun x =>
    ((constituentPrimePrior (schedule k 0) (sourceWidth cfg m) (sourcePrimeShells cfg m E)
      (sourcePrimeShells_positive cfg m E hE)).mass x : ℂ) * F x)]
  apply Finset.sum_congr rfl
  intro w _
  change _ = ((constituentPrimePrior _ _ _ _).mass (sourceSample cfg m w) : ℂ) * F (sourceSample cfg m w)
  rw [sourceSample_prior_mass cfg m E hE w]

@[simp] theorem sourceSample_originalWord_true {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (w : Fin (sourceHalfSize cfg m + sourceHalfSize cfg m) → PrimeUpTo Q) :
    templateOriginalWord cfg m (sourceSample cfg m w) true =
      originalWord (fun i => w (Fin.castAdd (sourceHalfSize cfg m) i)) := by
  funext a
  exact congrArg w (sourceIndexEquiv_word_true cfg m a)

@[simp] theorem sourceSample_originalWord_false {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (w : Fin (sourceHalfSize cfg m + sourceHalfSize cfg m) → PrimeUpTo Q) :
    templateOriginalWord cfg m (sourceSample cfg m w) false =
      originalWord (fun i => w (Fin.natAdd (sourceHalfSize cfg m) i)) := by
  funext a
  exact congrArg w (sourceIndexEquiv_word_false cfg m a)

theorem sourceSample_mask {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ) (J : ℤ)
    (w : Fin (sourceHalfSize cfg m + sourceHalfSize cfg m) → PrimeUpTo Q) :
    characterDoubleMask (sourceHalfMask J) w =
      templateWordMask cfg m J (sourceSample cfg m w) true *
        templateWordMask cfg m J (sourceSample cfg m w) false := by
  simp only [templateWordMask, sourceSample_originalWord_true, sourceSample_originalWord_false,
    characterDoubleMask, sourceHalfMask]

@[simp] theorem sourcePrimeShells_word {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (E : Fin (sourceHalfSize cfg m) → Finset (PrimeUpTo Q)) (side : Bool) (a : Fin (m+1)) :
    sourcePrimeShells cfg m E ⟨(.word,side),a⟩ = E (Fin.castAdd (configCellCount cfg) a) := by
  cases side
  · unfold sourcePrimeShells
    rw [sourceIndexEquiv_word_false cfg m a]
    exact Fin.append_right _ _ _
  · unfold sourcePrimeShells
    rw [sourceIndexEquiv_word_true cfg m a]
    exact Fin.append_left _ _ _

@[simp] theorem configurationPrimeShells_word {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (side : Bool) (a : Fin (m+1)) :
    configurationPrimeShells cfg m bulk top E ⟨(.word,side),a⟩ = roleShells bulk top m a := by
  unfold configurationPrimeShells
  rw [sourcePrimeShells_word cfg m _ side a]
  exact Fin.append_left _ _ _

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
