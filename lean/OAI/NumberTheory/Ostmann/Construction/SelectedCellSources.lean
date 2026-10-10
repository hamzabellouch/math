import OAI.NumberTheory.Ostmann.Construction.InitialSourceFamily
import OAI.NumberTheory.Ostmann.Construction.NominalCenterSelectionBasic
import OAI.NumberTheory.Ostmann.Construction.SourcePriors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

def balancedCellSource (d : Decomposition) (c : ℝ) (hc : BalancedCellAfterTwo d c)
    (E : Finset ℕ) (hE : E.card≤2) : PrimeSource :=
  logCellPrimeSource c E (hc E hE).choose

theorem balancedCellSource_probability (d : Decomposition) (c : ℝ)
    (hc : BalancedCellAfterTwo d c) (E : Finset ℕ) (hE : E.card≤2) :
    (1/2:ℝ) ≤ (balancedCellSource d c hc E hE).law.mean (fun p => balancedPrimeIndicator d p) :=
  (hc E hE).choose_spec

theorem balancedCellSource_mass (d : Decomposition) (c : ℝ)
    (hc : BalancedCellAfterTwo d c) (E : Finset ℕ) (hE : E.card≤2)
    (p : (balancedCellSource d c hc E hE).Sample) :
    (balancedCellSource d c hc E hE).law.mass p =
      Ostmann.smoothPartition (Real.log (p:ℕ)-c)/((p:ℕ)*logCellMass c E) :=
  logCellPrior_mass c E (hc E hE).choose p

theorem balancedCellSource_avoids (d : Decomposition) (c : ℝ)
    (hc : BalancedCellAfterTwo d c) (E : Finset ℕ) (hE : E.card≤2)
    (p : (balancedCellSource d c hc E hE).Sample) : (p:ℕ)∉E :=
  (Finset.mem_sdiff.mp p.property).2

abbrev AuxiliaryIndex (k : ℕ) := Fin 3 ⊕ (Fin k × Fin 2)

@[simp] theorem card_auxiliaryIndex (k : ℕ) : Fintype.card (AuxiliaryIndex k)=3+2*k := by
  simp only [AuxiliaryIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

namespace NominalCenterArray
variable {d : Decomposition} {k : ℕ} {L J tb : ℝ} {w : Fin k → ℝ}

def topSource (C : NominalCenterArray d k L J tb w) (E : Finset ℕ) (hE : E.card≤2)
    (i : Fin 3) : PrimeSource := balancedCellSource d (C.top i) (C.top_balanced i) E hE

def compSource (C : NominalCenterArray d k L J tb w) (E : Finset ℕ) (hE : E.card≤2)
    (j : Fin k) (i : Fin 2) : PrimeSource :=
  balancedCellSource d (C.comp j i) (C.comp_balanced j i) E hE

def auxSource (C : NominalCenterArray d k L J tb w) (E : Finset ℕ) (hE : E.card≤2) :
    AuxiliaryIndex k → PrimeSource := Sum.elim (C.topSource E hE) (fun ji => C.compSource E hE ji.1 ji.2)

def sources (C : NominalCenterArray d k L J tb w) (E : Finset ℕ) (hE : E.card≤2)
    (b : ℕ) (bulk : PrimeSource) : SourceFamily :=
  initialSourceFamily b k bulk (C.topSource E hE) (C.compSource E hE)

def center (C : NominalCenterArray d k L J tb w) (b : ℕ) : ℕ → ℝ :=
  initialSourceValue b k 0 (fun i => (C.top i:ℝ)) (fun j i => (C.comp j i:ℝ))

theorem auxSource_balanced (C : NominalCenterArray d k L J tb w)
    (E : Finset ℕ) (hE : E.card≤2) (i : AuxiliaryIndex k) :
    (1/2:ℝ) ≤ (C.auxSource E hE i).law.mean (fun p => balancedPrimeIndicator d p) := by
  cases i with
  | inl i => exact balancedCellSource_probability d (C.top i) (C.top_balanced i) E hE
  | inr ji => exact balancedCellSource_probability d (C.comp ji.1 ji.2) (C.comp_balanced ji.1 ji.2) E hE

theorem center_top (C : NominalCenterArray d k L J tb w) (b : ℕ) (h : Bool) (i : Fin 3) :
    C.center b (2*b+(if h then 3 else 0)+i)=(C.top i:ℝ) :=
  initialSourceValue_top _ _ _ _ _ _ _

theorem center_comp (C : NominalCenterArray d k L J tb w) (b : ℕ)
    (h : Bool) (j : Fin k) (i : Fin 2) :
    C.center b (2*b+6+4*j+(if h then 2 else 0)+i)=(C.comp j i:ℝ) :=
  initialSourceValue_comp _ _ _ _ _ _ _ _

end NominalCenterArray
end Ostmann.Construction

end

end OAI
