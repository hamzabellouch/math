import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ClosedLine
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Avg

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel
open OrdinaryCorrelations.FiniteIntegration
open OrdinaryCorrelations.SignedTrace

structure PrimeSystem where
  primes : Finset ℕ
  prime_mem : ∀ p ∈ primes, p.Prime
  core : Finset ℕ
  core_subset : core ⊆ primes

namespace PrimeSystem
abbrev Index (S : PrimeSystem) := {p // p ∈ S.primes}
def IsCore (S : PrimeSystem) (p : S.Index) : Prop := (p : ℕ) ∈ S.core
instance (S : PrimeSystem) (p : S.Index) : NeZero (p : ℕ) :=
  ⟨(S.prime_mem p p.property).ne_zero⟩
abbrev Residues (S : PrimeSystem) := ∀ p : S.Index, ZMod (p : ℕ)
abbrev CoreIndex (S : PrimeSystem) := {p : S.Index // S.IsCore p}
abbrev CoreResidues (S : PrimeSystem) := ∀ p : S.CoreIndex, ZMod (p.val : ℕ)

def epsilon : ℝ := 1 / 10000
def eta : ℝ := epsilon / 100
def kappa : ℝ := 400 / eta
def A : ℝ := Real.exp (2 * kappa)
def betaC : ℝ := (1 + A)⁻¹

def amplitude (S : PrimeSystem) (p : S.Index) : ℝ := if S.IsCore p then A else 1
def beta (S : PrimeSystem) (p : S.Index) : ℝ := (1 + S.amplitude p)⁻¹

def harmonicCore (S : PrimeSystem) : ℝ := ∑ p : S.CoreIndex, (p.val : ℝ)⁻¹

def shiftCore (S : PrimeSystem) (x : S.CoreResidues) (b : ℤ) : S.CoreResidues :=
  fun p => x p + (b : ZMod (p.val : ℕ))
def restrictCore (S : PrimeSystem) (x : S.Residues) : S.CoreResidues := fun p => x p.val

def cutoffCount (S : PrimeSystem) (d : ℕ) (x : S.CoreResidues) : ℕ :=
  (univ.filter (fun p : S.CoreIndex => x p = 0 ∧ ¬(p.val : ℕ) ∣ d)).card

structure Cutoffs (S : PrimeSystem) (T : ℝ) where
  value : ℕ → S.CoreResidues → ℝ
  nonneg : ∀ d x, 0 ≤ value d x
  le_one : ∀ d x, value d x ≤ 1
  support : ∀ d x, (S.cutoffCount d x : ℝ) < S.harmonicCore - T * Real.sqrt S.harmonicCore →
    value d x = 0

variable {h ℓ : ℕ}

def occurrenceCount (S : PrimeSystem) (w : ClosedLine h ℓ) (p : S.Index) : ℕ :=
  (univ.filter (fun i => (p : ℕ) ∣ w.label i)).card

def IsFixed (S : PrimeSystem) (w : ClosedLine h ℓ) (p : S.Index) : Prop :=
  (∃ i, (p : ℕ) ∣ w.label i) ∧ (S.IsCore p ∨ 2 ≤ S.occurrenceCount w p)

abbrev FixedIndex (S : PrimeSystem) (w : ClosedLine h ℓ) := {p : S.Index // S.IsFixed w p}
abbrev FreeIndex (S : PrimeSystem) (w : ClosedLine h ℓ) := {p : S.Index // ¬S.IsFixed w p}
abbrev FreeCoreIndex (S : PrimeSystem) (w : ClosedLine h ℓ) :=
  {p : S.FreeIndex w // S.IsCore p.val}
abbrev FreeCenterIndex (S : PrimeSystem) (w : ClosedLine h ℓ) :=
  {p : S.FreeIndex w // ¬S.IsCore p.val}
abbrev FixedResidues (S : PrimeSystem) (w : ClosedLine h ℓ) :=
  ∀ p : S.FixedIndex w, ZMod (p.val : ℕ)
abbrev FreeCoreResidues (S : PrimeSystem) (w : ClosedLine h ℓ) :=
  ∀ p : S.FreeCoreIndex w, ZMod (p.val.val : ℕ)
abbrev FreeCenterResidues (S : PrimeSystem) (w : ClosedLine h ℓ) :=
  ∀ p : S.FreeCenterIndex w, ZMod (p.val.val : ℕ)

def splitResidues (S : PrimeSystem) (w : ClosedLine h ℓ) :
    S.Residues ≃ S.FixedResidues w × (S.FreeCoreResidues w × S.FreeCenterResidues w) :=
  (Equiv.piEquivPiSubtypeProd (S.IsFixed w) (fun p : S.Index => ZMod (p : ℕ))).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.piEquivPiSubtypeProd
      (fun p : S.FreeIndex w => S.IsCore p.val) (fun p => ZMod (p.val : ℕ))))

def coreFromSplit (S : PrimeSystem) (w : ClosedLine h ℓ)
    (a : S.FixedResidues w) (b : S.FreeCoreResidues w) : S.CoreResidues := fun p =>
  if hp : S.IsFixed w p.val then a ⟨p.val, hp⟩ else b ⟨⟨p.val,hp⟩, p.property⟩

lemma restrictCore_merge (S : PrimeSystem) (w : ClosedLine h ℓ)
    (a : S.FixedResidues w) (b : S.FreeCoreResidues w) (c : S.FreeCenterResidues w) :
    S.restrictCore ((S.splitResidues w).symm (a,(b,c))) = S.coreFromSplit w a b := by
  ext p
  have hpc := p.property
  simp only [restrictCore, splitResidues, Equiv.symm_trans_apply,
    Equiv.piEquivPiSubtypeProd_symm_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.refl_symm, coreFromSplit]
  split_ifs <;> simp_all

def activity (p : ℕ) (x : ZMod p) (b : ℤ) : ℝ := if x + (b : ZMod p) = 0 then 1 else 0

def occurrenceFactor (S : PrimeSystem) (w : ClosedLine h ℓ) (p : S.Index)
    (i : Fin ℓ) (x : ZMod (p : ℕ)) : ℝ :=
  if (p : ℕ) ∣ w.label i then
    if S.IsCore p then A * activity p x (w.offset i.castSucc)
    else activity p x (w.offset i.castSucc) - theta / (p : ℝ)
  else 1

def primeFactor (S : PrimeSystem) (w : ClosedLine h ℓ) (p : S.Index)
    (x : ZMod (p : ℕ)) : ℝ :=
  ∏ i : Fin ℓ, S.occurrenceFactor w p i x *
    S.beta p ^ (if x + (w.offset i.castSucc : ZMod (p : ℕ)) = 0 then (1 : ℕ) else 0)

def cutoffProduct (S : PrimeSystem) (w : ClosedLine h ℓ) {T : ℝ}
    (cut : S.Cutoffs T) (x : S.CoreResidues) : ℝ :=
  ∏ i : Fin ℓ, cut.value (w.label i) (S.shiftCore x (w.offset i.castSucc)) *
    cut.value (w.label i) (S.shiftCore x (w.offset i.succ))

def kernel (S : PrimeSystem) (w : ClosedLine h ℓ) {T : ℝ}
    (cut : S.Cutoffs T) (x : S.Residues) : ℝ :=
  S.cutoffProduct w cut (S.restrictCore x) * ∏ p, S.primeFactor w p (x p)

lemma cutoffProduct_nonneg (S : PrimeSystem) (w : ClosedLine h ℓ) {T : ℝ}
    (cut : S.Cutoffs T) (x : S.CoreResidues) : 0 ≤ S.cutoffProduct w cut x := by
  exact prod_nonneg (fun i _ => mul_nonneg (cut.nonneg _ _) (cut.nonneg _ _))

lemma core_primeFactor_nonneg (S : PrimeSystem) (w : ClosedLine h ℓ) (p : S.Index)
    (hp : S.IsCore p) (x : ZMod (p : ℕ)) : 0 ≤ S.primeFactor w p x := by
  apply prod_nonneg
  intro i _
  apply mul_nonneg
  · simp only [occurrenceFactor, hp, ite_true]
    split_ifs
    · exact mul_nonneg (le_of_lt (Real.exp_pos _)) (by simp [activity]; positivity)
    · exact zero_le_one
  · apply pow_nonneg
    simp only [beta, amplitude, hp, ite_true, A]
    positivity

end PrimeSystem
end OrdinaryCorrelations.GraphKernel

end

end OAI
