import OAI.NumberTheory.Ostmann.Construction.BaseFactors
import OAI.NumberTheory.Ostmann.Construction.CanonicalEnumeration
import OAI.NumberTheory.Ostmann.Section07SmoothPartitionBasic

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction

namespace FinitePrior

def pair {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinitePrior α) (ν : FinitePrior β) : FinitePrior (α×β) where
  mass x := μ.mass x.1*ν.mass x.2
  mass_nonneg x := mul_nonneg (μ.mass_nonneg _) (ν.mass_nonneg _)
  mass_total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,ν.mass_total,mul_one]
    exact μ.mass_total

theorem pair_cmean {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinitePrior α) (ν : FinitePrior β) (f : α×β → ℂ) :
    (μ.pair ν).cmean f=μ.cmean (fun x => ν.cmean (fun y => f (x,y))) := by
  simp only [cmean,pair,Fintype.sum_prod_type,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]
end FinitePrior

abbrev OuterSample (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource) :=
  giant.Sample×giant.Sample×SourceAssignment sources T

def outerPrior (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource) :
    FinitePrior (OuterSample sources T giant) :=
  giant.law.pair (giant.law.pair (assignmentPrior sources T))

def outerState (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : OuterSample sources T giant) (s : ℤ) : State :=
  ⟨s,x.1.val,x.2.1.val,assignedSlots sources T x.2.2⟩

def spectatorPrior (spectator : PrimeSource) (m : ℕ) : FinitePrior (Fin m → spectator.Sample) :=
  dependentProductPrior (fun _ : Fin m => spectator.law)

def spectatorList (spectator : PrimeSource) {m : ℕ} (x : Fin m → spectator.Sample) : List ℕ :=
  List.ofFn (fun i => (x i).val)

def actualCoefficient (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (X G : ℝ) (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (l : ℕ) (a : State) : ℂ :=
  canonicalCoefficient sources seed V outside
    (baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) g bins outside)
    Ostmann.smoothPartition G l a

def actualAmplitude (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g giantTransform : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ)
    (l : ℕ) : ℂ :=
  (spectatorPrior spectator m).cmean (fun ds =>
    let outside := spectatorList spectator ds
    (outerPrior sources (Template.current seed l) giant).cmean (fun x =>
      ∑ s : AllowedFrequency V l,
        let a := outerState sources (Template.current seed l) giant x s.val
        regularTransform g giantTransform outside a *
          actualCoefficient sources seed V X G g bins outside l a))

theorem outerState_giants_prime (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : OuterSample sources T giant) (s : ℤ) :
    Nat.Prime (outerState sources T giant x s).giantPlus ∧
      Nat.Prime (outerState sources T giant x s).giantMinus :=
  ⟨giant.prime _ x.1.property,giant.prime _ x.2.1.property⟩

theorem actualCoefficient_zero_frequency (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (X G : ℝ) (g : (p : ℕ) → ZMod p → ℂ)
    (bins : List ℕ → State → ℝ) (outside : List ℕ) (l : ℕ) (a : State)
    (ha : a.frequency=0) : actualCoefficient sources seed V X G g bins outside l a=0 := by
  unfold actualCoefficient canonicalCoefficient
  apply Finset.sum_eq_zero
  intro c hc
  have hn : ¬(decodeHistory sources seed V l a c).Supported V outside := by
    intro hs
    have hs0 := History.supported_root_frequency_ne_zero hs
    rw [decodeHistory_root,ha] at hs0
    exact hs0 rfl
  simp only [History.supportedWeight,hn,ite_false,mul_zero]

end Ostmann.Construction

end

end OAI
