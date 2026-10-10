import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer
import OAI.NumberTheory.Ostmann.Construction.Template

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

structure PrimeSource where
  candidates : Finset ℕ
  prime : ∀ p∈candidates, Nat.Prime p
  law : FinitePrior ↥candidates

abbrev PrimeSource.Sample (S : PrimeSource) := ↥S.candidates
abbrev SourceFamily := ℕ → PrimeSource

def sourceMass (sources : SourceFamily) (q : SmallSlot) : ℝ :=
  if h : q.value∈(sources q.origin).candidates then
    (sources q.origin).law.mass ⟨q.value,h⟩ else 0

theorem sourceMass_nonneg (sources : SourceFamily) (q : SmallSlot) :
    0 ≤ sourceMass sources q := by
  unfold sourceMass
  split_ifs
  · exact (sources q.origin).law.mass_nonneg _
  · exact le_rfl

def dependentProductPrior {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (μ : ∀ i, FinitePrior (κ i)) :
    FinitePrior (∀ i, κ i) where
  mass x := ∏ i, (μ i).mass (x i)
  mass_nonneg x := Finset.prod_nonneg (fun i _ => (μ i).mass_nonneg (x i))
  mass_total := by rw [← Fintype.prod_sum]; simp only [FinitePrior.mass_total, Finset.prod_const_one]

theorem dependentProductPrior_cmean {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (μ : ∀ i, FinitePrior (κ i))
    (f : ∀ i, κ i → ℂ) :
    (dependentProductPrior μ).cmean (fun x => ∏ i, f i (x i)) =
      ∏ i, (μ i).cmean (f i) := by
  simp only [FinitePrior.cmean, dependentProductPrior, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => ((μ i).mass x:ℂ)*f i x)).symm

abbrev SourceAssignment (sources : SourceFamily) (T : List SourceSlot) :=
  ∀ i : Fin T.length, (sources T[i].origin).Sample

def assignmentPrior (sources : SourceFamily) (T : List SourceSlot) :
    FinitePrior (SourceAssignment sources T) :=
  dependentProductPrior (fun i => (sources T[i].origin).law)

def assignedSlots (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) : List SmallSlot :=
  Template.sample T (fun i => (x i : ℕ))

theorem assignedSlots_mass (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) :
    ((assignedSlots sources T x).map (sourceMass sources)).prod =
      (assignmentPrior sources T).mass x := by
  simp only [assignedSlots, Template.sample, List.map_ofFn, List.prod_ofFn,
    assignmentPrior, dependentProductPrior]
  apply Finset.prod_congr rfl
  intro i hi
  simp [sourceMass]

theorem assignedSlots_prime (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) :
    ∀ q∈assignedSlots sources T x, Nat.Prime q.value := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact (sources T[i].origin).prime _ (x i).property

@[simp] theorem assignedSlots_length (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) : (assignedSlots sources T x).length=T.length := by
  exact Template.sample_length T _

end Ostmann.Construction

end

end OAI
