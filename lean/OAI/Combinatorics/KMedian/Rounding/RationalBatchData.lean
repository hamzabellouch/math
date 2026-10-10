import Mathlib
import OAI.Combinatorics.KMedian.Process.CountSource

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {I E : Type} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

def graph (G : I → Finset I) : Actions I I where
  source := id
  erase := fun h => univ.filter (fun i => h ∈ G i)
  ordinary := univ

theorem graph_eq (G : I → Finset I) : graph G=graphActions G := rfl

def heavy (Full : Actions I I) (H : Finset I) : Actions I (HeavyAction Full H) where
  source := fun e => Full.source (heavyParent Full H e)
  erase := Sum.elim (fun h => Full.erase h) (fun p => {p.val.2})
  ordinary := univ.filter (fun e : HeavyAction Full H => e.isLeft = true)

theorem heavy_eq (Full : Actions I I) (H : Finset I) : heavy Full H=heavyActions Full H := rfl

def balanced (D : Actions I E) (Δ : ℕ) : Finset E :=
  D.ordinary.filter (fun e => (D.erase e).card=Δ)

def conflicts (D : Actions I E) (Δ : ℕ) (e : E) : Finset E :=
  if e ∈ balanced D Δ then
    (balanced D Δ).filter (fun f => f≠e ∧ (D.erase e ∩ D.erase f).Nonempty) else ∅

omit [Fintype I] [Fintype E] in
theorem balanced_eq (D : Actions I E) (Δ : ℕ) : balanced D Δ=balancedActions D Δ := rfl

def amount (m : I → ℚ) : ℚ := ∑ i, max (1-m i) 0

def bias (m : I → ℚ) (p φ : ℚ) (i : I) : ℚ := if 1< m i then (1+φ)*p else p

def heavySet (m : I → ℚ) (b : ℚ) : Finset I :=
  univ.filter (fun i => max 1 (b*amount m)< m i)

def graphMass (G : I → Finset I) (g : ℚ) (h : I) : ℚ := g*((graph G).erase h).card

omit [DecidableEq I] in
theorem cast_amount (m : I → ℚ) : (amount m:ℝ)=SourceBalance.amount (fun i => (m i:ℝ)) := by
  simp only [amount,SourceBalance.amount,Rat.cast_sum,Rat.cast_max,Rat.cast_sub,Rat.cast_one,Rat.cast_zero]

omit [DecidableEq I] [Fintype I] in
theorem cast_bias (m : I → ℚ) (p φ : ℚ) (i : I) :
    (bias m p φ i:ℝ)=SourceBalance.bias (fun i => (m i:ℝ)) (p:ℝ) (φ:ℝ) i := by
  have he : (1:ℚ)< m i ↔ (1:ℝ)<(m i:ℝ) := by exact_mod_cast Iff.rfl
  simp only [bias,SourceBalance.bias,he]
  split_ifs <;> simp only [Rat.cast_mul,Rat.cast_add,Rat.cast_one]

theorem cast_graphMass (G : I → Finset I) (g : ℚ) (h : I) :
    (graphMass G g h:ℝ)=mass (g:ℝ) ((graphActions G).erase h) := by
  simp only [graphMass,graph_eq,Rat.cast_mul,Rat.cast_natCast,mass]

omit [DecidableEq I] in
theorem heavySet_eq (m : I → ℚ) (b : ℚ) :
    heavySet m b=univ.filter (fun i => max (1:ℝ) ((b:ℝ)*SourceBalance.amount (fun i => (m i:ℝ)))<(m i:ℝ)) := by
  ext i
  simp only [heavySet,mem_filter,mem_univ,true_and,← cast_amount]
  exact_mod_cast (Iff.rfl : max (1:ℚ) (b*amount m)< m i ↔ max (1:ℚ) (b*amount m)< m i)

end MetricKMedian.RationalBatchData
end
end

end OAI
