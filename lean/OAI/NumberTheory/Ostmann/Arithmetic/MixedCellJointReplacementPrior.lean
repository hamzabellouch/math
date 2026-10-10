import OAI.NumberTheory.Ostmann.Arithmetic.IntegerCell
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellJointReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.MixedCellJointReplacement
open scoped BigOperators
open PrimeCellReplacement
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mixedComplexTestSum (NI : ℕ) (N : ι → ℕ) (M : ℕ) [NeZero M]
    (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ)
    (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) : ℂ :=
  ∑ n ∈ IntegerCell.cellSupport NI loI hiI,
    ((Real.exp (-G)*φ (Real.log n-G) : ℝ) : ℂ)*
      jointComplexTestSum N M lo hi Z (F (n : ZMod M))

theorem mixedComplexTestSum_expanded (NI : ℕ) (N : ι → ℕ) (M : ℕ) [NeZero M]
    (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ)
    (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) :
    mixedComplexTestSum NI N M loI hiI G φ lo hi Z F =
      ∑ n ∈ IntegerCell.cellSupport NI loI hiI, ∑ p : PrimeCellTuple N lo hi,
        ((Real.exp (-G)*φ (Real.log n-G) : ℝ) : ℂ)*
        (∏ i, (((Z i*((p i).val : ℝ))⁻¹ : ℝ) : ℂ))*
        jointUnitTest (F (n : ZMod M)) (fun i => ((p i).val : ZMod M)) := by
  simp only [mixedComplexTestSum, jointComplexTestSum, Finset.mul_sum, mul_assoc]

theorem mixedComplexTestSum_eq_integer (NI : ℕ) (N : ι → ℕ) (M : ℕ) [NeZero M]
    (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ)
    (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) :
    mixedComplexTestSum NI N M loI hiI G φ lo hi Z F =
      ∑ r : ZMod M, (IntegerCell.integerResidueMass NI M r loI hiI G φ : ℂ)*
        jointComplexTestSum N M lo hi Z (F r) := by
  exact IntegerCell.complexTestSum_eq NI M loI hiI G φ
    (fun r => jointComplexTestSum N M lo hi Z (F r))

theorem mixedComplexTestSum_eq (NI : ℕ) (N : ι → ℕ) (M : ℕ) [NeZero M]
    (loI hiI G : ℝ) (φ : ℝ → ℝ) (lo hi Z : ι → ℝ)
    (F : ZMod M → (ι → (ZMod M)ˣ) → ℂ) :
    mixedComplexTestSum NI N M loI hiI G φ lo hi Z F =
      ∑ r : ZMod M, ∑ u : ι → (ZMod M)ˣ,
        (IntegerCell.integerResidueMass NI M r loI hiI G φ : ℂ)*
        (∏ i, (residueMass (N i) M (u i) (lo i) (hi i) (Z i) : ℂ))*F r u := by
  rw [mixedComplexTestSum_eq_integer]
  simp only [jointComplexTestSum_eq, Finset.mul_sum, mul_assoc]

end Ostmann.Arithmetic.MixedCellJointReplacement
end

end OAI
