import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrameWeighted

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion HistoryBulkFibreGiantApproximation
open HistoryBulkFibreIntegralReplacementFrame
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}

def density (r : Frame (l:=l) C outside) (mixed : Bool) : ℝ :=
  if mixed then (Frame.extractedDensity (C:=C) r.leftSource).re else 1

theorem density_nonneg (r : Frame (l:=l) C outside) (mixed : Bool) :
    0 ≤ density r mixed := by
  cases mixed
  · exact zero_le_one
  · simp only [density,ite_true,Frame.extractedDensity,Complex.ofReal_re]
    exact Finset.prod_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

@[simp] theorem density_cast (r : Frame (l:=l) C outside) (mixed : Bool) :
    (density r mixed : ℂ) = rootDensity r mixed := by
  cases mixed
  · rfl
  · simp only [density,rootDensity,ite_true,Frame.extractedDensity,Complex.ofReal_re]

theorem density_le_one (r : Frame (l:=l) C outside) (mixed : Bool) :
    density r mixed ≤ 1 := by
  have h := norm_rootDensity_le r mixed
  rw [←density_cast,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (density_nonneg r mixed)] at h
  exact h

theorem density_mem (r : Frame (l:=l) C outside) (mixed : Bool) :
    0 ≤ density r mixed ∧ density r mixed ≤ 1 :=
  ⟨density_nonneg r mixed,density_le_one r mixed⟩

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
