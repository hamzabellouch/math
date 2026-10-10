import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellIntegralFreezing
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellJointNormMass

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellReplacement
open scoped BigOperators
open PrimeProgression PrimeCellFreezing Characters.RationalHistory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} [NeZero M]

def tupleLog (N : ι → ℕ) (lo hi : ι → ℝ) (p : PrimeCellTuple N lo hi) : ι → ℝ :=
  fun i => Real.log ((p i).val:ℝ)

omit [Fintype ι] [DecidableEq ι] in
theorem tupleLog_mem [_fintypeIndex : Fintype ι] [_decidableEqIndex : DecidableEq ι]
    (N : ι → ℕ) (lo hi : ι → ℝ) (p : PrimeCellTuple N lo hi) :
    tupleLog N lo hi p ∈ logRectangle lo hi := by
  intro i _
  exact (mem_logPrimeSupport _ _ _ _).mp (p i).property |>.2.2

omit [Fintype ι] [DecidableEq ι] in
theorem exp_tupleLog [_fintypeIndex : Fintype ι] [_decidableEqIndex : DecidableEq ι]
    (N : ι → ℕ) (lo hi : ι → ℝ) (p : PrimeCellTuple N lo hi) :
    (fun i => Real.exp (tupleLog N lo hi p i)) = fun i => ((p i).val:ℝ) := by
  funext i
  apply Real.exp_log
  exact_mod_cast ((mem_logPrimeSupport _ _ _ _).mp (p i).property).2.1.pos

def smoothJointTestSum (N : ι → ℕ) (M : ℕ) [NeZero M] (lo hi Z : ι → ℝ)
    (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ) : ℂ :=
  ∑ p : PrimeCellTuple N lo hi, (tupleWeight N lo hi Z p:ℂ)*
    jointUnitTest F (fun i => ((p i).val:ZMod M))*f (fun i => ((p i).val:ℝ))

theorem jointTestSum_tupleWeight (N : ι → ℕ) (lo hi Z : ι → ℝ)
    (F : (ι → (ZMod M)ˣ) → ℂ) :
    jointComplexTestSum N M lo hi Z F =
      ∑ p : PrimeCellTuple N lo hi,(tupleWeight N lo hi Z p:ℂ)*jointUnitTest F (fun i => ((p i).val:ZMod M)) := by
  simp only [jointComplexTestSum,tupleWeight,Complex.ofReal_prod]

theorem smooth_freezing_bound (N : ι → ℕ) (lo hi Z : ι → ℝ) (hZ : ∀ i,0 ≤ Z i)
    (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ)
    {D mesh : ℝ} (hD : 0 ≤ D) (hm : 0 ≤ mesh) (hwidth : ∀ i,hi i-lo i ≤ mesh)
    (hf : ∀ z∈logRectangle lo hi,DifferentiableAt ℝ (fun y => f (fun j => Real.exp (y j))) z)
    (hd : ∀ z∈logRectangle lo hi,∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤ D)
    {base : ι → ℝ} (hbase : base∈logRectangle lo hi) :
    ‖smoothJointTestSum N M lo hi Z F f-
      f (fun j => Real.exp (base j))*jointComplexTestSum N M lo hi Z F‖  ≤ 
      (Fintype.card ι:ℝ)*D*mesh*jointAbsMass N M lo hi Z F := by
  classical
  let c : PrimeCellTuple N lo hi → ℂ := fun p =>
    (tupleWeight N lo hi Z p:ℂ)*jointUnitTest F (fun i => ((p i).val:ZMod M))
  have he := positive_weighted_freezing_bound Finset.univ c f lo hi (tupleLog N lo hi)
    (fun _ => base) hD hm hf hd (fun p _ => tupleLog_mem N lo hi p) (fun _ _ => hbase)
    (fun p _ => logRectangle_coordinate_dist_le lo hi hwidth (tupleLog_mem N lo hi p) hbase)
  simp_rw [exp_tupleLog] at he
  have hconst : (∑ p : PrimeCellTuple N lo hi,c p*f (fun j => Real.exp (base j))) =
      f (fun j => Real.exp (base j))*jointComplexTestSum N M lo hi Z F := by
    rw [← Finset.sum_mul,jointTestSum_tupleWeight]
    exact mul_comm _ _
  rw [hconst] at he
  exact he.trans (mul_le_mul_of_nonneg_left (coefficient_norm_mass_le N lo hi Z hZ F)
    (by positivity))

end Ostmann.Arithmetic.PrimeCellReplacement

end

end OAI
