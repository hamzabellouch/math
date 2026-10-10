import Mathlib
import OAI.Combinatorics.UniformKServer.DyadicTiers
import OAI.Combinatorics.UniformKServer.GeometricMass
import OAI.Combinatorics.UniformKServer.LevelMap

namespace OAI

                                     
section

/-! Instantiation of the level construction from the true post-request GeometricMass.mass.
Tier qualifications are precisely the source exponential GeometricMass.mass test. -/
noncomputable section
namespace UniformKServer.PartitionLevel
open Finset FiniteProbability FirstStructure GeometricMass
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)

structure Input (X : Type) [Fintype X] [MetricSpace X] (N : ℕ) where
  k : ℕ
  two : 2 ≤ k
  P : TierPilot.Parameters
  C : ℝ
  C_one : 1 ≤ C
  r : ℝ
  r_pos : 0< r
  base : X
  center : Fin N → X
  μ : Fin N → X → ℝ
  μ_nonneg : ∀ n x, 0 ≤ μ n x
  μ_total : ∀ n, ∑ x, μ n x ≤ k
  served : ∀ n, 1 ≤ μ n (center n)

namespace Input

def height (I : Input X N) : ℕ := DyadicTiers.last (Real.log I.k)+1
def localLog (I : Input X N) (n : Fin N) : ℝ :=
  Real.log (GeometricMass.mass (I.μ n) (I.center n) (20480000*I.r)/GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaL*I.r))

def data (I : Input X N) : LevelMap.Data X N I.height where
  r := I.r
  positive := I.r_pos
  K i := TierParameters.cutoff I.C (DyadicTiers.value i.val)
  two i := TierParameters.cutoff_two I.C _ I.C_one (DyadicTiers.one_le_value i.val)
  base := I.base
  center := I.center
  heavy n := GeometricMass.mass (I.μ n) (I.center n) (51200*I.r) ≤
    (1+I.P.deltaH)*GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaH*I.r)
  qualify i n := GeometricMass.mass (I.μ n) (I.center n) (20480000*I.r) ≤
    Real.exp (DyadicTiers.value i.val)*GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaL*I.r)

def order (I : Input X N) : List (Fin I.height) := List.ofFn id

theorem inner_one (I : Input X N) (n : Fin N) :
    1 ≤ GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaL*I.r) :=
  (I.served n).trans (mass_center _ (I.μ_nonneg n) _ _ (mul_pos I.P.gammaL_pos I.r_pos).le)

theorem outer_pos (I : Input X N) (n : Fin N) :
    0< GeometricMass.mass (I.μ n) (I.center n) (20480000*I.r) := by
  have h := (I.served n).trans (mass_center (I.μ n) (I.μ_nonneg n) (I.center n) (20480000*I.r) (mul_nonneg (by norm_num) I.r_pos.le))
  linarith

theorem localLog_nonneg (I : Input X N) (n : Fin N) : 0 ≤ I.localLog n := by
  have hi := I.inner_one n
  have ho : I.P.gammaL ≤ 20480000 := by linarith [I.P.gammaL_small,I.P.sigma_small]
  apply Real.log_nonneg
  apply (le_div_iff₀ (by linarith : 0< GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaL*I.r))).mpr
  simpa only [one_mul] using mass_mono (I.μ n) (I.μ_nonneg n) (I.center n) (mul_le_mul_of_nonneg_right ho I.r_pos.le)

theorem localLog_bound (I : Input X N) (n : Fin N) : I.localLog n ≤ Real.log I.k := by
  have hi := I.inner_one n
  have hip : 0< GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaL*I.r) := by linarith
  have ho := (mass_total (I.μ n) (I.μ_nonneg n) (I.center n) (20480000*I.r)).trans (I.μ_total n)
  apply Real.log_le_log (div_pos (I.outer_pos n) hip)
  apply (div_le_iff₀ hip).mpr
  have hk : (0:ℝ) ≤ I.k := Nat.cast_nonneg _
  nlinarith

theorem qualification (I : Input X N) (n : Fin N) (i : Fin I.height) :
    I.data.qualify i n ↔ I.localLog n ≤ DyadicTiers.value i.val := by
  have hi := I.inner_one n
  have hip : 0< GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaL*I.r) := by linarith
  have hratio := div_pos (I.outer_pos n) hip
  change _ ↔ Real.log _ ≤ _
  rw [←Real.exp_le_exp,Real.exp_log hratio,div_le_iff₀ hip]
  rfl

def cutoff (I : Input X N) (n : Fin N) : ℕ := DyadicTiers.last (I.localLog n)+1

theorem cutoff_le (I : Input X N) (n : Fin N) : I.cutoff n ≤ I.height := by
  exact Nat.add_le_add_right (DyadicTiers.last_mono _ _ (I.localLog_bound n)) 1

theorem prefix_exists (I : Input X N) (n : Fin N) :
    ∃ i∈I.order.take (I.cutoff n), I.data.qualify i n := by
  let j : Fin (I.cutoff n) := ⟨DyadicTiers.last (I.localLog n),by simp [cutoff]⟩
  let i := j.castLE (I.cutoff_le n)
  refine ⟨i,?_,?_⟩
  · rw [order,←Fin.ofFn_take_eq_take_ofFn (I.cutoff_le n)]
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · apply (I.qualification n i).mpr
    exact DyadicTiers.last_ge _

theorem prefix_sum (I : Input X N) (n : Fin N) :
    ((I.order.take (I.cutoff n)).map (fun i => DyadicTiers.value i.val)).sum ≤ 4*max 1 (I.localLog n) := by
  rw [order,List.map_take,List.map_ofFn,←Fin.ofFn_take_eq_take_ofFn (I.cutoff_le n),List.sum_ofFn]
  change (∑ j : Fin (I.cutoff n), DyadicTiers.value j.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range]
  exact DyadicTiers.prefix_sum _

end Input
end UniformKServer.PartitionLevel

end


end

end OAI
