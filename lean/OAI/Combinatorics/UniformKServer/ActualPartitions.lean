import Mathlib
import OAI.Combinatorics.UniformKServer.HiddenCausality
import OAI.Combinatorics.UniformKServer.PartitionScales
import OAI.Combinatorics.UniformKServer.TierInsertion

namespace OAI

                                       
section

/-! The actual true-posterior partition, on every positive finite hidden law.
All inputs are the real post-request counts, not a fitted proxy mass. -/
noncomputable section
namespace UniformKServer.ActualPartitions
open Finset
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

structure Config (X : Type) where
  P : TierPilot.Parameters
  C : ℝ
  C_one : 1≤C
  C_large : TierInsertion.lifetimeExponent P≤C
  R : ℝ
  R_pos : 0<R
  q : ℝ
  q_pos : 0<q
  q_small : q≤1/2
  shiftH : 51200*q≤P.gammaH
  shiftL : 20480000*q≤P.gammaL
  base : X

namespace Config

def input (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) (ω : Ω) :
    PartitionScales.Input X N J where
  k := k
  two := hk
  P := A.P
  C := A.C
  C_one := A.C_one
  R := A.R
  R_pos := A.R_pos
  q := A.q
  q_pos := A.q_pos
  q_small := A.q_small
  shiftH := A.shiftH
  shiftL := A.shiftL
  base := A.base
  center n := D.request n.val ω
  μ n := HiddenFlow.current D (n.val+1) ω
  μ_nonneg n := (HiddenFlow.flow D).post_nonneg (n.val+1) ω
  μ_total n := ((HiddenFlow.flow D).post_total (n.val+1) ω).le
  served n := HiddenFlow.serving_mass D n.val ω

theorem lifetime_large (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω : Ω) (j : ℕ) (i : Fin ((A.input (N:=N) (J:=J) D hk ω).level j).height) :
    Real.exp (TierInsertion.lifetimeExponent A.P*DyadicTiers.value i.val)≤
      (((A.input (N:=N) (J:=J) D hk ω).level j).data.K i:ℝ) := by
  change _≤(TierParameters.cutoff A.C (DyadicTiers.value i.val):ℝ)
  calc
    _ ≤ Real.exp (A.C*DyadicTiers.value i.val) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right A.C_large (by linarith [DyadicTiers.one_le_value i.val]))
    _ ≤ _ := Nat.le_ceil _

theorem separation (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω : Ω) (n : Fin N) (p : X) :
    (∑ j∈range J, ((A.input (N:=N) (J:=J) D hk ω).level j).r*((A.input (N:=N) (J:=J) D hk ω).level j).separation n p)≤
      (A.input (N:=N) (J:=J) D hk ω).coefficient*(1+Real.log k)*dist (D.request n.val ω) p :=
  (A.input (N:=N) (J:=J) D hk ω).separation n p

theorem past_centers (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t : ℕ) (he : (D.filtration t).r ω v) (i : Fin N) (hi : i.val<t) :
    (A.input (J:=J) D hk ω).center i=(A.input (J:=J) D hk v).center i :=
  HiddenFlow.request_past D i.val t hi ω v he

theorem past_mass (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t : ℕ) (he : (D.filtration t).r ω v) (i : Fin N) (hi : i.val<t) :
    (A.input (J:=J) D hk ω).μ i=(A.input (J:=J) D hk v).μ i :=
  HiddenFlow.current_measurable D (i.val+1) t (by omega) ω v he

theorem past_heavy (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v) (i : Fin N) (hi : i.val<t) :
    ((A.input (J:=J) D hk ω).level j).data.heavy i ↔
      ((A.input (J:=J) D hk v).level j).data.heavy i := by
  change GeometricMass.mass ((A.input (J:=J) D hk ω).μ i) ((A.input (J:=J) D hk ω).center i) _ ≤ _ ↔ _
  dsimp only [PartitionLevel.Input.data,PartitionScales.Input.level]
  rw [A.past_mass (J:=J) D hk ω v t he i hi,A.past_centers (J:=J) D hk ω v t he i hi]
  rfl

theorem past_qualify (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v)
    (a : Fin ((A.input (N:=N) (J:=J) D hk ω).level j).height) (i : Fin N) (hi : i.val<t) :
    ((A.input (J:=J) D hk ω).level j).data.qualify a i ↔
      ((A.input (J:=J) D hk v).level j).data.qualify a i := by
  change GeometricMass.mass ((A.input (J:=J) D hk ω).μ i) ((A.input (J:=J) D hk ω).center i) _ ≤ _ ↔ _
  dsimp only [PartitionLevel.Input.data,PartitionScales.Input.level]
  rw [A.past_mass (J:=J) D hk ω v t he i hi,A.past_centers (J:=J) D hk ω v t he i hi]
  rfl

end Config
end UniformKServer.ActualPartitions

end


end

end OAI
