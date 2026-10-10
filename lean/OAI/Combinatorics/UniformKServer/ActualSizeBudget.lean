import Mathlib
import OAI.Combinatorics.UniformKServer.LabelParks
import OAI.Combinatorics.UniformKServer.PartitionMovement
import OAI.Combinatorics.UniformKServer.KeyCountVariation

namespace OAI

                                       
section

/-! The fixed-slot entropy refresh budget, instantiated with actual keys and
counted coupled hidden members, independent of the number of time steps. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry RankTracking TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem key_count_eq (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (t : ℕ) (ω : Ω) :
    HiddenFlow.regionCount D (keyRegion A D hk z j l) t ω=
      KeyCountVariation.count (fun a=>word A D hk z t ω (D.position t ω a) j) l := by
  simp only [HiddenFlow.regionCount,keyRegion,KeyCountVariation.count,KeyCountVariation.indicator,
    mem_filter,mem_univ,true_and]
  apply sum_congr rfl
  intro a _
  by_cases he : word A D hk z t ω (D.position t ω a) j=l <;> simp [he]

theorem key_count_variation (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
      |HiddenFlow.regionCount D (keyRegion A D hk z j l) (t+1) ω-
       HiddenFlow.regionCount D (keyRegion A D hk z j l) t ω|)≤
      2*A.q*coordinateCost A D hk z t ω := by
  have h (j : Fin J) := KeyCountVariation.total
    (fun a=>word A D hk z (t+1) ω (D.position (t+1) ω a) j)
    (fun a=>word A D hk z t ω (D.position t ω a) j)
  calc
    _≤∑ j : Fin J,GeometricMass.radius A.R A.q j.val*(2*∑ a : Fin k,
      PrefixMovement.diff (word A D hk z (t+1) ω (D.position (t+1) ω a) j)
      (word A D hk z t ω (D.position t ω a) j)) := by
        apply sum_le_sum
        intro j _
        simp only [key_count_eq]
        exact mul_le_mul_of_nonneg_left (h j) (GeometricMass.radius_pos _ _ A.R_pos A.q_pos _).le
    _=_ := by
      simp only [coordinateCost,mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro j _
      simp only [GeometricMass.radius,radius,pow_succ]
      ring

def sizeRefresh (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (H : ℕ) : ℝ :=
  ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
    ∑ t∈range H,average D.weight (KeySizeTracker.charge (labelTracker A D hk z j l) t)

def sizeEndpoint (A : ActualPartitions.Config X) (k J : ℕ) : ℝ :=
  (∑ j : Fin J,GeometricMass.radius A.R A.q j.val)*(Fintype.card (Label X A.C k):ℝ)*
    (288*(k+1)*(1+KeySizeTracker.ell (k+1)))

theorem label_size_budget (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (l : Label X A.C k) (H : ℕ) :
    (∑ t∈range H,average D.weight (KeySizeTracker.charge (labelTracker A D hk z j l) t))≤
      144*KeySizeTracker.ell (k+1)*(∑ t∈range H,average D.weight (fun ω=>
        |HiddenFlow.regionCount D (keyRegion A D hk z j l) (t+1) ω-
         HiddenFlow.regionCount D (keyRegion A D hk z j l) t ω|))+
      288*(k+1)*(1+KeySizeTracker.ell (k+1)) :=
  KeySizePosterior.budget D _ (HiddenFlow.regionCount_range D _) H

theorem weighted_integral {I L : Type*} [Fintype I] [Fintype L] (r : I→ℝ)
    (w : Ω→ℝ) (H : ℕ) (f : I→L→ℕ→Ω→ℝ) :
    (∑ i,r i*∑ l,∑ t∈range H,average w (f i l t))=
      ∑ t∈range H,average w (fun ω=>∑ i,r i*∑ l,f i l t ω) := by
  simp only [average,mul_sum]
  rw [sum_comm]
  conv_lhs => arg 2; ext l; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  rw [sum_comm]
  conv_lhs => arg 2; ext i; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro l _
  ring

theorem size_budget (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (H : ℕ) :
    sizeRefresh A D hk z H≤288*KeySizeTracker.ell (k+1)*A.q*
      integral (TreeCountData.data D (map A D hk z)) H (coordinateCost A D hk z)+sizeEndpoint A k J := by
  have h := sum_le_sum (s:=univ) (fun j (_ : j∈(univ : Finset (Fin J)))=>
    mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) (fun l _=>label_size_budget A D hk z j l H))
      (GeometricMass.radius_pos _ _ A.R_pos A.q_pos j.val).le)
  have he : 0≤144*KeySizeTracker.ell (k+1) := by
    unfold KeySizeTracker.ell
    have hk' : (1:ℝ)≤k+1 := by have := Nat.cast_nonneg (α:=ℝ) k; linarith
    have := Real.log_nonneg hk'
    positivity
  have hd := sum_le_sum (s:=range H) (fun t _=>average_mono (fun ω=>(D.positive ω).le)
    (key_count_variation A D hk z t))
  simp only [average_mul] at hd
  have hdm := mul_le_mul_of_nonneg_left hd he
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum] at h
  have hex := weighted_integral (fun j : Fin J=>GeometricMass.radius A.R A.q j.val) D.weight H
    (fun j l t ω=>|HiddenFlow.regionCount D (keyRegion A D hk z j l) (t+1) ω-
      HiddenFlow.regionCount D (keyRegion A D hk z j l) t ω|)
  -- Reassociate constants, keeping the two finite Fubini identities explicit.
  change sizeRefresh A D hk z H≤_ at h
  have hrw : (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*
      (144*KeySizeTracker.ell (k+1)*(∑ l : Label X A.C k,∑ t∈range H,average D.weight (fun ω=>
        |HiddenFlow.regionCount D (keyRegion A D hk z j l) (t+1) ω-
          HiddenFlow.regionCount D (keyRegion A D hk z j l) t ω|))))=
      144*KeySizeTracker.ell (k+1)*(∑ t∈range H,average D.weight (fun ω=>
        ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*∑ l : Label X A.C k,
          |HiddenFlow.regionCount D (keyRegion A D hk z j l) (t+1) ω-
           HiddenFlow.regionCount D (keyRegion A D hk z j l) t ω|)) := by
    rw [←hex,mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  simp only [mul_add,sum_add_distrib] at h
  rw [hrw] at h
  simp only [←sum_mul,←mul_sum] at h hdm
  dsimp only [sizeEndpoint,integral,TreeCountData.data] at *
  simp only [card_univ] at h
  nlinarith only [h,hdm]

end UniformKServer.PartitionTree

end


end

end OAI
