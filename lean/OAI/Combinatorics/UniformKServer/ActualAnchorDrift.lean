import Mathlib
import OAI.Combinatorics.UniformKServer.AnchorScalar
import OAI.Combinatorics.UniformKServer.SelectedParkCoefficients
import OAI.Combinatorics.UniformKServer.PrefixMovement

namespace OAI

                                        
section

/-! Height-free hidden-motion drift of the actual parked-heavy potential.
The coefficient is evaluated in the old completed state at the true old
member, with no event-conditioned filtering assumption. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance labelDecEq (C : ℝ) (m : ℕ) : DecidableEq (Label X C m) := fun a b=>Classical.propDecidable (a=b)

def heavyCoefficient (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (l : LevelMap.HeavySlot X) : ℝ :=
  labelPark A D hk z j (Sum.inl l) t ω/KeySizeTracker.held (labelTracker A D hk z j (Sum.inl l)) t ω

def heavySelection (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (y : X) (j : Fin J) : Option (LevelMap.HeavySlot X) :=
  match word A D hk z t ω y j with
  | Sum.inl l => if dist ((heavyState A D hk z j t ω).center l) y<7*GeometricMass.radius A.R A.q j.val then some l else none
  | Sum.inr _ => none

theorem heavySelection_near (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (y : X) (j : Fin J) (l : LevelMap.HeavySlot X)
    (hl : heavySelection A D hk z t ω y j=some l) : nearHeavy A D hk z j t ω y l := by
  unfold heavySelection at hl
  cases he : word A D hk z t ω y j with
  | inr a => simp only [he] at hl; cases hl
  | inl a =>
    simp only [he] at hl
    split_ifs at hl with hd
    · have hal : a=l := Option.some.inj hl
      subst a
      have hc := (LevelMap.Data.key_heavy_iff ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t y l).mp he
      exact ⟨hc.1,by simpa only [dist_comm] using hd.le⟩

def heavyNear (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (y : X) (j : Fin J) : ℝ :=
  AnchorScalar.near (GeometricMass.radius A.R A.q j.val) (heavyCoefficient A D hk z j t ω)
    (heavyState A D hk z j t ω).center (word A D hk z t ω y j) y

theorem near_sum (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (y : X) (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    (∑ j : Fin J,heavyNear A D hk z t ω y j)≤(6/5)*132*(2+7/Real.log 2)*Real.log (k+1) := by
  have h := selected_coefficients A D hk z (heavySelection A D hk z t ω y) t ω y
    (fun j l hl=>heavySelection_near A D hk z t ω y j l hl) hdiam
  rw [←Fin.sum_univ_eq_sum_range] at h
  convert h using 1
  apply sum_congr rfl
  intro j _
  simp only [selectedVertices,selectedDen,dite_eq_left j.isLt,heavySelection,heavyNear,AnchorScalar.near]
  cases he : word A D hk z t ω y j with
  | inr a => simp only [Option.map_none,Option.getD_none,sum_empty,zero_div]
  | inl a =>
    dsimp only
    split_ifs <;> simp only [Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,sum_empty,zero_div]
    rfl

def heavyValue (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (j : Fin J) (t : ℕ) (ω : Ω) (l : Label X A.C k) (p : X) : ℝ :=
  AnchorScalar.value (GeometricMass.radius A.R A.q j.val) (heavyCoefficient A D hk z j t ω)
    (heavyState A D hk z j t ω).center l p

def memberDrift (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (a : Fin k) : ℝ :=
  ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*
    (heavyValue A D hk z j t ω (word A D hk z (t+1) ω (D.position (t+1) ω a) j) (D.position (t+1) ω a)-
     heavyValue A D hk z j t ω (word A D hk z t ω (D.position t ω a) j) (D.position t ω a))

theorem member_drift (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (a : Fin k) (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    memberDrift A D hk z t ω a≤
      (6/5)*132*(∑ j : Fin J,GeometricMass.radius A.R A.q j.val*
        PrefixMovement.diff (word A D hk z (t+1) ω (D.position (t+1) ω a) j)
          (word A D hk z t ω (D.position t ω a) j))+
      dist (D.position t ω a) (D.position (t+1) ω a)/3*
        ((6/5)*132*(2+7/Real.log 2)*Real.log (k+1)) := by
  have hc (j : Fin J) (l : LevelMap.HeavySlot X) : 0≤heavyCoefficient A D hk z j t ω l :=
    div_nonneg (labelPark_nonneg A D hk z j (Sum.inl l) t ω)
      (by have := (KeySizeTracker.held_range (labelTracker A D hk z j (Sum.inl l)) t ω).1; linarith)
  have h (j : Fin J) := AnchorScalar.member (GeometricMass.radius A.R A.q j.val) ((6/5)*132)
    (GeometricMass.radius_pos _ _ A.R_pos A.q_pos _) (heavyCoefficient A D hk z j t ω)
    (heavyState A D hk z j t ω).center (hc j) (by norm_num)
    (fun l=>label_individual A D hk z j (Sum.inl l) t ω hdiam)
    (word A D hk z t ω (D.position t ω a) j)
    (word A D hk z (t+1) ω (D.position (t+1) ω a) j) (D.position t ω a) (D.position (t+1) ω a)
  have hs := sum_le_sum (s:=univ) (fun j (_ : j∈(univ : Finset (Fin J)))=>h j)
  have hn := mul_le_mul_of_nonneg_left (near_sum A D hk z t ω (D.position t ω a) hdiam)
    (show 0≤dist (D.position t ω a) (D.position (t+1) ω a)/3 by positivity)
  simp only [sum_add_distrib,←mul_sum] at hs
  change memberDrift A D hk z t ω a≤_ at hs
  refine hs.trans ?_
  convert add_le_add (le_refl ((6/5)*132*(∑ j : Fin J,GeometricMass.radius A.R A.q j.val*
      PrefixMovement.diff (word A D hk z (t+1) ω (D.position (t+1) ω a) j) (word A D hk z t ω (D.position t ω a) j)))) hn using 1
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  unfold PrefixMovement.diff
  by_cases he : word A D hk z t ω (D.position t ω a) j=word A D hk z (t+1) ω (D.position (t+1) ω a) j
  · simp only [he,ite_true,mul_zero]
  · simp only [ite_eq_right he,ite_eq_right (Ne.symm he),mul_one]

end UniformKServer.PartitionTree

end


end

end OAI
