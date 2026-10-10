import Mathlib
import OAI.Combinatorics.UniformKServer.CrossRule
import OAI.Combinatorics.UniformKServer.StarMovementData

namespace OAI

                                         
section

/-! Literal non-wholesale output movement with coefficient one on the parent.
The switch charge is the actual causal hysteresis charge. -/
noncomputable section
namespace UniformKServer.StarOutputMovement
open Finset StarRanks StarSchedules StarLower StarOutputData StarOutputFeasibility StarAllocator StarMovementData
open AllocationOutputs
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def alphaMove (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  StarOutputData.mass d (t+1) ω*variation (alpha d t ω) (alpha d (t+1) ω)
def sideMove (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : ℝ :=
  deficit d StarConstants.delta (t+1) ω*variation (side d hk t ω) (side d hk (t+1) ω)
def deficitMove (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ :=
  |deficit d StarConstants.delta (t+1) ω-deficit d StarConstants.delta t ω|
def expense (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : ℝ :=
  alphaMove d t ω+sideMove d hk t ω+deficitMove d t ω+StarMovementData.charge d t ω

theorem parts_nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    0 ≤ alphaMove d t ω ∧ 0 ≤ sideMove d hk t ω ∧ 0 ≤ deficitMove d t ω ∧
    0 ≤ StarMovementData.charge d t ω :=
  ⟨mul_nonneg (mass_nonneg d (t+1) ω) (sum_nonneg fun _ _ => abs_nonneg _),
   mul_nonneg (deficit_nonneg d StarConstants.delta (t+1) ω) (sum_nonneg fun _ _ => abs_nonneg _),
   abs_nonneg _,StarMovementData.charge_nonneg d t ω⟩

theorem one_move (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q₀ q₁ : ℝ)
    (hq : parentLower d (t+1) ω ≤ q₁)
    (hreg : deficit d StarConstants.delta (t+1) ω/2 ≤ StarOutputData.mass d (t+1) ω)
    (hs : (∑ i, alpha d t ω i)=1) :
    variation (one d t ω q₀) (one d (t+1) ω q₁) ≤ |q₁-q₀|+
      2*variation (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)+32*expense d hk t ω := by
  have h := rule_one_movement (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)
    (alpha d t ω) (alpha d (t+1) ω) q₀ q₁ (alpha_nonneg d t ω) hs
  have hm := mul_le_mul_of_nonneg_right (holes_one d hk (t+1) ω hq hreg)
    (show 0 ≤ variation (alpha d t ω) (alpha d (t+1) ω) from sum_nonneg fun _ _ => abs_nonneg _)
  change variation (one d t ω q₀) (one d (t+1) ω q₁) ≤ _ at h
  have hn := parts_nonneg d hk t ω
  dsimp only [expense,alphaMove] at *
  nlinarith only [h,hm,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]

theorem two_move (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q₀ q₁ : ℝ) (o : ι) :
    variation (two d hk t ω q₀ o) (two d hk (t+1) ω q₁ o) ≤ |q₁-q₀|+
      2*variation (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)+32*expense d hk t ω := by
  have h := rule_two_movement (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)
    (side d hk t ω) (side d hk (t+1) ω) q₀ q₁ (deficit d StarConstants.delta t ω)
    (deficit d StarConstants.delta (t+1) ω) o (deficit_nonneg d StarConstants.delta t ω)
    (deficit_nonneg d StarConstants.delta (t+1) ω) (side_nonneg d hk t ω) (side_nonneg d hk (t+1) ω)
  have hm := mul_le_mul_of_nonneg_left (side_sum d hk t ω)
    (abs_nonneg (deficit d StarConstants.delta (t+1) ω-deficit d StarConstants.delta t ω))
  change variation (two d hk t ω q₀ o) (two d hk (t+1) ω q₁ o) ≤ _ at h
  have hn := parts_nonneg d hk t ω
  dsimp only [expense,sideMove,deficitMove] at *
  nlinarith only [h,hm,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]

theorem down_move (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q₀ q₁ : ℝ) (o : ι)
    (hq : parentLower d (t+1) ω ≤ q₁)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=some o)
    (hs : (∑ i, alpha d t ω i)=1)
    (hreg : StarOutputData.mass d (t+1) ω < deficit d StarConstants.delta (t+1) ω/2)
    (hc : StarMovementData.charge d t ω=deficit d StarConstants.delta (t+1) ω) :
    variation (one d t ω q₀) (two d hk (t+1) ω q₁ o) ≤ |q₁-q₀|+
      2*variation (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)+32*expense d hk t ω := by
  have h := downcross (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω) (alpha d t ω)
    (side d hk (t+1) ω) q₀ q₁ (deficit d StarConstants.delta (t+1) ω) 4 11 o
    (alpha_nonneg d t ω) hs (deficit_nonneg d StarConstants.delta (t+1) ω)
    (side_nonneg d hk (t+1) ω) (side_sum d hk (t+1) ω) (holes_down d hk (t+1) ω hq o ho hreg.le)
  change variation (one d t ω q₀) (two d hk (t+1) ω q₁ o) ≤ _ at h
  have hn := parts_nonneg d hk t ω
  unfold expense
  rw [←hc] at h
  nlinarith only [h,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]

theorem up_move (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q₀ q₁ : ℝ) (o : ι)
    (hq : parentLower d (t+1) ω ≤ q₁) (hs : (∑ i, alpha d (t+1) ω i)=1)
    (hreg : 2*deficit d StarConstants.delta (t+1) ω < StarOutputData.mass d (t+1) ω)
    (hc : StarMovementData.charge d t ω=StarOutputData.mass d (t+1) ω) :
    variation (two d hk t ω q₀ o) (one d (t+1) ω q₁) ≤ |q₁-q₀|+
      2*variation (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)+32*expense d hk t ω := by
  have hreg' : deficit d StarConstants.delta (t+1) ω/2 ≤ StarOutputData.mass d (t+1) ω := by
    linarith [deficit_nonneg d StarConstants.delta (t+1) ω]
  have h := upcross (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω) (side d hk t ω)
    (alpha d (t+1) ω) q₀ q₁ (deficit d StarConstants.delta t ω) (deficit d StarConstants.delta (t+1) ω)
    (StarOutputData.mass d (t+1) ω) 4 11 o (alpha_nonneg d (t+1) ω) hs (deficit_nonneg d StarConstants.delta t ω)
    (side_nonneg d hk t ω) (side_sum d hk t ω) (holes_one d hk (t+1) ω hq hreg') (by linarith)
  change variation (two d hk t ω q₀ o) (one d (t+1) ω q₁) ≤ _ at h
  have hn := parts_nonneg d hk t ω
  unfold expense
  rw [←hc] at h
  change variation (two d hk t ω q₀ o) (one d (t+1) ω q₁) ≤ _+_+_*StarMovementData.charge d t ω+11*deficitMove d t ω at h
  nlinarith only [h,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]

theorem rule_move (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (q₀ q₁ : ℝ)
    (hq : parentLower d (t+1) ω ≤ q₁) (hr : StarCaps.wholesale d t ω=false) :
    variation (ruleOutput d hk t ω q₀) (ruleOutput d hk (t+1) ω q₁) ≤ |q₁-q₀|+
      2*variation (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω)+32*expense d hk t ω := by
  have hd := SideReferenceSchedule.not_reset_dominant hr
  change EpochGeometry.dominant (epoch d StarConstants.delta (t+1) ω)=
    EpochGeometry.dominant (epoch d StarConstants.delta t ω) at hd
  cases ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω) with
  | none =>
    rw [ho] at hd
    simp only [ruleOutput,ho,hd]
    by_cases ha : ∃ i, 0 < held d t ω i
    · obtain ⟨i,hi⟩ := ha
      apply one_move d hk t ω q₀ q₁ hq _ (alpha_sum d t ω i hi)
      simp only [deficit,hd,zero_div]
      exact mass_nonneg d (t+1) ω
    · have hz : ∀ i, held d t ω i=0 := fun i => le_antisymm
        (le_of_not_gt (fun h => ha ⟨i,h⟩)) (held_nonneg d t ω i)
      have hn := empty_next d t ω hr hz
      have he₀ : one d t ω q₀=fun _ => 0 := funext fun i => one_inactive d hk t ω q₀ i (hz i)
      have he₁ : one d (t+1) ω q₁=fun _ => 0 := funext fun i => one_inactive d hk (t+1) ω q₁ i (hn i)
      rw [he₀,he₁]
      simp only [variation,sub_self,abs_zero,sum_const_zero]
      have hp := parts_nonneg d hk t ω
      have hv : 0 ≤ ∑ i, |StarCaps.cap d (t+1) ω i-StarCaps.cap d t ω i| := sum_nonneg fun _ _ => abs_nonneg _
      unfold expense
      linarith [abs_nonneg (q₁-q₀),hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]
  | some o =>
    rw [ho] at hd
    have hs₀ := alpha_sum d t ω o (dominant_active d t ω o ho)
    have hs₁ := alpha_sum d (t+1) ω o (dominant_active d (t+1) ω o hd)
    have hstep := tag_step d t ω hr
    have hc := charge_step d t ω hr
    cases ht₀ : tag d t ω <;> cases ht₁ : tag d (t+1) ω <;>
      simp only [ruleOutput,ho,hd,ht₀,ht₁]
    · apply one_move d hk t ω q₀ q₁ hq _ hs₀
      have h := tag_valid d (t+1) ω
      simpa only [ht₁,SwitchTracker.valid] using h
    · have hh : StarOutputData.mass d (t+1) ω < deficit d StarConstants.delta (t+1) ω/2 := by
        by_contra hn
        simp only [ht₀,ht₁,SwitchTracker.update,ite_eq_right hn] at hstep
        cases hstep
      apply down_move d hk t ω q₀ q₁ o hq hd hs₀ hh
      simpa only [ht₀,SwitchTracker.charge,ite_eq_left hh] using hc
    · have hh : 2*deficit d StarConstants.delta (t+1) ω < StarOutputData.mass d (t+1) ω := by
        by_contra hn
        simp only [ht₀,ht₁,SwitchTracker.update,ite_eq_right hn] at hstep
        cases hstep
      apply up_move d hk t ω q₀ q₁ o hq hs₁ hh
      simpa only [ht₀,SwitchTracker.charge,ite_eq_left hh] using hc
    · exact two_move d hk t ω q₀ q₁ o

end UniformKServer.StarOutputMovement

end


end

end OAI
