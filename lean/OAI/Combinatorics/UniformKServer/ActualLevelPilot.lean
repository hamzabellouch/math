import Mathlib
import OAI.Combinatorics.UniformKServer.PartitionLevel
import OAI.Combinatorics.UniformKServer.TierShortSchedule

namespace OAI

                                       
section

                                                                         
                                                                 
noncomputable section
namespace UniformKServer.PartitionLevel.Input
open Finset PilotCompact
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

def longParameter (I : PartitionLevel.Input X N) (t : ℕ) : X→ℝ :=
  HeavyPilot.parameter I.r (HeavySchedule.centers I.r I.data.heavyFlag I.data.point t)

theorem long_bounds (I : PartitionLevel.Input X N) (t : ℕ) (p : X) :
    I.longParameter t p∈Set.Icc (0:ℝ) 1 := HeavyPilot.parameter_bounds _ _ _

theorem long_lip (I : PartitionLevel.Input X N) (t : ℕ) (p q : X) :
    |I.longParameter t p-I.longParameter t q|≤dist p q/I.r :=
  HeavyPilot.parameter_lip I.r I.r_pos _ p q

def shortProb (I : PartitionLevel.Input X N) (i : Fin I.height) : ℝ :=
  1/Real.sqrt (I.data.K i:ℝ)

theorem shortProb_bounds (I : PartitionLevel.Input X N) (i : Fin I.height) :
    I.shortProb i∈Set.Icc (0:ℝ) 1 := by
  have hk : (1:ℝ)≤I.data.K i := by exact_mod_cast (show 1≤I.data.K i by have := I.data.two i; omega)
  have hs : 1≤Real.sqrt (I.data.K i:ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hk)
  constructor
  · unfold shortProb; positivity
  · exact (div_le_one (by linarith)).mpr hs

def shortParameter (I : PartitionLevel.Input X N) (i : Fin I.height) (t : ℕ) : X→ℝ :=
  TierShortSchedule.parameter I.r (I.data.K i) (I.shortProb i) (I.shortProb_bounds i)
    (I.data.qualify i) I.center t

theorem short_bounds (I : PartitionLevel.Input X N) (i : Fin I.height) (t : ℕ) (p : X) :
    I.shortParameter i t p∈Set.Icc (0:ℝ) 1 := ShortRoster.parameter_bounds _ _ _ _

theorem short_lip (I : PartitionLevel.Input X N) (i : Fin I.height) (t : ℕ) (p q : X) :
    |I.shortParameter i t p-I.shortParameter i t q|≤8*(dist p q/I.r) := by
  simpa only [shortParameter,TierShortSchedule.parameter,mul_div_assoc] using ShortRoster.parameter_lip
    (TierShortSchedule.run I.r (I.data.K i) (I.shortProb i) (I.shortProb_bounds i)
      (I.data.qualify i) I.center t) I.center I.r I.r_pos p q

def longCharge (I : PartitionLevel.Input X N) (t : ℕ) : ℝ :=
  if ht : t<N then
    if HeavySchedule.trigger I.r (I.data.heavyFlag t)
        (HeavySchedule.centers I.r I.data.heavyFlag I.data.point t) (I.data.point t) then
      127*I.r*HeavyPilot.annulusMass I.r (I.μ ⟨t,ht⟩) (I.center ⟨t,ht⟩)
    else 0
  else 0

def shortCharge (I : PartitionLevel.Input X N) (i : Fin I.height) (t : ℕ) : ℝ :=
  if ht : t<N then
    if TierSchedule.trigger I.r (I.data.K i) (TierSchedule.run I.r (I.data.K i) (I.data.qualify i) I.center t)
        (I.data.qualify i) I.center ⟨t,ht⟩ then
      I.r*TierPilot.insertionMass I.P I.r (I.μ ⟨t,ht⟩) (I.center ⟨t,ht⟩)/(I.data.K i:ℝ)
    else 0
  else 0

theorem mass_bridge (r a : ℝ) (μ : X→ℝ) (x : X) :
    ballMass r a μ x=GeometricMass.mass μ x (a*r) := by
  unfold ballMass GeometricMass.mass
  rfl

theorem positive_inner (I : PartitionLevel.Input X N) (n : Fin N) :
    0<ballMass I.r I.P.gammaH (I.μ n) (I.center n) := by
  rw [mass_bridge]
  have h := (I.served n).trans (GeometricMass.mass_center _ (I.μ_nonneg n) _ _ (mul_pos I.P.gammaH_pos I.r_pos).le)
  linarith

theorem long_charge_nonneg (I : PartitionLevel.Input X N) (t : ℕ) : 0≤I.longCharge t := by
  unfold longCharge
  split_ifs with ht hn
  · apply mul_nonneg (mul_nonneg (by norm_num) I.r_pos.le)
    unfold HeavyPilot.annulusMass
    apply sum_nonneg
    intro p _
    split_ifs <;> [exact I.μ_nonneg ⟨t,ht⟩ p; exact le_rfl]
  all_goals exact le_rfl

theorem short_charge_nonneg (I : PartitionLevel.Input X N) (i : Fin I.height) (t : ℕ) :
    0≤I.shortCharge i t := by
  unfold shortCharge
  split_ifs with ht hn
  · exact div_nonneg (mul_nonneg I.r_pos.le
      (TierPilot.insertionMass_bounds I.P I.r I.r_pos.le _ (I.μ_nonneg ⟨t,ht⟩) _).1) (Nat.cast_nonneg _)
  all_goals exact le_rfl

theorem long_payment (I : PartitionLevel.Input X N) (t : ℕ) (μ : X→ℝ)
    (hμ : ∀ ht : t<N, μ=I.μ ⟨t,ht⟩) :
    I.longCharge t≤value I.r 1 512 μ (I.longParameter t)-
      value I.r 1 512 μ (I.longParameter (t+1)) := by
  by_cases ht : t<N
  · rw [hμ ht]
    unfold longCharge longParameter
    rw [dite_eq_left ht,HeavySchedule.centers]
    by_cases hi : HeavySchedule.trigger I.r (I.data.heavyFlag t)
        (HeavySchedule.centers I.r I.data.heavyFlag I.data.point t) (I.data.point t)
    · rw [ite_eq_left hi,HeavySchedule.step,ite_eq_left hi]
      have hx : I.data.point t=I.center ⟨t,ht⟩ := by simp only [LevelMap.Data.point,data,dite_eq_left ht]
      have hh : I.data.heavy ⟨t,ht⟩ := by obtain ⟨_,hh⟩ := hi.1; exact hh
      have hconc : ballMass I.r (100*512) (I.μ ⟨t,ht⟩) (I.center ⟨t,ht⟩)≤
          (1+I.P.deltaH)*ballMass I.r I.P.gammaH (I.μ ⟨t,ht⟩) (I.center ⟨t,ht⟩) := by
        simpa only [data,mass_bridge,show (100:ℝ)*512=51200 by norm_num] using hh
      rw [hx]
      exact HeavyPilot.heavy_gain I.r I.P.gammaH I.P.deltaH I.r_pos I.P.gammaH_pos
        (by linarith [I.P.gammaH_small]) I.P.deltaH_pos I.P.deltaH_small _ (I.μ_nonneg ⟨t,ht⟩)
        _ _ (by simpa only [hx] using hi.2) (I.positive_inner ⟨t,ht⟩) hconc
    · simp only [ite_eq_right hi,HeavySchedule.step,sub_self,le_refl]
  · have hf : ¬I.data.heavyFlag t := by rintro ⟨hnt,_⟩; exact ht hnt
    have hn : ¬HeavySchedule.trigger I.r (I.data.heavyFlag t)
        (HeavySchedule.centers I.r I.data.heavyFlag I.data.point t) (I.data.point t) := fun h => hf h.1
    simp only [longCharge,dite_eq_right ht,longParameter,HeavySchedule.centers,HeavySchedule.step,ite_eq_right hn,sub_self,le_refl]

theorem short_payment (I : PartitionLevel.Input X N) (i : Fin I.height)
    (hlarge : Real.exp (TierInsertion.lifetimeExponent I.P*DyadicTiers.value i.val)≤I.data.K i)
    (t : ℕ) (μ : X→ℝ) (hμ : ∀ ht : t<N, μ=I.μ ⟨t,ht⟩) :
    I.shortCharge i t≤Real.exp (-DyadicTiers.value i.val)*
      (value I.r I.P.sigma 204800 μ (I.shortParameter i t)-
        value I.r I.P.sigma 204800 μ (I.shortParameter i (t+1))) := by
  by_cases ht : t<N
  · rw [hμ ht]
    unfold shortCharge
    rw [dite_eq_left ht]
    by_cases hi : TierSchedule.trigger I.r (I.data.K i)
        (TierSchedule.run I.r (I.data.K i) (I.data.qualify i) I.center t) (I.data.qualify i) I.center ⟨t,ht⟩
    · rw [ite_eq_left hi]
      apply TierShortSchedule.insertion_payment I.P I.r _ I.r_pos (DyadicTiers.one_le_value i.val)
        (I.data.K i) (I.data.two i) hlarge (I.shortProb_bounds i) (I.data.qualify i) I.center ⟨t,ht⟩ hi
        (I.μ ⟨t,ht⟩) (I.μ_nonneg ⟨t,ht⟩) (I.positive_inner ⟨t,ht⟩)
      simpa only [data,mass_bridge] using hi.1
    · simp only [ite_eq_right hi,shortParameter,TierShortSchedule.parameter,TierShortSchedule.run,dite_eq_left ht,sub_self,mul_zero,le_refl]
  · simp only [shortCharge,dite_eq_right ht,shortParameter,TierShortSchedule.parameter,TierShortSchedule.run,sub_self,mul_zero,le_refl]

end UniformKServer.PartitionLevel.Input

end


end

end OAI
