import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SubtreeUnionWeightNonneg
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AvgAdd

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
noncomputable section
variable {S : PrimeSystem} {h ℓ : ℕ}

def localUnlitCount (w : ClosedLine h ℓ) (p : S.Index) (r : ZMod (p:ℕ)) : ℕ :=
  (univ.filter (fun i : Fin ℓ => (p:ℕ) ∣ w.label i ∧
    r+(w.offset i.castSucc : ZMod (p:ℕ)) ≠ 0)).card

def repeatedUnlitLocal (w : ClosedLine h ℓ) (p : S.Index) (r : ZMod (p:ℕ)) : ℕ :=
  if ¬S.IsCore p ∧ 2 ≤ S.occurrenceCount w p then localUnlitCount w p r else 0

def repeatedUnlitTotal (w : ClosedLine h ℓ) (r : S.Residues) : ℕ :=
  ∑ p, repeatedUnlitLocal w p (r p)

lemma center_tilt_point (w : ClosedLine h ℓ) (p : S.Index) (hc : ¬S.IsCore p)
    (r : ZMod (p:ℕ)) (z : ℝ) (hz : 0 ≤ z) :
    |S.primeFactor w p r| *z^(localUnlitCount w p r) ≤ (z/(p:ℝ))^(localUnlitCount w p r) := by
  have hp : (0:ℝ)<p := by exact_mod_cast S.prime_mem p p.property |>.pos
  have ht := theta_div_bounds p
  have hθ : theta ≤ 1 := by norm_num [theta,betaZ]
  have hb := beta_nonneg p
  have hb1 := beta_le_one p
  have hcprod : |S.primeFactor w p r| ≤ ((p:ℝ)⁻¹)^(localUnlitCount w p r) := by
    rw [primeFactor,abs_prod]
    calc
      _ ≤ ∏ i : Fin ℓ, if (p:ℕ) ∣ w.label i ∧ r+(w.offset i.castSucc : ZMod (p:ℕ)) ≠ 0
          then (p:ℝ)⁻¹ else 1 := by
        apply prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro i hi
        rw [abs_mul,abs_of_nonneg (pow_nonneg hb _)]
        apply (mul_le_mul_of_nonneg_left (pow_le_one₀ hb hb1) (abs_nonneg _)).trans
        simp only [mul_one]
        by_cases hd : (p:ℕ) ∣ w.label i
        · by_cases ha : r+(w.offset i.castSucc : ZMod (p:ℕ))=0
          · simp only [hd,ha,ne_eq,not_true_eq_false,and_false,ite_false,
              occurrenceFactor,hc,ite_true,activity]
            rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
            linarith [ht.1]
          · simp only [hd,ha,ne_eq,not_false_eq_true,and_self,ite_true,
              occurrenceFactor,hc,ite_false,activity,zero_sub,abs_neg,abs_of_nonneg ht.1]
            simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_right hθ (inv_nonneg.mpr hp.le)
        · simp [occurrenceFactor,hd]
      _ = _ := by rw [←prod_filter]; simp [localUnlitCount]
  calc
    _ ≤ ((p:ℝ)⁻¹)^(localUnlitCount w p r)*z^(localUnlitCount w p r) :=
      mul_le_mul_of_nonneg_right hcprod (pow_nonneg hz _)
    _ = _ := by rw [←mul_pow]; congr 1; simp [div_eq_mul_inv,mul_comm]

lemma center_tilt_mean (w : ClosedLine h ℓ) (p : S.Index) (hc : ¬S.IsCore p)
    (hm : 2 ≤ S.occurrenceCount w p) (z : ℝ) (hz : 1 ≤ z) (hzp : z^2 ≤ (p:ℝ)) :
    avg (fun r => |S.primeFactor w p r| *z^(localUnlitCount w p r)) ≤
      ((ℓ:ℝ)+1)*(p:ℝ)⁻¹ := by
  have hp : (0:ℝ)<p := by exact_mod_cast S.prime_mem p p.property |>.pos
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  have hq0 : 0 ≤ z/(p:ℝ) := div_nonneg hz0 hp.le
  have hq1 : z/(p:ℝ) ≤ 1 := (div_le_one hp).mpr (by nlinarith)
  have hq2 : (z/(p:ℝ))^2 ≤ (p:ℝ)⁻¹ := by
    rw [div_pow,div_le_iff₀ (sq_pos_of_pos hp)]
    calc
      z^2 ≤ (p:ℝ) := hzp
      _ = (p:ℝ)⁻¹*(p:ℝ)^2 := by field_simp
  calc
    _ ≤ avg (fun r : ZMod (p:ℕ) => (∑ i : Fin ℓ, activity p r (w.offset i.castSucc))+(p:ℝ)⁻¹) := by
      apply avg_mono
      intro r
      apply (center_tilt_point w p hc r z hz0).trans
      by_cases hl : ∃ i : Fin ℓ, (p:ℕ) ∣ w.label i ∧ r+(w.offset i.castSucc : ZMod (p:ℕ))=0
      · obtain ⟨i,hi,ha⟩ := hl
        have hs : 1 ≤ ∑ j : Fin ℓ, activity p r (w.offset j.castSucc) := by
          have hh := single_le_sum (fun j hj => activity_nonneg p r (w.offset j.castSucc)) (mem_univ i)
          simpa only [activity,ha,ite_true] using hh
        exact (pow_le_one₀ hq0 hq1).trans (by linarith [inv_nonneg.mpr hp.le])
      · have he : localUnlitCount w p r=S.occurrenceCount w p := by
          unfold localUnlitCount occurrenceCount
          congr 1
          ext i
          simp only [mem_filter,mem_univ,true_and]
          exact ⟨And.left,fun hd => ⟨hd,fun ha => hl ⟨i,hd,ha⟩⟩⟩
        rw [he]
        have hpow := pow_le_pow_of_le_one hq0 hq1 hm
        apply (hpow.trans hq2).trans
        exact le_add_of_nonneg_left (sum_nonneg (fun i hi => activity_nonneg p r _))
    _ = _ := by
      rw [OrdinaryCorrelations.SourceCylinder.avg_add',OrdinaryCorrelations.SourceCylinder.avg_sum',avg_const]
      simp only [activity_mean,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
