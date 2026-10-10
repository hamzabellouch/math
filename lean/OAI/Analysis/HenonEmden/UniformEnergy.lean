import OAI.Analysis.HenonEmden.RelativeLocalization

namespace OAI

section UniformEnergy

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff

lemma weighted_uniform_energy {n : ℕ} (hn : 3 ≤ n) {p q A B : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hsub : Subcritical n p q A B) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : Space n → ℝ, IsSolution n p q A B u v →
        weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A ≤ C := by
  let c₁ := ((n:ℝ)+B)/(q+1)-((n:ℝ)-2)
  let c₂ := ((n:ℝ)+A)/(p+1)
  let γ := c₁+c₂
  have hγ : 0 < γ := by dsimp [γ,c₁,c₂]; unfold Subcritical at hsub; linarith
  have hn2 : 0 ≤ (n:ℝ)-2 := by
    have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let K := (n:ℝ)-2+|(c₁-c₂)/2|
  have hK : 0 ≤ K := add_nonneg hn2 (abs_nonneg _)
  let ε := γ/(4*(1+K))
  have hε : 0 < ε := div_pos hγ (by positivity)
  have hεeq : (1+K)*ε=γ/4 := by
    dsimp [ε]
    field_simp
  obtain ⟨CP,hCP,hP⟩ := pressure_relative hn hp hq hε
  obtain ⟨CL,hCL,hL⟩ := localization_relative (by omega : 2 ≤ n) hp hq hε
  refine ⟨4*(CP+K*CL)/γ,by positivity,?_⟩
  intro u v h
  let Ef := weightedEnergy (eta n) u q B
  let Eg := weightedEnergy (eta n) v p A
  let Q := localQ (source u q B) (source v p A)
  let T := (q+1)⁻¹*weightedEnergy (w n) u q B+(p+1)⁻¹*weightedEnergy (w n) v p A-
      radialPressure (source u q B) (source v p A)
  have hEid : c₁*Ef+c₂*Eg=T+((n:ℝ)-2)*Q := h.closing_identity (by omega) hp hq
  have hT : T ≤ ε*(Ef+Eg)+CP := hP u v h
  have hQ : |Q|+|Ef-Eg| ≤ ε*(Ef+Eg)+CL := hL u v h
  have hcomb : γ/2*(Ef+Eg)=T+((n:ℝ)-2)*Q-((c₁-c₂)/2)*(Ef-Eg) := by
    dsimp only [γ]
    nlinarith [hEid]
  have hneg : -((c₁-c₂)/2)*(Ef-Eg) ≤ |(c₁-c₂)/2| *|Ef-Eg| := by
    simpa only [abs_mul,neg_mul] using neg_le_abs (((c₁-c₂)/2)*(Ef-Eg))
  have herror : ((n:ℝ)-2)*Q-((c₁-c₂)/2)*(Ef-Eg) ≤ K*(|Q|+|Ef-Eg|) := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self Q) hn2
    have h2 := mul_nonneg hn2 (abs_nonneg (Ef-Eg))
    have h3 := mul_nonneg (abs_nonneg ((c₁-c₂)/2)) (abs_nonneg Q)
    dsimp only [K]
    nlinarith [h1,hneg,h2,h3]
  have hclose : γ/2*(Ef+Eg) ≤ (1+K)*ε*(Ef+Eg)+CP+K*CL := by
    have hmul := mul_le_mul_of_nonneg_left hQ hK
    nlinarith [hcomb,herror,hT,hmul]
  rw [hεeq] at hclose
  apply (le_div_iff₀ hγ).mpr
  change (Ef+Eg)*γ ≤ 4*(CP+K*CL)
  nlinarith [hclose]

lemma IsSolution.unit_energy_le_weighted {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) :
    (∫⁻ x in ball (0:Space n) 1, ENNReal.ofReal (energyDensity u q B x)) ≤
      ENNReal.ofReal (weightedEnergy (eta n) u q B) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  rw [← h.weightedEnergyN_eq hn (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)]
  unfold weightedEnergyN
  rw [← lintegral_indicator measurableSet_ball]
  apply lintegral_mono_ae
  filter_upwards [ae_iff.mpr (by simp : volume {x : Space n | ¬ x ≠ 0}=0)] with x hx
  by_cases hb : x ∈ ball (0:Space n) 1
  · rw [indicator_of_mem hb,energyDensity_eq_source_mul h.positive_u q B hx,
      eta_eq_one (mem_ball_zero_iff.mp hb).le,one_mul]
  · rw [indicator_of_notMem hb]
    exact bot_le

lemma uniform_unit_energy {n : ℕ} (hn : 3 ≤ n) {p q A B : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hsub : Subcritical n p q A B) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : Space n → ℝ, IsSolution n p q A B u v →
        (∫⁻ x in ball (0:Space n) 1, ENNReal.ofReal (energyDensity u q B x)) ≤ ENNReal.ofReal C := by
  obtain ⟨C,hC,hbound⟩ := weighted_uniform_energy hn hp hq hsub
  refine ⟨C,hC,fun u v h => (h.unit_energy_le_weighted (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hEg : 0 ≤ weightedEnergy (eta n) v p A :=
    weightedEnergyN_nonneg (eta_nonneg n) (fun x => (h.positive_v x).le)
  linarith [hbound u v h]

end HenonLaneEmden
end
end UniformEnergy

end OAI
