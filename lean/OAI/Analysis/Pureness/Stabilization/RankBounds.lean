import OAI.Analysis.Pureness.Stabilization.RankCyclic

namespace OAI
noncomputable section
open scoped NNReal ENNReal Topology
open Filter
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace Positive

lemma power_cut_le (a : Positive A) (δ : ℝ≥0) (hδ : 0 < δ)
    (r : ℝ≥0) (hr : 0 < r) :
    power r (cut δ a) ≤ smul ((max ‖a.1‖₊ 1) ^ (r : ℝ) / δ) a := by
  change (cut δ a).1 ^ r ≤ _
  rw [CFC.nnrpow_eq_cfcₙ_real _ _ (cut δ a).2]
  change cfcₙ (fun t : ℝ => t ^ (r : ℝ))
      (cfcₙ (fun t : ℝ => max (t - δ) 0) a.1) ≤
    (↑((max ‖a.1‖₊ 1) ^ (r : ℝ) / δ) : ℝ) • a.1
  rw [← cfcₙ_comp' (fun t : ℝ => t ^ (r : ℝ)) (fun t : ℝ => max (t - δ) 0)
    a.1 (hg0 := Real.zero_rpow (by exact_mod_cast hr.ne'))]
  rw [← cfcₙ_const_mul_id (↑((max ‖a.1‖₊ 1) ^ (r : ℝ) / δ) : ℝ) a.1]
  apply (cfcₙ_le_iff (fun t : ℝ => max (t - δ) 0 ^ (r : ℝ))
    (fun t : ℝ => (↑((max ‖a.1‖₊ 1) ^ (r : ℝ) / δ) : ℝ) * t) a.1
    (hf0 := by simp [Real.zero_rpow (show (r : ℝ) ≠ 0 by exact_mod_cast hr.ne')])
    (ha := IsSelfAdjoint.of_nonneg a.2)).mpr
  intro t ht
  have ht0 := quasispectrum_nonneg_of_nonneg a.1 a.2 t ht
  have htM : t ≤ max ‖a.1‖ 1 := (le_abs_self t).trans
    ((NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a.1 ht
      (IsSelfAdjoint.of_nonneg a.2)).trans (le_max_left _ _))
  simp only [NNReal.coe_div, NNReal.coe_rpow, NNReal.coe_max, coe_nnnorm, NNReal.coe_one]
  by_cases htδ : t ≤ δ
  · rw [max_eq_right (sub_nonpos.mpr htδ), Real.zero_rpow (show (r : ℝ) ≠ 0 by exact_mod_cast hr.ne')]
    positivity
  · have hd : 0 < (δ : ℝ) := hδ
    have htδ' : (δ : ℝ) ≤ t := (lt_of_not_ge htδ).le
    have hM : 0 ≤ max ‖a.1‖ 1 := le_trans (norm_nonneg _) (le_max_left _ _)
    have hroot := Real.rpow_le_rpow (le_max_right (t - δ) 0)
      (max_le (by linarith) hM) r.2
    have hp : 0 ≤ (max ‖a.1‖ 1) ^ (r : ℝ) := Real.rpow_nonneg hM _
    have hratio : 1 ≤ t / (δ : ℝ) := (one_le_div hd).mpr htδ'
    calc
      max (t - δ) 0 ^ (r : ℝ) ≤ (max ‖a.1‖ 1) ^ (r : ℝ) := hroot
      _ ≤ (max ‖a.1‖ 1) ^ (r : ℝ) * (t / (δ : ℝ)) := by nlinarith
      _ = (max ‖a.1‖ 1) ^ (r : ℝ) / (δ : ℝ) * t := by ring

end Positive
namespace ExtendedTrace

theorem rank_cut_le_trace (τ : ExtendedTrace A) (a : Positive A) (δ : ℝ≥0) (hδ : 0 < δ) :
    τ.rank (Positive.cut δ a) ≤ (δ : ℝ≥0∞)⁻¹ * τ a := by
  let M : ℝ≥0 := max ‖a.1‖₊ 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hc : Tendsto (fun n => ((M ^ (Positive.rootExponent n : ℝ) / δ : ℝ≥0) : ℝ≥0∞))
      atTop (𝓝 ((δ : ℝ≥0∞)⁻¹)) := by
    simp only [div_eq_mul_inv, ENNReal.coe_mul, ENNReal.coe_inv hδ.ne']
    simpa using ENNReal.Tendsto.mul (root_scalars_tendsto_one M hM)
      (Or.inl one_ne_zero) (tendsto_const_nhds (x := (δ : ℝ≥0∞)⁻¹)) (Or.inr ENNReal.one_ne_top)
  have hc0 : (δ : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hctop : (δ : ℝ≥0∞)⁻¹ ≠ ∞ := by simp [hδ.ne']
  apply le_of_tendsto_of_tendsto (τ.tendsto_roots_rank_all (Positive.cut δ a))
    (ENNReal.Tendsto.mul hc (Or.inl hc0) tendsto_const_nhds (Or.inr hctop))
  apply Eventually.of_forall
  intro n
  have h := τ.monotone (Positive.power_cut_le a δ hδ _ (Positive.rootExponent_pos n))
  simpa only [τ.map_smul] using h

theorem rank_eq_zero_iff (τ : ExtendedTrace A) (a : Positive A) :
    τ.rank a = 0 ↔ τ a = 0 := by
  constructor
  · intro h
    have hn : τ (Positive.normalize a) = 0 := by
      apply le_antisymm _ bot_le
      exact (τ.apply_le_rank _ (Positive.normalize_norm_le_one a)).trans (by rw [τ.rank_normalize, h]; exact le_rfl)
    have hscale := τ.map_smul (max ‖a.1‖₊ 1)⁻¹ a
    change τ (Positive.normalize a) = _ at hscale
    rw [hn] at hscale
    exact (mul_eq_zero.mp hscale.symm).resolve_left (by simp)
  · intro h
    rw [τ.rank_eq_iSup_cuts_all a]
    apply le_antisymm _ bot_le
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    simpa [h] using τ.rank_cut_le_trace a δ hδ

end ExtendedTrace
namespace Positive

lemma cut_cut (a : Positive A) (δ ε : ℝ≥0) : cut ε (cut δ a) = cut (δ + ε) a := by
  apply Subtype.ext
  change cfcₙ (fun t : ℝ => max (t - ε) 0)
    (cfcₙ (fun t : ℝ => max (t - δ) 0) a.1) = _
  rw [← cfcₙ_comp' (fun t : ℝ => max (t - ε) 0) (fun t : ℝ => max (t - δ) 0) a.1
    (hg0 := by simp) (hf0 := by simp)]
  apply cfcₙ_congr
  intro t _
  change max (max (t - δ) 0 - ε) 0 = max (t - ↑(δ + ε)) 0
  rw [NNReal.coe_add]
  by_cases ht : t ≤ δ
  · rw [max_eq_right (sub_nonpos.mpr ht)]
    have hL : max ((0 : ℝ) - (ε : ℝ)) 0 = 0 := max_eq_right (sub_nonpos.mpr ε.2)
    have hR : max (t - ((δ : ℝ) + (ε : ℝ))) 0 = 0 :=
      max_eq_right (sub_nonpos.mpr (ht.trans (le_add_of_nonneg_right ε.2)))
    exact hL.trans hR.symm
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge ht))]
    congr 1
    ring

end Positive
namespace ExtendedTrace

theorem trace_le_norm_mul_rank (τ : ExtendedTrace A) (a : Positive A) :
    τ a ≤ (‖a.1‖₊ : ℝ≥0∞) * τ.rank a := by
  by_cases hz : a.1 = 0
  · have ha : a = Positive.zero := Subtype.ext hz
    rw [ha, τ.map_zero]
    exact bot_le
  · let s : ℝ≥0 := ‖a.1‖₊
    have hs : 0 < s := nnnorm_pos.mpr hz
    let b := Positive.smul s⁻¹ a
    have hb : ‖b.1‖ ≤ 1 := by
      change ‖((s⁻¹ : ℝ≥0) : ℝ) • a.1‖ ≤ 1
      rw [norm_smul, NNReal.norm_eq, NNReal.coe_inv]
      change (s : ℝ)⁻¹ * (s : ℝ) ≤ 1
      rw [inv_mul_cancel₀ (show (s : ℝ) ≠ 0 by exact_mod_cast hs.ne')]
    have heq : Positive.smul s b = a := by
      apply Subtype.ext
      change (s : ℝ) • (((s⁻¹ : ℝ≥0) : ℝ) • a.1) = a.1
      rw [smul_smul, NNReal.coe_inv, mul_inv_cancel₀ (show (s : ℝ) ≠ 0 by exact_mod_cast hs.ne'), one_smul]
    calc
      τ a = (s : ℝ≥0∞) * τ b := by simpa only [heq] using τ.map_smul s b
      _ ≤ (s : ℝ≥0∞) * τ.rank b := mul_le_mul_of_nonneg_left (τ.apply_le_rank b hb) bot_le
      _ = (s : ℝ≥0∞) * τ.rank a := by rw [τ.rank_smul _ (inv_pos.mpr hs)]

theorem controller_trace_bound (τ : ExtendedTrace A) (b c : Positive A)
    (δ : ℝ≥0) (hδ : 0 < δ) (hc : CuntzBelow c (Positive.cut δ b)) :
    τ.rank c ≤ (4 / (δ : ℝ≥0∞)) * τ (Positive.cut (3 * δ / 4) b) := by
  have hquarter : 0 < δ / 4 := div_pos hδ (by norm_num)
  have hsum : 3 * δ / 4 + δ / 4 = δ := by ring
  have hcut : Positive.cut (δ / 4) (Positive.cut (3 * δ / 4) b) = Positive.cut δ b := by
    rw [Positive.cut_cut, hsum]
  have h := τ.rank_cut_le_trace (Positive.cut (3 * δ / 4) b) (δ / 4) hquarter
  rw [hcut] at h
  have hcoeff : (↑(δ / 4) : ℝ≥0∞)⁻¹ = 4 / (δ : ℝ≥0∞) := by
    rw [ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
      ENNReal.inv_div (Or.inl (by norm_num : (4 : ℝ≥0∞) ≠ ∞))
        (Or.inl (by norm_num : (4 : ℝ≥0∞) ≠ 0))]
  rw [hcoeff] at h
  exact (τ.rank_le_of_cuntzBelow hc).trans h

theorem trace_cut_loss (τ : ExtendedTrace A) (a : Positive A) (ε : ℝ≥0) :
    τ a ≤ τ (Positive.cut ε a) + (ε : ℝ≥0∞) * τ.rank a := by
  let c : Positive A := ⟨a.1 - (Positive.cut ε a).1, sub_nonneg.mpr (Positive.cut_le ε a)⟩
  have hadd : Positive.add (Positive.cut ε a) c = a := Subtype.ext (add_sub_cancel _ _)
  have hca : c ≤ a := sub_le_self _ (Positive.cut ε a).2
  have hn : ‖c.1‖₊ ≤ ε := Positive.norm_sub_cut_le ε a
  have hc : τ c ≤ (ε : ℝ≥0∞) * τ.rank a := by
    calc
      τ c ≤ (‖c.1‖₊ : ℝ≥0∞) * τ.rank c := τ.trace_le_norm_mul_rank c
      _ ≤ (ε : ℝ≥0∞) * τ.rank c := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) bot_le
      _ ≤ (ε : ℝ≥0∞) * τ.rank a := mul_le_mul_of_nonneg_left (τ.rank_monotone hca) bot_le
  calc
    τ a = τ (Positive.cut ε a) + τ c := by simpa only [hadd] using τ.map_add (Positive.cut ε a) c
    _ ≤ _ := add_le_add le_rfl hc

end ExtendedTrace

end CuntzTrace

end

end OAI
