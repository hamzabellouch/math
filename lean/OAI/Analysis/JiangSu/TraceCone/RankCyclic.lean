import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Rank
import OAI.Analysis.JiangSu.Absorption.FunctionalIntertwining

namespace OAI


noncomputable section
open scoped NNReal ENNReal Topology
open Filter

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma supported_cfc_factor (f : ℝ → ℝ) (hf : Continuous f) (hfpos : ∀ t, 0 ≤ f t)
    (δ : ℝ≥0) (hδ : 0 < δ) (hfzero : ∀ t : ℝ, t ≤ δ → f t = 0) :
    ∃ g : ℝ → ℝ, Continuous g ∧ g 0 = 0 ∧ ∀ t, g t * t * g t = f t := by
  let g := fun t => Real.sqrt (f t / max t δ)
  have hg : Continuous g := Real.continuous_sqrt.comp (hf.div
    (continuous_id.max continuous_const) (fun t => ne_of_gt (lt_of_lt_of_le hδ (le_max_right _ _))))
  refine ⟨g, hg, by simp [g, hfzero 0 δ.2], ?_⟩
  intro t
  by_cases ht : t ≤ δ
  · simp [g, hfzero t ht]
  · have ht0 : 0 < t := lt_trans hδ (lt_of_not_ge ht)
    dsimp [g]
    rw [max_eq_left (le_of_not_ge ht)]
    calc
      Real.sqrt (f t / t) * t * Real.sqrt (f t / t) = t * Real.sqrt (f t / t) ^ 2 := by ring
      _ = t * (f t / t) := by rw [Real.sq_sqrt (div_nonneg (hfpos t) ht0.le)]
      _ = f t := mul_div_cancel₀ (f t) ht0.ne'

namespace ExtendedTrace

lemma tracial_supported_cfc (τ : ExtendedTrace A) (x : A) (f : ℝ → ℝ)
    (hf : Continuous f) (hfpos : ∀ t, 0 ≤ f t) (δ : ℝ≥0) (hδ : 0 < δ)
    (hfzero : ∀ t : ℝ, t ≤ δ → f t = 0) :
    τ ⟨cfcₙ f (star x * x), cfcₙ_nonneg (fun t _ => hfpos t)⟩ =
      τ ⟨cfcₙ f (x * star x), cfcₙ_nonneg (fun t _ => hfpos t)⟩ := by
  obtain ⟨g, hg, hg0, hgf⟩ := supported_cfc_factor f hf hfpos δ hδ hfzero
  let a := Positive.starMul x
  let b := Positive.mulStar x
  have ha : IsSelfAdjoint a.1 := IsSelfAdjoint.of_nonneg a.2
  have hb : IsSelfAdjoint b.1 := IsSelfAdjoint.of_nonneg b.2
  have hid (c : Positive A) : cfcₙ g c.1 * c.1 * cfcₙ g c.1 = cfcₙ f c.1 := by
    calc
      _ = cfcₙ (fun t : ℝ => g t * t * g t) c.1 := by
        rw [cfcₙ_mul (fun t : ℝ => g t * t) g c.1,
          cfcₙ_mul g (fun t : ℝ => t) c.1, cfcₙ_id' ℝ c.1]
      _ = _ := cfcₙ_congr (fun t _ => hgf t)
  have hcomm : x * cfcₙ g a.1 = cfcₙ g b.1 * x :=
    cfc_intertwine a b x (by dsimp [a, b, Positive.starMul, Positive.mulStar]; exact (mul_assoc _ _ _).symm) g hg hg0
  let y := x * cfcₙ g a.1
  have hleft : star y * y = cfcₙ f a.1 := by
    dsimp [y]
    rw [star_mul, (cfcₙ_predicate g a.1).star_eq]
    calc
      _ = cfcₙ g a.1 * a.1 * cfcₙ g a.1 := by dsimp [a, Positive.starMul]; noncomm_ring
      _ = _ := hid a
  have hright : y * star y = cfcₙ f b.1 := by
    dsimp [y]
    rw [hcomm, star_mul, (cfcₙ_predicate g b.1).star_eq]
    calc
      _ = cfcₙ g b.1 * b.1 * cfcₙ g b.1 := by dsimp [b, Positive.mulStar]; noncomm_ring
      _ = _ := hid b
  have h := τ.tracial y
  convert h using 1
  · exact congrArg τ (Subtype.ext hleft.symm)
  · exact congrArg τ (Subtype.ext hright.symm)

lemma tracial_power_cut (τ : ExtendedTrace A) (x : A) (r : ℝ≥0) (hr : 0 < r)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    τ (Positive.power r (Positive.cut δ (Positive.starMul x))) =
      τ (Positive.power r (Positive.cut δ (Positive.mulStar x))) := by
  let f := fun t : ℝ => max (t - δ) 0 ^ (r : ℝ)
  have hf : Continuous f := by
    exact ((continuous_id.sub continuous_const).max continuous_const).rpow_const
      (fun _ => Or.inr (show (0 : ℝ) ≤ r from r.2))
  have hfpos : ∀ t, 0 ≤ f t := fun t => Real.rpow_nonneg (le_max_right _ _) _
  have hzero : ∀ t : ℝ, t ≤ δ → f t = 0 := by
    intro t ht
    simp [f, max_eq_right (sub_nonpos.mpr ht), Real.zero_rpow (show (r : ℝ) ≠ 0 by exact_mod_cast hr.ne')]
  have heq (a : Positive A) : (Positive.power r (Positive.cut δ a)).1 = cfcₙ f a.1 := by
    change (Positive.cut δ a).1 ^ r = _
    rw [CFC.nnrpow_eq_cfcₙ_real _ _ (Positive.cut δ a).2]
    exact (cfcₙ_comp' (fun t : ℝ => t ^ (r : ℝ)) (fun t : ℝ => max (t - δ) 0) a.1
      (hg0 := Real.zero_rpow (show (r : ℝ) ≠ 0 by exact_mod_cast hr.ne'))).symm
  convert τ.tracial_supported_cfc x f hf hfpos δ hδ hzero using 1
  · exact congrArg τ (Subtype.ext (heq _))
  · exact congrArg τ (Subtype.ext (heq _))

lemma tracial_power_le (τ : ExtendedTrace A) (x : A) (r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1) :
    τ (Positive.power r (Positive.starMul x)) ≤ τ (Positive.power r (Positive.mulStar x)) := by
  have hc : Tendsto (fun n => Positive.cut (Positive.rootExponent n) (Positive.starMul x))
      atTop (𝓝 (Positive.starMul x)) := by
    apply Positive.tendsto_cut
    simpa [Positive.rootExponent] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  apply (τ.lowerSemicontinuous.isClosed_preimage _).mem_of_tendsto
    ((Positive.power_continuous r).continuousAt.tendsto.comp hc)
  apply Eventually.of_forall
  intro n
  change τ (Positive.power r (Positive.cut (Positive.rootExponent n) (Positive.starMul x))) ≤ _
  rw [τ.tracial_power_cut x r hr _ (Positive.rootExponent_pos n)]
  exact τ.monotone (Positive.power_monotone hr1 (Positive.cut_le _ _))

theorem tracial_power (τ : ExtendedTrace A) (x : A) (r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1) :
    τ (Positive.power r (Positive.starMul x)) = τ (Positive.power r (Positive.mulStar x)) := by
  apply le_antisymm (τ.tracial_power_le x r hr hr1)
  simpa only [Positive.starMul, Positive.mulStar, star_star] using
    τ.tracial_power_le (star x) r hr hr1

theorem rank_tracial (τ : ExtendedTrace A) (x : A) :
    τ.rank (Positive.starMul x) = τ.rank (Positive.mulStar x) := by
  unfold rank
  congr 1
  funext n
  exact τ.tracial_power x _ (Positive.rootExponent_pos n) (Positive.rootExponent_le_one n)

end ExtendedTrace
namespace Positive

def conjugate (v : A) (b : Positive A) : Positive A :=
  ⟨star v * b.1 * v, star_left_conjugate_nonneg b.2 v⟩

lemma conjugate_eq_starMul (v : A) (b : Positive A) :
    conjugate v b = starMul (CFC.sqrt b.1 * v) := by
  apply Subtype.ext
  change star v * b.1 * v = star (CFC.sqrt b.1 * v) * (CFC.sqrt b.1 * v)
  rw [star_mul, (CFC.sqrt_nonneg b.1).star_eq]
  calc
    _ = star v * (CFC.sqrt b.1 * CFC.sqrt b.1) * v := by rw [CFC.sqrt_mul_sqrt_self b.1 b.2]
    _ = _ := by noncomm_ring

lemma mulStar_sqrt_mul_le (v : A) (b : Positive A) :
    mulStar (CFC.sqrt b.1 * v) ≤ smul (‖v * star v‖₊ + 1) b := by
  have h := CStarAlgebra.star_right_conjugate_le_norm_smul
    (a := CFC.sqrt b.1) (b := v * star v) (IsSelfAdjoint.of_nonneg (mul_star_self_nonneg v))
  rw [(CFC.sqrt_nonneg b.1).star_eq, CFC.sqrt_mul_sqrt_self b.1 b.2] at h
  have heq : (CFC.sqrt b.1 * v) * star (CFC.sqrt b.1 * v) =
      CFC.sqrt b.1 * (v * star v) * CFC.sqrt b.1 := by
    rw [star_mul, (CFC.sqrt_nonneg b.1).star_eq]
    noncomm_ring
  change (CFC.sqrt b.1 * v) * star (CFC.sqrt b.1 * v) ≤ _
  rw [heq]
  exact h.trans (smul_le_smul_of_nonneg_right (by simp) b.2)

end Positive
namespace ExtendedTrace

lemma rank_conjugate_le (τ : ExtendedTrace A) (v : A) (b : Positive A) :
    τ.rank (Positive.conjugate v b) ≤ τ.rank b := by
  rw [Positive.conjugate_eq_starMul, τ.rank_tracial]
  have h := τ.rank_monotone (Positive.mulStar_sqrt_mul_le v b)
  simpa only [τ.rank_smul (‖v * star v‖₊ + 1) (by positivity)] using h

theorem rank_le_of_cuntzBelow (τ : ExtendedTrace A) {a b : Positive A}
    (hab : CuntzBelow a b) : τ.rank a ≤ τ.rank b := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := by intro n; dsimp [ε]; positivity
  choose v hv using fun n => hab (ε n) (hε n)
  have ht : Tendsto (fun n => Positive.conjugate (v n) b) atTop (𝓝 a) := by
    rw [tendsto_subtype_rng, Metric.tendsto_atTop]
    intro δ hδ
    have he : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp he).2 δ hδ)
    refine ⟨N, fun n hn => ?_⟩
    change dist (star (v n) * b.1 * v n) a.1 < δ
    rw [dist_eq_norm]
    exact (hv n).trans (hN n hn)
  exact τ.rank_le_of_tendsto_all a (fun n => Positive.conjugate (v n) b) ht _
    (fun n => τ.rank_conjugate_le (v n) b)

theorem rank_eq_of_cuntzEquivalent (τ : ExtendedTrace A) {a b : Positive A}
    (hab : CuntzBelow a b) (hba : CuntzBelow b a) : τ.rank a = τ.rank b :=
  le_antisymm (τ.rank_le_of_cuntzBelow hab) (τ.rank_le_of_cuntzBelow hba)

end ExtendedTrace


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

end TraceCone

end

end OAI
