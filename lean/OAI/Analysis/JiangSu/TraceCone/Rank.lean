import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Weights

namespace OAI


noncomputable section
open scoped NNReal ENNReal Topology
open Filter

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace Positive

lemma rootExponent_pos (n : ℕ) : 0 < rootExponent n := by
  unfold rootExponent
  positivity

lemma rootExponent_le_one (n : ℕ) : rootExponent n ≤ 1 := by
  unfold rootExponent
  exact (div_le_one (by positivity)).mpr (by simp)

lemma rootExponent_antitone : Antitone rootExponent := by
  intro m n h
  unfold rootExponent
  exact one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right h 1)

lemma power_monotone {r : ℝ≥0} (hr : r ≤ 1) : Monotone (power (A := A) r) := by
  intro a b hab
  exact CFC.nnrpow_le_nnrpow ⟨r.2, hr⟩ hab

lemma power_continuous (r : ℝ≥0) : Continuous (power (A := A) r) := by
  apply Continuous.subtype_mk
  exact (CFC.continuousOn_nnrpow r).comp_continuous continuous_subtype_val (fun a => a.2)

lemma power_norm_le_one (r : ℝ≥0) (hr : 0 < r) (a : Positive A) (ha : ‖a.1‖ ≤ 1) :
    ‖(power r a).1‖ ≤ 1 := by
  change ‖a.1 ^ r‖ ≤ 1
  rw [CFC.norm_nnrpow a.1 hr a.2]
  exact Real.rpow_le_one (norm_nonneg _) ha r.2

lemma roots_monotone (a : Positive A) (ha : ‖a.1‖ ≤ 1) :
    Monotone (fun n => power (rootExponent n) a) := by
  intro m n hmn
  change a.1 ^ rootExponent m ≤ a.1 ^ rootExponent n
  rw [CFC.nnrpow_eq_cfcₙ_real a.1 _ a.2, CFC.nnrpow_eq_cfcₙ_real a.1 _ a.2]
  have hm : 0 < (rootExponent m : ℝ) := rootExponent_pos m
  have hn : 0 < (rootExponent n : ℝ) := rootExponent_pos n
  apply (cfcₙ_le_iff (fun t : ℝ => t ^ (rootExponent m : ℝ))
    (fun t : ℝ => t ^ (rootExponent n : ℝ)) a.1 (hf0 := Real.zero_rpow hm.ne')
    (hg0 := Real.zero_rpow hn.ne') (ha := IsSelfAdjoint.of_nonneg a.2)).mpr
  intro t ht
  have ht0 := quasispectrum_nonneg_of_nonneg a.1 a.2 t ht
  have ht1 : t ≤ 1 :=
    (le_abs_self t).trans
      ((NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a.1 ht
        (IsSelfAdjoint.of_nonneg a.2)).trans ha)
  exact Real.rpow_le_rpow_of_exponent_ge' ht0 ht1 hn.le (rootExponent_antitone hmn)

@[simp] lemma power_one (a : Positive A) : power 1 a = a :=
  Subtype.ext (CFC.nnrpow_one a.1 a.2)

lemma cut_norm_le_one (a : Positive A) (ha : ‖a.1‖ ≤ 1) (ε : ℝ≥0) :
    ‖(cut ε a).1‖ ≤ 1 :=
  (CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (show (cut ε a).1 ≤ a.1 from cut_le ε a) (cut ε a).2).trans ha

end Positive
namespace ExtendedTrace

lemma rank_eq_iSup (τ : ExtendedTrace A) (a : Positive A) (ha : ‖a.1‖ ≤ 1) :
    τ.rank a = ⨆ n : ℕ, τ (Positive.power (Positive.rootExponent n) a) := by
  exact (tendsto_atTop_iSup (τ.monotone.comp (Positive.roots_monotone a ha))).liminf_eq

theorem tendsto_roots_rank (τ : ExtendedTrace A) (a : Positive A) (ha : ‖a.1‖ ≤ 1) :
    Tendsto (fun n : ℕ => τ (Positive.power (Positive.rootExponent n) a)) atTop
      (𝓝 (τ.rank a)) := by
  rw [rank_eq_iSup τ a ha]
  exact tendsto_atTop_iSup (τ.monotone.comp (Positive.roots_monotone a ha))

theorem rank_monotone (τ : ExtendedTrace A) : Monotone τ.rank := by
  intro a b hab
  exact liminf_le_liminf (Eventually.of_forall fun n =>
    τ.monotone (Positive.power_monotone (Positive.rootExponent_le_one n) hab))

theorem apply_le_rank (τ : ExtendedTrace A) (a : Positive A) (ha : ‖a.1‖ ≤ 1) :
    τ a ≤ τ.rank a := by
  rw [rank_eq_iSup τ a ha]
  have h := le_iSup (fun n : ℕ => τ (Positive.power (Positive.rootExponent n) a)) 0
  simpa [Positive.rootExponent] using h

theorem rank_le_of_tendsto (τ : ExtendedTrace A) (a : Positive A) (ha : ‖a.1‖ ≤ 1)
    (u : ℕ → Positive A) (hu : ∀ n, ‖(u n).1‖ ≤ 1) (hlim : Tendsto u atTop (𝓝 a))
    (r : ℝ≥0∞) (hr : ∀ n, τ.rank (u n) ≤ r) : τ.rank a ≤ r := by
  rw [rank_eq_iSup τ a ha]
  apply iSup_le
  intro k
  apply (τ.lowerSemicontinuous.isClosed_preimage r).mem_of_tendsto
    ((Positive.power_continuous (Positive.rootExponent k)).continuousAt.tendsto.comp hlim)
  apply Eventually.of_forall
  intro n
  exact (le_iSup (fun j : ℕ => τ (Positive.power (Positive.rootExponent j) (u n))) k).trans
    (by simpa only [rank_eq_iSup τ (u n) (hu n)] using hr n)

theorem rank_eq_iSup_cuts (τ : ExtendedTrace A) (a : Positive A) (ha : ‖a.1‖ ≤ 1) :
    τ.rank a = ⨆ ε : ℝ≥0, ⨆ (_ : 0 < ε), τ.rank (Positive.cut ε a) := by
  apply le_antisymm
  · let ε : ℕ → ℝ≥0 := Positive.rootExponent
    apply τ.rank_le_of_tendsto a ha (fun n => Positive.cut (ε n) a)
      (fun n => Positive.cut_norm_le_one a ha (ε n))
    · apply Positive.tendsto_cut
      simpa [ε, Positive.rootExponent] using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
    · intro n
      exact le_iSup_of_le (ε n) (le_iSup_of_le (Positive.rootExponent_pos n) le_rfl)
  · exact iSup_le fun ε => iSup_le fun _ => τ.rank_monotone (Positive.cut_le ε a)

end ExtendedTrace
namespace Positive

lemma power_smul (r : ℝ≥0) (hr : 0 < r) (s : ℝ≥0) (a : Positive A) :
    power r (smul s a) = smul (s ^ (r : ℝ)) (power r a) := by
  apply Subtype.ext
  change ((s : ℝ) • a.1) ^ r = ((s ^ (r : ℝ) : ℝ≥0) : ℝ) • (a.1 ^ r)
  rw [CFC.nnrpow_eq_cfcₙ_real ((s : ℝ) • a.1) r (smul_nonneg s.2 a.2),
    CFC.nnrpow_eq_cfcₙ_real _ _ a.2, NNReal.coe_rpow,
    ← cfcₙ_comp_const_mul (s : ℝ) (fun t : ℝ => t ^ (r : ℝ)) a.1
      (hf0 := Real.zero_rpow (show (r : ℝ) ≠ 0 by exact_mod_cast hr.ne')),
    ← cfcₙ_const_mul ((s : ℝ) ^ (r : ℝ)) (fun t : ℝ => t ^ (r : ℝ)) a.1
      (h0 := Real.zero_rpow (show (r : ℝ) ≠ 0 by exact_mod_cast hr.ne'))]
  exact cfcₙ_congr fun t ht => Real.mul_rpow s.2
    (quasispectrum_nonneg_of_nonneg a.1 a.2 t ht)

def normalize (a : Positive A) : Positive A := smul (max ‖a.1‖₊ 1)⁻¹ a

lemma normalize_norm_le_one (a : Positive A) : ‖(normalize a).1‖ ≤ 1 := by
  change ‖(((max ‖a.1‖₊ 1)⁻¹ : ℝ≥0) : ℝ) • a.1‖ ≤ 1
  rw [norm_smul, NNReal.norm_eq, NNReal.coe_inv, NNReal.coe_max, coe_nnnorm, NNReal.coe_one]
  exact (inv_mul_le_one₀ (lt_of_lt_of_le zero_lt_one (le_max_right _ _))).mpr
    (le_max_left _ _)

lemma normalize_continuous : Continuous (normalize (A := A)) := by
  apply Continuous.subtype_mk
  change Continuous (fun a : Positive A => (↑((max ‖a.1‖₊ 1)⁻¹) : ℝ) • a.1)
  simp only [NNReal.coe_inv, NNReal.coe_max, coe_nnnorm, NNReal.coe_one]
  exact (((continuous_subtype_val.norm.max continuous_const).inv₀
    (fun a => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))).smul
      continuous_subtype_val)

end Positive
namespace ExtendedTrace

lemma root_scalars_tendsto_one (s : ℝ≥0) (hs : 0 < s) :
    Tendsto (fun n => ((s ^ (Positive.rootExponent n : ℝ) : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 1) := by
  have he : Tendsto (fun n => (Positive.rootExponent n : ℝ)) atTop (𝓝 0) := by
    simpa [Positive.rootExponent] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  simpa only [Function.comp_def, NNReal.rpow_zero, ENNReal.coe_one] using
    ENNReal.continuous_coe.continuousAt.tendsto.comp
      (tendsto_const_nhds.nnrpow he (Or.inl hs.ne'))

theorem rank_smul (τ : ExtendedTrace A) (s : ℝ≥0) (hs : 0 < s) (a : Positive A) :
    τ.rank (Positive.smul s a) = τ.rank a := by
  let u : ℕ → ℝ≥0∞ := fun n => (s ^ (Positive.rootExponent n : ℝ) : ℝ≥0)
  let v : ℕ → ℝ≥0∞ := fun n => τ (Positive.power (Positive.rootExponent n) a)
  have hu : Tendsto u atTop (𝓝 1) := root_scalars_tendsto_one s hs
  have heq : τ.rank (Positive.smul s a) = liminf (u * v) atTop := by
    unfold rank
    congr 1
    funext n
    rw [Positive.power_smul _ (Positive.rootExponent_pos n), τ.map_smul]
    rfl
  rw [heq]
  change liminf (u * v) atTop = liminf v atTop
  apply le_antisymm
  · have h := ENNReal.liminf_mul_le (u := u) (v := v) (f := atTop)
      (Or.inl (by rw [hu.limsup_eq]; exact one_ne_zero))
      (Or.inl (by rw [hu.limsup_eq]; exact ENNReal.one_ne_top))
    simpa only [hu.limsup_eq, one_mul] using h
  · have h := ENNReal.le_liminf_mul (u := u) (v := v) (f := atTop)
    simpa only [hu.liminf_eq, one_mul] using h

lemma rank_normalize (τ : ExtendedTrace A) (a : Positive A) :
    τ.rank (Positive.normalize a) = τ.rank a :=
  τ.rank_smul _ (inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _))) a

theorem tendsto_roots_rank_all (τ : ExtendedTrace A) (a : Positive A) :
    Tendsto (fun n : ℕ => τ (Positive.power (Positive.rootExponent n) a)) atTop
      (𝓝 (τ.rank a)) := by
  let s : ℝ≥0 := max ‖a.1‖₊ 1
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have heq : Positive.smul s (Positive.normalize a) = a := by
    apply Subtype.ext
    change (s : ℝ) • ((s⁻¹ : ℝ≥0) : ℝ) • a.1 = a.1
    rw [smul_smul, NNReal.coe_inv,
      mul_inv_cancel₀ (show (s : ℝ) ≠ 0 by exact_mod_cast hs.ne'), one_smul]
  have ht := ENNReal.Tendsto.mul (root_scalars_tendsto_one s hs) (Or.inl one_ne_zero)
    (τ.tendsto_roots_rank (Positive.normalize a) (Positive.normalize_norm_le_one a))
    (Or.inr ENNReal.one_ne_top)
  simp only [one_mul, τ.rank_normalize] at ht
  convert ht using 1
  funext n
  nth_rw 1 [← heq]
  rw [Positive.power_smul _ (Positive.rootExponent_pos n), τ.map_smul]

theorem rank_le_of_tendsto_all (τ : ExtendedTrace A) (a : Positive A)
    (u : ℕ → Positive A) (hlim : Tendsto u atTop (𝓝 a))
    (r : ℝ≥0∞) (hr : ∀ n, τ.rank (u n) ≤ r) : τ.rank a ≤ r := by
  rw [← τ.rank_normalize a]
  apply τ.rank_le_of_tendsto (Positive.normalize a) (Positive.normalize_norm_le_one a)
    (fun n => Positive.normalize (u n)) (fun n => Positive.normalize_norm_le_one (u n))
    (Positive.normalize_continuous.continuousAt.tendsto.comp hlim) r
  intro n
  simpa only [τ.rank_normalize] using hr n

theorem rank_eq_iSup_cuts_all (τ : ExtendedTrace A) (a : Positive A) :
    τ.rank a = ⨆ ε : ℝ≥0, ⨆ (_ : 0 < ε), τ.rank (Positive.cut ε a) := by
  apply le_antisymm
  · apply τ.rank_le_of_tendsto_all a (fun n => Positive.cut (Positive.rootExponent n) a)
    · apply Positive.tendsto_cut
      simpa [Positive.rootExponent] using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
    · intro n
      exact le_iSup_of_le (Positive.rootExponent n)
        (le_iSup_of_le (Positive.rootExponent_pos n) le_rfl)
  · exact iSup_le fun ε => iSup_le fun _ => τ.rank_monotone (Positive.cut_le ε a)

end ExtendedTrace

end TraceCone

end

end OAI
