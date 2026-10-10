import OAI.Probability.RadialTransition.KacComparison

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma family_pressure_data {t β : ℝ} {b S : ℕ → ℝ} (ht : 1 ≤ t) (hβ : 0 < β)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, b n) ≤ (t^2/8)/8) :
    Continuous (grandPressure (familyPotential t b S) t β) ∧
    (∀ h, 0 ≤ grandPressure (familyPotential t b S) t β h) ∧
    (∀ h, ∃ d ≥ 0, grandPressure (familyPotential t b S) t β h = h*d-canonicalThermo (familyPotential t b S) t β d) ∧
    (∀ h d, 0 ≤ d → h*d-canonicalThermo (familyPotential t b S) t β d ≤ grandPressure (familyPotential t b S) t β h) ∧
    (∀ d, 0 ≤ d → β*t/3456*d^2-β*t/2*d-1/t ≤ canonicalThermo (familyPotential t b S) t β d) := by
  have ht0 : 0 < t := by linarith
  have hst := stable_family_of_master ht0.le hb hS hs hs (fun _ => le_rfl) hrow
  have hφ := continuous_familyPotential hb hS hs t
  have hbd := bounded_familyPotential hb hS hs t
  have hc := fun r hr => familyPotential_nonpos_outer hb hS ht (r := r) hr
  have hcoerc : 2197*t*bumpIntegral⁻¹*(∑' n, b n)/2 ≤ t^2/16 := by nlinarith [sq_nonneg t]
  have hl := fun d hd => (familyCanonicalThermo_spec ht hb hS hs hcoerc hβ.le (d := d) hd).1
  refine ⟨grandPressure_continuous_h hφ hbd hst ht0 hβ.le hc,
    fun h => (grandPressure_spec hφ hbd hst ht0 hβ.le hc h).2.1,
    grandPressure_exists_maximizing_density hφ hbd hst ht0 hβ.le hc hl, ?_, ?_⟩
  · intro h d hd
    exact canonical_le_grand_dual hφ hbd hst ht0 hβ.le hd hc (hl d hd) h
  · intro d hd
    have hh := (familyCanonicalThermo_spec ht hb hS hs hcoerc hβ.le hd).2.1
    have he := div_le_div_of_nonneg_right (entropy_lower hd) ht0.le
    have halg : β/t*(t^2/3456*d^2-t^2/2*d) = β*t/3456*d^2-β*t/2*d := by field_simp
    rw [halg] at hh
    simp only [neg_div] at he
    linarith

lemma family_ideal_exists_active {t β a h U κ : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, b n) ≤ (t^2/8)/8)
    (hκ : 0 < κ) (hc : κ ≤ β*t/3456-β*a/2) (hU : 1 ≤ U)
    (hcut : h+β*t/2+1/t+1 ≤ κ*U) :
    ∃ u ∈ Icc (0:ℝ) U, ActiveShift (grandPressure (familyPotential t b S) t) a β h u := by
  obtain ⟨hcont, hpos, hmax, hdual, hH⟩ := family_pressure_data ht hβ hb hS hs hrow
  apply ideal_exists_active_of_density_bound hcont (mul_nonneg hβ.le ha) (hpos h) hmax hdual hH
    (hκ.trans_le hc) (by positivity) hU
  exact hcut.trans (mul_le_mul_of_nonneg_right hc (by linarith))

lemma family_active_bound {t β a h U κ u : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 < a)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, b n) ≤ (t^2/8)/8)
    (hκ : 0 < κ) (hc : κ ≤ β*t/3456-β*a/2) (hU : 1 ≤ U)
    (hcut : h+β*t/2+1/t+1 ≤ κ*U)
    (hu : ActiveShift (grandPressure (familyPotential t b S) t) a β h u) : u ∈ Icc (0:ℝ) U := by
  obtain ⟨_, hpos, hmax, hdual, hH⟩ := family_pressure_data ht hβ hb hS hs hrow
  apply active_density_bound (mul_pos hβ ha) (hpos h) hmax hdual hH
    (hκ.trans_le hc) (by positivity) hU _ hu
  exact hcut.trans (mul_le_mul_of_nonneg_right hc (by linarith))

lemma ideal_bddAbove_of_active {Q : Pressure} {a β h u : ℝ} (hu : ActiveShift Q a β h u) :
    BddAbove (range fun v => attractionBranch Q a v β h) :=
  ⟨attractionBranch Q a u β h, fun _ ⟨v, hv⟩ => hv ▸ hu v⟩

lemma ideal_nonneg_of_active {Q : Pressure} {a β h u : ℝ} (hu : ActiveShift Q a β h u)
    (hQ : 0 ≤ Q β h) : 0 ≤ idealAttraction Q a β h := by
  rw [idealAttraction_eq_of_active hu]
  have hh := hu 0
  simp only [attractionBranch, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] at hh
  exact hQ.trans hh

end RadialTransition
end

end OAI
