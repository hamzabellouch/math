import OAI.Combinatorics.ThinTrees.ExtractionCriterion

namespace OAI

section
noncomputable section
open Filter
open scoped Topology
namespace StrongThinTree

def extractQ (r : ℕ) : ℕ := ⌊(1-(r:ℝ)^(-1/16:ℝ))*r⌋₊
def errorU (r : ℕ) : ℝ := (r:ℝ)^(-1/16:ℝ)
def resistanceT (r : ℕ) : ℝ := (r:ℝ)^(-1/2:ℝ)

lemma extractQ_bounds {r : ℕ} (hr : (4:ℝ) ≤ r) (hu : errorU r ≤ 1/4) :
    (r:ℝ)/2 ≤ extractQ r ∧ extractQ r ≤ r ∧
    (extractQ r:ℝ) ≤ (1-errorU r)*r ∧ (1-errorU r)*r-1 ≤ extractQ r := by
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hu0 : 0 ≤ errorU r := Real.rpow_nonneg hr0 _
  have ha : 0 ≤ (1-errorU r)*r := mul_nonneg (by linarith) hr0
  have hl := Nat.sub_one_lt_floor ((1-errorU r)*r)
  have hh := Nat.floor_le ha
  change (extractQ r:ℝ) ≤ (1-errorU r)*r at hh
  change (1-errorU r)*r-1 < (extractQ r:ℝ) at hl
  have hmul := mul_le_mul_of_nonneg_right hu hr0
  have hmul0 := mul_nonneg hu0 hr0
  refine ⟨by nlinarith,?_,hh,hl.le⟩
  have hqr : (extractQ r:ℝ) ≤ r := by nlinarith
  exact_mod_cast hqr

lemma negative_power_q_bound {x y : ℝ} (hx : 0 < x) (hxy : x/2 ≤ y) :
    y^(-31/40:ℝ) ≤ 2*x^(-31/40:ℝ) := by
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < x/2) hxy (by norm_num : (-31/40:ℝ) ≤ 0)
  have hp : (2:ℝ)^(31/40:ℝ) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have heq : (x/2)^(-31/40:ℝ)=x^(-31/40:ℝ)*(2:ℝ)^(31/40:ℝ) := by
    rw [Real.div_rpow hx.le (by norm_num), div_eq_mul_inv, ←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [heq] at hh
  exact hh.trans (by nlinarith [Real.rpow_nonneg hx.le (-31/40:ℝ)])

lemma extract_response_ratio {r q : ℕ} (hr : 0 < r) (hqr : (r:ℝ)/2 ≤ q)
    (hsmall : 64*((r:ℝ)^(-17/80:ℝ)+(r:ℝ)^(-15/16:ℝ)) < 1) :
    2*(16*((q:ℝ)^(-31/40:ℝ)/resistanceT r + 1/q)) < errorU r := by
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hqR : (0:ℝ) < q := lt_of_lt_of_le (by positivity) hqr
  have ht : 0 < resistanceT r := Real.rpow_pos_of_pos hrR _
  have hu : 0 < errorU r := Real.rpow_pos_of_pos hrR _
  have hpow := negative_power_q_bound hrR hqr
  have hdiv := div_le_div_of_nonneg_right hpow ht.le
  have hinv : 1/(q:ℝ) ≤ 2/(r:ℝ) := by
    apply (div_le_div_iff₀ hqR hrR).mpr
    nlinarith
  have hid : 64*((r:ℝ)^(-17/80:ℝ)+(r:ℝ)^(-15/16:ℝ))*errorU r =
      32*(2*(r:ℝ)^(-31/40:ℝ)/resistanceT r+2/(r:ℝ)) := by
    unfold errorU resistanceT
    rw [mul_add, add_mul]
    have h1 : (r:ℝ)^(-17/80:ℝ)*(r:ℝ)^(-1/16:ℝ) =
        (r:ℝ)^(-31/40:ℝ)/(r:ℝ)^(-1/2:ℝ) := by
      rw [←Real.rpow_add hrR, ←Real.rpow_sub hrR]
      norm_num
    have h2 : (r:ℝ)^(-15/16:ℝ)*(r:ℝ)^(-1/16:ℝ) = 1/(r:ℝ) := by
      rw [←Real.rpow_add hrR]
      norm_num [Real.rpow_neg_one]
    calc
      _ = 64*((r:ℝ)^(-17/80:ℝ)*(r:ℝ)^(-1/16:ℝ))+
          64*((r:ℝ)^(-15/16:ℝ)*(r:ℝ)^(-1/16:ℝ)) := by ring
      _ = _ := by rw [h1,h2]; ring
  have hh := mul_lt_mul_of_pos_right hsmall hu
  rw [one_mul,hid] at hh
  nlinarith

lemma eventual_extraction_numeric (qH : ℕ) : ∃R : ℕ, 4 ≤ R ∧ ∀r : ℕ, R ≤ r →
    qH ≤ extractQ r ∧ extractQ r ≤ r ∧
    (extractQ r:ℝ) < (1-2*(16*((extractQ r:ℝ)^(-31/40:ℝ)/resistanceT r+1/extractQ r)))*r := by
  have hu : Tendsto (fun r : ℕ => errorU r) atTop (𝓝 0) := by
    simpa [errorU, Function.comp_def, neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/16)).comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun r : ℕ => 64*((r:ℝ)^(-17/80:ℝ)+(r:ℝ)^(-15/16:ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def, neg_div] using (((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 17/80)).add
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 15/16))).const_mul 64).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ r : ℕ in atTop, 4 ≤ r ∧ 2*qH ≤ r ∧ errorU r ≤ 1/4 ∧
      64*((r:ℝ)^(-17/80:ℝ)+(r:ℝ)^(-15/16:ℝ)) < 1 := by
    filter_upwards [eventually_ge_atTop 4,eventually_ge_atTop (2*qH),
      hu.eventually_lt_const (by norm_num : (0:ℝ) < 1/4),
      hsmall.eventually_lt_const (by norm_num : (0:ℝ) < 1)] with r hr hq hu hs
    exact ⟨hr,hq,hu.le,hs⟩
  obtain ⟨R,hR⟩ := eventually_atTop.mp hevent
  refine ⟨max R 4,le_max_right _ _,fun r hr => ?_⟩
  obtain ⟨hr4,hqr,hu,hs⟩ := hR r ((le_max_left _ _).trans hr)
  have hrR : (4:ℝ) ≤ r := by exact_mod_cast hr4
  obtain ⟨hqlo,hqhi,hqfrac,_⟩ := extractQ_bounds hrR hu
  have hsmall' := extract_response_ratio (by omega : 0 < r) hqlo hs
  have hqH : (qH:ℝ) ≤ extractQ r := by
    have hh : (2:ℝ)*qH ≤ r := by exact_mod_cast hqr
    linarith
  refine ⟨by exact_mod_cast hqH,hqhi,?_⟩
  have hh := mul_lt_mul_of_pos_right hsmall' (show (0:ℝ) < r by exact_mod_cast (by omega : 0 < r))
  nlinarith

end StrongThinTree

end
end

end OAI
