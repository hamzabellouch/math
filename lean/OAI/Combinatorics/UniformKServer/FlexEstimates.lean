import Mathlib
import OAI.Combinatorics.UniformKServer.RankData
import OAI.Combinatorics.UniformKServer.FineCaps

namespace OAI

                                    
section

/-! Persistent endpoint interpolation of the noncore ranks and its true
parameter error. The endpoints and the tolerance are the manuscript's ones. -/
noncomputable section
namespace UniformKServer.FlexEstimates
open Finset RankFunctions RankData RankTracking
open scoped Classical
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

def mix (β : ℝ) : ℝ := 100*(β-3)

theorem mix_range {β : ℝ} (hβ : allowed β) : mix β ∈ Set.Icc (0:ℝ) 1 := by
  norm_num [allowed,mix] at *
  constructor <;> linarith [hβ.1,hβ.2]

theorem rank_mix (β p : ℝ) :
    rank β p = (1-mix β)*rank 3 p+mix β*rank (3+1/100) p := by
  rw [rank_affine β,rank_affine (3+1/100)]
  unfold mix
  ring

def term (I : Input Ω) (β ξ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (1-mix β)*estimate I (rank 3) ξ t ω+
    mix β*estimate I (rank (3+1/100)) ξ t ω

def estimateFlex (I : A → Input Ω) (β ξ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, if core (I a) t ω then 0 else term (I a) β ξ t ω

def trueFlex (I : A → Input Ω) (β : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  flex (fun a => core (I a) t ω) β (fun a => (I a).posterior t ω)

theorem endpoint_range (I : Input Ω) {β : ℝ} (hβ : allowed β) (ξ : ℝ) (t : ℕ) (ω : Ω) :
    estimate I (rank β) ξ t ω ∈ Set.Icc (0:ℝ) 1 :=
  ⟨rank_nonneg hβ,rank_le_one hβ (reference_range I (rank β) ξ t ω).1⟩

theorem term_range (I : Input Ω) {β : ℝ} (hβ : allowed β) (ξ : ℝ) (t : ℕ) (ω : Ω) :
    term I β ξ t ω ∈ Set.Icc (0:ℝ) 1 := by
  have h0 := endpoint_range I (show allowed 3 by norm_num [allowed]) ξ t ω
  have h1 := endpoint_range I (show allowed (3+1/100) by norm_num [allowed]) ξ t ω
  have hm := mix_range hβ
  have hm' : 0 ≤ 1-mix β := by linarith [hm.2]
  constructor
  · exact add_nonneg (mul_nonneg hm' h0.1) (mul_nonneg hm.1 h1.1)
  · dsimp [term]
    have h := add_le_add (mul_le_mul_of_nonneg_left h0.2 hm')
      (mul_le_mul_of_nonneg_left h1.2 hm.1)
    nlinarith only [h]

theorem term_comparison (I : Input Ω) {β ξ : ℝ} (hβ : allowed β) (hξ : 0 < ξ)
    (t : ℕ) (ω : Ω) :
    (1+ξ)⁻¹*rank β (I.posterior t ω) ≤ term I β ξ t ω ∧
    term I β ξ t ω ≤ (1+ξ)*rank β (I.posterior t ω) := by
  rw [rank_mix β]
  exact FineCaps.interpolate (mix_range hβ)
    (estimate_spec I (rank 3) ξ hξ (fun _ _ => rank_nonneg (by norm_num [allowed])) t ω)
    (estimate_spec I (rank (3+1/100)) ξ hξ (fun _ _ => rank_nonneg (by norm_num [allowed])) t ω)

theorem flex_comparison (I : A → Input Ω) {β ξ : ℝ} (hβ : allowed β) (hξ : 0 < ξ)
    (t : ℕ) (ω : Ω) :
    (1+ξ)⁻¹*trueFlex I β t ω ≤ estimateFlex I β ξ t ω ∧
    estimateFlex I β ξ t ω ≤ (1+ξ)*trueFlex I β t ω := by
  unfold trueFlex flex estimateFlex
  constructor
  · rw [mul_sum]
    apply sum_le_sum
    intro a _
    split_ifs
    · simp
    · exact (term_comparison (I a) hβ hξ t ω).1
  · rw [mul_sum]
    apply sum_le_sum
    intro a _
    split_ifs
    · simp
    · exact (term_comparison (I a) hβ hξ t ω).2

def flexGap (I : A → Input Ω) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, if core (I a) t ω then 0 else gap ((I a).posterior t ω)

theorem flex_nonneg (I : A → Input Ω) {β : ℝ} (hβ : allowed β) (t : ℕ) (ω : Ω) :
    0 ≤ trueFlex I β t ω := by
  apply sum_nonneg
  intro a _
  split_ifs
  · rfl
  · exact rank_nonneg hβ

theorem gap_bounds (I : A → Input Ω) {β : ℝ} (hβ : allowed β) (t : ℕ) (ω : Ω) :
    trueFlex I β t ω/96 ≤ flexGap I t ω ∧ flexGap I t ω ≤ trueFlex I β t ω := by
  have hp (a : A) (ha : core (I a) t ω=false) : pstar/4 ≤ (I a).posterior t ω := by
    have := noncore_large (I a) t ω ha
    norm_num [pstar] at *
    linarith
  unfold trueFlex flex flexGap
  rw [sum_div]
  constructor
  · apply sum_le_sum
    intro a _
    cases ha : core (I a) t ω
    · simpa [ha] using (gap_comparison hβ (hp a ha)).1
    · simp [ha]
  · apply sum_le_sum
    intro a _
    cases ha : core (I a) t ω
    · simpa [ha] using (gap_comparison hβ (hp a ha)).2
    · simp [ha]

theorem flex_affine (I : A → Input Ω) (β γ : ℝ) (t : ℕ) (ω : Ω) :
    trueFlex I γ t ω = trueFlex I β t ω-(γ-β)*flexGap I t ω := by
  unfold trueFlex flex flexGap
  rw [mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  split_ifs
  · ring
  · rw [rank_affine γ,rank_affine β]
    ring

theorem relative_error {ξ T F : ℝ} (hξ : 0 ≤ ξ) (hT : 0 ≤ T)
    (h : (1+ξ)⁻¹*T ≤ F ∧ F ≤ (1+ξ)*T) : |F-T| ≤ ξ*T := by
  have hi : 1-ξ ≤ (1+ξ)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ (by linarith : 0 < 1+ξ)).2
    nlinarith [sq_nonneg ξ]
  have hlo := (mul_le_mul_of_nonneg_right hi hT).trans h.1
  exact abs_le.mpr ⟨by nlinarith only [hlo],by nlinarith only [h.2]⟩

theorem parameter_error (I : A → Input Ω) {β γ ξ δ : ℝ}
    (hβ : allowed β) (hγ : allowed γ) (hξ : 0 < ξ)
    (hbg : β ≤ γ) (hgb : γ ≤ β+δ) (t : ℕ) (ω : Ω) :
    |estimateFlex I γ ξ t ω-trueFlex I β t ω| ≤ (ξ+δ)*trueFlex I β t ω := by
  have hg := gap_bounds I hβ t ω
  have hT := flex_nonneg I hβ t ω
  have hG := flex_nonneg I hγ t ω
  have hgap : 0 ≤ flexGap I t ω := le_trans (div_nonneg hT (by norm_num)) hg.1
  have hmul := mul_le_mul_of_nonneg_left hg.2 (sub_nonneg.mpr hbg)
  have hmul' := mul_le_mul_of_nonneg_right (show γ-β ≤ δ by linarith) hT
  have he := flex_affine I β γ t ω
  have hmono : trueFlex I γ t ω ≤ trueFlex I β t ω := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbg) hgap]
  have hd : |trueFlex I γ t ω-trueFlex I β t ω| ≤ δ*trueFlex I β t ω := by
    rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
    nlinarith only [he,hmul,hmul']
  have hr := relative_error hξ.le hG (flex_comparison I hγ hξ t ω)
  calc
    _ ≤ |estimateFlex I γ ξ t ω-trueFlex I γ t ω|+
        |trueFlex I γ t ω-trueFlex I β t ω| := abs_sub_le _ _ _
    _ ≤ ξ*trueFlex I γ t ω+δ*trueFlex I β t ω := add_le_add hr hd
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hmono hξ.le]

theorem child_slack (I : A → Input Ω) {β γ g ell : ℝ} (hβ : allowed β)
    (hbg : g/ell ≤ γ-β) (hg : 0 ≤ g) (hell : 0 < ell) (t : ℕ) (ω : Ω) :
    trueFlex I γ t ω ≤ (1-(g/96)/ell)*trueFlex I β t ω := by
  have hG := (gap_bounds I hβ t ω).1
  have hT := flex_nonneg I hβ t ω
  have hbg' : 0 ≤ γ-β := (div_nonneg hg hell.le).trans hbg
  have hmul := mul_le_mul_of_nonneg_left hG hbg'
  have hmul' := mul_le_mul_of_nonneg_right hbg (div_nonneg hT (by norm_num : (0:ℝ) ≤ 96))
  rw [flex_affine I β γ t ω]
  have hid : (g/ell)*(trueFlex I β t ω/96) = ((g/96)/ell)*trueFlex I β t ω := by ring
  rw [hid] at hmul'
  nlinarith only [hmul,hmul']

end UniformKServer.FlexEstimates

end


end

end OAI
