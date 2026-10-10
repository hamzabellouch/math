import OAI.Analysis.AncientFlat.Evolution.MeasurableTime

namespace OAI
noncomputable section
open Set Filter MeasureTheory
namespace EarlyIntegral
variable {V E : Type} [NormedAddCommGroup V] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma holder_of_bounds (F : ℝ → ℝ → V → E) (a b T γ : ℝ)
    (_ : 0<a) (hb : 0<b) (hγ : 0<γ) (hγ1 : γ<1)
    (w : ℝ → ℝ) (hw : IntegrableOn w (Ioo 0 b)) (hw₀ : ∀ r∈Ioo 0 b, 0≤w r)
    (B D E₀ : ℝ) (hB : 0≤B) (hD : 0≤D) (hE : 0≤E₀)
    (hi : ∀ t∈Icc a T, ∀ x, IntegrableOn (fun r => F t r x) (Ioo 0 b))
    (hbound : ∀ t∈Icc a T, ∀ r∈Ioo 0 b, ∀ x, ‖F t r x‖≤B*w r)
    (hspace : ∀ t∈Icc a T, ∀ r∈Ioo 0 b, ∀ x y, ‖F t r x-F t r y‖≤D*w r*‖x-y‖)
    (htime : ∀ s∈Icc a T, ∀ t∈Icc a T, s≤t → t-s≤b → ∀ r∈Ioo 0 b, ∀ x,
      ‖F t r x-F s r x‖≤E₀*w r*(t-s)) :
    ∃ C : ℝ, 0≤C ∧
      (∀ t∈Icc a T, ∀ x, ‖∫ r in Ioo 0 b, F t r x‖≤C) ∧
      (∀ t∈Icc a T, ∀ s∈Icc a T, ∀ x y,
        ‖(∫ r in Ioo 0 b, F t r x)-(∫ r in Ioo 0 b, F s r y)‖≤
          C*(‖x-y‖^γ+|t-s|^(γ/4))) := by
  let W := ∫ r in Ioo 0 b,w r
  have hW : 0≤W := integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hw₀ r hr)
  have hn (t) (ht : t∈Icc a T) (x : V) : ‖∫ r in Ioo 0 b,F t r x‖≤B*W := by
    have he := norm_integral_le_of_norm_le (hw.const_mul B) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hbound t ht r hr x)
    simpa only [integral_const_mul] using he
  have hs (t) (ht : t∈Icc a T) (x y : V) :
      ‖(∫ r in Ioo 0 b,F t r x)-(∫ r in Ioo 0 b,F t r y)‖≤D*W*‖x-y‖ := by
    rw [←integral_sub (hi t ht x) (hi t ht y)]
    have he := norm_integral_le_of_norm_le ((hw.const_mul D).mul_const ‖x-y‖) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hspace t ht r hr x y)
    simpa only [integral_mul_const,integral_const_mul] using he
  let E₁ := E₀*W+2*B*W/b
  have hE₁ : 0≤E₁ := by dsimp [E₁]; positivity
  have htord (s) (hs : s∈Icc a T) (t) (ht : t∈Icc a T) (hst : s≤t) (x : V) :
      ‖(∫ r in Ioo 0 b,F t r x)-(∫ r in Ioo 0 b,F s r x)‖≤E₁*(t-s) := by
    by_cases he : t-s≤b
    · have he' : ‖(∫ r in Ioo 0 b,F t r x)-(∫ r in Ioo 0 b,F s r x)‖≤E₀*W*(t-s) := by
        rw [←integral_sub (hi t ht x) (hi s hs x)]
        have hm := norm_integral_le_of_norm_le ((hw.const_mul E₀).mul_const (t-s)) (by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          exact htime s hs t ht hst he r hr x)
        simpa only [integral_mul_const,integral_const_mul] using hm
      apply he'.trans
      apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hst)
      dsimp [E₁]; exact le_add_of_nonneg_right (by positivity)
    · have hb' : b≤t-s := (lt_of_not_ge he).le
      calc
        _ ≤ ‖∫ r in Ioo 0 b,F t r x‖+‖∫ r in Ioo 0 b,F s r x‖ := norm_sub_le ..
        _ ≤ B*W+B*W := add_le_add (hn t ht x) (hn s hs x)
        _ = (2*B*W/b)*b := by field_simp; ring
        _ ≤ (2*B*W/b)*(t-s) := mul_le_mul_of_nonneg_left hb' (by positivity)
        _ ≤ E₁*(t-s) := mul_le_mul_of_nonneg_right (by dsimp [E₁]; exact le_add_of_nonneg_left (by positivity)) (sub_nonneg.mpr hst)
  have htime' (s) (hs : s∈Icc a T) (t) (ht : t∈Icc a T) (x : V) :
      ‖(∫ r in Ioo 0 b,F t r x)-(∫ r in Ioo 0 b,F s r x)‖≤E₁*|t-s| := by
    rcases le_total s t with hst|hts
    · rw [abs_of_nonneg (sub_nonneg.mpr hst)]; exact htord s hs t ht hst x
    · rw [norm_sub_rev,abs_of_nonpos (sub_nonpos.mpr hts),neg_sub]; exact htord t ht s hs hts x
  let Cs := (2*B*W)^(1-γ)*(D*W)^γ
  let Ct := (2*B*W)^(1-γ/4)*E₁^(γ/4)
  have hCs : 0≤Cs := by dsimp [Cs]; positivity
  have hCt : 0≤Ct := by dsimp [Ct]; positivity
  refine ⟨B*W+Cs+Ct,by positivity,fun t ht x => (hn t ht x).trans (by linarith),?_⟩
  intro t ht s hs' x y
  have hsp : ‖(∫ r in Ioo 0 b,F t r x)-(∫ r in Ioo 0 b,F t r y)‖≤Cs*‖x-y‖^γ := by
    apply HolderInterpolation.scalar (norm_nonneg _) (by positivity) (by positivity) (norm_nonneg _) hγ hγ1
    · exact (norm_sub_le ..).trans ((add_le_add (hn t ht x) (hn t ht y)).trans_eq (by ring))
    · exact hs t ht x y
  have hti : ‖(∫ r in Ioo 0 b,F t r y)-(∫ r in Ioo 0 b,F s r y)‖≤Ct*|t-s|^(γ/4) := by
    apply HolderInterpolation.scalar (norm_nonneg _) (by positivity) hE₁ (abs_nonneg _) (by positivity) (by linarith)
    · exact (norm_sub_le ..).trans ((add_le_add (hn t ht y) (hn s hs' y)).trans_eq (by ring))
    · exact htime' s hs' t ht y
  calc
    _ ≤ ‖(∫ r in Ioo 0 b,F t r x)-(∫ r in Ioo 0 b,F t r y)‖+
        ‖(∫ r in Ioo 0 b,F t r y)-(∫ r in Ioo 0 b,F s r y)‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ Cs*‖x-y‖^γ+Ct*|t-s|^(γ/4) := add_le_add hsp hti
    _ ≤ (B*W+Cs+Ct)*‖x-y‖^γ+(B*W+Cs+Ct)*|t-s|^(γ/4) := by gcongr <;> nlinarith
    _ = _ := by ring
end EarlyIntegral

end

end OAI
