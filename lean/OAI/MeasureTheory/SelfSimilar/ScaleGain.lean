import OAI.MeasureTheory.SelfSimilar.WindowCount

namespace OAI

universe uα uβ

namespace EntropyRateDimension
open scoped BigOperators ENNReal
open MeasureTheory FairPairs MeasureEntropy

theorem scaled_band_distance (ν : Law) {a : ℝ} (ha : a ≠ 0) (L : ℤ)
    (e : ν.edges (L-⌈-Real.log |a|/Real.log 2⌉)) :
    (2 : ℝ)^(-L) ≤ |a*e.val.2-a*e.val.1| ∧
      |a*e.val.2-a*e.val.1| < 4*(2 : ℝ)^(-L) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hap : 0 < |a| := abs_pos.mpr ha
  let σ := -Real.log |a|/Real.log 2
  let c := ⌈σ⌉
  have hp : 0 < |a| *(2 : ℝ)^c := mul_pos hap (zpow_pos (by norm_num) _)
  have hlog : Real.log (|a| *(2 : ℝ)^c)=Real.log |a|+(c : ℝ)*Real.log 2 := by
    rw [Real.log_mul hap.ne' (zpow_ne_zero _ (by norm_num : (2 : ℝ)≠0)),Real.log_zpow]
  have hc1 := (div_le_iff₀ hl).mp (Int.le_ceil σ)
  have hc2 := Int.ceil_lt_add_one σ
  have hid : σ*Real.log 2= -Real.log |a| := div_mul_cancel₀ _ hl.ne'
  have ha1 : 1 ≤ |a| *(2 : ℝ)^c := by
    apply (Real.log_nonneg_iff hp).mp
    rw [hlog]
    dsimp only [c]
    linarith
  have ha2 : |a| *(2 : ℝ)^c < 2 := by
    apply (Real.log_lt_log_iff hp (by norm_num : (0 : ℝ)<2)).mp
    rw [hlog]
    have hh := mul_lt_mul_of_pos_right hc2 hl
    dsimp only [c]
    nlinarith
  have he := (Finset.mem_filter.mp e.property).2
  have hxy : 0 < e.val.2-e.val.1 := sub_pos.mpr he.1
  have habs : |a*e.val.2-a*e.val.1|=|a| *(e.val.2-e.val.1) := by
    rw [← mul_sub,abs_mul,abs_of_pos hxy]
  have hz1 : (2 : ℝ)^(-(L-c))=(2 : ℝ)^c*(2 : ℝ)^(-L) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ)≠0)]
    congr 1
    ring
  have hz2 : (2 : ℝ)^(1-(L-c))=2*((2 : ℝ)^c*(2 : ℝ)^(-L)) := by
    rw [show 1-(L-c)=1+(-(L-c)) by ring,zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one,hz1]
  change _ ∧ (2 : ℝ)^(-(L-c)) ≤ _ ∧ _ < (2 : ℝ)^(1-(L-c)) at he
  rw [hz1,hz2] at he
  rw [habs]
  have hr : 0 < (2 : ℝ)^(-L) := zpow_pos (by norm_num) _
  have hlow := mul_le_mul_of_nonneg_left he.2.1 hap.le
  have hupp := mul_lt_mul_of_pos_left he.2.2 hap
  have hlow' := mul_le_mul_of_nonneg_right ha1 hr.le
  have hupp' := mul_lt_mul_of_pos_right ha2 (by positivity : 0 < 2*(2 : ℝ)^(-L))
  constructor <;> nlinarith

theorem distance_window_bounds {r v : ℝ} (hr : 0 < r) (hv : r ≤ v) (hv4 : v < 4*r)
    {M : ℕ} (hM : 4 < M) :
    r/M < v ∧ v < ((M*M : ℕ) : ℝ)*(r/M) ∧
      (r/M)/v+v/(((M*M : ℕ) : ℝ)*(r/M)) ≤ 5/(M : ℝ) := by
  have hMR : (4 : ℝ)<M := by exact_mod_cast hM
  have hMp : (0 : ℝ)<M := by linarith
  have hvp : 0 < v := hr.trans_le hv
  have hid : ((M*M : ℕ) : ℝ)*(r/M)=(M : ℝ)*r := by push_cast; field_simp
  rw [hid]
  refine ⟨?_,?_,?_⟩
  · apply (div_lt_iff₀ hMp).mpr
    nlinarith
  · nlinarith
  · have h1 : (r/M)/v ≤ 1/(M : ℝ) := by
      apply (div_le_div_iff₀ hvp hMp).mpr
      rw [div_mul_cancel₀ _ hMp.ne']
      simpa only [one_mul] using hv
    have h2 : v/((M : ℝ)*r) ≤ 4/(M : ℝ) := by
      apply (div_le_div_iff₀ (mul_pos hMp hr) hMp).mpr
      nlinarith
    have hh : 1/(M : ℝ)+4/(M : ℝ)=5/(M : ℝ) := by ring
    linarith

namespace Typed
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem conditional_gain (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) {δ : ℝ}
    (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) {M : ℕ} (hM : 4 < M)
    (he : 5/(M : ℝ)*Real.log 2 ≤ δ/2)
    {j n : ℕ} (u : Fin j → α) (w : Fin n → α) (t : ℕ) (L : ℤ) :
    δ/2*capacity (law S tag w) (L-⌈S.wordDepth u⌉) ≤
      ∑ z : Fin t → α, S.wordWeight z*
        (window (scaledTail S tag μ (S.completeMap u).1 (Fin.append w z))
          ((2 : ℝ)^(-L)/M) (((M*M : ℕ) : ℝ)*((2 : ℝ)^(-L)/M))-
        window (scaledTail S tag μ ((S.completeMap u).1*(S.completeMap w).1) z)
          ((2 : ℝ)^(-L)/M) (((M*M : ℕ) : ℝ)*((2 : ℝ)^(-L)/M))) := by
  have ha : (S.completeMap u).1≠0 := S.completeMap_slope_ne_zero u
  have hb : (S.completeMap u).1*(S.completeMap w).1≠0 := mul_ne_zero ha (S.completeMap_slope_ne_zero w)
  have hMp : (0 : ℝ)<M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hs : 0 < (2 : ℝ)^(-L)/(M : ℝ) := div_pos (zpow_pos (by norm_num) _) hMp
  have hv (e : (law S tag w).edges (L-⌈S.wordDepth u⌉)) :=
    scaled_band_distance (law S tag w) ha L e
  have hd (e : (law S tag w).edges (L-⌈S.wordDepth u⌉)) :=
    distance_window_bounds (zpow_pos (by norm_num : (0 : ℝ)<2) (-L)) (hv e).1 (hv e).2 hM
  have hg := finiteConv_mean_gain (law S tag w) (S.completeMap u).1
    ((S.completeMap u).1*(S.completeMap w).1) hb μ hc
    (scaledTail S tag μ ((S.completeMap u).1*(S.completeMap w).1))
    (fun z : Fin t → α => scaledTail_compact S tag μ hc _ z)
    S.wordWeight (fun z => (S.wordWeight_pos z).le) (S.wordWeight_sum t)
    (scaledTail_mean S tag μ hμ _ t).symm hδ hs (by positivity : 0 < M*M)
    (L-⌈S.wordDepth u⌉) (fun e => ⟨(hd e).1,(hd e).2.1⟩)
    (fun e => (mul_le_mul_of_nonneg_right (hd e).2.2 (Real.log_pos (by norm_num : (1 : ℝ)<2)).le).trans he)
  simp only [← scaledTail_append S tag hr] at hg
  convert hg using 1
  ring

end Typed
end EntropyRateDimension

end OAI
