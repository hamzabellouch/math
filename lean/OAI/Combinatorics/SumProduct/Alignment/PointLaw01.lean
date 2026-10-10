import Mathlib
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section RawSuccessInlineScope0
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
end
end RawSuccessInlineScope0

 

 

section RawSuccessInlineScope1

 

open scoped Topology BigOperators
open Filter MeasureTheory Set

namespace SourcePointLaw

noncomputable section

 

theorem interval_induction (p : ℝ → ℝ → Prop)
    (hjoin : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      p a ((a + b) / 2) → p ((a + b) / 2) b → p a b)
    (hlocal : ∀ x ∈ Icc (0 : ℝ) 1, ∃ δ > 0, ∀ a b : ℝ,
      0 ≤ a → a < b → b ≤ 1 → a ≤ x → x ≤ b → b - a < δ → p a b) :
    p 0 1 := by
  let I : BoxIntegral.Box Unit := ⟨fun _ => 0, fun _ => 1, fun _ => by norm_num⟩
  change p (I.lower ()) (I.upper ())
  apply I.subbox_induction_on' (p := fun J => p (J.lower ()) (J.upper ()))
  · intro J hJ hs
    have hlo : 0 ≤ J.lower () := (BoxIntegral.Box.le_iff_bounds.mp hJ).1 ()
    have hup : J.upper () ≤ 1 := (BoxIntegral.Box.le_iff_bounds.mp hJ).2 ()
    have h₁ := hs (∅ : Set Unit)
    have h₂ := hs (univ : Set Unit)
    simp [BoxIntegral.Box.splitCenterBox] at h₁ h₂
    exact hjoin _ _ hlo (J.lower_lt_upper ()) hup h₁ h₂
  · intro z hz
    have hz' : z () ∈ Icc (0 : ℝ) 1 := ⟨hz.1 (), hz.2 ()⟩
    obtain ⟨δ, hδ, hδp⟩ := hlocal (z ()) hz'
    refine ⟨{y : Unit → ℝ | |y () - z ()| < δ / 3}, ?_, ?_⟩
    · apply mem_nhdsWithin_of_mem_nhds
      have hh : Continuous (fun y : Unit → ℝ => |y () - z ()|) :=
        ((continuous_apply ()).sub continuous_const).abs
      exact IsOpen.mem_nhds (isOpen_lt hh continuous_const) (by simp only [Set.mem_ofPred_eq, sub_self, abs_zero]; positivity)
    · intro J hJ m hzJ hsub _
      have hlo : 0 ≤ J.lower () := (BoxIntegral.Box.le_iff_bounds.mp hJ).1 ()
      have hup : J.upper () ≤ 1 := (BoxIntegral.Box.le_iff_bounds.mp hJ).2 ()
      have hl := hsub J.lower_mem_Icc
      have hu := hsub J.upper_mem_Icc
      change |J.lower () - z ()| < δ / 3 at hl
      change |J.upper () - z ()| < δ / 3 at hu
      apply hδp _ _ hlo (J.lower_lt_upper ()) hup (hzJ.1 ()) (hzJ.2 ())
      have hl' := (abs_lt.mp hl).1
      have hu' := (abs_lt.mp hu).2
      linarith

 

theorem tendsto_of_local_interval_law
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ι : Type*} (l : Filter ι) (A : ι → ℝ → ℝ → E) (f : ℝ → E)
    (hadd : ∀ N a b c, 0 ≤ a → a ≤ b → b ≤ c → c ≤ 1 →
      A N a c = A N a b + A N b c)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hlocal : ∀ x ∈ Icc (0 : ℝ) 1, ∀ ε > 0, ∃ δ > 0,
      ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → a ≤ x → x ≤ b → b - a < δ →
        ∀ᶠ N : ι in l, ‖A N a b - (b - a) • f x‖ ≤ ε * (b - a)) :
    Tendsto (fun N => A N 0 1) l (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  have hint (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      IntervalIntegrable f volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hf.mono (Icc_subset_Icc ha hb))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  have hevent : ∀ᶠ N : ι in l,
      ‖A N 0 1 - ∫ x in (0 : ℝ)..1, f x‖ ≤ ε / 2 * (1 - 0) := by
    apply interval_induction (fun a b => ∀ᶠ N : ι in l,
      ‖A N a b - ∫ x in a..b, f x‖ ≤ ε / 2 * (b - a))
    · intro a b ha hab hb hl hr
      let c := (a + b) / 2
      have hac : a ≤ c := by dsimp [c]; linarith
      have hcb : c ≤ b := by dsimp [c]; linarith
      have hic := hint a c ha hac (hcb.trans hb)
      have hci := hint c b (ha.trans hac) hcb hb
      filter_upwards [hl, hr] with N hNl hNr
      rw [hadd N a c b ha hac hcb hb,
        ← intervalIntegral.integral_add_adjacent_intervals hic hci]
      calc
        ‖A N a c + A N c b -
            ((∫ x in a..c, f x) + ∫ x in c..b, f x)‖ =
            ‖(A N a c - ∫ x in a..c, f x) + (A N c b - ∫ x in c..b, f x)‖ :=
          congrArg norm (by abel)
        _ ≤ ‖A N a c - ∫ x in a..c, f x‖ + ‖A N c b - ∫ x in c..b, f x‖ :=
          norm_add_le _ _
        _ ≤ ε / 2 * (b - a) := by dsimp [c] at *; linarith
    · intro x hx
      obtain ⟨δ₁, hδ₁, hδ₁p⟩ := hlocal x hx (ε / 4) hε4
      obtain ⟨δ₂, hδ₂, hδ₂p⟩ := Metric.continuousWithinAt_iff.mp (hf x hx) (ε / 4) hε4
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro a b ha hab hb hax hxb hδ
      have hδa : b - a < δ₁ := hδ.trans_le (min_le_left _ _)
      have hδb : b - a < δ₂ := hδ.trans_le (min_le_right _ _)
      have hi := hint a b ha hab.le hb
      have herr : ‖(b - a) • f x - ∫ y in a..b, f y‖ ≤ ε / 4 * (b - a) := by
        rw [← intervalIntegral.integral_const,
          ← intervalIntegral.integral_sub intervalIntegrable_const hi]
        have hbound : ∀ y ∈ uIoc a b, ‖f x - f y‖ ≤ ε / 4 := by
          intro y hy
          rw [uIoc_of_le hab.le] at hy
          have hy' : y ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hy.1.le, hy.2.trans hb⟩
          have hdist : dist y x ≤ b - a := by
            rw [Real.dist_eq, abs_le]
            constructor <;> linarith [hy.1, hy.2]
          have hc := (hδ₂p hy' (hdist.trans_lt hδb)).le
          simpa only [dist_eq_norm, norm_sub_rev] using hc
        simpa only [abs_of_pos (sub_pos.mpr hab)] using
          intervalIntegral.norm_integral_le_of_norm_le_const hbound
      filter_upwards [hδ₁p a b ha hab hb hax hxb hδa] with N hN
      calc
        ‖A N a b - ∫ y in a..b, f y‖ ≤
            ‖A N a b - (b - a) • f x‖ + ‖(b - a) • f x - ∫ y in a..b, f y‖ :=
          by simpa only [dist_eq_norm] using
            dist_triangle (A N a b) ((b - a) • f x) (∫ y in a..b, f y)
        _ ≤ ε / 2 * (b - a) := by linarith
  filter_upwards [hevent] with N hN
  rw [dist_eq_norm]
  have : ε / 2 < ε := by linarith
  exact hN.trans_lt (by simpa using this)

end
end SourcePointLaw

 

open scoped Topology BigOperators
open Filter MeasureTheory Set

namespace SourcePointLaw
noncomputable section

 
def residueInterval (d : ℕ) (r : ℤ) (a b : ℝ) : Finset ℤ :=
  (Finset.Ico ⌈a⌉ ⌈b⌉).filter (fun n => n % (d : ℤ) = r)

lemma mem_residueInterval (d : ℕ) (r n : ℤ) (a b : ℝ) :
    n ∈ residueInterval d r a b ↔ (a ≤ (n : ℝ) ∧ (n : ℝ) < b) ∧ n % (d : ℤ) = r := by
  simp only [residueInterval, Finset.mem_filter, Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]

lemma residueInterval_affine (d : ℕ) (hd : 0 < d) (r : ℤ)
    (hr : 0 ≤ r ∧ r < (d : ℤ)) (a b : ℝ) :
    residueInterval d r a b =
      (Finset.Ico ⌈(a - (r : ℝ)) / (d : ℝ)⌉ ⌈(b - (r : ℝ)) / (d : ℝ)⌉).map
        ⟨fun k => r + (d : ℤ) * k, by
          intro x y h
          have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
          exact mul_left_cancel₀ hd' (add_left_cancel h)⟩ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmem (k : ℤ) :
      k ∈ Finset.Ico ⌈(a - (r : ℝ)) / (d : ℝ)⌉ ⌈(b - (r : ℝ)) / (d : ℝ)⌉ ↔
        a ≤ ((r + (d : ℤ) * k : ℤ) : ℝ) ∧ ((r + (d : ℤ) * k : ℤ) : ℝ) < b := by
    simp only [Finset.mem_Ico, Int.ceil_le, Int.lt_ceil, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, div_le_iff₀ hdR, lt_div_iff₀ hdR]
    constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]
  ext n
  rw [mem_residueInterval, Finset.mem_map]
  constructor
  · rintro ⟨hn, hmod⟩
    have he : r + (d : ℤ) * (n / (d : ℤ)) = n := by
      rw [← hmod]
      exact Int.emod_add_mul_ediv n d
    refine ⟨n / (d : ℤ), hmem _ |>.mpr ?_, he⟩
    simpa only [he] using hn
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(hmem k).mp hk, ?_⟩
    change (r + (d : ℤ) * k) % (d : ℤ) = r
    rw [Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt hr.1 hr.2

 
theorem residueInterval_card_error (d : ℕ) (hd : 0 < d) (r : ℤ)
    (hr : 0 ≤ r ∧ r < (d : ℤ)) (a b : ℝ) (hab : a ≤ b) :
    |((residueInterval d r a b).card : ℝ) - (b - a) / (d : ℝ)| < 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let u := (a - (r : ℝ)) / (d : ℝ)
  let v := (b - (r : ℝ)) / (d : ℝ)
  have huv : u ≤ v := div_le_div_of_nonneg_right (sub_le_sub_right hab _) hdR.le
  have hceil : ⌈u⌉ ≤ ⌈v⌉ := Int.ceil_mono huv
  have hcard : ((residueInterval d r a b).card : ℤ) = ⌈v⌉ - ⌈u⌉ := by
    rw [residueInterval_affine d hd r hr, Finset.card_map, Int.card_Ico]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hceil)
  have hcardR : ((residueInterval d r a b).card : ℝ) = (⌈v⌉ : ℝ) - (⌈u⌉ : ℝ) := by
    exact_mod_cast hcard
  have hvu : v - u = (b - a) / (d : ℝ) := by dsimp [v, u]; ring
  rw [hcardR, ← hvu, abs_lt]
  constructor <;> linarith [Int.le_ceil u, Int.ceil_lt_add_one u,
    Int.le_ceil v, Int.ceil_lt_add_one v]

 
theorem residueInterval_card_scaled_error (d : ℕ) (hd : 0 < d) (r : ℤ)
    (hr : 0 ≤ r ∧ r < (d : ℤ)) (a b : ℝ) (hab : a ≤ b)
    (N : ℕ) (hN : 0 < N) :
    |((residueInterval d r (a * N) (b * N)).card : ℝ) / N - (b - a) / (d : ℝ)| <
      1 / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have he := residueInterval_card_error d hd r hr (a * N) (b * N)
    (mul_le_mul_of_nonneg_right hab hNR.le)
  have hi : ((residueInterval d r (a * N) (b * N)).card : ℝ) / N - (b - a) / (d : ℝ) =
      (((residueInterval d r (a * N) (b * N)).card : ℝ) -
        (b * N - a * N) / (d : ℝ)) / N := by
    field_simp
  rw [hi, abs_div, abs_of_pos hNR]
  exact (div_lt_div_iff_of_pos_right hNR).mpr he

 
theorem residueInterval_card_tendsto (d : ℕ) (hd : 0 < d) (r : ℤ)
    (hr : 0 ≤ r ∧ r < (d : ℤ)) (a b : ℝ) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => ((residueInterval d r (a * N) (b * N)).card : ℝ) / N)
      atTop (𝓝 ((b - a) / (d : ℝ))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    simpa only [Real.norm_eq_abs] using
      (residueInterval_card_scaled_error d hd r hr a b hab N (by omega)).le
  · exact tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)

lemma residueInterval_union (d : ℕ) (r : ℤ) (a b c : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    residueInterval d r a c = residueInterval d r a b ∪ residueInterval d r b c := by
  ext n
  simp only [mem_residueInterval, Finset.mem_union]
  constructor
  · rintro ⟨⟨hna, hnc⟩, hnmod⟩
    by_cases hnb : (n : ℝ) < b
    · exact Or.inl ⟨⟨hna, hnb⟩, hnmod⟩
    · exact Or.inr ⟨⟨le_of_not_gt hnb, hnc⟩, hnmod⟩
  · rintro (⟨⟨hna, hnb⟩, hnmod⟩ | ⟨⟨hnb, hnc⟩, hnmod⟩)
    · exact ⟨⟨hna, hnb.trans_le hbc⟩, hnmod⟩
    · exact ⟨⟨hab.trans hnb, hnc⟩, hnmod⟩

lemma residueInterval_disjoint (d : ℕ) (r : ℤ) (a b c : ℝ) :
    Disjoint (residueInterval d r a b) (residueInterval d r b c) := by
  apply Finset.disjoint_left.mpr
  intro n hn hm
  rw [mem_residueInterval] at hn hm
  exact (not_lt_of_ge hm.1.1) hn.1.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 

def windowSum (P : ℕ → ℤ → E) (d : ℕ) (r : ℤ) (N : ℕ) (a b : ℝ) : E :=
  (N : ℝ)⁻¹ • ∑ n ∈ residueInterval d r (a * N) (b * N), P N n

lemma windowSum_add (P : ℕ → ℤ → E) (d : ℕ) (r : ℤ) (N : ℕ)
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    windowSum P d r N a c = windowSum P d r N a b + windowSum P d r N b c := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  simp only [windowSum, residueInterval_union d r _ _ _
    (mul_le_mul_of_nonneg_right hab hN) (mul_le_mul_of_nonneg_right hbc hN),
    Finset.sum_union (residueInterval_disjoint d r _ _ _), smul_add]

 

lemma windowSum_eq [Module ℚ≥0 E] (P : ℕ → ℤ → E) (d : ℕ) (r : ℤ) (N : ℕ) (a b : ℝ) :
    windowSum P d r N a b =
      (((residueInterval d r (a * N) (b * N)).card : ℝ) / N) •
        (𝔼 n ∈ residueInterval d r (a * N) (b * N), P N n) := by
  rw [windowSum, ← Finset.card_smul_expect]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  ring

end
end SourcePointLaw

end RawSuccessInlineScope1
end

end OAI
