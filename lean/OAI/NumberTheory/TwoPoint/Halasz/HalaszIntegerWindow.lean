import OAI.NumberTheory.TwoPoint.Halasz.HalaszWindowSampling
import Mathlib.Data.Int.Interval

namespace OAI

/-! Counting lattice points near integers, with all interval endpoints real. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_integer_interval_card (S : Finset ℤ) {a b : ℝ} (hab : a≤b)
    (hS : ∀ d∈S,a≤(d:ℝ) ∧ (d:ℝ)≤b) : (S.card:ℝ)≤b-a+1 := by
  have hcf : ⌈a⌉≤⌊b⌋+1 := by
    apply Int.ceil_le.mpr
    push_cast
    exact hab.trans (Int.lt_floor_add_one b).le
  have hsub : S⊆Icc ⌈a⌉ ⌊b⌋ := by
    intro d hd
    exact mem_Icc.mpr ⟨Int.ceil_le.mpr (hS d hd).1,Int.le_floor.mpr (hS d hd).2⟩
  have hcard : ((Icc ⌈a⌉ ⌊b⌋).card:ℝ)=(⌊b⌋:ℝ)+1-(⌈a⌉:ℝ) := by
    exact_mod_cast Int.card_Icc_of_le ⌈a⌉ ⌊b⌋ hcf
  have hh : (S.card:ℝ)≤((Icc ⌈a⌉ ⌊b⌋).card:ℝ) := by
    exact_mod_cast card_le_card hsub
  rw [hcard] at hh
  linarith [Int.floor_le b,Int.le_ceil a]

/-- A finite set of integers lying in [-K,K] whose multiples by γ are close
to integers. This is the lattice count used by the double mean-value method. -/
theorem halasz_integer_window_card (S : Finset ℤ) {K γ δ : ℝ}
    (hK : 0≤K) (hγ : 0<γ) (hδ : 0≤δ) (hδhalf : δ≤1/2)
    (hS : ∀ d∈S, |(d:ℝ)|≤K ∧ ‖((γ*(d:ℝ):ℝ):AddCircle (1:ℝ))‖≤δ) :
    (S.card:ℝ)≤4*K*δ+2*K*γ+4*δ/γ+2 := by
  let f : ℤ → ℤ := fun d => round (γ*(d:ℝ))
  have hnear (d : ℤ) (hd : d∈S) : |γ*(d:ℝ)-(f d:ℝ)|≤δ := by
    simpa only [AddCircle.norm_eq,inv_one,one_mul,mul_one,f] using (hS d hd).2
  have himage : ∀ j∈S.image f, -K*γ-δ≤(j:ℝ) ∧ (j:ℝ)≤K*γ+δ := by
    intro j hj
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hj
    have hdK := abs_le.mp (hS d hd).1
    have hnd := abs_le.mp (hnear d hd)
    constructor <;> nlinarith
  have hjcard := halasz_integer_interval_card (S.image f)
    (show -K*γ-δ≤K*γ+δ by nlinarith [mul_nonneg hK hγ.le]) himage
  have hfcard (j : ℤ) : ((S.filter (fun d => f d=j)).card:ℝ)≤2*δ/γ+1 := by
    have hh := halasz_integer_interval_card (S.filter (fun d => f d=j))
      (show ((j:ℝ)-δ)/γ≤((j:ℝ)+δ)/γ from
        (div_le_div_iff_of_pos_right hγ).mpr (by linarith)) (by
          intro d hd
          obtain ⟨hd,hf⟩ := mem_filter.mp hd
          have hn := abs_le.mp (hnear d hd)
          rw [hf] at hn
          constructor
          · apply (div_le_iff₀ hγ).mpr
            nlinarith [hn.2]
          · apply (le_div_iff₀ hγ).mpr
            nlinarith [hn.1])
    convert hh using 1; ring
  have hsum : (S.card:ℝ)=∑ j∈S.image f,((S.filter (fun d => f d=j)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image f S
  calc
    _ = _ := hsum
    _ ≤ ∑ _j∈S.image f,(2*δ/γ+1) := sum_le_sum (fun j _ => hfcard j)
    _ = ((S.image f).card:ℝ)*(2*δ/γ+1) := by simp; ring
    _ ≤ (2*K*γ+2*δ+1)*(2*δ/γ+1) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ _ := by
      have hδ2 : 4*δ^2≤2*δ := by nlinarith
      have hγ0 : γ≠0 := ne_of_gt hγ
      apply (le_of_sub_nonneg ?_)
      field_simp
      nlinarith

end TwoPointCorrelations

end OAI
