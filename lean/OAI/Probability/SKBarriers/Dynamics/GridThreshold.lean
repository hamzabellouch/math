import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.FiniteLaw

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical MeasureTheory Set
namespace SK.Analytic

namespace FiniteLaw

def uniformFin (n : ℕ) (hn : 0 < n) : FiniteLaw (Fin n) where
  weight _ := 1/(n:ℝ)
  nonneg _ := by positivity
  sum_one := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp

theorem uniformFin_prob (n : ℕ) (hn : 0 < n) (E : Fin n → Prop) :
    (uniformFin n hn).prob E=(Finset.univ.filter E).card/(n:ℝ) := by
  simp only [prob,expect,uniformFin,← Finset.mul_sum]
  rw [Finset.sum_boole]
  ring

theorem markov {n : ℕ} (P : FiniteLaw (Fin n)) (f : Fin n → ℝ) (hf : ∀ x, 0 ≤ f x)
    (c : ℝ) (_hc : 0 < c) : c*P.prob (fun x => c < f x) ≤ P.expect f := by
  rw [prob,← expect_const_mul]
  apply expect_mono
  intro x
  split_ifs with h
  · simpa only [mul_one] using h.le
  · simpa only [mul_zero] using hf x
end FiniteLaw

def thresholdGrid (n : ℕ) (a ρ : ℝ) (i : Fin n) : ℝ := a+ρ*(i:ℕ)/(n:ℝ)

theorem thresholdGrid_mem {n : ℕ} (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ)
    (a : ℝ) (i : Fin n) : thresholdGrid n a ρ i ∈ Icc a (a+ρ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hi : (i:ℝ)<n := by exact_mod_cast i.isLt
  unfold thresholdGrid
  constructor
  · have : 0 ≤ ρ*(i:ℕ)/(n:ℝ) := by positivity
    linarith only [this]
  · have : ρ*(i:ℕ)/(n:ℝ) ≤ ρ := (div_le_iff₀ hnR).mpr (by gcongr)
    linarith only [this]

theorem thresholdGrid_count {n : ℕ} (hn : 0 < n) {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 ≤ w)
    (a x : ℝ) :
    ((Finset.univ.filter (fun i : Fin n => |thresholdGrid n a ρ i-x| ≤ w)).card:ℝ) ≤
      2*w*(n:ℝ)/ρ+1 := by
  let S := Finset.univ.filter (fun i : Fin n => |thresholdGrid n a ρ i-x| ≤ w)
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  by_cases hs : S.Nonempty
  · let i := S.min' hs
    let j := S.max' hs
    have hi : i∈S := Finset.min'_mem S hs
    have hj : j∈S := Finset.max'_mem S hs
    have hij : i≤j := Finset.min'_le S j hj
    have hcard : S.card ≤ (j:ℕ)+1-(i:ℕ) := by
      rw [← Fin.card_Icc]
      apply Finset.card_le_card
      intro z hz
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S z hz,Finset.le_max' S z hz⟩
    have hcard' : (S.card:ℝ) ≤ (j:ℝ)-(i:ℝ)+1 := by
      have hnat : (i:ℕ)≤(j:ℕ)+1 := by omega
      have hc : (S.card:ℝ) ≤ (((j:ℕ)+1-(i:ℕ):ℕ):ℝ) := by exact_mod_cast hcard
      rw [Nat.cast_sub hnat,Nat.cast_add,Nat.cast_one] at hc
      linarith only [hc]
    have hdi := abs_le.mp ((Finset.mem_filter.mp hi).2)
    have hdj := abs_le.mp ((Finset.mem_filter.mp hj).2)
    have hgap : ρ*((j:ℝ)-(i:ℝ)) ≤ 2*w*(n:ℝ) := by
      have H : thresholdGrid n a ρ j-thresholdGrid n a ρ i ≤ 2*w := by linarith only [hdi.1,hdj.2]
      have HH : thresholdGrid n a ρ j-thresholdGrid n a ρ i=ρ*((j:ℝ)-(i:ℝ))/(n:ℝ) := by
        unfold thresholdGrid
        ring
      rw [HH,div_le_iff₀ hnR] at H
      exact H
    have hgap' : (j:ℝ)-(i:ℝ) ≤ 2*w*(n:ℝ)/ρ := (le_div_iff₀ hρ).mpr (by nlinarith only [hgap])
    exact hcard'.trans (by linarith only [hgap'])
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (S.card:ℝ)≤_
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem thresholdGrid_window {n : ℕ} (hn : 0 < n) {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 ≤ w)
    (a x : ℝ) :
    (FiniteLaw.uniformFin n hn).prob (fun i => |thresholdGrid n a ρ i-x| ≤ w) ≤ 2*w/ρ+1/(n:ℝ) := by
  rw [FiniteLaw.uniformFin_prob]
  have h := div_le_div_of_nonneg_right (thresholdGrid_count hn hρ hw a x) (by positivity : (0:ℝ)≤n)
  refine h.trans_eq ?_
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp

theorem thresholdGrid_mass_expect {n : ℕ} (hn : 0 < n) (μ : ProbabilityMeasure ℝ)
    {ρ h : ℝ} (hρ : 0 < ρ) (hh : 0 ≤ h) (a : ℝ) :
    (FiniteLaw.uniformFin n hn).expect (fun i => (μ:Measure ℝ).real
      (Icc (thresholdGrid n a ρ i-h) (thresholdGrid n a ρ i+h))) ≤ 2*h/ρ+1/(n:ℝ) := by
  let f (i : Fin n) := (Icc (thresholdGrid n a ρ i-h) (thresholdGrid n a ρ i+h)).indicator (fun _ : ℝ => (1:ℝ))
  have hi (i : Fin n) : Integrable (f i) (μ:Measure ℝ) :=
    (integrable_const 1).indicator measurableSet_Icc
  have he : (FiniteLaw.uniformFin n hn).expect (fun i => (μ:Measure ℝ).real
      (Icc (thresholdGrid n a ρ i-h) (thresholdGrid n a ρ i+h))) =
      ∫ x, (1/(n:ℝ))*∑ i, f i x ∂(μ:Measure ℝ) := by
    unfold FiniteLaw.expect FiniteLaw.uniformFin
    rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f]
    rw [integral_indicator_const (1:ℝ) measurableSet_Icc]
    simp only [smul_eq_mul,mul_one]
  rw [he]
  have hb (x : ℝ) : (1/(n:ℝ))*∑ i, f i x ≤ 2*h/ρ+1/(n:ℝ) := by
    have H := thresholdGrid_window hn hρ hh a x
    change (1/(n:ℝ))*(∑ i, f i x)≤_
    convert H using 1
    unfold FiniteLaw.prob FiniteLaw.expect FiniteLaw.uniformFin
    rw [← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have he : x∈Icc (thresholdGrid n a ρ i-h) (thresholdGrid n a ρ i+h) ↔ |thresholdGrid n a ρ i-x|≤h := by
      rw [Set.mem_Icc,abs_le]
      constructor <;> intro H <;> constructor <;> linarith only [H.1,H.2]
    simp only [f,Set.indicator_apply,he]
  exact (integral_mono_of_nonneg (ae_of_all _ (fun x => by
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x)))
    (integrable_const _) (ae_of_all _ hb)).trans_eq (by simp)

end SK.Analytic

end
end

end OAI
