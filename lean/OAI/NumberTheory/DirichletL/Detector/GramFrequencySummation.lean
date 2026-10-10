import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Detector.LowGramExceptional

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.ProbeGramFrequencySummation
local notation "O" => ActualEisensteinCubic.O

def frequencyNorm (k : O) : ℝ := Ideal.absNorm (Ideal.span {k})

lemma frequencyNorm_nonneg (k : O) : 0 ≤ frequencyNorm k := Nat.cast_nonneg _

lemma frequencyNorm_one_le (k : O) (hk : k ≠ 0) : 1 ≤ frequencyNorm k := by
  unfold frequencyNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hk))

theorem finite_weighted_of_count {α : Type*} (E : Finset α) (q : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (C d H : ℝ) (hC : 0 ≤ C) (hd : d ≤ 1) (hH : 0 < H)
    (hcount : ∀ F : Finset α, F ⊆ E → ∀ R : ℝ, 0 < R →
      (∀ x ∈ F, q x ≤ R) → (F.card : ℝ) ≤ C * R ^ d) :
    ∑ x ∈ E, (1 + q x / H) ^ (-2 : ℝ) ≤ 4 * C * H ^ d := by
  have hex (x : α) : ∃ n : ℕ, (2:ℝ)^n ≤ 1 + q x / H ∧
      1 + q x / H < (2:ℝ)^(n+1) :=
    exists_nat_pow_near (by linarith [div_nonneg (hq x) hH.le]) (by norm_num)
  let bin (x : α) : ℕ := Classical.choose (hex x)
  have hlo (x : α) : (2:ℝ)^(bin x) ≤ 1 + q x / H := (Classical.choose_spec (hex x)).1
  have hhi (x : α) : 1 + q x / H < (2:ℝ)^(bin x+1) := (Classical.choose_spec (hex x)).2
  have hbin (n : ℕ) :
      ∑ x ∈ E.filter (fun x => bin x = n), (1 + q x / H) ^ (-2 : ℝ) ≤
        (2*C*H^d) * (1/2:ℝ)^n := by
    let F := E.filter (fun x => bin x = n)
    have hcard : (F.card:ℝ) ≤ C * ((2:ℝ)^(n+1)*H)^d := by
      apply hcount F (Finset.filter_subset _ _) _ (by positivity)
      intro x hx
      have he := (Finset.mem_filter.mp hx).2
      have hh := hhi x
      rw [he] at hh
      have hqdiv : q x/H ≤ (2:ℝ)^(n+1) := by linarith
      exact (div_le_iff₀ hH).mp hqdiv
    have hweight (x : α) (hx : x∈F) : (1+q x/H)^(-2:ℝ) ≤ (1/4:ℝ)^n := by
      have hl := hlo x
      rw [(Finset.mem_filter.mp hx).2] at hl
      apply (Real.rpow_le_rpow_of_nonpos (by positivity) hl (by norm_num)).trans_eq
      rw [Real.rpow_neg (by positivity), Real.rpow_two, ← pow_mul, Nat.mul_comm, pow_mul, ← inv_pow]
      norm_num
    have hp : ((2:ℝ)^(n+1))^d ≤ (2:ℝ)^(n+1) :=
      Real.rpow_le_self_of_one_le (one_le_pow₀ (by norm_num)) hd
    calc
      _ ≤ (F.card:ℝ)*(1/4:ℝ)^n := by
        apply (Finset.sum_le_sum hweight).trans_eq
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C*((2:ℝ)^(n+1)*H)^d)*(1/4:ℝ)^n :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (C*((2:ℝ)^(n+1)*H^d))*(1/4:ℝ)^n := by
        rw [Real.mul_rpow (by positivity) hH.le]
        gcongr
      _ = (2*C*H^d)*((2:ℝ)^n*(1/4:ℝ)^n) := by rw [pow_succ]; ring
      _ = _ := by rw [←mul_pow]; norm_num
  have hsum : (∑ x∈E,(1+q x/H)^(-2:ℝ)) =
      ∑ n∈E.image bin, ∑ x∈E.filter (fun x=>bin x=n), (1+q x/H)^(-2:ℝ) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) _
  rw [hsum]
  apply (Finset.sum_le_sum (fun n _=>hbin n)).trans
  have hs := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).mul_left (2*C*H^d)
  apply (Summable.sum_le_tsum _ (by intro n _; positivity) hs).trans_eq
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)]
  ring

theorem nonzero_frequency_count (E : Finset O) (R : ℝ) (hR : 0 < R)
    (hE : ∀ k∈E, k≠0) (hN : ∀ k∈E, frequencyNorm k≤R) :
    (E.card:ℝ) ≤ 128*R := by
  by_cases hr : 1≤R
  · apply DescentFiberCost.finite_element_count_real E R hr
    intro k hk
    simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,frequencyNorm]
      using hN k hk
  · have he : E=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro k hk
      have hh := frequencyNorm_one_le k (hE k hk)
      have hb := hN k hk
      linarith)
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem frequency_weighted_sum :
    ∃ K : ℝ, 0<K ∧ ∀ (E : Finset O) (H : ℝ), 0<H →
      (∀ k∈E,k≠0) →
      ∑ k∈E,(1+frequencyNorm k/H)^(-2:ℝ) ≤ K*H := by
  refine ⟨512,by norm_num,?_⟩
  intro E H hH hE
  have hh := finite_weighted_of_count E frequencyNorm frequencyNorm_nonneg
    128 1 H (by norm_num) (by norm_num) hH (by
      intro F hFE R hR hN
      simpa only [Real.rpow_one] using
        nonzero_frequency_count F R hR (fun k hk=>hE k (hFE hk)) hN)
  norm_num only [Real.rpow_one,show (4:ℝ)*128=512 by norm_num] at hh
  exact hh

theorem exceptional_frequency_weighted_sum (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ, 0<K ∧ ∀ G : Ideal O, G≠0 → ∀ (E : Finset O) (H : ℝ), 0<H →
      (∀ k∈E,k≠0) →
      (∀ k∈E,∀ P∉IdealMobiusDivisorSum.primeSupport G,
        CenteredExceptionalCount.valuation (Ideal.span {k}) P % 6=0) →
      ∑ k∈E,(1+frequencyNorm k/H)^(-2:ℝ) ≤
        K*(Ideal.absNorm G:ℝ)^ε*H^(1/6:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := ProbePhysical.lowGramExceptional_count ε hε
  refine ⟨4*C,by positivity,?_⟩
  intro G hG E H hH hE hres
  have hh := finite_weighted_of_count E frequencyNorm frequencyNorm_nonneg
    (C*(Ideal.absNorm G:ℝ)^ε) (1/6) H (by positivity) (by norm_num) hH (by
      intro F hFE R hR hN
      exact hcount G hG F R hR.le (fun k hk=>hE k (hFE hk))
        (fun k hk=>hres k (hFE hk)) hN)
  convert hh using 1
  ring

end SevenEighths.ProbeGramFrequencySummation

end

end OAI
