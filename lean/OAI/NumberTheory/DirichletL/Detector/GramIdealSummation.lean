import OAI.NumberTheory.DirichletL.Foundation

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

def gramIdealNorm (I : SupportedIdeal) : ℝ := Ideal.absNorm I.val

lemma gramIdealNorm_pos (I : SupportedIdeal) : 0 < gramIdealNorm I := by
  unfold gramIdealNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property.1)

lemma gramIdealNorm_one_le (I : SupportedIdeal) : 1 ≤ gramIdealNorm I := by
  unfold gramIdealNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property.1)

theorem supportedIdeal_rpow_summable (r : ℝ) (hr : r < -1) :
    Summable (fun I : SupportedIdeal => gramIdealNorm I ^ r) := by
  have hs := CubicEisenstein.fullIdealWeight_summable_norm ((-r:ℝ):ℂ)
    (by simp only [Complex.ofReal_re]; linarith)
  have hinj : Function.Injective (fun I : SupportedIdeal => I.val) := Subtype.val_injective
  have ht := hs.comp_injective hinj
  apply ht.congr
  intro I
  rw [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right I.property.1]
  have he : (Ideal.absNorm I.val:ℂ) = ((gramIdealNorm I:ℝ):ℂ) := by simp [gramIdealNorm]
  rw [he,Complex.norm_cpow_eq_rpow_re_of_pos (gramIdealNorm_pos I)]
  simp only [Complex.neg_re,Complex.ofReal_re,neg_neg]

theorem supportedIdeal_rpow_finite_bound (r : ℝ) (hr : r < -1) :
    ∃ K : ℝ, 0 < K ∧ ∀ F : Finset SupportedIdeal,
      (∑ I ∈ F, gramIdealNorm I ^ r) ≤ K := by
  have hs := supportedIdeal_rpow_summable r hr
  let K := 1 + ∑' I : SupportedIdeal, gramIdealNorm I ^ r
  have hn : 0 ≤ ∑' I : SupportedIdeal, gramIdealNorm I ^ r :=
    tsum_nonneg (fun I => Real.rpow_nonneg (gramIdealNorm_pos I).le _)
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro F
  exact (hs.sum_le_tsum F (fun I _ => Real.rpow_nonneg (gramIdealNorm_pos I).le _)).trans
    (by dsimp [K]; linarith)

lemma ideal_sum_min_power_bound (t : ℝ) (ht : 0 < t) (A : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hA : θ ≤ A) : min 1 (t^A) ≤ t^θ := by
  by_cases h : t ≤ 1
  · apply (min_le_right _ _).trans
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge ht h hA
  · exact (min_le_left _ _).trans (Real.one_le_rpow (le_of_not_ge h) hθ)

lemma gram_ideal_term_bound (δ Λ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hΛ : 0 < Λ) (A : ℕ) (hA : 1 ≤ A) (I J : SupportedIdeal) :
    gramIdealNorm I ^ (-2:ℝ) * gramIdealNorm J ^ (-2:ℝ) *
      min 1 ((gramIdealNorm I*gramIdealNorm J/Λ)^A) ≤
      Λ^(-1+δ) * (gramIdealNorm I^(-1-δ) * gramIdealNorm J^(-1-δ)) := by
  have hi := gramIdealNorm_pos I
  have hj := gramIdealNorm_pos J
  have ha : (1-δ:ℝ) ≤ A := by
    have hh : (1:ℝ) ≤ A := by exact_mod_cast hA
    linarith
  have hm := ideal_sum_min_power_bound (gramIdealNorm I*gramIdealNorm J/Λ)
    (by positivity) A (1-δ) (by linarith) ha
  apply (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
  rw [Real.div_rpow (by positivity) hΛ.le,Real.mul_rpow hi.le hj.le,
    div_eq_mul_inv,← Real.rpow_neg hΛ.le]
  have hi' : gramIdealNorm I^(-2:ℝ)*gramIdealNorm I^(1-δ)=gramIdealNorm I^(-1-δ) := by
    rw [←Real.rpow_add hi]
    congr 1
    ring
  have hj' : gramIdealNorm J^(-2:ℝ)*gramIdealNorm J^(1-δ)=gramIdealNorm J^(-1-δ) := by
    rw [←Real.rpow_add hj]
    congr 1
    ring
  rw [show -(1-δ) = -1+δ by ring]
  calc
    _ = Λ^(-1+δ)*((gramIdealNorm I^(-2:ℝ)*gramIdealNorm I^(1-δ))*
        (gramIdealNorm J^(-2:ℝ)*gramIdealNorm J^(1-δ))) := by ring
    _ = _ := by rw [hi',hj']

theorem gram_supported_double_sum (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : ℕ), 1 ≤ A → ∀ (Λ : ℝ), 0 < Λ →
      ∀ (F G : Finset SupportedIdeal),
      (∑ I ∈ F, ∑ J ∈ G, gramIdealNorm I^(-2:ℝ) * gramIdealNorm J^(-2:ℝ) *
        min 1 ((gramIdealNorm I*gramIdealNorm J/Λ)^A)) ≤ K*Λ^(-1+δ) := by
  obtain ⟨C,hC,hb⟩ := supportedIdeal_rpow_finite_bound (-1-δ) (by linarith)
  refine ⟨C^2, by positivity, ?_⟩
  intro A hA Λ hΛ F G
  have hF := hb F
  have hG := hb G
  have hGn : 0 ≤ ∑ J ∈ G, gramIdealNorm J^(-1-δ) :=
    Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (gramIdealNorm_pos J).le _)
  calc
    _ ≤ ∑ I ∈ F, ∑ J ∈ G, Λ^(-1+δ)*
        (gramIdealNorm I^(-1-δ)*gramIdealNorm J^(-1-δ)) :=
      Finset.sum_le_sum (fun I _ => Finset.sum_le_sum
        (fun J _ => gram_ideal_term_bound δ Λ hδ hδ1 hΛ A hA I J))
    _ = Λ^(-1+δ)*((∑ I ∈ F, gramIdealNorm I^(-1-δ))*
        (∑ J ∈ G, gramIdealNorm J^(-1-δ))) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ Λ^(-1+δ)*C^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [pow_two] using mul_le_mul hF hG hGn hC.le
    _ = _ := by ring

theorem gram_supported_exceptional_sum (ε : ℝ) (_hε : 0 ≤ ε) (hε1 : ε < 1/6) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F G : Finset SupportedIdeal),
      (∑ I ∈ F, ∑ J ∈ G,
        gramIdealNorm I^(-7/6+ε:ℝ)*gramIdealNorm J^(-2:ℝ)) ≤ K := by
  obtain ⟨C,hC,hb⟩ := supportedIdeal_rpow_finite_bound (-7/6+ε) (by linarith)
  obtain ⟨D,hD,hd⟩ := supportedIdeal_rpow_finite_bound (-2) (by norm_num)
  refine ⟨C*D, by positivity, ?_⟩
  intro F G
  rw [← Finset.sum_mul_sum]
  exact mul_le_mul (hb F) (hd G)
    (Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (gramIdealNorm_pos J).le _)) hC.le

end SevenEighths.ProbeGramCommon

end

end OAI
