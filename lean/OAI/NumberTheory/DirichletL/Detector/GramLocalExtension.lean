import OAI.NumberTheory.DirichletL.Detector.GramCommonLinear
import OAI.NumberTheory.DirichletL.Moments.Canonical

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge CenteredMomentCorrelation CenteredMomentCanonical
local notation "O" => ActualEisensteinCubic.O

lemma finiteField_local_norm {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (u v k : F) (huv : u≠0 ∨ v≠0) :
    ‖localCorrelation χ u v k‖≤(Fintype.card F:ℝ) := by
  rcases huv with hu|hv
  · exact fullCorrelation_bezout_norm u v u⁻¹ 0 k (by simp [hu]) χ χ
      (FiniteRayExpansion.norm_char_le_one χ) (FiniteRayExpansion.norm_char_le_one χ)
  · exact fullCorrelation_bezout_norm u v 0 v⁻¹ k (by simp [hv]) χ χ
      (FiniteRayExpansion.norm_char_le_one χ) (FiniteRayExpansion.norm_char_le_one χ)

def localExtension (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (n₁ n₂ k : O) : ℂ := by
  letI : Fintype (O⧸P) := Fintype.ofFinite _
  letI : Field (O⧸P) := Ideal.Quotient.field P
  exact if n₁∈P ∧ n₂∈P then 0 else (Ideal.absNorm P:ℂ)^(c-1)*
    localCorrelation (actualSextic P hg^c) (Ideal.Quotient.mk P n₁)
      (Ideal.Quotient.mk P n₂) (Ideal.Quotient.mk P k)

lemma localExtension_both_zero (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (n₁ n₂ k : O) (h₁ : n₁∈P) (h₂ : n₂∈P) :
    localExtension P hg c n₁ n₂ k=0 := by simp [localExtension,h₁,h₂]

theorem localExtension_periodic (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (n₁ n₂ m₁ m₂ k l : O)
    (h₁ : n₁-m₁∈P) (h₂ : n₂-m₂∈P) (hk : k-l∈P) :
    localExtension P hg c n₁ n₂ k=localExtension P hg c m₁ m₂ l := by
  have he₁ := Ideal.Quotient.eq.mpr h₁
  have he₂ := Ideal.Quotient.eq.mpr h₂
  have hek := Ideal.Quotient.eq.mpr hk
  have hm₁ : n₁∈P↔m₁∈P := by
    rw [←Ideal.Quotient.eq_zero_iff_mem,he₁,Ideal.Quotient.eq_zero_iff_mem]
  have hm₂ : n₂∈P↔m₂∈P := by
    rw [←Ideal.Quotient.eq_zero_iff_mem,he₂,Ideal.Quotient.eq_zero_iff_mem]
  simp only [localExtension,hm₁,hm₂,he₁,he₂,hek]

theorem localExtension_norm (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (hc : 1≤c) (n₁ n₂ k : O) :
    ‖localExtension P hg c n₁ n₂ k‖≤(Ideal.absNorm P:ℝ)^c := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  let : Field (O⧸P) := Ideal.Quotient.field P
  unfold localExtension
  split_ifs with hn
  · simp only [norm_zero]
    positivity
  have huv : Ideal.Quotient.mk P n₁≠0 ∨ Ideal.Quotient.mk P n₂≠0 := by
    by_contra hh
    push Not at hh
    exact hn ⟨Ideal.Quotient.eq_zero_iff_mem.mp hh.1,Ideal.Quotient.eq_zero_iff_mem.mp hh.2⟩
  have hh := finiteField_local_norm (actualSextic P hg^c) (Ideal.Quotient.mk P n₁)
    (Ideal.Quotient.mk P n₂) (Ideal.Quotient.mk P k) huv
  rw [norm_mul,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ (Ideal.absNorm P:ℝ)^(c-1)*(Ideal.absNorm P:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hh
    _ = _ := by rw [←pow_succ,Nat.sub_add_cancel hc]

theorem primePower_common_extension (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (hc : 1≤c) [Fintype (O⧸P^c)] (n₁ n₂ k : O)
    (hn : n₁∉P ∨ n₂∉P) :
    fullCorrelation (fun x : O⧸P^c=>Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸P^c=>Ideal.Quotient.mk _ n₁*y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) (Ideal.Quotient.mk _ k)=
      localExtension P hg c n₁ n₂ k := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  let : Field (O⧸P) := Ideal.Quotient.field P
  have hn' : ¬(n₁∈P ∧ n₂∈P) := by tauto
  rw [localExtension,ite_eq_right hn']
  rcases hn with h₁|h₂
  · have hu : IsUnit (Ideal.Quotient.mk (P^c) n₁) :=
      (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
        (isUnit_iff_ne_zero.mpr (fun hz=>h₁ (Ideal.Quotient.eq_zero_iff_mem.mp hz)))
    obtain ⟨u,hu⟩ := hu
    rw [←hu]
    unfold primePowerRow
    rw [primePower_localCorrelation]
    simp only [primePowerReduction,Ideal.Quotient.factor_mk,hu]
  · have hv : IsUnit (Ideal.Quotient.mk (P^c) n₂) :=
      (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
        (isUnit_iff_ne_zero.mpr (fun hz=>h₂ (Ideal.Quotient.eq_zero_iff_mem.mp hz)))
    obtain ⟨v,hv⟩ := hv
    rw [←hv]
    unfold primePowerRow
    rw [fullCorrelation_reduction_unit_left _ (primePowerReduction_surjective P hc),
      primePowerReduction_multiplicity,Nat.cast_pow]
    change (Ideal.absNorm P:ℂ)^(c-1)*localCorrelation (actualSextic P hg^c)
      (primePowerReduction P hc (Ideal.Quotient.mk _ n₁)) (primePowerReduction P hc v)
      (primePowerReduction P hc (Ideal.Quotient.mk _ k))=_
    simp only [hv,primePowerReduction,Ideal.Quotient.factor_mk]

end SevenEighths.ProbeGramCommon
end

end OAI
