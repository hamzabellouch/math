import OAI.NumberTheory.DirichletL.Moments.ReflectionLength
import OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.CenteredMomentCommonMaskChildCapacity
open HeckeFamily HeckeDyadic CenteredMomentComparisonReflection
local notation "O" => HeckeFamily.O

lemma polynomial_nonzero_support (χ : Character) (W : ℝ→ℂ) (X sigma t b : ℝ)
    (hX : 0<X) (hs : Function.support W⊆Set.Iic b)
    (hn : polynomial χ false W X sigma t≠0) : 1≤b*X := by
  by_contra hh
  have hb : b*X<1:=lt_of_not_ge hh
  apply hn
  unfold polynomial
  have hzero : ∀I : NonzeroIdeal,summand χ false W X sigma t I=0 := by
    intro I
    have hW : W (norm I/X)=0 := by
      by_contra hW
      have hu:=hs hW
      have hle : norm I≤b*X:=(div_le_iff₀ hX).mp hu
      have hi : 1≤norm I := by
        change 1≤(I.val.absNorm:ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
      linarith
    simp only [summand,hW,mul_zero,zero_mul]
  simp only [hzero,tsum_zero,mul_zero]

lemma actual_clipped_log (χ : Character) (W : ℝ→ℂ) (Z X sigma t b : ℝ)
    (hZ : 1<Z) (hX : 0<X) (hs : Function.support W⊆Set.Iic b)
    (hn : polynomial χ false W X sigma t≠0) :
    0≤Real.logb Z (max 1 X) ∧
      Real.logb Z (max 1 X)≤Real.logb Z X+Real.logb Z (max 1 b) := by
  have hB : 0<max 1 b:=zero_lt_one.trans_le (le_max_left _ _)
  have hclip : max 1 X≤max 1 b*X := by
    apply max_le
    · exact (polynomial_nonzero_support χ W X sigma t b hX hs hn).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hX.le)
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 b) hX.le
  refine ⟨Real.logb_nonneg hZ (le_max_left _ _),?_⟩
  have hh:=Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (le_max_left 1 X)) hclip
  rw [Real.logb_mul hB.ne' hX.ne'] at hh
  linarith

lemma deleted_same_product (X₁ X₂ Y₁ Y₂ T d₁ d₂ : ℝ)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/d₁)*(X₂/d₂)=T/(d₁*d₂) ∧
      (Y₁/d₁)*(Y₂/d₂)=T/(d₁*d₂) := by
  constructor <;> rw [div_mul_div_comm]
  · rw [hX]
  · rw [hY]

theorem actual_deleted_capacity {α : Type*} [DecidableEq α]
    (F J : Finset α) (hJ : J⊆F) (P : α→ℝ) (hP : ∀i∈F,1≤P i)
    (χ : Character) (W₁ W₂ : ℝ→ℂ) (Z X₁ X₂ t₁ t₂ b₁ b₂ kappa M : ℝ)
    (D₁ D₂ : Ideal O) (hD₁ : D₁≠0) (hD₂ : D₂≠0)
    (hZ : 1<Z) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hk : 0≤kappa)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hn : polynomial χ false W₁ (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
      polynomial χ false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂≠0)
    (hcap : Real.logb Z (X₁*X₂)+6*kappa*(∑i∈F,Real.logb Z (P i))≤M) :
    let n₁:=Real.logb Z (max 1 (X₁/(D₁.absNorm:ℝ)))
    let n₂:=Real.logb Z (max 1 (X₂/(D₂.absNorm:ℝ)))
    0≤n₁ ∧ 0≤n₂ ∧ n₁+n₂+6*kappa*(∑i∈J,Real.logb Z (P i))≤
      M+Real.logb Z (max 1 b₁*max 1 b₂) := by
  have hd₁ : 1≤(D₁.absNorm:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD₁)
  have hd₂ : 1≤(D₂.absNorm:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD₂)
  have hd₁p : 0<(D₁.absNorm:ℝ):=zero_lt_one.trans_le hd₁
  have hd₂p : 0<(D₂.absNorm:ℝ):=zero_lt_one.trans_le hd₂
  have hc₁:=actual_clipped_log χ W₁ Z _ 0 t₁ b₁ hZ (div_pos hX₁ hd₁p) hs₁ (mul_ne_zero_iff.mp hn).1
  have hc₂:=actual_clipped_log χ W₂ Z _ 0 t₂ b₂ hZ (div_pos hX₂ hd₂p) hs₂ (mul_ne_zero_iff.mp hn).2
  have hslots : (∑i∈J,Real.logb Z (P i))≤∑i∈F,Real.logb Z (P i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hJ (fun i hi _=>Real.logb_nonneg hZ (hP i hi))
  have hslots' := mul_le_mul_of_nonneg_left hslots (by positivity : 0≤6*kappa)
  have hlog₁:=Real.logb_nonneg hZ hd₁
  have hlog₂:=Real.logb_nonneg hZ hd₂
  rw [Real.logb_div hX₁.ne' hd₁p.ne'] at hc₁
  rw [Real.logb_div hX₂.ne' hd₂p.ne'] at hc₂
  rw [Real.logb_mul hX₁.ne' hX₂.ne'] at hcap
  have hb₁ : 0<max 1 b₁:=zero_lt_one.trans_le (le_max_left _ _)
  have hb₂ : 0<max 1 b₂:=zero_lt_one.trans_le (le_max_left _ _)
  dsimp only
  refine ⟨hc₁.1,hc₂.1,?_⟩
  rw [Real.logb_mul hb₁.ne' hb₂.ne']
  linarith [hc₁.2,hc₂.2]

lemma eventually_fixed_clipping_cost (b₁ b₂ delta : ℝ) (hdelta : 0<delta) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ Real.logb Z (max 1 b₁*max 1 b₂)≤delta := by
  have hc:=(tendsto_rpow_atTop hdelta).eventually (eventually_ge_atTop (max 1 b₁*max 1 b₂))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc] with Z hZ hC
  refine ⟨hZ,?_⟩
  exact (Real.logb_le_iff_le_rpow hZ (mul_pos
    (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _)))).mpr hC
end SevenEighths.CenteredMomentCommonMaskChildCapacity

end

end OAI
