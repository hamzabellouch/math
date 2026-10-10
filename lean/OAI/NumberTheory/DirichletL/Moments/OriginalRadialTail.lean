import OAI.NumberTheory.DirichletL.Moments.OriginalRadialComparison
import OAI.NumberTheory.DirichletL.Moments.InductionEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentOriginalRadialTail
open HeckeFamily ConcreteTraceCRT CenteredMomentAbsoluteEnergy
open CenteredMomentPositiveSummability CenteredMomentOriginalRadialComparison
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

def tailControl (A : ℕ) (Φ : 𝓢(ℝ,ℂ)) : ℝ :=
  (2:ℝ)^(A+2)*(Finset.Iic (A+2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ

lemma cauchy_all (K : ℝ) (hK : 0<K) :
    (∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹)≤4*(1+Real.pi)^2*max 1 K := by
  by_cases hk : 1≤K
  · have hh:=scaled_eisenstein_cauchy_small K⁻¹ (inv_pos.mpr hK) (inv_le_one_of_one_le₀ hk)
    rw [max_eq_right hk]
    have he : K*(K⁻¹*(∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹))=
        ∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹ := by rw [←mul_assoc,mul_inv_cancel₀ hK.ne',one_mul]
    have hb:=mul_le_mul_of_nonneg_left hh hK.le
    rw [he] at hb
    simpa only [mul_comm K] using hb
  · have hk' : K≤1:=(not_le.mp hk).le
    have hi : 1≤K⁻¹:=(one_le_inv₀ hK).mpr hk'
    have hs:=scaled_eisenstein_cauchy_summable K⁻¹ (inv_pos.mpr hK)
    have hh:=hs.tsum_le_tsum (g:=fun z:O=>((1+1*‖eisEmbedding z‖^2)^2)⁻¹) (fun z=>by
      apply inv_anti₀ (by positivity)
      gcongr)
      (scaled_eisenstein_cauchy_summable 1 (by norm_num))
    have hb:=scaled_eisenstein_cauchy_small 1 (by norm_num) (by norm_num)
    rw [max_eq_left hk',mul_one]
    exact hh.trans (by simpa only [one_mul] using hb)

lemma tail_pointwise (A : ℕ) (Φ : 𝓢(ℝ,ℂ)) (x r : ℝ) (hr : 0≤r) (hx : r≤x) :
    ‖Φ x‖≤tailControl A Φ*((1+r)^A)⁻¹*((1+x)^2)⁻¹ := by
  have hxp : 0≤x:=hr.trans hx
  have hh:=SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℝ)
    (m:=(A+2,0)) (k:=A+2) (n:=0) le_rfl le_rfl Φ x
  simp only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hxp] at hh
  change (1+x)^(A+2)*‖Φ x‖≤tailControl A Φ at hh
  have hp : (1+r)^A≤(1+x)^A:=pow_le_pow_left₀ (by positivity) (by linarith) A
  have hb : (1+r)^A*((1+x)^2*‖Φ x‖)≤tailControl A Φ := by
    apply (mul_le_mul_of_nonneg_right hp (by positivity)).trans
    simpa only [pow_add,mul_assoc] using hh
  have hd : 0<(1+r)^A*(1+x)^2:=by positivity
  rw [show tailControl A Φ*((1+r)^A)⁻¹*((1+x)^2)⁻¹=
    tailControl A Φ/((1+r)^A*(1+x)^2) by field_simp]
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hb)

theorem actual_radial_tail (A : ℕ) (F : O→ℂ) (B : ℝ) (hF : ∀z,‖F z‖≤B)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) (hR : 0≤R) :
    radialEnergy F (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K≤
      4*(1+Real.pi)^2*tailControl A Φ*B^2*max 1 K*((1+R/K)^A)⁻¹ := by
  let C:=tailControl A Φ*B^2*((1+R/K)^A)⁻¹
  have hC : 0≤C:=by dsimp [C,tailControl];positivity
  have hs:=bounded_radial_summable F B hF (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K hK
  have hp (z:O) :
      (if keep z ∧ R<‖eisEmbedding z‖^2 then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0)
      ≤C*((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹ := by
    split_ifs with hz
    · have ht:=tail_pointwise A Φ (‖eisEmbedding z‖^2/K) (R/K)
        (div_nonneg hR hK.le) (div_le_div_of_nonneg_right hz.2.le hK.le)
      have hf:=pow_le_pow_left₀ (norm_nonneg _) (hF z) 2
      have hh:=(mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul hf ht (norm_nonneg _) (sq_nonneg B))
      convert hh using 1 ; dsimp [C] ; simp only [div_eq_mul_inv] ; ring
    · exact mul_nonneg hC (by positivity)
  have hb:=Summable.tsum_le_tsum hp (hs.congr (fun z=>by by_cases hz:keep z ∧ R<‖eisEmbedding z‖^2 <;> simp [hz])) ((scaled_eisenstein_cauchy_summable K⁻¹ (inv_pos.mpr hK)).mul_left C)
  rw [tsum_mul_left] at hb
  have hh:=mul_le_mul_of_nonneg_left (cauchy_all K hK) hC
  have hh' : C*(∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹)≤
      4*(1+Real.pi)^2*tailControl A Φ*B^2*max 1 K*((1+R/K)^A)⁻¹ := by
    convert hh using 1 ; dsimp [C] ; ring
  convert hb.trans hh' using 1
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hz:keep z ∧ R<‖eisEmbedding z‖^2 <;> simp [hz]

lemma actual_radial_split (F : O→ℂ) (B : ℝ) (hF : ∀z,‖F z‖≤B)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    radialEnergy F keep Φ K=
      radialEnergy F (fun z=>keep z ∧ ‖eisEmbedding z‖^2≤R) Φ K+
      radialEnergy F (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K := by
  unfold radialEnergy
  rw [←Summable.tsum_add (bounded_radial_summable F B hF _ Φ K hK)
    (bounded_radial_summable F B hF _ Φ K hK)]
  apply tsum_congr
  intro z
  by_cases hk:keep z
  · by_cases hr:‖eisEmbedding z‖^2≤R
    · simp [hk,hr,not_lt.mpr hr]
    · simp [hk,hr,not_le.mp hr]
  · simp [hk]

theorem actual_positive_row_tail {ι:Type*} [Fintype ι] [DecidableEq ι]
    (order:ℕ) (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁) (hb₂:0≤b₂) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤B₁) (hW₂:∀x,‖W₂ x‖≤B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0<P i) (hb:∀i,0≤b i) (hB:∀i,0≤B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K R:ℝ) (hK:0<K) (hR:0≤R) :
    radialEnergy (fun z=>CenteredMomentRetainedEnergy.positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂)
      (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K≤
      4*(1+Real.pi)^2*tailControl order Φ*
        (((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i))*
        max 1 K*((1+R/K)^order)⁻¹ := by
  let E:=((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)
  have hE:0≤E:=mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hX₁.le hX₂.le)
    (Finset.prod_nonneg (fun i _=>(hP i).le)))
  have hp (z:O):‖CenteredMomentRetainedEnergy.positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤E:=
    CenteredMomentInductionEnergy.positive_squared_absolute η m A z t W₁ W₂
      b₁ b₂ B₁ B₂ X₁ X₂ hb₁ hb₂ hB₁ hB₂ hX₁ hX₂ hs₁ hs₂ hW₁ hW₂
      S β P b B hP hb hB hβ hN
  have hh:=actual_radial_tail order _ (Real.sqrt E)
    (fun z=>Real.le_sqrt_of_sq_le (hp z)) keep Φ K R hK hR
  simpa only [Real.sq_sqrt hE] using hh

end SevenEighths.CenteredMomentOriginalRadialTail

end

end OAI
