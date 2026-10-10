import Mathlib
import OAI.Computability.MinUncut.Analysis.LowGradientEnergyLowerWeighted
import OAI.Computability.MinUncut.Analysis.FreshCorrelation

namespace OAI

section
noncomputable section
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sourceSigma (J : ℝ) : ℝ := 1/(2560*J)
def sourceEta (J : ℝ) : ℝ := (sourceSigma J)^2/(2560*J)
def sourceR (J : ℝ) : ℕ := ⌈(sourceEta J)⁻¹^2⌉₊
def sourceT (J : ℝ) : ℕ := ⌈32*J/(sourceEta J*(sourceSigma J)^4)⌉₊

lemma sourceSigma_pos {J : ℝ} (hJ : 1 ≤ J) : 0 < sourceSigma J := by
  unfold sourceSigma
  positivity
lemma sourceEta_pos {J : ℝ} (hJ : 1 ≤ J) : 0 < sourceEta J := by
  unfold sourceEta
  have hs := sourceSigma_pos hJ
  positivity
lemma sourceSigma_le_one {J : ℝ} (hJ : 1 ≤ J) : sourceSigma J ≤ 1 := by
  unfold sourceSigma
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2560*J)).mpr
  linarith
lemma sourceEta_le_sigma {J : ℝ} (hJ : 1 ≤ J) : sourceEta J ≤ sourceSigma J := by
  have hs := sourceSigma_pos hJ
  have hs1 := sourceSigma_le_one hJ
  have hJpos : 0 < J := by linarith
  unfold sourceEta
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2560*J)).mpr
  nlinarith
lemma sourceR_bound {J : ℝ} (hJ : 1 ≤ J) : 1 ≤ (sourceR J:ℝ)*(sourceEta J)^2 := by
  have hη := sourceEta_pos hJ
  have hh := Nat.le_ceil ((sourceEta J)⁻¹^2)
  have hw := mul_le_mul_of_nonneg_right hh (sq_nonneg (sourceEta J))
  have he : (sourceEta J)⁻¹^2*(sourceEta J)^2=1 := by field_simp
  simpa only [he,sourceR] using hw
lemma sourceT_pos {J : ℝ} (hJ : 1 ≤ J) : 0 < sourceT J := by
  apply Nat.ceil_pos.mpr
  have hη := sourceEta_pos hJ
  have hσ := sourceSigma_pos hJ
  positivity
lemma sourceT_bound {J : ℝ} (hJ : 1 ≤ J) :
    32*J ≤ (sourceT J:ℝ)*sourceEta J*(sourceSigma J)^4 := by
  have hη := sourceEta_pos hJ
  have hσ := sourceSigma_pos hJ
  have hh := Nat.le_ceil (32*J/(sourceEta J*(sourceSigma J)^4))
  exact (div_le_iff₀ (by positivity)).mp hh |>.trans_eq (by unfold sourceT; ring)

lemma source_row_rate {J : ℝ} (hJ : 1 ≤ J) {m : ℕ} (hm : 0 < m) :
    0 ≤ (sourceEta J)^2/(m:ℝ) ∧ (sourceEta J)^2/(m:ℝ) ≤ 1 ∧
    ∀ k : ℕ, sourceR J*m < k → 1 ≤ (k:ℝ)*((sourceEta J)^2/(m:ℝ)) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hetapos := sourceEta_pos hJ
  have heta1 : sourceEta J ≤ 1 := (sourceEta_le_sigma hJ).trans (sourceSigma_le_one hJ)
  refine ⟨by positivity,?_,?_⟩
  · apply (div_le_iff₀ hm').mpr
    nlinarith
  · intro k hk
    have hk' : (sourceR J:ℝ)*(m:ℝ) ≤ k := by exact_mod_cast hk.le
    have hh := mul_le_mul_of_nonneg_right hk' (show 0 ≤ (sourceEta J)^2/(m:ℝ) by positivity)
    have he : (sourceR J:ℝ)*(m:ℝ)*((sourceEta J)^2/(m:ℝ)) =
        (sourceR J:ℝ)*(sourceEta J)^2 := by field_simp
    rw [he] at hh
    exact (sourceR_bound hJ).trans hh
end MinUncut.Inner

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)] {m n : ℕ}

theorem source_lowGradient_energy (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ)
    (hw1 : ∑ ξ, w ξ=1) (f : ∀ ξ, FoldedProof (A ξ)) {J : ℝ} (hJ : 1 ≤ J)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : ℕ)
    (hs : ∀ k : ℕ, s+2 ≤ k → (k:ℝ)*(smoothingRho (sourceSigma J))^(2*k) ≤ 1/16)
    (h1 : (∑ ξ, w ξ*firstError (m := m) (n := n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J*(10*sourceSigma J))
    (h2 : (∑ ξ, w ξ*secondError (m := m) (n := n) (f ξ)
      ((sourceEta J)^2/(m:ℝ)) (sourceSigma J) (sourceEta J)) ≤ J*(10*(sourceEta J+sourceEta J))) :
    1/2 ≤ (∑ ξ, w ξ*averagedEnergy
      (lowGradient (m := m) (n := n) (sourceR J*m) s (f ξ) (sourceSigma J) (sourceEta J))) ∧
    (∑ ξ, w ξ*averagedEnergy
      (lowGradient (m := m) (n := n) (sourceR J*m) s (f ξ) (sourceSigma J) (sourceEta J))) ≤
        (sourceSigma J)⁻¹^2 := by
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  have hσ := sourceSigma_pos hJ
  have hη := sourceEta_pos hJ
  obtain ⟨ha,ha1,hD⟩ := source_row_rate hJ hm0
  have hL := lowGradient_energy_lower_weighted (m := m) (n := n) V A w hw hw1 f hn0 hσ.ne' hη.ne' ha ha1
    (by norm_num : (0:ℝ) ≤ 1/16) (sourceR J*m) s hD hs
  have hJ0 : J≠0 := ne_of_gt (by linarith)
  have hc1 : 4*(J*(10*sourceSigma J))=1/64 := by
    unfold sourceSigma
    field_simp
    ring
  have hc2 : 8*(sourceSigma J)⁻¹^2*(J*(10*(sourceEta J+sourceEta J)))=1/16 := by
    unfold sourceEta sourceSigma
    field_simp
    ring
  have hf1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 4)
  have hf2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 8*(sourceSigma J)⁻¹^2 by positivity)
  rw [hc1] at hf1
  rw [hc2] at hf2
  constructor
  · linarith
  · calc
      _ ≤ ∑ ξ, w ξ*(sourceSigma J)⁻¹^2 := Finset.sum_le_sum
        (fun ξ _ => mul_le_mul_of_nonneg_left
          (averagedEnergy_lowGradient_le (m := m) (sourceR J*m) s (f ξ) hn0 hσ.ne' (sourceEta J)) (hw ξ))
      _ = _ := by rw [← Finset.sum_mul,hw1,one_mul]

theorem source_lowGradient_correlation (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ)
    (hw1 : ∑ ξ, w ξ=1) (f : ∀ ξ, FoldedProof (A ξ)) {J : ℝ} (hJ : 1 ≤ J)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : ℕ)
    (hs : ∀ k : ℕ, s+2 ≤ k → (k:ℝ)*(smoothingRho (sourceSigma J))^(2*k) ≤ 1/16)
    (h1 : (∑ ξ, w ξ*firstError (m := m) (n := n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J*(10*sourceSigma J))
    (h2 : (∑ ξ, w ξ*secondError (m := m) (n := n) (f ξ)
      ((sourceEta J)^2/(m:ℝ)) (sourceSigma J) (sourceEta J)) ≤ J*(10*(sourceEta J+sourceEta J)))
    (h3 : (∑ ξ, w ξ*thirdError (m := m) (n := n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J/(Fintype.card (Code m n):ℝ)) :
    1/(4*(sourceT J:ℝ)) ≤ ∑ ξ, w ξ*averagedCorrelation
      (lowGradient (m := m) (n := n) (sourceR J*m) s (f ξ) (sourceSigma J) (sourceEta J)) := by
  have hn0 : 0 < n := by omega
  have hσ := sourceSigma_pos hJ
  have hη := sourceEta_pos hJ
  have hT : (0:ℝ) < sourceT J := by exact_mod_cast sourceT_pos hJ
  obtain ⟨hE,hE'⟩ := source_lowGradient_energy V A w hw hw1 f hJ hm hn s hs h1 h2
  have hU := lowGradient_correlation_truncated_weighted (m := m) (n := n) V A (sourceR J*m) s w hw f hn0 hσ.ne' hη hT
    (show 0 < (sourceSigma J)^2/8 by positivity)
  have he := mul_le_mul_of_nonneg_left hE'
    (show 0 ≤ (sourceSigma J)^2/8 by positivity)
  have hea : ((sourceSigma J)^2/8)*(sourceSigma J)⁻¹^2=1/8 := by field_simp
  rw [hea] at he
  have hc : (0:ℝ) < Fintype.card (Code m n) := by positivity
  have hz := mul_le_mul_of_nonneg_left h3
    (show 0 ≤ ((sourceSigma J)⁻¹^2/(4*((sourceSigma J)^2/8)*(sourceT J:ℝ)))*
      ((Fintype.card (Code m n):ℝ)/sourceEta J) by positivity)
  have hzb : ((sourceSigma J)⁻¹^2/(4*((sourceSigma J)^2/8)*(sourceT J:ℝ)))*
      ((Fintype.card (Code m n):ℝ)/sourceEta J)*(J/(Fintype.card (Code m n):ℝ)) =
      2*J/(sourceEta J*(sourceSigma J)^4*(sourceT J:ℝ)) := by
    field_simp
    ring
  rw [hzb] at hz
  have hzt : 2*J/(sourceEta J*(sourceSigma J)^4*(sourceT J:ℝ)) ≤ 1/16 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sourceT_bound hJ]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 4*(sourceT J:ℝ))).mpr
  nlinarith
end MinUncut.Inner

end
end

end OAI
