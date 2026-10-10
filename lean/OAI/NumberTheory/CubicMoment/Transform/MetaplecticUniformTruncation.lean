import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformTail
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTailTruncation

namespace OAI

/-! Uniform arbitrary-power truncation for the original weight family.
The far-left line and the constant are chosen before the weight index. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_twisted_tail_natural_cutoff
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ) (m : ℕ)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hm : σ ≤ (m:ℝ)-1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ X J T : ℝ, 0 < X → 0 < J → 1 ≤ T → ∀ t : ℝ, |t| ≤ 2*T →
      ‖∑' nd, metaplecticFarTailTerm a r ℓ (fun x => W i x*mellinPhase t x)
          ((m:ℝ)-1/2) X J nd‖ ≤
        C*norm r^ε*T^2*(norm r^2*T^4/X)^σ*
          ((norm r^2*T^4/X)/J)^(((m:ℝ)-1/2)-σ) := by
  obtain ⟨C,hC,hbound⟩ := h.metaplectic_twisted_tail_bound ha ℓ m hε hσ hm
  refine ⟨C*3^(4*m),mul_nonneg hC (by positivity),?_⟩
  intro i r hr hsr X J T hX hJ hT t ht
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hTp : 0 < T := zero_lt_one.trans_le hT
  calc
    _ ≤ C*norm r^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*
        J^(-(((m:ℝ)-1/2)-σ))*(1+|t|)^(4*m) := hbound i r hr hsr X J hX hJ t
    _ ≤ C*norm r^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*
        J^(-(((m:ℝ)-1/2)-σ))*(3^(4*m)*T^(4*m)) :=
      mul_le_mul_of_nonneg_left (metaplectic_height_nat_power hT ht m) (by positivity)
    _ = (C*3^(4*m))*(norm r^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*
        J^(-(((m:ℝ)-1/2)-σ))*T^(4*m)) := by ring
    _ = _ := by rw [metaplectic_tail_scale_identity hR hX hTp hJ]; ring


theorem UniformLogWeights.metaplectic_twisted_tail_arbitrary_power
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ)
    {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (B H : ℝ) :
    ∃ (m : ℕ) (C : ℝ), 2 ≤ m ∧ σ ≤ (m:ℝ)-1/2 ∧ 0 ≤ C ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X J T : ℝ, 1 ≤ Y → 0 < X → 0 < J → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → norm r^2*T^4/X ≤ Y^B →
      (norm r^2*T^4/X)/J ≤ Y^(-δ) → ∀ t : ℝ, |t| ≤ 2*T →
      ‖∑' nd, metaplecticFarTailTerm a r ℓ (fun x => W i x*mellinPhase t x)
          ((m:ℝ)-1/2) X J nd‖ ≤ C*Y^(-H) := by
  obtain ⟨m,hm2,hms,horder⟩ := exists_metaplectic_tail_order hδ B 1 σ H
  obtain ⟨C,hC,hbound⟩ := h.metaplectic_twisted_tail_natural_cutoff ha ℓ m
    (by norm_num : (0:ℝ) < 1) hσ hms
  refine ⟨m,C,hm2,hms,hC,?_⟩
  intro i r hr hsr Y X J T hY hX hJ hT hRB hTB hDB hcut t ht
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hD : 0 < norm r^2*T^4/X := by positivity
  have hs := metaplectic_tail_power_absorption hY hR hTp hD hJ
    (by norm_num : (0:ℝ) ≤ 1) hσ.le (sub_nonneg.mpr hms)
    hRB hTB hDB hcut horder
  calc
    _ ≤ C*norm r^(1:ℝ)*T^2*(norm r^2*T^4/X)^σ*
        ((norm r^2*T^4/X)/J)^(((m:ℝ)-1/2)-σ) := hbound i r hr hsr X J T hX hJ hT t ht
    _ = C*(norm r^(1:ℝ)*T^2*(norm r^2*T^4/X)^σ*
        ((norm r^2*T^4/X)/J)^(((m:ℝ)-1/2)-σ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hC


end CubicFirstMoment

end

end OAI
