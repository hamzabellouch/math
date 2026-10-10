import OAI.Analysis.Triangular.Energy.Density
import OAI.Analysis.Triangular.Energy.Mixtures

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open Filter MeasureTheory
namespace TriangularUniversal
open PositiveMixture
/-- The shift/Fatou/Tonelli assembly applies to the exact extended ordered-pair
energy. It does not presume finite lattice energy or spacing of a competitor. -/
lemma universal_from_power_bounds (C : Set Plane)
    (hpower : ∀ v : I, latticeEnergy (powerPotential v) ≤ energy (powerPotential v) C)
    {g : ℝ → ℝ} (hg : AdmissiblePotential g) : latticeEnergy g ≤ energy g C := by
  rw [latticeEnergy_shift_iSup hg]
  apply iSup_le
  intro n
  have hε : 0<(1:ℝ)/(n+1) := by positivity
  obtain ⟨ρ,_,he,hl⟩ := shifted_mixture_energy g hg hε C
  rw [← he]
  apply (lintegral_mono (fun v => hpower v)).trans
  exact hl.trans (shifted_energy_le hg hε.le C)
end TriangularUniversal
end

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Filter
namespace TriangularUniversal
lemma diskEnergy_one {C : Set Plane} {R : ℝ} (hN : 0<diskCount C R) :
    diskEnergy (fun _ => 1) C R=((diskCount C R-1:ℕ):ℝ≥0∞) := by
  classical
  have hs : (∑ x ∈ diskPoints C R, ∑ _y ∈ (diskPoints C R).erase x, (1:ℝ≥0∞))=
      (diskCount C R:ℝ≥0∞)*((diskCount C R-1:ℕ):ℝ≥0∞) := by
    calc
      _=∑ _x ∈ diskPoints C R, ((diskCount C R-1:ℕ):ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.sum_const,Finset.card_erase_of_mem hx,nsmul_eq_mul,mul_one,diskCount]
      _=_ := by simp only [Finset.sum_const,nsmul_eq_mul,diskCount]
  unfold diskEnergy
  simp only [ENNReal.ofReal_one]
  rw [hs,← mul_assoc,ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (by simp),one_mul]
lemma count_sub_one_tendsto {C : Set Plane} (hD : DensityOne C) :
    Tendsto (fun R : ℝ => ((diskCount C R-1:ℕ):ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  have hp := hD.eventually (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  filter_upwards [hp,eventually_ge_atTop (max (1:ℝ) (K+2)),density_count_eventually_pos hD] with R h hR hn
  have hR1 : 1≤R := le_trans (le_max_left _ _) hR
  have hRK : K+2≤R := le_trans (le_max_right _ _) hR
  have hrp : 0<R := by linarith
  have hh := (lt_div_iff₀ (mul_pos Real.pi_pos (sq_pos_of_pos hrp))).mp h
  have hn' : (1:ℕ)≤diskCount C R := hn
  rw [Nat.cast_sub hn',Nat.cast_one]
  have hpi := Real.pi_gt_three
  have hp2 := mul_le_mul_of_nonneg_right hpi.le (sq_nonneg R)
  nlinarith [sq_nonneg (R-1)]
lemma energy_one {C : Set Plane} (hD : DensityOne C) : energy (fun _ => 1) C=∞ := by
  have ht := ENNReal.tendsto_ofReal_atTop.comp (count_sub_one_tendsto hD)
  have he : (fun R : ℝ => diskEnergy (fun _ => 1) C R)=ᶠ[atTop]
      (fun R : ℝ => ENNReal.ofReal ((diskCount C R-1:ℕ):ℝ)) := by
    filter_upwards [density_count_eventually_pos hD] with R hR
    rw [diskEnergy_one hR,ENNReal.ofReal_natCast]
  exact (ht.congr' he.symm).liminf_eq
end TriangularUniversal
end

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
namespace TriangularUniversal
def gaussPot (α s : ℝ) : ℝ := Real.exp (-Real.pi*α*s)
open PositiveMixture
lemma power_bounds_from_gaussians {C : Set Plane} (hD : DensityOne C)
    (hgauss : ∀ α : ℝ, 0<α → latticeEnergy (gaussPot α)≤energy (gaussPot α) C)
    (v : I) : latticeEnergy (powerPotential v)≤energy (powerPotential v) C := by
  by_cases h0 : (v:ℝ)=0
  · have hl : latticeEnergy (powerPotential v)=0 := by
      unfold latticeEnergy
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      have ht : 0<‖x.val‖^2 := sq_pos_of_pos (norm_pos_iff.mpr x.property.2)
      simp only [powerPotential,h0,Real.zero_rpow ht.ne',ENNReal.ofReal_zero]
    rw [hl]
    exact zero_le
  by_cases h1 : (v:ℝ)=1
  · have he : powerPotential v=(fun _ => (1:ℝ)) := by
      funext t
      simp only [powerPotential,h1,Real.one_rpow]
    rw [he,energy_one hD]
    exact le_top
  have hv : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm h0)
  have hv1 : (v:ℝ)<1 := lt_of_le_of_ne v.property.2 h1
  let α : ℝ := -Real.log (v:ℝ)/Real.pi
  have hα : 0<α := div_pos (neg_pos.mpr (Real.log_neg hv hv1)) Real.pi_pos
  have he : powerPotential v=gaussPot α := by
    funext t
    rw [powerPotential,Real.rpow_def_of_pos hv]
    unfold gaussPot
    congr 1
    dsimp [α]
    field_simp
  rw [he]
  exact hgauss α hα
lemma universal_from_gaussian_bounds {C : Set Plane} (hD : DensityOne C)
    (hgauss : ∀ α : ℝ, 0<α → latticeEnergy (gaussPot α)≤energy (gaussPot α) C)
    {g : ℝ → ℝ} (hg : AdmissiblePotential g) :
    latticeEnergy g≤energy g C ∧ latticeEnergy g=energy g triangularLattice :=
  ⟨universal_from_power_bounds C (power_bounds_from_gaussians hD hgauss) hg,lattice_energy_eq g⟩
end TriangularUniversal
end

end OAI
