import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.WeightedAveragingError

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SignalCutoff
open Classical

theorem scaledSiteConjugate_displacement {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) :
    ∃Q : ℝ,0 ≤ Q ∧ ∀N : ℝ,0<N → ∀z : FlagSite a m D v,
      ‖scaledSiteConjugate N (flagSiteAction hD g z)-scaledSiteConjugate N z‖ ≤ Q/N := by
  obtain ⟨Q,hQ,hb⟩ := flagSiteAction_displacement (v:=v) hD g
  refine ⟨Q,hQ,fun N hN z => ?_⟩
  rw [Prod.norm_def]
  apply max_le <;> simp only [scaledSiteConjugate,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs,
    ← sub_div,abs_div,abs_of_pos hN]
  · apply div_le_div_of_nonneg_right _ hN.le
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans (hb z)
  · apply div_le_div_of_nonneg_right _ hN.le
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hb z)

theorem flagSignalDifference_ne_zero_near {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ) {K Q N : ℝ} (q : ℝ)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hQ : 0 ≤ Q) (hN : 0<N)
    (hdisp : ∀z : FlagSite a m D v,
      ‖scaledSiteConjugate N (flagSiteAction hD g⁻¹ z)-scaledSiteConjugate N z‖ ≤ Q/N)
    (z : FlagSite a m D v) (hz : flagSignalDifference hD g (fun x => q+ψ x) N z≠0) :
    ‖scaledSiteConjugate N z‖ < K+Q/N := by
  rw [flagSignalDifference_add_constant] at hz
  by_cases hh : ψ (scaledSiteConjugate N z)=0
  · have hi : ψ (scaledSiteConjugate N (flagSiteAction hD g⁻¹ z))≠0 := by
      intro he
      exact hz (by simp [flagSignalDifference,flagMeanSignal,he,hh])
    have hn : ‖scaledSiteConjugate N (flagSiteAction hD g⁻¹ z)‖<K :=
      lt_of_not_ge (fun he => hi (hcompact _ he))
    have ht := norm_le_norm_add_norm_sub (scaledSiteConjugate N (flagSiteAction hD g⁻¹ z))
      (scaledSiteConjugate N z)
    linarith [hdisp z]
  · have hn : ‖scaledSiteConjugate N z‖<K := lt_of_not_ge (fun he => hh (hcompact _ he))
    exact hn.trans_le (le_add_of_nonneg_right (div_nonneg hQ hN.le))

theorem flagSignalDifference_cutoff {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ) {K : ℝ} (q : ℝ)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,‖x‖ ≤ K+2 → χ x=1) :
    ∃Q : ℝ,0 ≤ Q ∧ ∀(N r η : ℝ),0<N → Q ≤ N → 0<η → η ≤ 1 →
      ∀z w : FlagSite a m D v,flagRowTent (r/N) (N*η) z w≠0 →
        flagSignalDifference hD g (fun x => q+ψ x) N w≠0 →
        χ (scaledSiteConjugate N z)=1 ∧ χ (scaledSiteConjugate N w)=1 := by
  obtain ⟨Q,hQ,hdisp⟩ := scaledSiteConjugate_displacement (v:=v) hD g⁻¹
  refine ⟨Q,hQ,fun N r η hN hQN hη hη₁ z w hkw hw => ?_⟩
  have hwn := flagSignalDifference_ne_zero_near hD g ψ q hcompact hQ hN (hdisp N hN) w hw
  have hQN' : Q/N ≤ 1 := (div_le_one hN).mpr hQN
  have hn := planeTent_scaled_near hN hη z w
    ((flagRowTent_ne_zero_iff _ _ _ _).mp hkw).2.2
  have hz := norm_le_norm_add_norm_sub (scaledSiteConjugate N w) (scaledSiteConjugate N z)
  rw [norm_sub_rev] at hz
  exact ⟨hχ _ (by linarith),hχ _ (by linarith)⟩

theorem compactSignal_amplitude {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hs : HasCompactSupport ψ) (q : ℝ) :
    ∃C : ℝ,0 ≤ C ∧ ∀N : ℝ,0<N → ∀z : FlagSite a m D v,
      |flagSignalDifference hD g (fun x => q+ψ x) N z| ≤ C/N := by
  obtain ⟨L₀,L₁,hL₀,hL₁⟩ := compactSignal_uniform_constants ψ hψ hs
  obtain ⟨C,hC,hamp⟩ := flagSignalDifference_amplitude (v:=v) hD g ψ L₀.coe_nonneg (by
    intro x y
    have hh := hL₀.dist_le_mul x y
    rw [Real.dist_eq,dist_eq_norm,Prod.norm_def] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ L₀.coe_nonneg)
    simp only [Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _)))
  refine ⟨C,hC,fun N hN z => ?_⟩
  rw [flagSignalDifference_add_constant]
  exact hamp N hN z

end SignalCutoff

section AveragingL1Rows
open Classical

theorem flagAveragingMatrix_row_sum {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N r η κ : ℝ} (hρ : 0<ρ) (hN : 0<N) (hr : 0<r) (hη : 0<η) (hκ : 0<κ)
    (z : FlagSite a m D v) (S : Finset (FlagSite a m D v)) :
    ∑w∈S,flagAveragingMatrix χ ρ N r η κ z w ≤
      (4*(D:ℝ)^2*r*η+2)^2/(ρ*(r*η)^2) := by
  let T := S.filter (fun w => flagAveragingMatrix χ ρ N r η κ z w≠0)
  have he : (∑w∈S,flagAveragingMatrix χ ρ N r η κ z w)=
      ∑w∈T,flagAveragingMatrix χ ρ N r η κ z w := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w hw hwt
    simpa [T,hw] using hwt
  rw [he]
  have hc := flagAveragingMatrix_row_card hD χ ρ κ hN hr hη z T
    (fun w hw => (Finset.mem_filter.mp hw).2)
  calc
    _ ≤ ∑_w∈T,(ρ*(r*η)^2)⁻¹ := Finset.sum_le_sum
      (fun w _ => (flagAveragingMatrix_entry_bounds χ hχ hρ hN hr hη hκ z w).2)
    _ = (T.card:ℝ)*(ρ*(r*η)^2)⁻¹ := by simp
    _ ≤ (4*(D:ℝ)^2*r*η+2)^2*(ρ*(r*η)^2)⁻¹ := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [div_eq_mul_inv]

theorem flagAveragingMatrix_row_sum_uniform {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N r η κ : ℝ} (hρ : 0<ρ) (hN : 0<N) (hr : 0<r) (hη : 0<η) (hκ : 0<κ)
    (hscale : 1 ≤ r*η) (z : FlagSite a m D v) (S : Finset (FlagSite a m D v)) :
    ∑w∈S,flagAveragingMatrix χ ρ N r η κ z w ≤ (4*(D:ℝ)^2+2)^2/ρ := by
  have hh := flagAveragingMatrix_row_sum hD χ hχ hρ hN hr hη hκ z S
  refine hh.trans ?_
  have hle : 4*(D:ℝ)^2*r*η+2 ≤ (4*(D:ℝ)^2+2)*(r*η) := by nlinarith
  have hb := pow_le_pow_left₀ (show 0 ≤ 4*(D:ℝ)^2*r*η+2 by positivity) hle 2
  calc
    _ ≤ ((4*(D:ℝ)^2+2)*(r*η))^2/(ρ*(r*η)^2) := div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by field_simp

theorem flagAveragingMatrix_crude_error {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    (h : FlagSite a m D v → ℝ) {ρ N r η κ H : ℝ}
    (hρ : 0<ρ) (hN : 0<N) (hr : 0<r) (hη : 0<η) (hκ : 0<κ)
    (hscale : 1 ≤ r*η) (hH : 0 ≤ H) (hamp : ∀z,|h z| ≤ H)
    (z : FlagSite a m D v) (S : Finset (FlagSite a m D v)) :
    |(∑w∈S,flagAveragingMatrix χ ρ N r η κ z w*h w)-h z| ≤
      ((4*(D:ℝ)^2+2)^2/ρ+1)*H := by
  have hsum : |∑w∈S,flagAveragingMatrix χ ρ N r η κ z w*h w| ≤
      ((4*(D:ℝ)^2+2)^2/ρ)*H := by
    calc
      _ ≤ ∑w∈S,|flagAveragingMatrix χ ρ N r η κ z w*h w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑w∈S,flagAveragingMatrix χ ρ N r η κ z w*H := by
        apply Finset.sum_le_sum
        intro w hw
        have hm := (flagAveragingMatrix_entry_bounds χ hχ hρ hN hr hη hκ z w).1
        rw [abs_mul,abs_of_nonneg hm]
        exact mul_le_mul_of_nonneg_left (hamp w) hm
      _ = (∑w∈S,flagAveragingMatrix χ ρ N r η κ z w)*H := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (flagAveragingMatrix_row_sum_uniform hD χ hχ hρ hN hr hη hκ hscale z S) hH
  have ht := abs_sub (∑w∈S,flagAveragingMatrix χ ρ N r η κ z w*h w) (h z)
  nlinarith [hamp z]

end AveragingL1Rows

end SimpleAmenable
end
end

end OAI
