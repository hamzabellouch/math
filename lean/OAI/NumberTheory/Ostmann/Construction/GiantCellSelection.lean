import OAI.NumberTheory.Ostmann.Construction.FavorableBlock
import OAI.NumberTheory.Ostmann.Construction.LogCellPrimePrior
import OAI.NumberTheory.Ostmann.Construction.LogCellSelection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped BigOperators

theorem exists_positive_giant_cell (d : Decomposition) {δ : ℝ} (hδ : 0<δ)
    (r : ℝ) (hr : 4≤r) :
    ∀ᶠ L : ℝ in atTop,
      (3/20:ℝ)*L≤(∑p∈Supply.nonsparsePrimes d δ L,(1:ℝ)/p) →
      ∃ G : ℝ, ∃ c : ℤ, ∃ P : Finset ℕ,
        P⊆Supply.nonsparsePrimes d δ L ∧
        Real.exp ((1/20:ℝ)*L)≤G ∧ G+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) ∧
        G-2<(c:ℝ) ∧ (c:ℝ)<G+favorableBlockWidth L+2 ∧
        (∀p∈P,G≤Real.log p ∧ Real.log p<G+favorableBlockWidth L) ∧
        0<logCellMass c ∅ ∧
        (δ/(320*Real.sqrt 2))<
          (∑p∈P,logCellWeight c p*giantEmpiricalMean d (giantWindowScale r G L) p)/
            logCellMass c ∅ := by
  let a := δ/(20*Real.sqrt 2)
  have ha : 0<a := div_pos hδ (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num)))
  obtain ⟨c₀,hc₀⟩ := eventually_atTop.mp logCell_normalization_eventually
  have hgrowth := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/20)).eventually_ge_atTop
    (max (c₀+2) 5)
  have hwidth := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/100)).eventually_ge_atTop 5
  filter_upwards [exists_nonsparse_log_block d,eventually_robust_favorable_mean d hδ r hr,
    hgrowth,hwidth] with L hblock hrobust hgrow hh5
  intro hnonsparse
  obtain ⟨G,P,hP,hGlo,hGhi,hwin,hmass⟩ := hblock δ hnonsparse
  have hh : 0<favorableBlockWidth L := Real.exp_pos _
  have hGhi' : G≤Real.exp ((9/10:ℝ)*L) := by linarith
  have hrob := hrobust G P hGlo hGhi' hP (fun p hp => ⟨(hwin p hp).1,(hwin p hp).2.le⟩) hmass.le
  have hsel := exists_positive_logCell P G (favorableBlockWidth L) a
    (fun p => (Real.log p/(p:ℝ))*giantRobustMean d (giantWindowScale r G L) p)
    hh5 ha (fun p hp => ⟨(hwin p hp).1,(hwin p hp).2.le⟩) hrob
  obtain ⟨c,hc,hcmean⟩ := hsel
  obtain ⟨hclo,hchi⟩ := logBlockCenters_bounds G (favorableBlockWidth L) hc
  have hGbig : max (c₀+2) 5≤G := hgrow.trans hGlo
  have hcmin : c₀≤(c:ℝ) := by have := (le_max_left _ _).trans hGbig; linarith
  have hc3 : 3≤(c:ℝ) := by have := (le_max_right _ _).trans hGbig; linarith
  obtain ⟨hZ,hZinv,hZupper⟩ := hc₀ (c:ℝ) hcmin ∅ (by simp)
  have hsupport (p : ℕ) (hp : p∈P) : 0≤giantSupportMean d p := by
    have ht := (Finset.mem_filter.mp (hP hp)).2
    have hl := giantSupportMean_lower d ht.1 hδ.le ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2
    exact (div_pos hδ (Real.sqrt_pos.mpr (by norm_num))).le.trans hl
  have hconvert := smooth_cell_giant_robust_le d (giantWindowScale r G L) P c hc3 hsupport
  let H := ∑p∈P,logCellWeight c p*giantEmpiricalMean d (giantWindowScale r G L) p
  have hcell : a/4<((c:ℝ)+1)*H := by
    apply lt_of_lt_of_le _ hconvert
    simpa only [mul_assoc] using hcmean
  have hH : 0<H := by nlinarith
  have hdiv : ((c:ℝ)/2)*H≤H/logCellMass c ∅ := by
    have h := mul_le_mul_of_nonneg_right hZinv hH.le
    simpa only [div_eq_mul_inv,mul_comm] using h
  refine ⟨G,c,P,hP,hGlo,hGhi,hclo,hchi,hwin,hZ,?_⟩
  have ht : ((c:ℝ)+1)*H≤2*(c:ℝ)*H := by nlinarith
  have hout : a/16<H/logCellMass c ∅ := by nlinarith
  have heq : a/16=δ/(320*Real.sqrt 2) := by dsimp [a]; ring
  rwa [heq] at hout

end Ostmann.Construction

end

end OAI
