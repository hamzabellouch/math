import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.ActualUpperDeficitBarrier
import OAI.Analysis.CoulombIonization.Ionization.SelectedProfileSubsequence
import OAI.Analysis.CoulombIonization.RadialBounds.SelectionDiagonal

namespace OAI

noncomputable section

namespace CoulombBarrier
open MeasureTheory Filter Set Metric
open scoped Topology
open CoulombAtom CoulombAnalysis

lemma actual_priced_deficit_subsequence (Z N : ℕ → ℕ) (s : ℕ → ℝ)
    (hZ : ∀ n, 1 ≤ Z n) (hs : ∀ n, 0 < s n) (hs0 : Tendsto s atTop (𝓝 0))
    (hscale : Tendsto (fun n => (Z n:ℝ)*(s n)^3) atTop atTop)
    (hN : ∀ n, PriceMinimizes (energy (Z n)) ((s n)^(-4:ℝ)) (N n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (s (φ n))^3*((Z (φ n):ℝ)-(N (φ n):ℝ))) atTop (𝓝 tfResidualCharge) := by
  classical
  obtain ⟨B,C,hB,hC,hfinite⟩ := exists_actual_selected_data_constants
  let R := selectedTailRadius
  have hR : 0 < R := by
    have hh := actualScreenRadius_ge16
    dsimp [R,selectedTailRadius]
    linarith
  let l : ℕ → ℝ := fun k => (k:ℝ)+max R 1
  have hl (k) : 1 ≤ l k := by dsimp [l]; linarith [Nat.cast_nonneg (α := ℝ) k,le_max_right R 1]
  have hRl (k) : R ≤ l k := by dsimp [l]; linarith [Nat.cast_nonneg (α := ℝ) k,le_max_left R 1]
  have hl0 : Tendsto l atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hτ0 := selectedTailThreshold_tendsto hs0
  have hsmall := hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  have hτsmall := hτ0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  have hu := actual_uniform_upper_deficit (Eventually.of_forall hs) hs0
  have hchoose (k : ℕ) : ∀ᶠ n in atTop,
      Nonempty (SelectedQuantumData (Z n) (N n) (s n) (l k) (selectedTailThreshold (s n)) B C R) ∧
      s n ≤ 1 ∧ selectedTailThreshold (s n) ≤ 1 ∧
      (s n)^3*((Z n:ℝ)-(N n:ℝ)) ≤ quantumUpperDeficitConstant := by
    filter_upwards [hfinite Z s N hZ hs hs0 hscale hN (l k) (hl k),hsmall,hτsmall,hu]
      with n hd hs1 hτ1 hu1
    refine ⟨hd,hs1.le,hτ1.le,hu1 (Z n) (Nat.cast_nonneg _) (N n) ?_⟩
    simpa only [price_scale_inverse (hs n),one_div] using hN n
  obtain ⟨φ,hφ,hchosen⟩ := diagonal_of_eventually hchoose
  let d (k : ℕ) := Classical.choice (hchosen k).1
  let Q := quantumUpperDeficitConstant+(2+64*volume.real (closedBall (0:TFSpace) R))
  have hQ : 0 ≤ Q := by
    have hh := quantumUpperDeficitConstant_pos
    dsimp [Q]
    positivity
  have hbound (k) : |(s (φ k))^3*((Z (φ k):ℝ)-(N (φ k):ℝ))| ≤ Q := by
    have hlow := (d k).rough_lower (hs _) (hchosen k).2.1 (hl k) (hchosen k).2.2.1 hB.le (hRl k)
    have hhigh := (hchosen k).2.2.2
    have hv : 0 ≤ volume.real (closedBall (0:TFSpace) R) := ENNReal.toReal_nonneg
    have hqu := quantumUpperDeficitConstant_pos
    apply abs_le.mpr
    dsimp [Q]
    constructor <;> linarith
  obtain ⟨ψ,hψ,hlim⟩ := selected_data_profile_subsequence d
    (fun k => Nat.cast_nonneg (Z (φ k))) (fun k => hs (φ k)) hl
    (hs0.comp hφ.tendsto_atTop) hl0 (hτ0.comp hφ.tendsto_atTop) hB hC hR hQ hbound
  exact ⟨φ ∘ ψ,hφ.comp hψ,hlim⟩

end CoulombBarrier

section
open Filter Set
open scoped Topology

lemma real_tendsto_of_subsequences {a : ℕ → ℝ} {b : ℝ}
    (h : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ φ : ℕ → ℕ, Tendsto (fun n => a (ns (φ n))) atTop (𝓝 b)) :
    Tendsto a atTop (𝓝 b) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_contra hh
  have hfreq : ∃ᶠ n in atTop, ¬dist (a n) b < ε := not_eventually.mp hh
  obtain ⟨ns,hns,hbad⟩ := subseq_forall_of_frequently (x := fun n : ℕ => n) (p := fun n => ¬dist (a n) b < ε) tendsto_id hfreq
  obtain ⟨φ,hφ⟩ := h ns hns
  obtain ⟨n,hn⟩ := (Metric.tendsto_nhds.mp hφ ε hε).exists
  exact hbad (φ n) hn

end
open Filter
open scoped Topology
namespace CoulombAtom
open CoulombAnalysis CoulombBarrier

theorem actual_priced_deficit_limit (Z N : ℕ → ℕ) (s : ℕ → ℝ)
    (hZ : ∀ n, 1 ≤ Z n) (hs : ∀ n, 0 < s n) (hs0 : Tendsto s atTop (𝓝 0))
    (hscale : Tendsto (fun n => (Z n:ℝ)*(s n)^3) atTop atTop)
    (hN : ∀ n, PriceMinimizes (energy (Z n)) ((s n)^(-4:ℝ)) (N n)) :
    Tendsto (fun n => (s n)^3*((Z n:ℝ)-(N n:ℝ))) atTop (𝓝 tfResidualCharge) := by
  apply real_tendsto_of_subsequences
  intro ns hns
  obtain ⟨φ,_hφ,hlim⟩ := actual_priced_deficit_subsequence (Z ∘ ns) (N ∘ ns) (s ∘ ns)
    (fun n => hZ (ns n)) (fun n => hs (ns n)) (hs0.comp hns) (hscale.comp hns)
    (fun n => hN (ns n))
  exact ⟨φ,hlim⟩

end CoulombAtom

open Filter
open scoped Topology
namespace CoulombAtom

def fixedSectorScale (t m : ℝ) : ℝ := t^(-1/4:ℝ)*m^(-1/3:ℝ)
lemma fixedSectorScale_pos {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    0 < fixedSectorScale t m := mul_pos (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos hm _)
lemma fixedSectorScale_price {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    (fixedSectorScale t m)^(-4:ℝ) = t*m^(4/3:ℝ) := by
  rw [fixedSectorScale,Real.mul_rpow (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg hm.le _),
    ←Real.rpow_mul ht.le,←Real.rpow_mul hm.le]
  norm_num
lemma fixedSectorScale_cube {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    (fixedSectorScale t m)^3 = t^(-3/4:ℝ)/m := by
  rw [fixedSectorScale,mul_pow,←Real.rpow_natCast (t^(-1/4:ℝ)) 3,
    ←Real.rpow_natCast (m^(-1/3:ℝ)) 3,←Real.rpow_mul ht.le,←Real.rpow_mul hm.le]
  norm_num [Real.rpow_neg_one,div_eq_mul_inv]
lemma fixedSectorScale_deficit {t m Z N : ℝ} (ht : 0 < t) (hm : 0 < m) :
    t^(3/4:ℝ)*((fixedSectorScale t m)^3*(Z-N)) = (Z-N)/m := by
  rw [fixedSectorScale_cube ht hm]
  calc
    t^(3/4:ℝ)*(t^(-3/4:ℝ)/m*(Z-N)) = (t^(3/4:ℝ)*t^(-3/4:ℝ))*((Z-N)/m) := by ring
    _ = (Z-N)/m := by rw [←Real.rpow_add ht]; norm_num
lemma fixedSectorScale_tendsto {ι : Type*} {f : Filter ι} {m : ι → ℝ} {t : ℝ}
    (hm : Tendsto m f atTop) : Tendsto (fun i => fixedSectorScale t (m i)) f (𝓝 0) := by
  have hh := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).comp hm).const_mul (t^(-1/4:ℝ))
  simpa only [mul_zero,fixedSectorScale,Function.comp_def,neg_div] using hh
lemma fixedSectorScale_joint {ι : Type*} {f : Filter ι} {m Z : ι → ℝ} {t : ℝ}
    (ht : 0 < t) (hm : ∀ i, 0 < m i) (hr : Tendsto (fun i => Z i/m i) f atTop) :
    Tendsto (fun i => Z i*(fixedSectorScale t (m i))^3) f atTop := by
  have hh := hr.const_mul_atTop (Real.rpow_pos_of_pos ht (-3/4:ℝ))
  convert hh using 1
  funext i
  rw [fixedSectorScale_cube ht (hm i)]
  ring
end CoulombAtom

end

end OAI
