import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.SupplyCalibration

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma physical_trial_scalar_tail {c M : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c)
    (htail : ∀R : ℝ,0 ≤ R → wiener {β | R ≤ ‖β‖} ≤
      ENNReal.ofReal M*ENNReal.ofReal (Real.exp (-c*R^2)))
    (L : Length) (n : ℕ) (hn : 0 < n) {t r D Cn a b C : ℝ}
    (ht : 0 < t) (hr : 0 < r) (hD : 1 ≤ D) (hb : 0 < b) (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hnlo : a*D^2 ≤ (n:ℝ)) (hnhi : (n:ℝ) ≤ Cn*D^2)
    (hτr : t/(n:ℝ) ≤ r^2) (y z u v : Point) (w : Time)
    (hw : t*(w:ℝ)=D⁻¹) (hy : ‖y-v‖ ≤ 3) (hz : ‖z-v‖ ≤ 3) (hu : ‖u-v‖ ≤ 3)
    (hdu : ‖u-y‖ ≤ C) (hdz : ‖u-z‖ ≤ C)
    (hdrift : (C+Real.sqrt (2*t)*D^(1/12:ℝ))/(n:ℝ) ≤ r)
    (hsmall : (D^(1/12:ℝ)/6)*r < L.val/2)
    (hwindow : (w:ℝ)*C ≤ (b*D^(-(1/3):ℝ)/8)/12)
    (hrelax : 3*(1+D^(1/12:ℝ)/6) ≤ D^(1/12:ℝ)) :
    trialKernel t y z u {f | ¬TrialCutoff L n r (D^(1/12:ℝ))
      (64*(meanCost+1)) w (b*D^(-(1/3):ℝ)/8) v f} ≤
      ENNReal.ofReal (2*(scalarTrialRemainder Cn M c a b D+3888*t*normPowerMean 2)) := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hm := trial_cutoff_physical_tail htail L n hn ht hr hτr
    (by positivity : 0 ≤ D^(1/12:ℝ)/6) (by positivity : 0 ≤ D^(1/12:ℝ)) hC
    (by positivity : 0 < b*D^(-(1/3):ℝ)/8) y z u v w 2 (by norm_num)
    hy hz hu hdu hdz hdrift hsmall hwindow
  have hsub : {f | ¬TrialCutoff L n r (D^(1/12:ℝ))
      (64*(meanCost+1)) w (b*D^(-(1/3):ℝ)/8) v f} ⊆
      {f | ¬TrialCutoff L n r (3*(1+D^(1/12:ℝ)/6))
      (64*(meanCost+1)) w (b*D^(-(1/3):ℝ)/8) v f} := by
    intro f hf hh
    exact hf (trialCutoff_mono_constants hrelax le_rfl hh)
  apply ((measure_mono hsub).trans hm).trans
  have hs := trial_scalar_bound (b:=b) hD hM hc ha ht.le hnlo hnhi w hw
  apply le_trans _ (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2)))
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  simp only [ENNReal.ofReal_ofNat]
  apply mul_le_mul' le_rfl
  have hw0 := scaleMoment_nonneg 2 (t:=t) (by positivity : 0 ≤ b*D^(-(1/3):ℝ)/8) 0 w
  have h10 := scaleMoment_nonneg 2 (t:=t) (by norm_num : (0:ℝ) ≤ 1) 0 1
  simp (disch := positivity) only [ENNReal.ofReal_add,ENNReal.ofReal_mul,
    ENNReal.ofReal_div_of_pos,ENNReal.ofReal_pow,ENNReal.ofReal_natCast,
    ENNReal.ofReal_ofNat,le_refl]

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local instance] Classical.propDecidable

theorem physical_useful_list {ell b A H : ℝ}
    (hell : 0 < ell) (hb : 0 < b) (hA : 0 < A) (hH : 0 < H) :
    ∃t₀ : ℝ,0 < t₀  ∧  ∀t : ℝ,0 < t  →  t ≤ t₀  →
    ∀Cn M c a : ℝ,0 ≤ M  →  0 < c  →  0 < a  →
    (∀R : ℝ,0 ≤ R  →  wiener {β | R ≤ ‖β‖} ≤ ENNReal.ofReal M*ENNReal.ofReal (Real.exp (-c*R^2)))  →
    ∃D₀ : ℝ,1 ≤ D₀  ∧  ∀D α : ℝ,D₀ ≤ D  →  0 < α  →  α ≤ A  →
    ∀(L : Length) (N m n : ℕ), 0 < n  →  50 < L.val  →  ell*D/2 ≤ (m:ℝ)  →  (m:ℝ) ≤ H*D  →
    ∀(y z : Fin m → Point) (v : Point) (ω : Fin N → ConfigurationPath 1 L)
      (label : Fin m → Fin N) (J : Finset (Fin N)) (w : Time) (B : Fin 7 → Set Point),
    (J.card:ℝ) ≤ H*D  →  a*D^2 ≤ (n:ℝ)  →  (n:ℝ) ≤ Cn*D^2  →
    (α/D) ≤ 1  →  (α/D)*D^(1/12:ℝ) ≤ 1  →  t/(n:ℝ) ≤ (α/D)^2  →  (n:ℝ)*(α/D)^2 ≤ 2*t  →
    t*(w:ℝ)=D⁻¹  →  2*(t/(n:ℝ)) ≤ D⁻¹  →  8*t ≤ (n:ℝ)*D⁻¹  →  2*13/(n:ℝ) ≤ α/D  →
    (13+Real.sqrt (2*t)*D^(1/12:ℝ))/(n:ℝ) ≤ α/D  →
    (w:ℝ)*13 ≤ (b*D^(-(1/3):ℝ)/8)/12  →  3*(1+D^(1/12:ℝ)/6) ≤ D^(1/12:ℝ)  →
    (∀i,‖y i-v‖ ≤ 3)  →  (∀i,‖z i-v‖ ≤ 3)  →
    (∀i j,i≠j  →  (b*D^(-(1/3):ℝ))^2 ≤ square (y i-y j))  →
    (∀i j,i≠j  →  (b*D^(-(1/3):ℝ))^2 ≤ square (z i-z j))  →
    (∀j∈J,Regular (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (prefixTime midpointTime w) (b*D^(-(1/3):ℝ)/8) (ω j))  →
    (∀j∈J,∀i,j≠label i  →  α/D+2*(b*D^(-(1/3):ℝ)/8) < torusDistance L (projectPoint L (y i)) (ω j 0 0))  →
    (∀j∈J,∀i,j≠label i  →  α/D+2*(b*D^(-(1/3):ℝ)/8) < torusDistance L (projectPoint L (z i)) (ω j 1 0))  →
    (∀j,j∉J  →  ∀s,12 < torusDistance L (ω j s 0) (projectPoint L v))  →
    (∀j,MeasurableSet (B j))  →  (∀j,volume (B j)=1)  →  (∀j u,u∈B j  →  ‖u-v‖ ≤ 3)  →
    ((Finset.univ.filter (fun i ↦ ¬StrongExcept n t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) w (y i) (z i) v ω (label i) B)).card:ℝ) ≤ (m:ℝ)/10 := by
  have hC : 0 < 64*(meanCost+1) := by have := meanCost_nonneg; positivity
  obtain ⟨t₀,ht₀,hs⟩ := source_supply_error_small hell hb hA hH hC
  refine ⟨t₀,ht₀,?_⟩
  intro t ht htt Cn M c a hM hc ha htail
  obtain ⟨D₀,hD₀,hd⟩ := hs t ht htt Cn M c a hc ha
  refine ⟨D₀,hD₀,?_⟩
  intro D α hDD hα hαA L N m n hn hL hm hmH y z v ω label J w B hj hnlo hnhi
    hr1 hsmall hτ hnscale hw hwindow hlarge hdrift hdrift' hwin hrelax hy hz hsepY hsepZ
    hreg hisoY hisoZ hfar hB hBvol hBv
  have hD : 1 ≤ D := hD₀.trans hDD
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hr : 0 < α/D := by positivity
  have hwd : (w:ℝ)=D⁻¹/t := (eq_div_iff ht.ne').mpr (by nlinarith [hw])
  have hdistance (p : Point) (hp : ‖p-v‖ ≤ 3) (j : Fin 7) (u : Point) (hu : u∈B j) : ‖u-p‖ ≤ 13 := by
    have hh := norm_sub_le (u-v) (p-v)
    have he : (u-v)-(p-v)=u-p := by abel
    rw [he] at hh
    linarith [hBv j u hu]
  apply full_success_count n t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
    (b*D^(-(1/3):ℝ)/8) w y z v ω label B hB hBvol
  intro j
  apply (physical_failure_sum hn y z v ω label J w hL ht hr hr1
    (by positivity) (by positivity) hC.le (by positivity : 0 < D⁻¹) hwd hsepY hsepZ hreg
    hsmall hτ hnscale hwindow hlarge hdrift (hB j) (hBvol j).le (hBv j)
    (fun i u hu ↦ hdistance (y i) (hy i) j u hu)
    (fun i u hu ↦ hdistance (z i) (hz i) j u hu) hisoY hisoZ hfar _ ?_).trans
  · exact hd D α m J.card hDD hα.le hαA hm hmH hj
  · intro i u hu
    apply physical_trial_scalar_tail hM hc.le htail L n hn ht hr hD hb (by norm_num : (0:ℝ) ≤ 13)
      ha.le hnlo hnhi hτ (y i) (z i) u v w hw (hy i) (hz i) (hBv j u hu)
      (hdistance (y i) (hy i) j u hu) (hdistance (z i) (hz i) j u hu) hdrift' _ hwin hrelax
    have hrr : 0 ≤ D^(1/12:ℝ) := by positivity
    nlinarith

end HardSphere.Bridge

end
end

end

end OAI
