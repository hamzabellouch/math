import Mathlib
import OAI.Analysis.Conductivity.Fourier.CylinderModeGreen

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def flatCylinderEnergyLeftCLM (s : Fin 3 → ℝ) {R : ℝ} (v : FiniteCylinderJets R) :
    FiniteCylinderJets R →L[ℝ] ℂ where
  toFun u := flatCylinderEnergy s u v
  map_add' u w := by
    simp only [flatCylinderEnergy,PiLp.add_apply,inner_add_left]
    ring
  map_smul' c u := by
    simp only [flatCylinderEnergy,PiLp.smul_apply,inner_smul_left_eq_smul,Complex.real_smul,RingHom.id_apply]
    ring
  cont := flatCylinderEnergy_continuous_left s v

def flatCylinderEnergyRightCLM (s : Fin 3 → ℝ) {R : ℝ} (u : FiniteCylinderJets R) :
    FiniteCylinderJets R →L[ℂ] ℂ where
  toFun v := flatCylinderEnergy s u v
  map_add' v w := by
    simp only [flatCylinderEnergy,PiLp.add_apply,inner_add_right]
    ring
  map_smul' c v := by
    simp only [flatCylinderEnergy,PiLp.smul_apply,inner_smul_right,smul_eq_mul,RingHom.id_apply]
    ring
  cont := flatCylinderEnergy_continuous_right s u

theorem flatCylinder_series_mode_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (R : ℝ) (hR : 0≤R)
    (f : spectralTraceGraph (torusRate s)) (k : TorusModes) :
    flatCylinderEnergy s (endPoissonJet s hs R hR f) (smoothCylinderModeJet hq R k)=
      (torusRate s k:ℂ)*inner ℂ (f.val 0 k) (q 0)-
        (torusRate s k*Real.exp (-torusRate s k*R):ℝ)*inner ℂ (f.val 0 k) (q R) := by
  have H := (flatCylinderEnergyLeftCLM s (smoothCylinderModeJet hq R k)).hasSum
    (endPoissonJet_hasSum s hs R hR f)
  have Hsingle : HasSum (fun h => flatCylinderEnergy s
      (endPoissonModeJet s R h (f.val 0 h)) (smoothCylinderModeJet hq R k))
      (flatCylinderEnergy s (endPoissonModeJet s R k (f.val 0 k)) (smoothCylinderModeJet hq R k)) :=
    hasSum_single k (fun h hne => flatCylinderEnergy_distinct_modes s hq R h k _ hne)
  have he := H.unique Hsingle
  change flatCylinderEnergy s (endPoissonJet s hs R hR f) (smoothCylinderModeJet hq R k)=_ at he
  rw [he,flatCylinderEnergy_same_mode s hs hq R k _]
  exact finiteDecay_green_inner hq _ R hR _

theorem flatCylinder_series_polynomial_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (q : TorusModes → ℝ → ℂ) (hq : ∀ k,ContDiff ℝ (↑(⊤:ℕ∞)) (q k))
    (R : ℝ) (hR : 0≤R) (f : spectralTraceGraph (torusRate s)) (F : Finset TorusModes) :
    flatCylinderEnergy s (endPoissonJet s hs R hR f) (∑ k∈F,smoothCylinderModeJet (hq k) R k)=
      ∑ k∈F,((torusRate s k:ℂ)*inner ℂ (f.val 0 k) (q k 0)-
        (torusRate s k*Real.exp (-torusRate s k*R):ℝ)*inner ℂ (f.val 0 k) (q k R)) := by
  change flatCylinderEnergyRightCLM s (endPoissonJet s hs R hR f) _=_
  rw [map_sum]
  exact Finset.sum_congr rfl (fun k _ => flatCylinder_series_mode_green s hs (hq k) R hR f k)

end ScalarConductivity

end

end OAI
