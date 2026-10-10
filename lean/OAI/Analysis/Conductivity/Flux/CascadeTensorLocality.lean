import Mathlib
import OAI.Analysis.Conductivity.Branching.CascadeCoefficient

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma cascadeIndex_eq_of_strict_phase {D k : ℝ} (hD : 0<D) (x : Coord3) (j : ℕ)
    (hj0 : 0<cascadePhase D k j (x 0)) (hjD : cascadePhase D k j (x 0)<D) :
    cascadeIndex D k x=j := by
  have ht : k*x 0<2*D := cascadePhase_lt_terminal (by linarith : cascadePhase _ k j (x 0)<2*_)
  have ht0 : 0≤k*x 0 := by
    have hh := cascadePhase_antitone ht.le (Nat.zero_le j)
    dsimp only at hh
    rw [cascadePhase_zero] at hh
    exact le_trans hj0.le hh
  have hs := cascadeIndex_spec x ht0 ht
  rcases lt_trichotomy (cascadeIndex D k x) j with hij|he|hji
  · have hh := cascadePhase_antitone ht.le (show cascadeIndex D k x+1≤j by omega)
    dsimp only at hh
    rw [cascadePhase_succ] at hh
    linarith
  · exact he
  · have hh := cascadePhase_before hD hji hs.1
    linarith

lemma cascadeTensor_connector_eq {L K k : ℝ} (hL : 0<L) (hK : 0<K)
    (x : Coord3) (j : ℕ)
    (hj0 : 0<cascadePhase (cascadeLength L K) k j (x 0))
    (hjK : cascadePhase (cascadeLength L K) k j (x 0)<K+2) :
    cascadeTensor L K k x =
      pureModeTensor (connectorAngular K (cascadePhase (cascadeLength L K) k j (x 0))) (cascadeAxis j) := by
  have hD : 0<cascadeLength L K := by unfold cascadeLength; positivity
  have hjD : cascadePhase (cascadeLength L K) k j (x 0)<cascadeLength L K := by
    have he : cascadeLength L K=K+2+2*L := rfl
    linarith
  have ht := cascadePhase_lt_terminal (by linarith : cascadePhase _ k j (x 0)<2*_)
  have ht0 : 0≤k*x 0 := by
    have hh := cascadePhase_antitone ht.le (Nat.zero_le j)
    dsimp only at hh
    rw [cascadePhase_zero] at hh
    exact le_trans hj0.le hh
  rw [cascadeTensor,ite_eq_left ⟨ht0,ht⟩,cascadeIndex_eq_of_strict_phase hD x j hj0 hjD,
    cascadeStageTensor,ite_eq_left hjK]

lemma cascadeTensor_crossing_eq {L K k : ℝ} (hL : 0<L) (hK : 0<K)
    (x : Coord3) (j : ℕ)
    (hjK : K+2<cascadePhase (cascadeLength L K) k j (x 0))
    (hjD : cascadePhase (cascadeLength L K) k j (x 0)<cascadeLength L K) :
    cascadeTensor L K k x = crossingTensor L (cascadeAxis j) (cascadeAxis (j+1))
      ((k*2^j) • (x-cascadeCenter (cascadeLength L K) k j)-Pi.single 0 (K+2+L)) := by
  have hD : 0<cascadeLength L K := by unfold cascadeLength; positivity
  have hj0 : 0<cascadePhase (cascadeLength L K) k j (x 0) := by linarith
  have ht := cascadePhase_lt_terminal (by linarith : cascadePhase _ k j (x 0)<2*_)
  have ht0 : 0≤k*x 0 := by
    have hh := cascadePhase_antitone ht.le (Nat.zero_le j)
    dsimp only at hh
    rw [cascadePhase_zero] at hh
    exact le_trans hj0.le hh
  rw [cascadeTensor,ite_eq_left ⟨ht0,ht⟩,cascadeIndex_eq_of_strict_phase hD x j hj0 hjD,
    cascadeStageTensor,ite_eq_right (not_lt.mpr hjK.le)]

lemma connectorAngular_smooth (K : ℝ) : ContDiff ℝ (↑(⊤:ℕ∞)) (connectorAngular K) := by
  unfold connectorAngular
  exact (smooth_deriv_infty (smooth_deriv_infty (connectorProfile_smooth K))).div
    (connectorProfile_smooth K) (fun x => (connectorProfile_pos K x).ne')

lemma crossingValue3_smooth (L : ℝ) (a b : Fin 3) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (crossingValue3 L a b) := by
  have hf := crossingFirst_smooth L
  have hg := crossingSecond_smooth L
  unfold crossingValue3 crossingValue
  fun_prop

end ScalarConductivity

end

end OAI
