import Mathlib
import OAI.Analysis.Conductivity.Branching.CascadeGeometry
import OAI.Analysis.Conductivity.Branching.CascadeStreams

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cascadePhase_lt_terminal {D k t : ℝ} {j : ℕ}
    (hj : cascadePhase D k j t  <  2*D) : k*t  <  2*D := by
  have hp : 0  <  (2:ℝ)^j := by positivity
  unfold cascadePhase at hj
  nlinarith

lemma cascadePhase_before_wide {D k t : ℝ} {i j : ℕ} (ht : k*t ≤ 2*D) (hij : i < j) :
    D+cascadePhase D k j t/2  ≤  cascadePhase D k i t := by
  have hh := cascadePhase_antitone ht (show i+1 ≤ j by omega)
  dsimp only at hh
  rw [cascadePhase_succ] at hh
  linarith

lemma cascadePhase_after_wide {D k t : ℝ} {i j : ℕ} (ht : k*t ≤ 2*D) (hij : j+1 < i) :
    cascadePhase D k i t  ≤  4*cascadePhase D k j t-6*D := by
  have hh := cascadePhase_antitone ht (show j+2 ≤ i by omega)
  dsimp only at hh
  rw [show j+2=(j+1)+1 by omega,cascadePhase_succ,cascadePhase_succ] at hh
  linarith

lemma cascadePhase_inactive_wide {L K k t : ℝ} (hL : 0  <  L) (hK : 0  <  K) {j i : ℕ}
    (hj₁ : -L/8  <  cascadePhase (cascadeLength L K) k j t)
    (hj₂ : cascadePhase (cascadeLength L K) k j t  <  cascadeLength L K+L/8)
    (hi : i≠j) (hi' : i≠j+1) :
    cascadePhase (cascadeLength L K) k i t  <  -7*L/2 ∨
      K+2+7*L/4  <  cascadePhase (cascadeLength L K) k i t := by
  have ht : k*t < 2*cascadeLength L K := cascadePhase_lt_terminal (hj₂.trans
    (by unfold cascadeLength; linarith))
  by_cases hij : i < j
  · right
    have hh := cascadePhase_before_wide ht.le hij
    unfold cascadeLength at *
    linarith
  · left
    have hh := cascadePhase_after_wide ht.le (show j+1 < i by omega)
    unfold cascadeLength at *
    linarith

lemma cascadeProfile_deriv_zero_left {L K t : ℝ} (hL : 0 < L) (ht : t <  -7*L/2) :
    deriv (cascadeProfile L K) t = 0 := by
  have he : cascadeProfile L K =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with y hy
    exact cascadeProfile_zero_left hL hy.le
  simpa using he.deriv_eq
lemma cascadeProfile_deriv_zero_right {L K t : ℝ} (hL : 0 < L) (ht : K+2+7*L/4 < t) :
    deriv (cascadeProfile L K) t = 0 := by
  have he : cascadeProfile L K =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with y hy
    exact cascadeProfile_zero_right hL hy.le
  simpa using he.deriv_eq

lemma cascadeBaseStream_zero {L K : ℝ} (hL : 0 < L) (a : Fin 3) (x : Coord3)
    (ht : x 0 <  -7*L/2 ∨ K+2+7*L/4 < x 0) : cascadeBaseStream L K a x = 0 := by
  have hd : deriv (cascadeProfile L K) (x 0) = 0 :=
    ht.elim (cascadeProfile_deriv_zero_left hL) (cascadeProfile_deriv_zero_right hL)
  simp [cascadeBaseStream,hd]

lemma cascadeCrossStream_zero_left {L K : ℝ} (hL : 0 < L) (a b : Fin 3) (x : Coord3)
    (ht : x 0 < K+2+L/4) : cascadeCrossStream L K a b x = 0 := by
  have hf := crossingResidualFirst_zero hL (show x 0-(K+2+L) < L/2 by linarith)
  have hg := crossingResidualSecond_zero_left hL (show x 0-(K+2+L) <  -3*L/4 by linarith)
  simp [cascadeCrossStream,hf,hg]
lemma cascadeCrossStream_zero_right {L K : ℝ} (hL : 0 < L) (a b : Fin 3) (x : Coord3)
    (ht : K+2+7*L/4 < x 0) : cascadeCrossStream L K a b x = 0 := by
  have hf := crossingResidualFirst_zero_right hL (show 3*L/4 < x 0-(K+2+L) by linarith)
  have hg := crossingResidualSecond_zero hL (show -L/2 < x 0-(K+2+L) by linarith)
  simp [cascadeCrossStream,hf,hg]

lemma cascadeMother_inactive_wide {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (hk : k≠0)
    (x : Coord3) {j n : ℕ}
    (hj₁ : -L/8  <  cascadePhase (cascadeLength L K) k j (x 0))
    (hj₂ : cascadePhase (cascadeLength L K) k j (x 0)  <  cascadeLength L K+L/8)
    (hn : n≠j) (hn' : n≠j+1) :
    cascadeMother L K (cascadeAxis n) ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)) = 0 ∧
    cascadeBaseStream L K (cascadeAxis n) ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)) = 0 ∧
    cascadeCrossStream L K (cascadeAxis n) (cascadeAxis (n+1))
      ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)) = 0 := by
  let y := (k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)
  have ht : y 0 <  -7*L/2 ∨ K+2+7*L/4 < y 0 := by
    dsimp only [y]
    rw [cascade_dilation_time hk]
    exact cascadePhase_inactive_wide hL hK hj₁ hj₂ hn hn'
  refine ⟨?_,cascadeBaseStream_zero hL _ y ht,?_⟩
  · have hp : cascadeProfile L K (y 0) = 0 := ht.elim
      (fun h => cascadeProfile_zero_left hL h.le) (fun h => cascadeProfile_zero_right hL h.le)
    exact show cascadeProfile L K (y 0)*cos (y (cascadeAxis n))=0 by rw [hp,zero_mul]
  · rcases ht with ht | ht
    · apply cascadeCrossStream_zero_left hL _ _ y
      linarith
    · exact cascadeCrossStream_zero_right hL _ _ y ht

lemma cascadeCrossStream_next_zero_wide {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (hk : k≠0)
    (x : Coord3) {j : ℕ}
    (hj₂ : cascadePhase (cascadeLength L K) k j (x 0)  <  cascadeLength L K+L/8) :
    cascadeCrossStream L K (cascadeAxis (j+1)) (cascadeAxis (j+2))
      ((k*2^(j+1)) • (x-cascadeCenter (cascadeLength L K) k (j+1))) = 0 := by
  apply cascadeCrossStream_zero_left hL
  rw [cascade_dilation_time hk,cascadePhase_succ]
  linarith

end ScalarConductivity

end

end OAI
