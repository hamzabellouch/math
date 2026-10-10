import Mathlib
import OAI.Analysis.Conductivity.Scalarization.CascadeConnectorConstitution
import OAI.Analysis.Conductivity.Branching.CascadeCoefficient

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma ae_coord3_ne (i : Fin 3) (r : ℝ) : ∀ᵐ x : Coord3, x i≠r := by
  exact MeasureTheory.Measure.ae_eval_ne (fun _ : Fin 3 => (volume : Measure ℝ)) i r

lemma ae_cascadePhase_ne {k : ℝ} (hk : k≠0) (D r : ℝ) (n : ℕ) :
    ∀ᵐ x : Coord3, cascadePhase D k n (x 0)≠r := by
  filter_upwards [ae_coord3_ne 0 ((r-2*D+2^n*(2*D))/(2^n*k))] with x hx
  intro he
  apply hx
  apply (eq_div_iff (mul_ne_zero (by positivity) hk)).mpr
  unfold cascadePhase at he
  nlinarith

lemma cascadeValue_direction_terminal {L K k : ℝ} (hL : 0<L) (hK : 0<K)
    (A : ℝ) (x : Coord3) (ht : 2*cascadeLength L K<k*x 0) (i : Fin 3) :
    direction (Pi.single i 1) (cascadeValue L K k A) x=0 := by
  have hn : {y : Coord3 | 2*cascadeLength L K<k*y 0} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (continuous_const.mul (continuous_apply 0))).mem_nhds ht
  have he : cascadeValue L K k A =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [hn] with y hy
    exact cascadeValue_terminal hL hK A y hy.le
  simp [direction,he.fderiv_eq]

theorem cascadeTensor_constitution_ae {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) : ∀ᵐ x : Coord3, 0≤k*x 0 →
      cascadeTensor L K k x *ᵥ (fun i => direction (Pi.single i 1) (cascadeValue L K k A) x) =
        cascadeFlux L K k A x := by
  have h0 : ∀ᵐ x : Coord3, ∀ n : ℕ, cascadePhase (cascadeLength L K) k n (x 0)≠0 :=
    ae_all_iff.mpr (fun n => ae_cascadePhase_ne hk _ _ n)
  have hD : ∀ᵐ x : Coord3, ∀ n : ℕ, cascadePhase (cascadeLength L K) k n (x 0)≠cascadeLength L K :=
    ae_all_iff.mpr (fun n => ae_cascadePhase_ne hk _ _ n)
  have hK2 : ∀ᵐ x : Coord3, ∀ n : ℕ, cascadePhase (cascadeLength L K) k n (x 0)≠K+2 :=
    ae_all_iff.mpr (fun n => ae_cascadePhase_ne hk _ _ n)
  have ht : ∀ᵐ x : Coord3, k*x 0≠2*cascadeLength L K := by
    simpa only [cascadePhase_zero] using ae_cascadePhase_ne hk (cascadeLength L K) (2*cascadeLength L K) 0
  filter_upwards [h0,hD,hK2,ht] with x hx0 hxD hxK hxt
  intro hx
  by_cases hterm : k*x 0<2*cascadeLength L K
  · have hs := cascadeIndex_spec x hx hterm
    have hs₁ := lt_of_le_of_ne hs.1 (Ne.symm (hx0 _))
    have hs₂ := lt_of_le_of_ne hs.2 (hxD _)
    rw [cascadeTensor,ite_eq_left ⟨hx,hterm⟩,cascadeStageTensor]
    split_ifs with hc
    · exact cascade_connector_constitution hL hK hk A x _ hs₁ hc
    · exact cascade_crossing_constitution hL hK hk A x _
        (lt_of_le_of_ne (le_of_not_gt hc) (Ne.symm (hxK _))) hs₂
  · have ht' : 2*cascadeLength L K<k*x 0 := lt_of_le_of_ne (le_of_not_gt hterm) (Ne.symm hxt)
    have hz (i : Fin 3) := cascadeValue_direction_terminal hL hK A x ht' i
    ext i
    rw [cascadeFlux_terminal_strict hL hK hk A x ht' i]
    simp [Matrix.mulVec,dotProduct,hz]

end ScalarConductivity

end

end OAI
