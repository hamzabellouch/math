import Mathlib
import OAI.Analysis.Conductivity.Scalarization.LocalConstitution
import OAI.Analysis.Conductivity.Fourier.PureMode

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma cascadeProfile_deriv_connector {L K t : ℝ} (hL : 0<L)
    (ht₁ : 0<t) (ht₂ : t<K+2) :
    deriv (cascadeProfile L K) t = deriv (connectorProfile K) t := by
  have he : cascadeProfile L K =ᶠ[𝓝 t] connectorProfile K := by
    filter_upwards [Ioo_mem_nhds ht₁ ht₂] with r hr
    exact cascadeProfile_connector hL hr.1.le hr.2.le
  exact he.deriv_eq

lemma cascadeValue_connector {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : 0<cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0)<K+2) :
    cascadeValue L K k A x =
      (A*cascadeRatio L K^m)*pureModeValue (connectorProfile K) (cascadeAxis m)
        ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)) := by
  rw [cascadeValue_two_modes hL hK A x m hs₁.le (by have hD : cascadeLength L K = K+2+2*L := rfl; linarith)]
  simp only [cascadeTerm,cascadePhase_succ,cascadeProfile_next_connector_zero hL hs₂.le,
    mul_zero,zero_mul,add_zero,cascadeProfile_connector hL hs₁.le hs₂.le,pureModeValue,
    cascade_dilation_time hk,cascade_dilation_coord _ _ _ _ (cascadeAxis_ne_zero m)]
  ring

lemma cascadePotentialTerm_connector_pair {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : 0<cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0)<K+2) (i j : Fin 3) :
    cascadePotentialTerm L K k A m i j x+ cascadePotentialTerm L K k A (m+1) i j x =
      (A*cascadeRatio L K^m)*pureModePotential (connectorProfile K) (cascadeAxis m) i j
        ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)) := by
  let y : Coord3 := (k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)
  let z : Coord3 := (k*2^(m+1)) • (x-cascadeCenter (cascadeLength L K) k (m+1))
  have hy : y 0 = cascadePhase (cascadeLength L K) k m (x 0) := cascade_dilation_time hk _ _ _
  have hz : z 0 = 2*(y 0-cascadeLength L K) := by
    rw [←cascade_dilation_time hk] at hs₁
    dsimp only [z]
    rw [cascade_dilation_time hk,cascadePhase_succ,←hy]
  have hc : cascadeCrossStream L K (cascadeAxis m) (cascadeAxis (m+1)) y=0 :=
    cascadeCrossStream_zero_left hL _ _ _ (by rw [hy]; linarith)
  have hnext : cascadeBaseStream L K (cascadeAxis (m+1)) z=0 := by
    apply cascadeBaseStream_zero hL
    left
    rw [hz,hy]
    have hD : cascadeLength L K = K+2+2*L := rfl
    linarith
  have hcnext : cascadeCrossStream L K (cascadeAxis (m+1)) (cascadeAxis (m+1+1)) z=0 := by
    apply cascadeCrossStream_zero_left hL
    rw [hz,hy]
    have hD : cascadeLength L K = K+2+2*L := rfl
    linarith
  have hb : cascadeBaseStream L K (cascadeAxis m) y =
      deriv (connectorProfile K) (y 0)*sin (y (cascadeAxis m)) := by
    rw [cascadeBaseStream,cascadeProfile_deriv_connector hL (by rw [hy]; exact hs₁)
      (by rw [hy]; exact hs₂)]
  change (A*cascadeRatio L K^m)*cascadePotentialMother L K _ _ i j y+
    (A*cascadeRatio L K^(m+1))*cascadePotentialMother L K _ _ i j z = _
  simp only [cascadePotentialMother,hc,hnext,hcnext,hb,mul_zero,add_zero,
    pureModePotential,wedgePotential,ite_self,sub_self]
  rfl

lemma cascade_connector_nhds {L K k : ℝ} (x : Coord3) (m : ℕ)
    (hs₁ : 0<cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0)<K+2) :
    {y : Coord3 | 0<cascadePhase (cascadeLength L K) k m (y 0) ∧
      cascadePhase (cascadeLength L K) k m (y 0)<K+2} ∈ 𝓝 x := by
  have hc : Continuous (fun y : Coord3 => cascadePhase (cascadeLength L K) k m (y 0)) := by
    unfold cascadePhase
    fun_prop
  exact (hc.isOpen_preimage _ isOpen_Ioo).mem_nhds ⟨hs₁,hs₂⟩

theorem cascade_connector_constitution {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : 0<cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0)<K+2) :
    pureModeTensor (connectorAngular K (cascadePhase (cascadeLength L K) k m (x 0))) (cascadeAxis m) *ᵥ
      (fun i => direction (Pi.single i 1) (cascadeValue L K k A) x) = cascadeFlux L K k A x := by
  have hf := (connectorProfile_smooth K).differentiable (by simp)
  have hf' := (smooth_deriv_infty (connectorProfile_smooth K)).differentiable (by simp)
  apply local_scaled_constitution (pureModeValue_diff hf _) (pureModePotential_diff hf' _)
    (A*cascadeRatio L K^m) (k*2^m) (cascadeCenter (cascadeLength L K) k m) 0 x
  · filter_upwards [cascade_connector_nhds x m hs₁ hs₂] with y hy
    simpa only [sub_zero] using cascadeValue_connector hL hK hk A y m hy.1 hy.2
  · intro i j
    filter_upwards [cascade_connector_nhds x m hs₁ hs₂] with y hy
    rw [cascadePotential_two_terms hL hK hk A y (m := m) (by linarith [hy.1])
      (by have hh : K+2<cascadeLength L K := by unfold cascadeLength; linarith
          linarith [hy.2]) i j]
    simpa only [sub_zero] using cascadePotentialTerm_connector_pair hL hK hk A y m hy.1 hy.2 i j
  · apply pureMode_constitution hf hf' (cascadeAxis_ne_zero m)
    simp only [sub_zero,cascade_dilation_time hk,connectorAngular]
    rw [div_mul_cancel₀ _ (connectorProfile_pos K _).ne']

end ScalarConductivity

end

end OAI
