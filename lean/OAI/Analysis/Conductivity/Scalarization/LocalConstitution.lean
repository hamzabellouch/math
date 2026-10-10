import Mathlib
import OAI.Analysis.Conductivity.Flux.CascadeStageCurl
import OAI.Analysis.Conductivity.Variational.CrossingGradient

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma direction_affineShift {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    (s r : ℝ) (c d v x : Coord3) :
    direction v (fun y => s*f (r • (y-c)-d)) x = s*r*direction v f (r • (x-c)-d) := by
  have hT : Differentiable ℝ (fun y : Coord3 => f (y-d)) := hf.comp (differentiable_id.sub_const d)
  rw [direction_dilation hT]
  have hh := direction_dilation hf 1 1 d v (r • (x-c))
  simpa only [one_mul,one_smul] using congrArg (fun z => s*r*z) hh

lemma potentialCurl_affineShift {S : Fin 3 → Fin 3 → Coord3 → ℝ}
    (hS : ∀ i j, Differentiable ℝ (S i j)) (s r : ℝ) (c d x : Coord3) (i : Fin 3) :
    potentialCurl (fun i j y => s*S i j (r • (y-c)-d)) x i =
      s*r*potentialCurl S (r • (x-c)-d) i := by
  simp only [potentialCurl,direction_affineShift (hS _ _),Finset.mul_sum]

lemma local_scaled_constitution {V v : Coord3 → ℝ}
    {T S : Fin 3 → Fin 3 → Coord3 → ℝ}
    (hv : Differentiable ℝ v) (hS : ∀ i j, Differentiable ℝ (S i j))
    (s r : ℝ) (c d x : Coord3) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hV : V =ᶠ[𝓝 x] fun y => s*v (r • (y-c)-d))
    (hT : ∀ i j, T i j =ᶠ[𝓝 x] fun y => s*S i j (r • (y-c)-d))
    (hc : A *ᵥ (fun i => direction (Pi.single i 1) v (r • (x-c)-d)) =
      potentialCurl S (r • (x-c)-d)) :
    A *ᵥ (fun i => direction (Pi.single i 1) V x) = potentialCurl T x := by
  ext i
  rw [potentialCurl_congr_nhds x hT i,potentialCurl_affineShift hS]
  have hg (j : Fin 3) : direction (Pi.single j 1) V x =
      (s*r)*direction (Pi.single j 1) v (r • (x-c)-d) := by
    rw [direction_congr_nhds hV,direction_affineShift hv]
  simp only [mulVec,dotProduct,hg]
  calc
    _ = s*r*∑ j, A i j*direction (Pi.single j 1) v (r • (x-c)-d) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ = _ := by rw [←hc]; rfl

lemma cascadeValue_crossing {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : K+2 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K) :
    cascadeValue L K k A x =
      ((A*cascadeRatio L K^m)*(connectorProfile K (K+2)*exp (-3*L)))*
      crossingValue3 L (cascadeAxis m) (cascadeAxis (m+1))
        ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)-Pi.single 0 (K+2+L)) := by
  rw [cascadeValue_two_modes hL hK A x m (by linarith) hs₂.le]
  have h := cascade_overlap_value hL hK hs₁.le hs₂.le (A*cascadeRatio L K^m)
    (k*2^m*x (cascadeAxis m)) (k*2^m*x (cascadeAxis (m+1)))
  simp only [crossingValue3,Pi.sub_apply,Pi.single_eq_same,
    Pi.single_eq_of_ne (cascadeAxis_ne_zero m),Pi.single_eq_of_ne (cascadeAxis_ne_zero (m+1)),
    sub_zero,cascade_dilation_time hk,cascade_dilation_coord _ _ _ _ (cascadeAxis_ne_zero m),
    cascade_dilation_coord _ _ _ _ (cascadeAxis_ne_zero (m+1))]
  rw [cascadeTerm,cascadeTerm,cascadePhase_succ,pow_succ]
  convert h using 1 <;> ring_nf

lemma cascade_crossing_nhds {L K k : ℝ} (x : Coord3) (m : ℕ)
    (hs₁ : K+2 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K) :
    {y : Coord3 | K+2 < cascadePhase (cascadeLength L K) k m (y 0) ∧
      cascadePhase (cascadeLength L K) k m (y 0) < cascadeLength L K} ∈ 𝓝 x := by
  have hc : Continuous (fun y : Coord3 => cascadePhase (cascadeLength L K) k m (y 0)) := by
    unfold cascadePhase
    fun_prop
  exact (hc.isOpen_preimage _ isOpen_Ioo).mem_nhds ⟨hs₁,hs₂⟩

theorem cascade_crossing_constitution {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : K+2 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K) :
    crossingTensor L (cascadeAxis m) (cascadeAxis (m+1))
        ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)-Pi.single 0 (K+2+L)) *ᵥ
      (fun i => direction (Pi.single i 1) (cascadeValue L K k A) x) =
      cascadeFlux L K k A x := by
  apply local_scaled_constitution (crossingValue3_diff L _ _) (crossingPotential_diff L _ _)
    ((A*cascadeRatio L K^m)*(connectorProfile K (K+2)*exp (-3*L))) (k*2^m)
    (cascadeCenter (cascadeLength L K) k m) (Pi.single 0 (K+2+L)) x
  · filter_upwards [cascade_crossing_nhds x m hs₁ hs₂] with y hy
    exact cascadeValue_crossing hL hK hk A y m hy.1 hy.2
  · intro i j
    filter_upwards [cascade_crossing_nhds x m hs₁ hs₂] with y hy
    rw [cascadePotential_two_terms hL hK hk A y (m := m) (by linarith [hy.1]) (by linarith [hy.2])]
    exact cascadePotentialTerm_crossing_pair hL hK hk A y m hy.1 hy.2 i j
  · exact crossingTensor_constitution hL (cascadeAxis_ne_zero m)
      (cascadeAxis_ne_zero (m+1)) (cascadeAxis_ne_succ m) _

end ScalarConductivity

end

end OAI
