import Mathlib
import OAI.Analysis.Conductivity.Flux.CascadeFluxLocal
import OAI.Analysis.Conductivity.Branching.CascadeProfileDeriv
import OAI.Analysis.Conductivity.Flux.PotentialCurl

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cascadeAxis_ne_succ (m : ℕ) : cascadeAxis m ≠ cascadeAxis (m+1) := by
  rw [cascadeAxis_succ]
  unfold cascadeAxis
  split <;> decide

lemma cascade_dilation_coord (D k : ℝ) (m : ℕ) (x : Coord3) {a : Fin 3} (ha : a≠0) :
    ((k*2^m) • (x-cascadeCenter D k m)) a = k*2^m*x a := by
  simp [cascadeCenter,Pi.single_eq_of_ne ha]

lemma cascade_dilation_succ {k : ℝ} (hk : k≠0) (D : ℝ) (m : ℕ) (x : Coord3) :
    (k*2^(m+1)) • (x-cascadeCenter D k (m+1)) =
      (2:ℝ) • (((k*2^m) • (x-cascadeCenter D k m))-Pi.single 0 D) := by
  ext a
  by_cases ha : a=0
  · subst a
    change ((k*2^(m+1)) • (x-cascadeCenter D k (m+1))) 0 =
      2*(((k*2^m) • (x-cascadeCenter D k m)) 0-D)
    rw [cascade_dilation_time hk,cascade_dilation_time hk,cascadePhase_succ]
  · change ((k*2^(m+1)) • (x-cascadeCenter D k (m+1))) a =
      2*(((k*2^m) • (x-cascadeCenter D k m)) a-(Pi.single 0 D : Coord3) a)
    rw [cascade_dilation_coord _ _ _ _ ha,cascade_dilation_coord _ _ _ _ ha,
      Pi.single_eq_of_ne ha,pow_succ]
    ring

lemma cascadePotentialMother_wedges (L K : ℝ) (a b i j : Fin 3) (x : Coord3) :
    cascadePotentialMother L K a b i j x =
      wedgePotential 0 a (cascadeBaseStream L K a) i j x +
      wedgePotential a b (cascadeCrossStream L K a b) i j x := by
  unfold cascadePotentialMother wedgePotential
  ring

lemma wedgePotential_scalar (a b i j : Fin 3) (c : ℝ) (H : Coord3 → ℝ) (x : Coord3) :
    wedgePotential a b (fun y => c*H y) i j x = c*wedgePotential a b H i j x := by
  unfold wedgePotential
  split <;> split <;> ring

lemma wedgePotential_as_mul (a b i j : Fin 3) (H : Coord3 → ℝ) (x : Coord3) :
    wedgePotential a b H i j x =
      ((if i=a ∧ j=b then (1:ℝ) else 0)-(if j=a ∧ i=b then (1:ℝ) else 0))*H x := by
  unfold wedgePotential
  split <;> split <;> ring

lemma cascade_stage_potential_crossing {L K : ℝ} (hL : 0<L) (hK : 0<K)
    {a b : Fin 3} (ha : a≠0) (hb : b≠0) (x : Coord3)
    (hs₁ : K+2 < x 0) (hs₂ : x 0 < cascadeLength L K) (i j : Fin 3) :
    cascadePotentialMother L K a b i j x + cascadeRatio L K*
      cascadePotentialMother L K b a i j ((2:ℝ) • (x-Pi.single 0 (cascadeLength L K))) =
    (connectorProfile K (K+2)*exp (-3*L))*
      crossingPotential L a b i j (x-Pi.single 0 (K+2+L)) := by
  let y : Coord3 := x-Pi.single 0 (K+2+L)
  let z : Coord3 := (2:ℝ) • (x-Pi.single 0 (cascadeLength L K))
  have hy0 : y 0=x 0-(K+2+L) := by simp [y]
  have hya : y a=x a := by simp [y,Pi.single_eq_of_ne ha]
  have hyb : y b=x b := by simp [y,Pi.single_eq_of_ne hb]
  have hz0 : z 0=2*(x 0-cascadeLength L K) := by simp [z]
  have hzb : z b=2*x b := by simp [z,Pi.single_eq_of_ne hb]
  have hc : cascadeCrossStream L K b a z=0 := by
    apply cascadeCrossStream_zero_left hL
    rw [hz0]
    linarith
  have hbase : cascadeBaseStream L K a x =
      (connectorProfile K (K+2)*exp (-3*L))*(deriv (crossingFirst L) (y 0)*sin (y a)) := by
    rw [cascadeBaseStream,cascadeProfile_crossing_current_deriv hL hK hs₁,hy0,hya]
    ring
  have hnext : cascadeRatio L K*cascadeBaseStream L K b z =
      (connectorProfile K (K+2)*exp (-3*L))*((deriv (crossingSecond L) (y 0)/2)*sin (2*y b)) := by
    rw [cascadeBaseStream,hz0,hzb,←mul_assoc,cascadeProfile_crossing_next_deriv hL hK hs₂,hy0,hyb]
    ring
  have hcross : cascadeCrossStream L K a b x =
      (connectorProfile K (K+2)*exp (-3*L))*
      angularStream (crossingResidualFirst L) (crossingResidualSecond L) a b y := by
    simp only [cascadeCrossStream,angularStream,hy0,hya,hyb]
  change cascadePotentialMother L K a b i j x +
    cascadeRatio L K*cascadePotentialMother L K b a i j z = _
  rw [cascadePotentialMother_wedges,cascadePotentialMother_wedges]
  change _ = (connectorProfile K (K+2)*exp (-3*L))*crossingPotential L a b i j y
  simp only [crossingPotential,wedgePotential_as_mul,hc,hbase,hcross]
  linear_combination
    ((if i=0 ∧ j=b then (1:ℝ) else 0)-(if j=0 ∧ i=b then (1:ℝ) else 0))*hnext

lemma cascadePotentialTerm_crossing_pair {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : K+2 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K) (i j : Fin 3) :
    cascadePotentialTerm L K k A m i j x + cascadePotentialTerm L K k A (m+1) i j x =
      (A*cascadeRatio L K^m)*(connectorProfile K (K+2)*exp (-3*L))*
      crossingPotential L (cascadeAxis m) (cascadeAxis (m+1)) i j
        ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)-Pi.single 0 (K+2+L)) := by
  have haxis : cascadeAxis (m+1+1)=cascadeAxis m := by
    simp [cascadeAxis,Nat.even_add_one]
  simp only [cascadePotentialTerm,haxis]
  rw [cascade_dilation_succ hk,pow_succ]
  have he := cascade_stage_potential_crossing hL hK (cascadeAxis_ne_zero m)
    (cascadeAxis_ne_zero (m+1)) ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m))
    (by simpa only [cascade_dilation_time hk] using hs₁)
    (by simpa only [cascade_dilation_time hk] using hs₂) i j
  linear_combination (A*cascadeRatio L K^m)*he

end ScalarConductivity

end

end OAI
