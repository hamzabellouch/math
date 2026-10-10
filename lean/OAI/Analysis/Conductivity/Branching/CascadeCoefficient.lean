import Mathlib
import OAI.Analysis.Conductivity.Flux.CascadeStageCurl
import OAI.Analysis.Conductivity.Flux.CascadeTensorBounds

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

local instance cascadeCoefficientMeasurableSpace : MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance cascadeCoefficientBorelSpace : BorelSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

lemma exists_cascade_index (D k t : ℝ) :
    ∃ n : ℕ, cascadePhase D k n t ≤ D ∨ 2*D ≤ k*t := by
  by_cases ht : 2*D ≤ k*t
  · exact ⟨0,Or.inr ht⟩
  · obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (D/(2*D-k*t)) (by norm_num : (1:ℝ)<2)
    refine ⟨n,Or.inl ?_⟩
    have hh := (div_le_iff₀ (by linarith : 0<2*D-k*t)).mp hn.le
    unfold cascadePhase
    nlinarith

def cascadeIndex (D k : ℝ) (x : Coord3) : ℕ := Nat.find (exists_cascade_index D k (x 0))

lemma cascadeIndex_measurable (D k : ℝ) : Measurable (cascadeIndex D k) := by
  apply measurable_find
  intro n
  have hc : Continuous (fun x : Coord3 => cascadePhase D k n (x 0)) := by
    unfold cascadePhase
    fun_prop
  exact (isClosed_le hc continuous_const).measurableSet.union
    (isClosed_le continuous_const (continuous_const.mul (continuous_apply 0))).measurableSet

lemma cascadeIndex_spec {D k : ℝ} (x : Coord3) (ht₀ : 0≤k*x 0) (ht : k*x 0<2*D) :
    0≤cascadePhase D k (cascadeIndex D k x) (x 0) ∧
      cascadePhase D k (cascadeIndex D k x) (x 0)≤D := by
  have hs := Nat.find_spec (exists_cascade_index D k (x 0))
  have hu : cascadePhase D k (cascadeIndex D k x) (x 0)≤D := hs.resolve_right (not_le.mpr ht)
  refine ⟨?_,hu⟩
  cases hn : cascadeIndex D k x with
  | zero => simpa [cascadePhase_zero] using ht₀
  | succ n =>
    have hmin := Nat.find_min (exists_cascade_index D k (x 0)) (show n<cascadeIndex D k x by omega)
    have hprev : D<cascadePhase D k n (x 0) := lt_of_not_ge (fun h => hmin (Or.inl h))
    rw [cascadePhase_succ]
    linarith

def cascadeStageTensor (L K k : ℝ) (n : ℕ) (x : Coord3) : Matrix (Fin 3) (Fin 3) ℝ :=
  if cascadePhase (cascadeLength L K) k n (x 0)<K+2 then
    pureModeTensor (connectorAngular K (cascadePhase (cascadeLength L K) k n (x 0))) (cascadeAxis n)
  else crossingTensor L (cascadeAxis n) (cascadeAxis (n+1))
    ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)-Pi.single 0 (K+2+L))

def cascadeTensor (L K k : ℝ) (x : Coord3) : Matrix (Fin 3) (Fin 3) ℝ :=
  if 0≤k*x 0 ∧ k*x 0<2*cascadeLength L K then
    cascadeStageTensor L K k (cascadeIndex (cascadeLength L K) k x) x
  else 1

lemma connectorAngular_continuous (K : ℝ) : Continuous (connectorAngular K) := by
  have hf := (connectorProfile_smooth K).continuous
  have hff := (smooth_deriv_infty (smooth_deriv_infty (connectorProfile_smooth K))).continuous
  unfold connectorAngular
  exact hff.div hf (fun x => (connectorProfile_pos K x).ne')

lemma cascadeStageTensor_measurable (L K k : ℝ) (n : ℕ) :
    Measurable (cascadeStageTensor L K k n) := by
  have hp : Continuous (fun x : Coord3 => cascadePhase (cascadeLength L K) k n (x 0)) := by
    unfold cascadePhase
    fun_prop
  have hc : Continuous (fun x : Coord3 =>
      pureModeTensor (connectorAngular K (cascadePhase (cascadeLength L K) k n (x 0))) (cascadeAxis n)) := by
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    simp only [pureModeTensor, Matrix.diagonal_apply]
    split_ifs
    · exact (connectorAngular_continuous K).comp hp
    · exact continuous_const
    · exact continuous_const
  have hx : Continuous (fun x : Coord3 => crossingTensor L (cascadeAxis n) (cascadeAxis (n+1))
      ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)-Pi.single 0 (K+2+L))) :=
    (crossingTensor_continuous L _ _).comp (by fun_prop)
  exact Measurable.ite (isOpen_lt hp continuous_const).measurableSet hc.measurable hx.measurable

lemma cascadeTensor_measurable (L K k : ℝ) : Measurable (cascadeTensor L K k) := by
  have hs : Measurable (fun x : Coord3 => cascadeStageTensor L K k
      (cascadeIndex (cascadeLength L K) k x) x) := by
    apply Measurable.find (cascadeStageTensor_measurable L K k)
    intro n
    have hc : Continuous (fun x : Coord3 => cascadePhase (cascadeLength L K) k n (x 0)) := by
      unfold cascadePhase
      fun_prop
    exact (isClosed_le hc continuous_const).measurableSet.union
      (isClosed_le continuous_const (continuous_const.mul (continuous_apply 0))).measurableSet
  have hp : MeasurableSet {x : Coord3 | 0≤k*x 0 ∧ k*x 0<2*cascadeLength L K} := by
    apply MeasurableSet.inter
    · exact (isClosed_le continuous_const (continuous_const.mul (continuous_apply 0))).measurableSet
    · exact (isOpen_lt (continuous_const.mul (continuous_apply 0)) continuous_const).measurableSet
  exact Measurable.ite hp hs measurable_const

lemma cascadeTensor_symm (L K k : ℝ) (x : Coord3) : (cascadeTensor L K k x).IsSymm := by
  unfold cascadeTensor cascadeStageTensor
  split_ifs
  · exact pureModeTensor_symm _ _
  · exact crossingTensor_symm _ _ _ _
  · exact isSymm_one

lemma cascadeTensor_normal (L K k : ℝ) (x : Coord3) :
    cascadeTensor L K k x *ᵥ (Pi.single 0 1 : Coord3) = Pi.single 0 1 := by
  unfold cascadeTensor cascadeStageTensor
  split_ifs
  · exact pureModeTensor_normal (cascadeAxis_ne_zero _) _
  · exact crossingTensor_normal (cascadeAxis_ne_zero _) (cascadeAxis_ne_zero _) _ _
  · exact one_mulVec _

lemma cascadeTensor_bounds {L K k : ℝ}
    (hL : ∀ z x y X Y : ℝ,
      (1/8)*(X^2+Y^2) ≤ crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ∧
      crossingXX L z x y*X^2+2*crossingXY L z x y*X*Y+crossingYY L z x y*Y^2 ≤ 10*(X^2+Y^2))
    (hK : ∀ z, 1/8≤connectorAngular K z ∧ connectorAngular K z≤10)
    (x v : Coord3) :
    (1/8)*(v ⬝ᵥ v) ≤ v ⬝ᵥ (cascadeTensor L K k x *ᵥ v) ∧
      v ⬝ᵥ (cascadeTensor L K k x *ᵥ v) ≤ 10*(v ⬝ᵥ v) := by
  unfold cascadeTensor cascadeStageTensor
  split_ifs
  · exact pureModeTensor_bounds (hK _).1 (hK _).2 _ _
  · exact crossingTensor_bounds hL (cascadeAxis_ne_zero _) (cascadeAxis_ne_zero _)
      (cascadeAxis_ne_succ _) _ _
  · rw [one_mulVec]
    have hp : 0≤v ⬝ᵥ v := by
      apply Finset.sum_nonneg; intro i _; exact mul_self_nonneg _
    constructor <;> nlinarith

end ScalarConductivity

end

end OAI
