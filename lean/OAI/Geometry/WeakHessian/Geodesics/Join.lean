import Mathlib
import OAI.Geometry.WeakHessian.Entropy.EntropyCell

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

namespace CellMidpoint
variable {c : EntropyCell m K N} (p : CellMidpoint c) (env : CDEnvironment m K N)

omit [SigmaFinite m] in
lemma exists_join (l : CellPlan (p.leftCell env)) (r : CellPlan (p.rightCell env)) :
    ∃ q : CellPlan c,
      (∀ t, interpolation (q.law:Measure (Curve X)) (halfTime t) = interpolation (l.law:Measure (Curve X)) t) ∧
      (∀ t, interpolation (q.law:Measure (Curve X)) (rightTime t) = interpolation (r.law:Measure (Curve X)) t) ∧
      (q.law:Measure (Curve X)).map halfCurve = (l.law:Measure (Curve X)) ∧
      (q.law:Measure (Curve X)).map rightCurve = (r.law:Measure (Curve X)) := by
  have hl0 : interpolation (l.law:Measure (Curve X)) timeZero = (c.leftLaw:Measure X) :=
    l.optimal.1.interpolation_endpoints.1
  have hl1 : interpolation (l.law:Measure (Curve X)) timeOne = (p.middle:Measure X) :=
    l.optimal.1.interpolation_endpoints.2
  have hr0 : interpolation (r.law:Measure (Curve X)) timeZero = (p.middle:Measure X) :=
    r.optimal.1.interpolation_endpoints.1
  have hr1 : interpolation (r.law:Measure (Curve X)) timeOne = (c.rightLaw:Measure X) :=
    r.optimal.1.interpolation_endpoints.2
  have hlopt : IsOptimalCoupling (endpointCoupling (l.law:Measure (Curve X)))
      (interpolation ((p.law:Measure (Curve X)).map halfCurve) timeZero)
      (interpolation ((p.law:Measure (Curve X)).map halfCurve) timeOne) := by
    rw [interpolation_map_half,interpolation_map_half,halfTime_zero,halfTime_one,p.optimal.1.interpolation_endpoints.1]
    exact l.optimal
  have hropt : IsOptimalCoupling (endpointCoupling (r.law:Measure (Curve X)))
      (interpolation ((p.law:Measure (Curve X)).map rightCurve) timeZero)
      (interpolation ((p.law:Measure (Curve X)).map rightCurve) timeOne) := by
    rw [interpolation_map_right,interpolation_map_right,rightTime_zero,rightTime_one,p.optimal.1.interpolation_endpoints.2]
    exact r.optimal
  have hel := (optimalPlan_energy_le hlopt (integrable_plan_energy_half p.geodesic p.toCellPlan.integrable_energy)).2
  have her := (optimalPlan_energy_le hropt (integrable_plan_energy_right p.geodesic p.toCellPlan.integrable_energy)).2
  rw [planEnergy_half p.geodesic] at hel
  rw [planEnergy_right p.geodesic] at her
  obtain ⟨q,hqp,hqg,hqo,hql,hqr,hqlm,hqrm⟩ := exists_optimal_geodesic_join
    (l.law:Measure (Curve X)) (r.law:Measure (Curve X)) (p.law:Measure (Curve X))
    (hl1.trans hr0.symm) l.geodesic r.geodesic l.integrable_energy r.integrable_energy
    p.toCellPlan.integrable_energy (by simpa only [hl0,hr1] using p.optimal) (by linarith)
  have hqo' : IsOptimalCoupling (endpointCoupling q) c.leftLaw c.rightLaw := by
    rwa [hl0,hr1] at hqo
  exact ⟨⟨⟨q,hqp⟩,hqg,hqo'⟩,hql,hqr,hqlm,hqrm⟩

noncomputable def join (l : CellPlan (p.leftCell env)) (r : CellPlan (p.rightCell env)) :
    CellPlan c := Classical.choose (p.exists_join env l r)

omit [SigmaFinite m] in
lemma join_half (l : CellPlan (p.leftCell env)) (r : CellPlan (p.rightCell env)) (t : Time) :
    interpolation ((p.join env l r).law:Measure (Curve X)) (halfTime t) =
      interpolation (l.law:Measure (Curve X)) t := (Classical.choose_spec (p.exists_join env l r)).1 t

omit [SigmaFinite m] in
lemma join_right (l : CellPlan (p.leftCell env)) (r : CellPlan (p.rightCell env)) (t : Time) :
    interpolation ((p.join env l r).law:Measure (Curve X)) (rightTime t) =
      interpolation (r.law:Measure (Curve X)) t := (Classical.choose_spec (p.exists_join env l r)).2.1 t

lemma left_energy (l : CellPlan (p.leftCell env)) :
    planEnergy (l.law:Measure (Curve X)) = planEnergy (p.law:Measure (Curve X))/4 := by
  let r := (env.midpoint (p.rightCell env)).toCellPlan
  have H := (Classical.choose_spec (p.exists_join env l r)).2.2.1
  change ((p.join env l r).law:Measure (Curve X)).map halfCurve = (l.law:Measure (Curve X)) at H
  rw [← H,planEnergy_half (p.join env l r).geodesic]
  rw [(p.join env l r).energy_eq p.toCellPlan]

lemma right_energy (r : CellPlan (p.rightCell env)) :
    planEnergy (r.law:Measure (Curve X)) = planEnergy (p.law:Measure (Curve X))/4 := by
  let l := (env.midpoint (p.leftCell env)).toCellPlan
  have H := (Classical.choose_spec (p.exists_join env l r)).2.2.2
  change ((p.join env l r).law:Measure (Curve X)).map rightCurve = (r.law:Measure (Curve X)) at H
  rw [← H,planEnergy_right (p.join env l r).geodesic]
  rw [(p.join env l r).energy_eq p.toCellPlan]

end CellMidpoint

namespace CDEnvironment
variable (env : CDEnvironment m K N)

noncomputable def build : (n : ℕ) → (c : EntropyCell m K N) → CellPlan c
  | 0,c => (env.midpoint c).toCellPlan
  | n+1,c => (env.midpoint c).join env
    (build n ((env.midpoint c).leftCell env))
    (build n ((env.midpoint c).rightCell env))

lemma build_half (n : ℕ) (c : EntropyCell m K N) (t : Time) :
    interpolation ((env.build (n+1) c).law:Measure (Curve X)) (halfTime t) =
      interpolation ((env.build n ((env.midpoint c).leftCell env)).law:Measure (Curve X)) t :=
  (env.midpoint c).join_half env _ _ t

lemma build_right (n : ℕ) (c : EntropyCell m K N) (t : Time) :
    interpolation ((env.build (n+1) c).law:Measure (Curve X)) (rightTime t) =
      interpolation ((env.build n ((env.midpoint c).rightCell env)).law:Measure (Curve X)) t :=
  (env.midpoint c).join_right env _ _ t

lemma build_stable (n k : ℕ) (hnk : n ≤ k) (c : EntropyCell m K N) (t : Time)
    (ht : t ∈ dyadicTimes n) :
    interpolation ((env.build k c).law:Measure (Curve X)) t =
      interpolation ((env.build n c).law:Measure (Curve X)) t := by
  induction n generalizing k c t with
  | zero =>
    rcases ht with rfl | ht
    · rw [(env.build k c).optimal.1.interpolation_endpoints.1,
        (env.build 0 c).optimal.1.interpolation_endpoints.1]
    · have H : t = timeOne := ht
      rw [H,(env.build k c).optimal.1.interpolation_endpoints.2,
        (env.build 0 c).optimal.1.interpolation_endpoints.2]
  | succ n ih =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [env.build_half,env.build_half]
      exact ih k (by omega) _ s hs
    · rw [env.build_right,env.build_right]
      exact ih k (by omega) _ s hs

lemma build_dominated (n : ℕ) (c : EntropyCell m K N) (t : Time) (ht : t ∈ dyadicTimes n) :
    interpolation ((env.build n c).law:Measure (Curve X)) t ≤ c.uniformCap • m := by
  induction n generalizing c t with
  | zero =>
    rcases ht with rfl | ht
    · rw [(env.build 0 c).optimal.1.interpolation_endpoints.1]
      exact dominated_mono_constant c.left_dominated (c.cap_le_uniformCap env)
    · have H : t = timeOne := ht
      rw [H,(env.build 0 c).optimal.1.interpolation_endpoints.2]
      exact dominated_mono_constant c.right_dominated (c.cap_le_uniformCap env)
  | succ n ih =>
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [env.build_half,← (env.midpoint c).left_uniformCap env]
      exact ih _ s hs
    · rw [env.build_right,← (env.midpoint c).right_uniformCap env]
      exact ih _ s hs

lemma build_finite_entropy (n : ℕ) (c : EntropyCell m K N) (t : Time) (ht : t ∈ dyadicTimes n) :
    FiniteEntropy m (interpolation ((env.build n c).law:Measure (Curve X)) t) := by
  induction n generalizing c t with
  | zero =>
    rcases ht with rfl | ht
    · rw [(env.build 0 c).optimal.1.interpolation_endpoints.1]; exact c.left_entropy
    · have H : t = timeOne := ht
      rw [H,(env.build 0 c).optimal.1.interpolation_endpoints.2]; exact c.right_entropy
  | succ n ih =>
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [env.build_half]; exact ih _ s hs
    · rw [env.build_right]; exact ih _ s hs

lemma entropy_chord_half {A B M K E s : ℝ} (hM : M ≤ (A+B)/2-K/8*E) (hs : 0 ≤ s) :
    (1-s)*A+s*M-K/2*(s*(1-s))*(E/4) ≤
      (1-s/2)*A+(s/2)*B-K/2*((s/2)*(1-s/2))*E := by
  calc
    _ ≤ (1-s)*A+s*((A+B)/2-K/8*E)-K/2*(s*(1-s))*(E/4) := by
      have H := mul_le_mul_of_nonneg_left hM hs
      linarith only [H]
    _ = _ := by ring

lemma entropy_chord_right {A B M K E s : ℝ} (hM : M ≤ (A+B)/2-K/8*E) (hs : s ≤ 1) :
    (1-s)*M+s*B-K/2*(s*(1-s))*(E/4) ≤
      (1-(s+1)/2)*A+((s+1)/2)*B-K/2*(((s+1)/2)*(1-(s+1)/2))*E := by
  calc
    _ ≤ (1-s)*((A+B)/2-K/8*E)+s*B-K/2*(s*(1-s))*(E/4) := by
      have H := mul_le_mul_of_nonneg_left hM (sub_nonneg.mpr hs)
      linarith only [H]
    _ = _ := by ring

lemma build_entropy_bound (n : ℕ) (c : EntropyCell m K N) (t : Time) (ht : t ∈ dyadicTimes n) :
    entropyReal m (interpolation ((env.build n c).law:Measure (Curve X)) t) ≤
      (1-(t:ℝ))*entropyReal m (c.leftLaw:Measure X)+(t:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((t:ℝ)*(1-(t:ℝ)))*planEnergy ((env.build n c).law:Measure (Curve X)) := by
  induction n generalizing c t with
  | zero =>
    rcases ht with rfl | ht
    · rw [(env.build 0 c).optimal.1.interpolation_endpoints.1]
      simp only [timeZero,sub_zero,one_mul,zero_mul,mul_zero,add_zero,le_refl]
    · have H : t = timeOne := ht
      rw [H,(env.build 0 c).optimal.1.interpolation_endpoints.2]
      simp only [timeOne,sub_self,zero_mul,one_mul,zero_add,mul_zero,sub_zero,le_refl]
  | succ n ih =>
    have hE := (env.build (n+1) c).energy_eq (env.midpoint c).toCellPlan
    rw [hE]
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [env.build_half]
      apply (ih ((env.midpoint c).leftCell env) s hs).trans
      rw [(env.midpoint c).left_energy env]
      exact entropy_chord_half (env.midpoint c).entropy_bound s.2.1
    · rw [env.build_right]
      apply (ih ((env.midpoint c).rightCell env) s hs).trans
      rw [(env.midpoint c).right_energy env]
      exact entropy_chord_right (env.midpoint c).entropy_bound s.2.2

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
