import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ClosedQuadraticEnergy
import OAI.Geometry.WeakHessian.Entropy.NonnegativeParallelogram

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology

namespace WeakHessianFunctional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

def ClosedQuadraticEnergy.domain : Submodule ℝ E where
  carrier := {f | Q f < ∞}
  zero_mem' := by simp [hQ.zero]
  add_mem' := hQ.add_lt_top
  smul_mem' := by
    intro a f hf
    change Q (a • f) < ∞
    rw [hQ.smul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

def ClosedQuadraticEnergy.realEnergy (f : hQ.domain) : ℝ := (Q f).toReal

lemma ClosedQuadraticEnergy.realEnergy_quadratic :
    NonnegativeParallelogram hQ.realEnergy where
  nonneg _ := ENNReal.toReal_nonneg
  smul a f := by
    change (Q (a • (f:E))).toReal = _
    rw [hQ.smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
    rfl
  parallelogram f g := by
    have H := congrArg ENNReal.toReal (hQ.parallelogram f g f.property g.property)
    rw [ENNReal.toReal_add (hQ.add_lt_top f.property g.property).ne
      (hQ.sub_lt_top f.property g.property).ne,
      ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num) f.property.ne)
        (ENNReal.mul_ne_top (by norm_num) g.property.ne)] at H
    simpa only [ClosedQuadraticEnergy.realEnergy, Submodule.coe_add, Submodule.coe_sub,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat] using H

def ClosedQuadraticEnergy.form : hQ.domain →ₗ[ℝ] hQ.domain →ₗ[ℝ] ℝ :=
  hQ.realEnergy_quadratic.bilin

lemma ClosedQuadraticEnergy.form_apply (f g : hQ.domain) :
    hQ.form f g = energyPolar hQ.realEnergy f g := rfl

lemma ClosedQuadraticEnergy.form_comm (f g : hQ.domain) : hQ.form f g = hQ.form g f :=
  hQ.realEnergy_quadratic.polar_comm f g

lemma ClosedQuadraticEnergy.form_self (f : hQ.domain) :
    hQ.form f f = hQ.realEnergy f := hQ.realEnergy_quadratic.polar_self f

lemma ClosedQuadraticEnergy.realEnergy_add (f g : hQ.domain) :
    hQ.realEnergy (f+g) = hQ.realEnergy f + 2*hQ.form f g + hQ.realEnergy g :=
  hQ.realEnergy_quadratic.polar_add f g

lemma ClosedQuadraticEnergy.proximal_expansion (u : E) (f v : hQ.domain) (t : ℝ) :
    (proximalFunctional Q u (f + t • v)).toReal =
      (proximalFunctional Q u f).toReal +
      t * (2*hQ.form f v + ⟪(f:E)-u, (v:E)⟫_ℝ) +
      t^2 * (hQ.realEnergy v + ‖(v:E)‖^2/2) := by
  have hft : Q ((f:E)+t • (v:E)) < ∞ := (f+t • v).property
  rw [proximalFunctional_toReal hft, proximalFunctional_toReal f.property]
  change hQ.realEnergy (f+t • v) + ‖(f:E) + t • (v:E)-u‖^2/2 = _
  rw [hQ.realEnergy_add, hQ.realEnergy_quadratic.smul]
  have hn : ‖(f:E) + t • (v:E)-u‖^2 =
      ‖(f:E)-u‖^2 + 2*t*⟪(f:E)-u,(v:E)⟫_ℝ + t^2*‖(v:E)‖^2 := by
    have e : (f:E) + t • (v:E)-u = ((f:E)-u) + t • (v:E) := by module
    rw [e, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      inner_smul_right, real_inner_comm (v:E) ((f:E)-u), real_inner_self_eq_norm_sq]
    ring
  rw [hn, map_smul, smul_eq_mul]
  change hQ.realEnergy f + _ + _ + _ = hQ.realEnergy f + _ + _ + _
  ring

lemma ClosedQuadraticEnergy.minimizer_iff_euler (u : E) (f : hQ.domain) :
    (∀ g : E, proximalFunctional Q u f ≤ proximalFunctional Q u g) ↔
      ∀ v : hQ.domain, 2*hQ.form f v + ⟪(f:E)-u,(v:E)⟫_ℝ = 0 := by
  constructor
  · intro hf v
    let a := hQ.realEnergy v + ‖(v:E)‖^2/2
    let b := 2*hQ.form f v + ⟪(f:E)-u,(v:E)⟫_ℝ
    let c := (proximalFunctional Q u f).toReal
    have hmin : IsLocalMin (fun t : ℝ => c + t*b + t^2*a) 0 := by
      apply Filter.Eventually.of_forall
      intro t
      have H := (ENNReal.toReal_le_toReal (proximalFunctional_lt_top f.property).ne
        (proximalFunctional_lt_top (f+t • v).property).ne).mpr (hf (f+t • v))
      simp only [Submodule.coe_add, Submodule.coe_smul] at H
      rw [hQ.proximal_expansion] at H
      simpa [a,b,c] using H
    have hd : HasDerivAt (fun t : ℝ => c + t*b + t^2*a) b 0 := by
      convert (((hasDerivAt_const (0:ℝ) c).add ((hasDerivAt_id (0:ℝ)).mul_const b)).add
        (((hasDerivAt_id (0:ℝ)).pow 2).mul_const a)) using 1 <;> first | rfl | simp
    exact hmin.hasDerivAt_eq_zero hd
  · intro hf g
    by_cases hg : Q g < ∞
    · let v : hQ.domain := ⟨g-(f:E), hQ.sub_lt_top hg f.property⟩
      have heq : (f:E)+(1:ℝ) • (v:E) = g := by simp [v]
      apply (ENNReal.toReal_le_toReal (proximalFunctional_lt_top f.property).ne
        (proximalFunctional_lt_top hg).ne).mp
      have H := hQ.proximal_expansion u f v 1
      rw [heq, hf v] at H
      have hnonneg := hQ.realEnergy_quadratic.nonneg v
      nlinarith [sq_nonneg ‖(v:E)‖]
    · have hg' : Q g = ∞ := eq_top_iff.mpr (not_lt.mp hg)
      simp [proximalFunctional, hg']

variable [CompleteSpace E]

def ClosedQuadraticEnergy.resolvent (u : E) : E :=
  Classical.choose (hQ.exists_minimizer u)

lemma ClosedQuadraticEnergy.resolvent_minimizes (u : E) :
    ∀ g, proximalFunctional Q u (hQ.resolvent u) ≤ proximalFunctional Q u g :=
  Classical.choose_spec (hQ.exists_minimizer u)

lemma ClosedQuadraticEnergy.resolvent_finite (u : E) : Q (hQ.resolvent u) < ∞ := by
  have H := hQ.resolvent_minimizes u 0
  have h0 : proximalFunctional Q u 0 < ∞ := proximalFunctional_lt_top (by simp [hQ.zero])
  exact (le_add_right le_rfl).trans_lt (H.trans_lt h0)

def ClosedQuadraticEnergy.resolventDomain (u : E) : hQ.domain :=
  ⟨hQ.resolvent u, hQ.resolvent_finite u⟩

lemma ClosedQuadraticEnergy.resolvent_euler (u : E) (v : hQ.domain) :
    2*hQ.form (hQ.resolventDomain u) v + ⟪hQ.resolvent u-u, (v:E)⟫_ℝ = 0 :=
  (hQ.minimizer_iff_euler u (hQ.resolventDomain u)).mp (hQ.resolvent_minimizes u) v

lemma ClosedQuadraticEnergy.resolvent_add (u w : E) :
    hQ.resolvent (u+w) = hQ.resolvent u + hQ.resolvent w := by
  apply hQ.minimizer_unique (hQ.resolvent_minimizes (u+w))
  apply (hQ.minimizer_iff_euler (u+w) (hQ.resolventDomain u+hQ.resolventDomain w)).mpr
  intro v
  have hu := hQ.resolvent_euler u v
  have hw := hQ.resolvent_euler w v
  simp only [map_add, LinearMap.add_apply, Submodule.coe_add]
  change 2 * (hQ.form (hQ.resolventDomain u) v + hQ.form (hQ.resolventDomain w) v) +
    ⟪hQ.resolvent u + hQ.resolvent w - (u+w), (v:E)⟫_ℝ = 0
  have heq : hQ.resolvent u + hQ.resolvent w - (u+w) =
    (hQ.resolvent u-u)+(hQ.resolvent w-w) := by abel
  rw [heq, inner_add_left]
  linarith

lemma ClosedQuadraticEnergy.resolvent_smul (a : ℝ) (u : E) :
    hQ.resolvent (a • u) = a • hQ.resolvent u := by
  apply hQ.minimizer_unique (hQ.resolvent_minimizes (a • u))
  apply (hQ.minimizer_iff_euler (a • u) (a • hQ.resolventDomain u)).mpr
  intro v
  have hu := hQ.resolvent_euler u v
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Submodule.coe_smul]
  change 2 * (a * hQ.form (hQ.resolventDomain u) v) +
    ⟪a • hQ.resolvent u-a • u,(v:E)⟫_ℝ = 0
  rw [← smul_sub, real_inner_smul_left]
  calc
    _ = a * (2 * hQ.form (hQ.resolventDomain u) v + ⟪hQ.resolvent u-u,(v:E)⟫_ℝ) := by ring
    _ = 0 := by rw [hu, mul_zero]

lemma ClosedQuadraticEnergy.resolvent_zero : hQ.resolvent 0 = 0 := by
  simpa only [zero_smul] using hQ.resolvent_smul 0 (0:E)

lemma ClosedQuadraticEnergy.resolvent_firm (u w : E) :
    ‖hQ.resolvent u-hQ.resolvent w‖^2 ≤
      ⟪u-w,hQ.resolvent u-hQ.resolvent w⟫_ℝ := by
  let v := hQ.resolventDomain u-hQ.resolventDomain w
  have hu := hQ.resolvent_euler u v
  have hw := hQ.resolvent_euler w v
  have hform : hQ.form (hQ.resolventDomain u) v - hQ.form (hQ.resolventDomain w) v =
      hQ.realEnergy v := by rw [← LinearMap.sub_apply, ← map_sub, hQ.form_self]
  have hinner : ⟪hQ.resolvent u-u,(v:E)⟫_ℝ - ⟪hQ.resolvent w-w,(v:E)⟫_ℝ =
      ‖hQ.resolvent u-hQ.resolvent w‖^2 - ⟪u-w,hQ.resolvent u-hQ.resolvent w⟫_ℝ := by
    rw [← inner_sub_left]
    have heq : hQ.resolvent u-u-(hQ.resolvent w-w) =
      (hQ.resolvent u-hQ.resolvent w)-(u-w) := by abel
    rw [heq, inner_sub_left]
    change ⟪hQ.resolvent u-hQ.resolvent w,hQ.resolvent u-hQ.resolvent w⟫_ℝ - _ = _
    rw [real_inner_self_eq_norm_sq]
    rfl
  have hnonneg := hQ.realEnergy_quadratic.nonneg v
  linarith

lemma ClosedQuadraticEnergy.resolvent_nonexpansive (u w : E) :
    ‖hQ.resolvent u-hQ.resolvent w‖ ≤ ‖u-w‖ := by
  have hf := hQ.resolvent_firm u w
  have hc := real_inner_le_norm (u-w) (hQ.resolvent u-hQ.resolvent w)
  nlinarith [norm_nonneg (hQ.resolvent u-hQ.resolvent w), norm_nonneg (u-w)]

def ClosedQuadraticEnergy.resolventLinear : E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := hQ.resolvent
      map_add' := hQ.resolvent_add
      map_smul' := hQ.resolvent_smul } 1
    (fun u => by
      change ‖hQ.resolvent u‖ ≤ 1 * ‖u‖
      simpa only [hQ.resolvent_zero, sub_zero, one_mul] using hQ.resolvent_nonexpansive u 0)

lemma ClosedQuadraticEnergy.resolvent_symmetric (u w : E) :
    ⟪hQ.resolvent u,w⟫_ℝ = ⟪u,hQ.resolvent w⟫_ℝ := by
  have hu := hQ.resolvent_euler u (hQ.resolventDomain w)
  have hw := hQ.resolvent_euler w (hQ.resolventDomain u)
  rw [hQ.form_comm] at hu
  change 2 * _ + ⟪hQ.resolvent u-u,hQ.resolvent w⟫_ℝ = 0 at hu
  change 2 * _ + ⟪hQ.resolvent w-w,hQ.resolvent u⟫_ℝ = 0 at hw
  rw [inner_sub_left] at hu hw
  rw [real_inner_comm (hQ.resolvent u) (hQ.resolvent w),
    real_inner_comm (hQ.resolvent u) w] at hw
  linarith

end WeakHessianFunctional

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
