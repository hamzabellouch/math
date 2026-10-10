import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.Domain

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
open Set
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.resolvent_injective
    (hd : hQ.domain.topologicalClosure = ⊤) : Function.Injective hQ.resolvent := by
  intro u w huw
  have hv : u-w ∈ hQ.domainᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hu := hQ.resolvent_euler u ⟨v,hv⟩
    have hw := hQ.resolvent_euler w ⟨v,hv⟩
    have he : hQ.resolventDomain u = hQ.resolventDomain w := Subtype.ext huw
    rw [he] at hu
    rw [huw] at hu
    rw [inner_sub_left] at hu hw
    rw [inner_sub_right, real_inner_comm u v, real_inner_comm w v]
    linarith
  rw [Submodule.topologicalClosure_eq_top_iff.mp hd] at hv
  exact sub_eq_zero.mp hv

lemma ClosedQuadraticEnergy.resolvent_range_dense
    (hd : hQ.domain.topologicalClosure = ⊤) :
    hQ.resolventLinear.toLinearMap.range.topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro u hu
  change u = 0
  apply hQ.resolvent_injective hd
  rw [hQ.resolvent_zero]
  have hz : ∀ w, ⟪hQ.resolvent u,w⟫_ℝ = 0 := by
    intro w
    rw [hQ.resolvent_symmetric, real_inner_comm (hQ.resolvent w) u]
    exact (Submodule.mem_orthogonal _ _).mp hu (hQ.resolvent w) ⟨w,rfl⟩
  exact inner_self_eq_zero.mp (hz (hQ.resolvent u))

lemma ClosedQuadraticEnergy.resolvent_positive : hQ.resolventLinear.IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨hQ.resolvent_symmetric, ?_⟩
  intro u
  have H := hQ.resolvent_firm u 0
  rw [hQ.resolvent_zero, sub_zero, sub_zero, real_inner_comm] at H
  exact (sq_nonneg _).trans H

lemma ClosedQuadraticEnergy.resolvent_le_one :
    (1 - hQ.resolventLinear).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  constructor
  · intro u w
    change ⟪u-hQ.resolvent u,w⟫_ℝ = ⟪u,w-hQ.resolvent w⟫_ℝ
    rw [inner_sub_left, inner_sub_right, hQ.resolvent_symmetric]
  · intro u
    change 0 ≤ ⟪u-hQ.resolvent u,u⟫_ℝ
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
    have H := hQ.resolvent_nonexpansive u 0
    rw [hQ.resolvent_zero, sub_zero, sub_zero] at H
    have hc := real_inner_le_norm (hQ.resolvent u) u
    nlinarith [norm_nonneg u]

lemma ClosedQuadraticEnergy.resolvent_norm_le_one : ‖hQ.resolventLinear‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖hQ.resolvent u‖ ≤ 1*‖u‖
  simpa [hQ.resolvent_zero] using hQ.resolvent_nonexpansive u 0

def ClosedQuadraticEnergy.IsFormGenerator (u A : E) : Prop :=
  ∃ hu : Q u < ∞, ∀ v : hQ.domain,
    2*hQ.form ⟨u,hu⟩ v = -⟪A,(v:E)⟫_ℝ

lemma ClosedQuadraticEnergy.isFormGenerator_resolvent (u : E) :
    hQ.IsFormGenerator (hQ.resolvent u) (hQ.resolvent u-u) := by
  refine ⟨hQ.resolvent_finite u, ?_⟩
  intro v
  have h := hQ.resolvent_euler u v
  change 2*hQ.form (hQ.resolventDomain u) v = _
  linarith

lemma ClosedQuadraticEnergy.isFormGenerator_iff (u A : E) :
    hQ.IsFormGenerator u A ↔ hQ.resolvent (u-A) = u := by
  constructor
  · rintro ⟨hu, hgen⟩
    apply hQ.minimizer_unique (hQ.resolvent_minimizes (u-A))
    apply (hQ.minimizer_iff_euler (u-A) ⟨u,hu⟩).mpr
    intro v
    rw [hgen v]
    change -⟪A,(v:E)⟫_ℝ + ⟪u-(u-A),(v:E)⟫_ℝ = 0
    simp only [sub_sub_cancel]
    ring
  · intro h
    have H := hQ.isFormGenerator_resolvent (u-A)
    rw [h, sub_sub_cancel] at H
    exact H

lemma ClosedQuadraticEnergy.formGenerator_unique (hd : hQ.domain.topologicalClosure = ⊤)
    {u A B : E} (hA : hQ.IsFormGenerator u A) (hB : hQ.IsFormGenerator u B) : A = B := by
  have he : hQ.resolvent (u-A) = hQ.resolvent (u-B) :=
    ((hQ.isFormGenerator_iff _ _).mp hA).trans ((hQ.isFormGenerator_iff _ _).mp hB).symm
  exact (sub_right_inj).mp (hQ.resolvent_injective hd he)

lemma ClosedQuadraticEnergy.formGenerator_add {u v A B : E}
    (hu : hQ.IsFormGenerator u A) (hv : hQ.IsFormGenerator v B) :
    hQ.IsFormGenerator (u+v) (A+B) := by
  rw [hQ.isFormGenerator_iff]
  have he : u+v-(A+B) = (u-A)+(v-B) := by abel
  rw [he, hQ.resolvent_add, (hQ.isFormGenerator_iff _ _).mp hu,
    (hQ.isFormGenerator_iff _ _).mp hv]

lemma ClosedQuadraticEnergy.formGenerator_smul {u A : E} (c : ℝ)
    (hu : hQ.IsFormGenerator u A) : hQ.IsFormGenerator (c • u) (c • A) := by
  rw [hQ.isFormGenerator_iff, ← smul_sub, hQ.resolvent_smul,
    (hQ.isFormGenerator_iff _ _).mp hu]

lemma ClosedQuadraticEnergy.formGenerator_sub {u v A B : E}
    (hu : hQ.IsFormGenerator u A) (hv : hQ.IsFormGenerator v B) :
    hQ.IsFormGenerator (u-v) (A-B) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using
    hQ.formGenerator_add hu (hQ.formGenerator_smul (-1) hv)

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.formGenerator_energy {u A : E}
    (hu : hQ.IsFormGenerator u A) : 2*(Q u).toReal = -⟪A,u⟫_ℝ := by
  rcases hu with ⟨hfin,hgen⟩
  simpa only [hQ.form_self, ClosedQuadraticEnergy.realEnergy] using hgen ⟨u,hfin⟩

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.formGenerator_energy_bound {u A : E}
    (hu : hQ.IsFormGenerator u A) : 2*(Q u).toReal ≤ ‖A‖*‖u‖ := by
  rw [hQ.formGenerator_energy hu]
  calc
    _ ≤ |⟪A,u⟫_ℝ| := neg_le_abs _
    _ ≤ _ := abs_real_inner_le_norm _ _

lemma ClosedQuadraticEnergy.formGenerator_closed {ι : Type*} {l : Filter ι} [NeBot l]
    {u A : ι → E} {v B : E} (hu : ∀ᶠ i in l, hQ.IsFormGenerator (u i) (A i))
    (hv : Tendsto u l (𝓝 v)) (hB : Tendsto A l (𝓝 B)) : hQ.IsFormGenerator v B := by
  rw [hQ.isFormGenerator_iff]
  have hlim := hQ.resolventLinear.continuous.continuousAt.tendsto.comp (hv.sub hB)
  apply tendsto_nhds_unique hlim
  apply hv.congr'
  filter_upwards [hu] with i hi
  exact ((hQ.isFormGenerator_iff _ _).mp hi).symm

end WeakHessianFunctional

end
end InlinedFile0

end OAI
