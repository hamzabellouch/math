import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.Domain
import OAI.Geometry.WeakHessian.HeatFlow.FormGenerator

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
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.formGenerator_young {u A v : E}
    (hu : hQ.IsFormGenerator u A) (hv : Q v < ∞) {α : ℝ} (hα : 0 < α) (c : ℝ) :
    c * ⟪A,v⟫_ℝ - α*(Q v).toReal ≤ c^2/α*(Q u).toReal := by
  obtain ⟨huf, hgen⟩ := hu
  let u' : hQ.domain := ⟨u,huf⟩
  let v' : hQ.domain := ⟨v,hv⟩
  have H := hQ.realEnergy_quadratic.nonneg ((c/α) • u' + v')
  rw [hQ.realEnergy_add, hQ.realEnergy_quadratic.smul,
    map_smul, LinearMap.smul_apply, smul_eq_mul] at H
  have hg := hgen v'
  change 2*hQ.form u' v' = -⟪A,v⟫_ℝ at hg
  have heq : α*((c/α)^2*hQ.realEnergy u' +
      2*(c/α * hQ.form u' v') + hQ.realEnergy v') =
      c^2/α*(Q u).toReal + 2*c*hQ.form u' v' + α*(Q v).toReal := by
    dsimp [ClosedQuadraticEnergy.realEnergy, u', v']
    field_simp
  have H' := mul_nonneg hα.le H
  rw [heq] at H'
  have hg' := congrArg (fun x : ℝ => c*x) hg
  nlinarith

lemma ClosedQuadraticEnergy.transport_pairing_le
    {q ρ u A : ℝ → E} {a b α c C : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α)
    (hq : ContinuousOn q (Icc a b)) (hρ : ContinuousOn ρ (Icc a b))
    (hqfin : ∀ t ∈ Ico a b, Q (q t) < ∞)
    (hgen : ∀ t ∈ Ico a b, hQ.IsFormGenerator (u t) (A t))
    (hener : ∀ t ∈ Ico a b, (Q (u t)).toReal ≤ C)
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt ρ (c • A t) (Ici t) t)
    (hinc : ∀ t ∈ Ico a b, ∀ s ∈ Ioc t b,
      ⟪q s-q t,ρ t⟫_ℝ ≤ -(s-t)*t/s*α*(Q (q t)).toReal) :
    ⟪q b,ρ b⟫_ℝ - ⟪q a,ρ a⟫_ℝ ≤ (b-a)*c^2/α*C := by
  let J : ℝ → ℝ := fun t => ⟪q t,ρ t⟫_ℝ
  let M : ℝ := c^2/α*C
  have hJ : ContinuousOn J (Icc a b) := hq.inner hρ
  have HB : ∀ t, HasDerivAt (fun s => J a + M*(s-a)) M t := by
    intro t
    simpa only [mul_one, id_eq] using! (((hasDerivAt_id t).sub_const a).const_mul M).const_add (J a)
  have hbound : ∀ t ∈ Ico a b, ∀ r : ℝ, M < r →
      ∃ᶠ s in 𝓝[>] t, slope J t s < r := by
    intro t ht r hr
    have ht0 : 0 < t := ha.trans_le ht.1
    have hqs : Tendsto q (𝓝[>] t) (𝓝 (q t)) :=
      (hq t (Ico_subset_Icc_self ht)).mono_left
        (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ht))
    have hρs : Tendsto (slope ρ t) (𝓝[>] t) (𝓝 (c • A t)) :=
      (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mp (hderiv t ht).Ioi_of_Ici
    have hl : Tendsto (fun s : ℝ => -t/s*α*(Q (q t)).toReal + ⟪q s,slope ρ t s⟫_ℝ)
        (𝓝[>] t) (𝓝 (-α*(Q (q t)).toReal + ⟪q t,c • A t⟫_ℝ)) := by
      have hrat : Tendsto (fun s : ℝ => -t/s*α*(Q (q t)).toReal)
          (𝓝[>] t) (𝓝 (-α*(Q (q t)).toReal)) := by
        have H : Tendsto (fun s : ℝ => -t/s*α*(Q (q t)).toReal)
            (𝓝[>] t) (𝓝 (-t/t*α*(Q (q t)).toReal)) :=
          (((tendsto_const_nhds.div (tendsto_id.mono_left nhdsWithin_le_nhds) ht0.ne').mul_const α).mul_const
            ((Q (q t)).toReal))
        simpa [ht0.ne'] using H
      exact hrat.add (hqs.inner hρs)
    have hy : -α*(Q (q t)).toReal + ⟪q t,c • A t⟫_ℝ ≤ M := by
      rw [real_inner_smul_right, real_inner_comm (A t) (q t)]
      have H := hQ.formGenerator_young (hgen t ht) (hqfin t ht) hα c
      have H' := mul_le_mul_of_nonneg_left (hener t ht) (by positivity : 0 ≤ c^2/α)
      dsimp [M]
      linarith
    have hev : ∀ᶠ s in 𝓝[>] t, slope J t s < r := by
      filter_upwards [hl.eventually_lt_const (hy.trans_lt hr), Ioc_mem_nhdsGT ht.2] with s hs hsI
      apply lt_of_le_of_lt _ hs
      have hi := (div_le_div_of_nonneg_right (hinc t ht s hsI) (sub_nonneg.mpr hsI.1.le))
      have heq : slope J t s = ⟪q s-q t,ρ t⟫_ℝ/(s-t) + ⟪q s,slope ρ t s⟫_ℝ := by
        simp only [slope_def_field, slope_def_module, real_inner_smul_right, inner_sub_left,
          inner_sub_right, J]
        ring
      rw [heq]
      have he : (-(s-t)*t/s*α*(Q (q t)).toReal)/(s-t) =
          -t/s*α*(Q (q t)).toReal := by
        field_simp [sub_ne_zero.mpr hsI.1.ne']
      rw [he] at hi
      linarith
    exact hev.frequently
  have H := image_le_of_liminf_slope_right_le_deriv_boundary hJ
    (show J a ≤ J a+M*(a-a) by simp)
    (by fun_prop : ContinuousOn (fun s => J a+M*(s-a)) (Icc a b))
    (fun t _ => (HB t).hasDerivWithinAt) hbound (right_mem_Icc.mpr hab)
  calc
    _ ≤ M*(b-a) := by change J b-J a ≤ M*(b-a); linarith
    _ = _ := by dsimp [M]; ring

end WeakHessianFunctional

end
end InlinedFile0

end OAI
