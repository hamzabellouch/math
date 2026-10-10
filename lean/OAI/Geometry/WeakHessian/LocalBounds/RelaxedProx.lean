import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.L2SlopeGraph

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

namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [BorelSpace X] in
lemma slopeGraph_hom (a : ℝ) {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)}
    (hp : p ∈ l2SlopeGraph m) :
    WithLp.toLp 2 (a • p.fst,|a| • p.snd) ∈ l2SlopeGraph m := by
  obtain ⟨f,hf,hm,hfp,hD⟩ := hp
  have ha := hm.const_mul a
  refine ⟨fun x => a*f x,⟨_,lipschitz_const_mul_real hf.choose_spec a⟩,ha,?_,?_⟩
  · apply Lp.ext
    filter_upwards [ha.coeFn_toLp,Lp.coeFn_smul a p.fst,hm.coeFn_toLp] with x hx hy hz
    change _ = (a • p.fst) x
    rw [hx,hy,Pi.smul_apply,smul_eq_mul,←hfp,hz]
  · filter_upwards [hD,Lp.coeFn_smul |a| p.snd] with x hx hy
    change (localSlope (fun x => a*f x) x).toReal ≤ (|a| • p.snd) x
    rw [localSlope_toReal_const_mul,hy,Pi.smul_apply,smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg a)

omit [BorelSpace X] in
lemma relaxedGraph_hom (a : ℝ) {f D : Lp ℝ 2 m}
    (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m) :
    WithLp.toLp 2 (a • f,|a| • D) ∈ l2RelaxedGraph m := by
  let T : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) → WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) :=
    fun p => WithLp.toLp 2 (a • p.fst,|a| • p.snd)
  have hT : Continuous T :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
      (((WithLp.continuous_fst 2 _ _).const_smul a).prodMk
        ((WithLp.continuous_snd 2 _ _).const_smul |a|))
  have H : l2SlopeGraph m ⊆ T ⁻¹' l2RelaxedGraph m := fun p hp => subset_closure (slopeGraph_hom a hp)
  exact closure_minimal H (isClosed_l2RelaxedGraph.preimage hT) hD

omit [BorelSpace X] in
lemma relaxedGraph_add {f g D E : Lp ℝ 2 m}
    (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m)
    (hE : WithLp.toLp 2 (g,E) ∈ l2RelaxedGraph m) :
    WithLp.toLp 2 (f+g,D+E) ∈ l2RelaxedGraph m := by
  have H := convex_l2RelaxedGraph (m := m) hD hE
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  have HH := relaxedGraph_hom 2 (f := (1/2 : ℝ) • f+(1/2 : ℝ) • g)
    (D := (1/2 : ℝ) • D+(1/2 : ℝ) • E) H
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2),smul_add,smul_smul,
    show (2 : ℝ)*(1/2)=1 by norm_num,one_smul] at HH
  exact HH

omit [BorelSpace X] in
lemma relaxedGraph_zero : WithLp.toLp 2 ((0 : Lp ℝ 2 m),0) ∈ l2RelaxedGraph m := by
  apply subset_closure
  refine ⟨fun _ => 0,⟨0,LipschitzWith.const 0⟩,MemLp.zero,?_,?_⟩
  · exact MemLp.toLp_zero _
  · filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
    change (localSlope (fun _ : X => (0 : ℝ)) x).toReal ≤ (0 : Lp ℝ 2 m) x
    simp only [localSlope_zero,hx,ENNReal.toReal_zero,Pi.zero_apply,le_refl]

end WeakHessian

namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable {m : Measure X}

structure RelaxedProx (u : Lp ℝ 2 m) (t : ℝ) (v D : Lp ℝ 2 m) : Prop where
  graph : WithLp.toLp 2 (v,D) ∈ l2RelaxedGraph m
  variation : ∀ q E : Lp ℝ 2 m, WithLp.toLp 2 (q,E) ∈ l2RelaxedGraph m →
    ⟪u-v,q-v⟫_ℝ ≤ t^2 * ⟪D,E-D⟫_ℝ

lemma exists_relaxedProx (u : Lp ℝ 2 m) {t : ℝ} (ht : t ≠ 0) :
    ∃ v D : Lp ℝ 2 m, RelaxedProx u t v D := by
  let T : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) → WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) :=
    fun p => WithLp.toLp 2 (p.fst,t⁻¹ • p.snd)
  let S := T ⁻¹' l2RelaxedGraph m
  have hTc : Continuous T :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
      ((WithLp.continuous_fst 2 _ _).prodMk ((WithLp.continuous_snd 2 _ _).const_smul t⁻¹))
  have hScl : IsClosed S := isClosed_l2RelaxedGraph.preimage hTc
  have hSc : Convex ℝ S := by
    intro p hp q hq a b ha hb hab
    have H := convex_l2RelaxedGraph (m := m) hp hq ha hb hab
    change WithLp.toLp 2 (a • p.fst+b • q.fst,
      a • (t⁻¹ • p.snd)+b • (t⁻¹ • q.snd)) ∈ l2RelaxedGraph m at H
    change WithLp.toLp 2 (a • p.fst+b • q.fst,t⁻¹ • (a • p.snd+b • q.snd)) ∈ l2RelaxedGraph m
    simpa only [smul_add,smul_comm t⁻¹ a,smul_comm t⁻¹ b] using H
  have hSne : S.Nonempty := ⟨0,by
    change WithLp.toLp 2 (0,t⁻¹ • (0 : Lp ℝ 2 m)) ∈ l2RelaxedGraph m
    simpa only [smul_zero] using (relaxedGraph_zero (m := m))⟩
  let z := WithLp.toLp 2 (u,(0 : Lp ℝ 2 m))
  obtain ⟨w,hw,hn⟩ := exists_norm_eq_iInf_of_complete_convex hSne hScl.isComplete hSc z
  let v := w.fst
  let D := t⁻¹ • w.snd
  have hwD : w.snd = t • D := by dsimp [D]; simp only [smul_smul,mul_inv_cancel₀ ht,one_smul]
  refine ⟨v,D,hw,?_⟩
  intro q E hE
  have hq : WithLp.toLp 2 (q,t • E) ∈ S := by
    change WithLp.toLp 2 (q,t⁻¹ • (t • E)) ∈ l2RelaxedGraph m
    simpa only [smul_smul,inv_mul_cancel₀ ht,one_smul] using hE
  have H := (norm_eq_iInf_iff_real_inner_le_zero hSc hw).mp hn _ hq
  rw [WithLp.prod_inner_apply] at H
  change ⟪u-v,q-v⟫_ℝ + ⟪0-w.snd,t • E-w.snd⟫_ℝ ≤ 0 at H
  rw [zero_sub,hwD,←smul_sub,inner_neg_left,real_inner_smul_left,real_inner_smul_right] at H
  nlinarith

lemma RelaxedProx.euler {u v D : Lp ℝ 2 m} {t : ℝ} (h : RelaxedProx u t v D) :
    ⟪u-v,v⟫_ℝ = t^2 * ‖D‖^2 := by
  have H0 := h.variation 0 0 relaxedGraph_zero
  simp only [zero_sub,inner_neg_right,real_inner_self_eq_norm_sq] at H0
  have H2 := h.variation ((2 : ℝ) • v) ((2 : ℝ) • D) (by
    simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] using relaxedGraph_hom 2 h.graph)
  rw [show (2 : ℝ) • v-v=v by module,show (2 : ℝ) • D-D=D by module,
    real_inner_self_eq_norm_sq] at H2
  linarith

lemma RelaxedProx.dual {u v D q E : Lp ℝ 2 m} {t : ℝ} (h : RelaxedProx u t v D)
    (hE : WithLp.toLp 2 (q,E) ∈ l2RelaxedGraph m) :
    |⟪u-v,q⟫_ℝ| ≤ t^2 * ‖D‖ * ‖E‖ := by
  have H := h.variation (v+q) (D+E) (relaxedGraph_add h.graph hE)
  rw [add_sub_cancel_left,add_sub_cancel_left] at H
  have hneg : WithLp.toLp 2 (-q,E) ∈ l2RelaxedGraph m := by
    simpa only [abs_neg,abs_one,neg_one_smul,one_smul] using relaxedGraph_hom (-1) hE
  have Hneg := h.variation (v+ -q) (D+E) (relaxedGraph_add h.graph hneg)
  rw [add_sub_cancel_left,add_sub_cancel_left,inner_neg_right] at Hneg
  have HB := (abs_real_inner_le_norm D E).trans' (le_abs_self _)
  have HB' := mul_le_mul_of_nonneg_left HB (sq_nonneg t)
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

lemma RelaxedProx.displacement {u v D : Lp ℝ 2 m} {t : ℝ} (h : RelaxedProx u t v D) :
    ‖u-v‖^2 + t^2 * ‖D‖^2 = ⟪u-v,u⟫_ℝ := by
  rw [←real_inner_self_eq_norm_sq,←h.euler,←inner_add_right,sub_add_cancel]

lemma RelaxedProx.comparison {u v D q E : Lp ℝ 2 m} {t : ℝ} (h : RelaxedProx u t v D)
    (hE : WithLp.toLp 2 (q,E) ∈ l2RelaxedGraph m) :
    ‖u-v‖^2 + t^2 * ‖D‖^2 ≤ ‖u-q‖^2 + t^2 * ‖E‖^2 := by
  have H := h.variation q E hE
  have HQ := norm_sub_sq_real u q
  have HV := norm_sub_sq_real u v
  have HVQ := norm_sub_sq_real v q
  have HDE := norm_sub_sq_real D E
  simp only [inner_sub_left,inner_sub_right,
    real_inner_self_eq_norm_sq] at H
  have Hsq := sq_nonneg ‖v-q‖
  have HE := mul_nonneg (sq_nonneg t) (sq_nonneg ‖D-E‖)
  rw [HDE] at HE
  nlinarith
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
