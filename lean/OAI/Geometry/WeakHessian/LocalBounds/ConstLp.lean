import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.RelaxedProx
import OAI.Geometry.WeakHessian.Transport.LocalSlopeCompContraction
import OAI.Geometry.WeakHessian.LocalBounds.RealClip

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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter Set WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable {m : Measure X}

lemma slopeGraph_normalContraction {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hη0 : η 0 = 0)
    {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)} (hp : p ∈ l2SlopeGraph m) :
    WithLp.toLp 2 (hη.compLp hη0 p.fst,p.snd) ∈ l2SlopeGraph m := by
  obtain ⟨f,hf,hm,hfp,hD⟩ := hp
  have ha := hη.comp_memLp hη0 hm
  refine ⟨η ∘ f,⟨_,hη.comp hf.choose_spec⟩,ha,?_,?_⟩
  · apply Lp.ext
    filter_upwards [ha.coeFn_toLp,hη.coeFn_compLp hη0 p.fst,hm.coeFn_toLp] with x hx hy hz
    change _ = hη.compLp hη0 p.fst x
    rw [hx,hy,Function.comp_apply,Function.comp_apply,←hfp,hz]
  · filter_upwards [hD] with x hx
    exact (ENNReal.toReal_mono (localSlope_ne_top hf x) (localSlope_comp_contraction hη f x)).trans hx

lemma relaxedGraph_normalContraction {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hη0 : η 0 = 0)
    {f D : Lp ℝ 2 m} (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m) :
    WithLp.toLp 2 (hη.compLp hη0 f,D) ∈ l2RelaxedGraph m := by
  let T : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) → WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) :=
    fun p => WithLp.toLp 2 (hη.compLp hη0 p.fst,p.snd)
  have hT : Continuous T :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
      (((hη.lipschitzWith_compLp hη0).continuous.comp (WithLp.continuous_fst 2 _ _)).prodMk
        (WithLp.continuous_snd 2 _ _))
  have H : l2SlopeGraph m ⊆ T ⁻¹' l2RelaxedGraph m := fun p hp =>
    subset_closure (slopeGraph_normalContraction hη hη0 hp)
  exact closure_minimal H (isClosed_l2RelaxedGraph.preimage hT) hD

lemma realClip_pairing_bound (n : ℕ) {a b : ℝ} (ha : |a| ≤ (n:ℝ)) :
    (realClip n b-b)^2 ≤ (a-b)*(realClip n b-b) := by
  rcases abs_le.mp ha with ⟨ha0,ha1⟩
  by_cases hb : b ≤ n
  · by_cases hb' : -(n:ℝ) ≤ b
    · simp only [realClip,min_eq_left hb,max_eq_right hb',sub_self,mul_zero,zero_pow (by decide : 2 ≠ 0),le_refl]
    · have hb' := le_of_lt (lt_of_not_ge hb')
      simp only [realClip,min_eq_left hb,max_eq_left hb']
      nlinarith
  · have hb := le_of_lt (lt_of_not_ge hb)
    simp only [realClip,min_eq_right hb,max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) n] : -(n:ℝ) ≤ n)]
    nlinarith

lemma RelaxedProx.bounded {u v D : Lp ℝ 2 m} {t : ℝ} (h : RelaxedProx u t v D)
    (n : ℕ) (hu : ∀ᵐ x ∂m, |u x| ≤ (n:ℝ)) : ∀ᵐ x ∂m, |v x| ≤ (n:ℝ) := by
  let w := (realClip_lipschitz n).compLp (realClip_zero n) v
  have hg := relaxedGraph_normalContraction (realClip_lipschitz n) (realClip_zero n) h.graph
  have H := h.variation w D hg
  simp only [sub_self,inner_zero_right,mul_zero] at H
  have HI : ⟪w-v,w-v⟫_ℝ ≤ ⟪u-v,w-v⟫_ℝ := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_mono_ae (L2.integrable_inner (w-v) (w-v) (𝕜 := ℝ))
      (L2.integrable_inner (u-v) (w-v) (𝕜 := ℝ))
    filter_upwards [Lp.coeFn_sub w v,Lp.coeFn_sub u v,
      (realClip_lipschitz n).coeFn_compLp (realClip_zero n) v,hu] with x hw huv hx hu
    simp only [RCLike.inner_apply,conj_trivial,hw,huv,Pi.sub_apply]
    change (w x-v x)*(w x-v x) ≤ (w x-v x)*(u x-v x)
    change (realClip_lipschitz n).compLp (realClip_zero n) v x = realClip n (v x) at hx
    change w x = realClip n (v x) at hx
    rw [hx]
    nlinarith [realClip_pairing_bound n hu (b := v x)]
  rw [real_inner_self_eq_norm_sq] at HI
  have he : w=v := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (w-v)]))
  have hae := (realClip_lipschitz n).coeFn_compLp (realClip_zero n) v
  change (w : X → ℝ) =ᵐ[m] realClip n ∘ (v : X → ℝ) at hae
  rw [he] at hae
  filter_upwards [hae] with x hx
  rw [hx,Function.comp_apply]
  exact realClip_abs_le n (v x)

variable [IsFiniteMeasure m]
def constLp (c : ℝ) : Lp ℝ 2 m := (memLp_const c).toLp (fun _ : X => c)
omit [MetricSpace X] in
lemma constLp_coe (c : ℝ) : (constLp (m := m) c : X → ℝ) =ᵐ[m] (fun _ => c) :=
  (memLp_const c).coeFn_toLp

lemma relaxedGraph_const (c : ℝ) : WithLp.toLp 2 (constLp (m := m) c,0) ∈ l2RelaxedGraph m := by
  apply subset_closure
  refine ⟨fun _ => c,⟨0,LipschitzWith.const c⟩,memLp_const c,rfl,?_⟩
  filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
  change (localSlope (fun _ : X => c) x).toReal ≤ (0 : Lp ℝ 2 m) x
  have hs : localSlope (fun _ : X => c) x = 0 :=
    le_antisymm (by simpa using localSlope_le_lipschitz (LipschitzWith.const c) x) bot_le
  simp only [hs,hx,ENNReal.toReal_zero,Pi.zero_apply,le_refl]

lemma RelaxedProx.mass {u v D : Lp ℝ 2 m} {t : ℝ} (h : RelaxedProx u t v D) :
    (∫ x, v x ∂m) = ∫ x, u x ∂m := by
  have H := h.dual (relaxedGraph_const (m := m) 1)
  simp only [norm_zero,mul_zero] at H
  rw [L2.inner_def] at H
  have he : (∫ x, ⟪(u-v) x,constLp (m := m) 1 x⟫_ℝ ∂m) =
      (∫ x, u x ∂m) - ∫ x, v x ∂m := by
    rw [←integral_sub ((Lp.memLp u).integrable (by norm_num)) ((Lp.memLp v).integrable (by norm_num))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u v,constLp_coe (m := m) 1] with x hx hy
    simp only [RCLike.inner_apply,conj_trivial,hx,hy,Pi.sub_apply,one_mul]
  rw [he] at H
  exact (sub_eq_zero.mp (le_antisymm (abs_le.mp H).2 (by linarith [(abs_le.mp H).1]))).symm
end WeakHessian

end
end InlinedFile0

end OAI
