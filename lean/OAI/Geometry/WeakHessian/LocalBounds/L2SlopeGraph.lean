import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.L2GradientGraph
import OAI.Geometry.WeakHessian.LocalBounds.SlopeApproxAntitone

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
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma localSlope_ne_top {f : X → ℝ} (hf : GloballyLipschitz f) (x : X) :
    localSlope f x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top
      (localSlope_le_lipschitz hf.choose_spec x)

omit [MeasurableSpace X] [BorelSpace X] in
lemma localSlope_toReal_add_le {f g : X → ℝ}
    (hf : GloballyLipschitz f) (hg : GloballyLipschitz g) (x : X) :
    (localSlope (fun y => f y+g y) x).toReal ≤
      (localSlope f x).toReal+(localSlope g x).toReal := by
  rw [← ENNReal.toReal_add (localSlope_ne_top hf x) (localSlope_ne_top hg x)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨localSlope_ne_top hf x,
    localSlope_ne_top hg x⟩) (localSlope_add_le f g x)

omit [MeasurableSpace X] [BorelSpace X] in
lemma localSlope_toReal_const_mul (a : ℝ) (f : X → ℝ) (x : X) :
    (localSlope (fun y => a*f y) x).toReal = |a| * (localSlope f x).toReal := by
  rw [localSlope_const_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg a)]

def l2SlopeGraph (m : Measure X) : Set (WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)) :=
  {p | ∃ f : X → ℝ, GloballyLipschitz f ∧ ∃ hf : MemLp f 2 m,
    hf.toLp f = p.fst ∧ ∀ᵐ x ∂m, (localSlope f x).toReal ≤ p.snd x}

def l2RelaxedGraph (m : Measure X) : Set (WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)) :=
  closure (l2SlopeGraph m)

omit [BorelSpace X] in
lemma convex_l2SlopeGraph : Convex ℝ (l2SlopeGraph m) := by
  intro p hp q hq a b ha hb _hab
  obtain ⟨f,hf,hm,hp,hD⟩ := hp
  obtain ⟨g,hg,hn,hq,hE⟩ := hq
  have hfg : MemLp (fun x => a*f x+b*g x) 2 m := (hm.const_mul a).add (hn.const_mul b)
  refine ⟨fun x => a*f x+b*g x, ?_, hfg, ?_, ?_⟩
  · exact ⟨_, (lipschitz_const_mul_real hf.choose_spec a).add
      (lipschitz_const_mul_real hg.choose_spec b)⟩
  · apply Lp.ext
    filter_upwards [hfg.coeFn_toLp,
      Lp.coeFn_add (a • p.fst) (b • q.fst), Lp.coeFn_smul a p.fst,
      Lp.coeFn_smul b q.fst, hm.coeFn_toLp,hn.coeFn_toLp] with x h1 h2 h3 h4 h5 h6
    change _ = (a • p.fst+b • q.fst) x
    rw [h1,h2,Pi.add_apply,h3,h4,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul]
    simp only [← hp,← hq,h5,h6]
  · have haf : GloballyLipschitz (fun x => a*f x) :=
      ⟨_,lipschitz_const_mul_real hf.choose_spec a⟩
    have hbg : GloballyLipschitz (fun x => b*g x) :=
      ⟨_,lipschitz_const_mul_real hg.choose_spec b⟩
    filter_upwards [hD,hE, Lp.coeFn_add (a • p.snd) (b • q.snd),
      Lp.coeFn_smul a p.snd, Lp.coeFn_smul b q.snd] with x hx hy hsum hpa hqb
    change _ ≤ (a • p.snd+b • q.snd) x
    rw [hsum, Pi.add_apply,hpa,hqb,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul]
    calc _ ≤ (localSlope (fun y => a*f y) x).toReal+
          (localSlope (fun y => b*g y) x).toReal := localSlope_toReal_add_le haf hbg x
      _ = a*(localSlope f x).toReal+b*(localSlope g x).toReal := by
        rw [localSlope_toReal_const_mul,localSlope_toReal_const_mul,
          abs_of_nonneg ha,abs_of_nonneg hb]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

omit [BorelSpace X] in
lemma isClosed_l2RelaxedGraph : IsClosed (l2RelaxedGraph m) := isClosed_closure
omit [BorelSpace X] in
lemma convex_l2RelaxedGraph : Convex ℝ (l2RelaxedGraph m) :=
  (convex_l2SlopeGraph (m := m)).closure

lemma IsLocalWeakUpperGradient.mono {f D E : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hDE : D ≤ᵐ[m] E)
    (hE : LocallyL2 m E) : IsLocalWeakUpperGradient m f E := by
  refine ⟨hE,?_,?_⟩
  · filter_upwards [hD.2.1,hDE] with x hx hy
    exact hx.trans hy
  · intro π hπ hb
    apply (hD.2.2 π hπ hb).trans
    apply lintegral_mono_ae
    filter_upwards [hπ.ae_ae_eval_of_ae hDE] with γ hγ
    apply lintegral_mono_ae
    filter_upwards [hγ] with t ht
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal ht) le_rfl

lemma slopeGraph_isUpperGradient (hfinite : FiniteOnBoundedSets m)
    {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)} (hp : p ∈ l2SlopeGraph m) :
    IsLocalWeakUpperGradient m p.fst p.snd := by
  obtain ⟨f,hf,hm,hp,hD⟩ := hp
  have H := (localSlope_isLocalWeakUpperGradient hfinite hf.choose_spec).mono hD
    (fun o R _ => (Lp.memLp p.snd).restrict (Metric.ball o R))
  exact H.congr_ae (hp ▸ hm.coeFn_toLp.symm) Filter.EventuallyEq.rfl

lemma relaxedGraph_isUpperGradient (hfinite : FiniteOnBoundedSets m)
    {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)} (hp : p ∈ l2RelaxedGraph m) :
    IsLocalWeakUpperGradient m p.fst p.snd := by
  exact (closure_minimal (fun _ hp => slopeGraph_isUpperGradient hfinite hp)
    isClosed_l2GradientGraph) hp

omit [BorelSpace X] in
lemma isClosed_relaxedGradient_sublevel (B : ℝ) :
    IsClosed {f : Lp ℝ 2 m | ∃ D : Lp ℝ 2 m,
      WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m ∧ ‖D‖ ≤ B} := by
  apply IsSeqClosed.isClosed
  intro fn f hfn hf
  choose Dn hDn hB using hfn
  exact WeakHessianFunctional.exists_snd_of_tendsto_fst_of_bounded
    isClosed_l2RelaxedGraph convex_l2RelaxedGraph
    (u := fun n => WithLp.toLp 2 (fn n,Dn n)) hDn hf hB

omit [BorelSpace X] in
lemma exists_norm_minimal_relaxedGradient {f : Lp ℝ 2 m}
    (h : ∃ D : Lp ℝ 2 m, WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m) :
    ∃ D : Lp ℝ 2 m, WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m ∧
      ∀ E : Lp ℝ 2 m, WithLp.toLp 2 (f,E) ∈ l2RelaxedGraph m → ‖D‖ ≤ ‖E‖ := by
  let S : Set (Lp ℝ 2 m) := {D | WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m}
  have hScl : IsClosed S := isClosed_l2RelaxedGraph.preimage
    ((WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
      (continuous_const.prodMk continuous_id))
  have hSc : Convex ℝ S := by
    intro D hD E hE a b ha hb hab
    have H := convex_l2RelaxedGraph (m := m) hD hE ha hb hab
    change WithLp.toLp 2 (a • f+b • f,a • D+b • E) ∈ l2RelaxedGraph m at H
    rwa [← add_smul,hab,one_smul] at H
  obtain ⟨D,hD,hnorm⟩ := exists_norm_eq_iInf_of_complete_convex h hScl.isComplete hSc (0 : Lp ℝ 2 m)
  refine ⟨D,hD,fun E hE => ?_⟩
  rw [zero_sub,norm_neg] at hnorm
  rw [hnorm]
  have hlow : BddBelow (Set.range fun w : S => ‖(0 : Lp ℝ 2 m)-w‖) :=
    ⟨0,by rintro _ ⟨w,rfl⟩; exact norm_nonneg _⟩
  calc
    _ ≤ ‖(0 : Lp ℝ 2 m)-E‖ := ciInf_le hlow (⟨E,hE⟩ : S)
    _ = ‖E‖ := by rw [zero_sub,norm_neg]
end WeakHessian

end
end InlinedFile0

end OAI
