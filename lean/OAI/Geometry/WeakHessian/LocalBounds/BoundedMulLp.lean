import Mathlib
import OAI.Geometry.WeakHessian.Calculus.LipschitzMulCompact

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma memLp_mul_bounded {f g : X → ℝ} (hf : MemLp f 2 m)
    (hg : AEStronglyMeasurable g m) {B : ℝ} (hb : ∀ᵐ x ∂m, |g x| ≤ B) :
    MemLp (fun x => f x * g x) 2 m := by
  apply (hf.const_mul B).mono (hf.aestronglyMeasurable.mul hg)
  filter_upwards [hb] with x hx
  simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
  calc
    |f x| * |g x| ≤ |f x| * |B| :=
      mul_le_mul_of_nonneg_left (hx.trans (le_abs_self _)) (abs_nonneg _)
    _ = |B| * |f x| := mul_comm _ _

def boundedMulLp {φ : X → ℝ} (hφ : AEStronglyMeasurable φ m) {B : ℝ}
    (hB : ∀ᵐ x ∂m, |φ x| ≤ B) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mul_bounded (Lp.memLp f) hφ hB).toLp (fun x => f x*φ x)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(memLp_mul_bounded (Lp.memLp (f+g)) hφ hB).coeFn_toLp,
          Lp.coeFn_add f g,Lp.coeFn_add
            ((memLp_mul_bounded (Lp.memLp f) hφ hB).toLp (fun x => f x*φ x))
            ((memLp_mul_bounded (Lp.memLp g) hφ hB).toLp (fun x => g x*φ x)),
          (memLp_mul_bounded (Lp.memLp f) hφ hB).coeFn_toLp,
          (memLp_mul_bounded (Lp.memLp g) hφ hB).coeFn_toLp] with x hx hfg hsum hf hg
        simp only [hx,hfg,hsum,hf,hg,Pi.add_apply,add_mul]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(memLp_mul_bounded (Lp.memLp (c • f)) hφ hB).coeFn_toLp,
          Lp.coeFn_smul c f,Lp.coeFn_smul c
            ((memLp_mul_bounded (Lp.memLp f) hφ hB).toLp (fun x => f x*φ x)),
          (memLp_mul_bounded (Lp.memLp f) hφ hB).coeFn_toLp] with x hx hcf hsm hf
        simp only [hx,hcf,hsm,hf,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc] }
    |B| (by
      intro f
      change ‖(memLp_mul_bounded (Lp.memLp f) hφ hB).toLp (fun x => f x*φ x)‖ ≤ |B| * ‖f‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(memLp_mul_bounded (Lp.memLp f) hφ hB).coeFn_toLp,hB] with x hx hb
      simp only [hx,Real.norm_eq_abs,abs_mul]
      calc |f x| * |φ x| ≤ |f x| * |B| :=
            mul_le_mul_of_nonneg_left (hb.trans (le_abs_self B)) (abs_nonneg _)
        _ = _ := mul_comm _ _)

lemma boundedMulLp_ae {φ : X → ℝ} (hφ : AEStronglyMeasurable φ m) {B : ℝ}
    (hB : ∀ᵐ x ∂m, |φ x| ≤ B) (f : Lp ℝ 2 m) :
    boundedMulLp hφ hB f =ᵐ[m] (fun x => f x*φ x) :=
  (memLp_mul_bounded (Lp.memLp f) hφ hB).coeFn_toLp

end WeakHessian

namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma realAbs_lipschitz : LipschitzWith 1 (abs : ℝ → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y

omit [MetricSpace X] [BorelSpace X] in
def slopeMixMap (T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (L : ℝ)
    (pq : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) × WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)) :
    WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) :=
  WithLp.toLp 2 (T pq.1.fst+pq.2.fst-T pq.2.fst,
    T pq.1.snd+pq.2.snd-T pq.2.snd+
      L • realAbs_lipschitz.compLp (abs_zero) (pq.1.fst-pq.2.fst))

omit [MetricSpace X] [BorelSpace X] in
lemma continuous_slopeMixMap (T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (L : ℝ) :
    Continuous (slopeMixMap T L) := by
  have hf := WithLp.continuous_fst 2 (Lp ℝ 2 m) (Lp ℝ 2 m)
  have hg := WithLp.continuous_snd 2 (Lp ℝ 2 m) (Lp ℝ 2 m)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
    ((((T.continuous.comp (hf.comp continuous_fst)).add (hf.comp continuous_snd)).sub
      (T.continuous.comp (hf.comp continuous_snd))).prodMk
      ((((T.continuous.comp (hg.comp continuous_fst)).add (hg.comp continuous_snd)).sub
        (T.continuous.comp (hg.comp continuous_snd))).add
        (((realAbs_lipschitz.continuous_compLp abs_zero).comp
          ((hf.comp continuous_fst).sub (hf.comp continuous_snd))).const_smul L)))

lemma slopeMixMap_mem_raw {φ : X → ℝ} (hφ : GloballyLipschitz φ)
    (hc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L : ℝ≥0} (hL : LipschitzWith L φ)
    (hB : ∀ᵐ x ∂m, |φ x| ≤ 1)
    {p q : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)}
    (hp : p ∈ l2SlopeGraph m) (hq : q ∈ l2SlopeGraph m) :
    slopeMixMap (boundedMulLp hL.continuous.aestronglyMeasurable hB) L (p,q) ∈ l2SlopeGraph m := by
  obtain ⟨f,hf,hfm,hfp,hD⟩ := hp
  obtain ⟨g,hg,hgm,hgq,hE⟩ := hq
  let T := boundedMulLp hL.continuous.aestronglyMeasurable hB
  let w : X → ℝ := fun x => φ x*f x+(1-φ x)*g x
  have hw : GloballyLipschitz w := by
    have hh := lipschitz_mul_compact hφ ⟨_,hf.choose_spec.sub hg.choose_spec⟩ hc
    have htt := hh.choose_spec.add hg.choose_spec
    have heq : (fun x => φ x*(f x-g x)+g x) = w := by funext x; dsimp only [w]; ring
    exact ⟨_,heq ▸ htt⟩
  have hwm : MemLp w 2 m := by
    have h := ((memLp_mul_bounded hfm hL.continuous.aestronglyMeasurable hB).add hgm).sub
      (memLp_mul_bounded hgm hL.continuous.aestronglyMeasurable hB)
    convert h using 1
    funext x; dsimp only [w]; simp only [Pi.add_apply,Pi.sub_apply]; ring
  refine ⟨w,hw,hwm,?_,?_⟩
  · apply Lp.ext
    filter_upwards [hwm.coeFn_toLp, boundedMulLp_ae hL.continuous.aestronglyMeasurable hB p.fst,
      boundedMulLp_ae hL.continuous.aestronglyMeasurable hB q.fst,
      Lp.coeFn_add (T p.fst) q.fst,Lp.coeFn_sub (T p.fst+q.fst) (T q.fst),
      hfm.coeFn_toLp,hgm.coeFn_toLp] with x hx hpφ hqφ hadd hsub hfx hgx
    change _ = (T p.fst+q.fst-T q.fst) x
    rw [hx,hsub,Pi.sub_apply,hadd,Pi.add_apply]
    change w x = (boundedMulLp hL.continuous.aestronglyMeasurable hB p.fst) x+q.fst x-
      (boundedMulLp hL.continuous.aestronglyMeasurable hB q.fst) x
    rw [hpφ,hqφ,← hfp,← hgq,hfx,hgx]
    dsimp only [w]; ring
  · let A := realAbs_lipschitz.compLp abs_zero (p.fst-q.fst)
    filter_upwards [hD,hE,boundedMulLp_ae hL.continuous.aestronglyMeasurable hB p.snd,
      boundedMulLp_ae hL.continuous.aestronglyMeasurable hB q.snd,
      Lp.coeFn_add (T p.snd) q.snd,Lp.coeFn_sub (T p.snd+q.snd) (T q.snd),
      Lp.coeFn_add (T p.snd+q.snd-T q.snd) ((L:ℝ) • A),Lp.coeFn_smul (L:ℝ) A,
      realAbs_lipschitz.coeFn_compLp abs_zero (p.fst-q.fst),Lp.coeFn_sub p.fst q.fst,
      hfm.coeFn_toLp,hgm.coeFn_toLp] with x hdx hex hpφ hqφ hadd hsub hfin hsm hab hfg hfx hgx
    change (localSlope w x).toReal ≤ (T p.snd+q.snd-T q.snd+(L:ℝ) • A) x
    rw [hfin,Pi.add_apply,hsub,Pi.sub_apply,hadd,Pi.add_apply,hsm,Pi.smul_apply,smul_eq_mul]
    change _ ≤ (boundedMulLp hL.continuous.aestronglyMeasurable hB p.snd) x+q.snd x-
      (boundedMulLp hL.continuous.aestronglyMeasurable hB q.snd) x+(L:ℝ)*A x
    rw [hpφ,hqφ]
    have hax : A x = |f x-g x| := by
      change (realAbs_lipschitz.compLp abs_zero (p.fst-q.fst)) x = _
      rw [hab,Function.comp_apply,hfg,Pi.sub_apply,← hfp,← hgq,hfx,hgx]
    rw [hax]
    have hs : (localSlope φ x).toReal ≤ (L:ℝ) := by
      exact ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_lipschitz hL x)
    have H := localSlope_mix_le hφ hf hg x (hφ0 x) (hφ1 x)
    have H' := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hdx (hφ0 x))
        (mul_le_mul_of_nonneg_left hex (sub_nonneg.mpr (hφ1 x))))
      (mul_le_mul_of_nonneg_left hs (abs_nonneg (f x-g x)))
    exact H.trans (H'.trans_eq (by ring))

lemma relaxedGradient_mix {φ : X → ℝ} (hφ : GloballyLipschitz φ)
    (hc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (hB : ∀ᵐ x ∂m, |φ x| ≤ 1)
    {f D E : Lp ℝ 2 m} (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m)
    (hE : WithLp.toLp 2 (f,E) ∈ l2RelaxedGraph m) :
    WithLp.toLp 2 (f,boundedMulLp hφ.choose_spec.continuous.aestronglyMeasurable hB D+E-
      boundedMulLp hφ.choose_spec.continuous.aestronglyMeasurable hB E) ∈ l2RelaxedGraph m := by
  let T := boundedMulLp hφ.choose_spec.continuous.aestronglyMeasurable hB
  have hclosed : IsClosed ((slopeMixMap T hφ.choose) ⁻¹' l2RelaxedGraph m) :=
    isClosed_l2RelaxedGraph.preimage (continuous_slopeMixMap T hφ.choose)
  have hraw : l2SlopeGraph m ×ˢ l2SlopeGraph m ⊆
      (slopeMixMap T hφ.choose) ⁻¹' l2RelaxedGraph m := by
    rintro ⟨p,q⟩ ⟨hp,hq⟩
    exact subset_closure (slopeMixMap_mem_raw hφ hc hφ0 hφ1 hφ.choose_spec hB hp hq)
  have hmem : (WithLp.toLp 2 (f,D),WithLp.toLp 2 (f,E)) ∈ closure (l2SlopeGraph m ×ˢ l2SlopeGraph m) := by
    rw [closure_prod_eq]
    exact ⟨hD,hE⟩
  have H := closure_minimal hraw hclosed hmem
  change WithLp.toLp 2 (T f+f-T f,T D+E-T E+(hφ.choose:ℝ) •
    realAbs_lipschitz.compLp abs_zero (f-f)) ∈ l2RelaxedGraph m at H
  simpa only [sub_self,LipschitzWith.compLp_zero,smul_zero,add_zero,add_sub_cancel_left] using H
end WeakHessian

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

end
end InlinedFile0

end OAI
