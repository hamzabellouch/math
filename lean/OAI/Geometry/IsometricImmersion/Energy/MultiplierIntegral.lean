import OAI.Geometry.IsometricImmersion.Energy.MultiplierDivergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def boxPoint (t s : ℝ) : Coord :=
  t • Pi.single 0 1 + s • Pi.single 1 1

def closedRectangle (tl tr sb st : ℝ) : Set Coord :=
  {p | p 0 ∈ Icc tl tr ∧ p 1 ∈ Icc sb st}

def rectangleIntegral (tl tr sb st : ℝ) (f : Coord → ℝ) : ℝ :=
  ∫ s in sb..st, ∫ t in tl..tr, f (boxPoint t s)

def zeroRectangleBoundary (tl tr sb st : ℝ) (f : Coord → ℝ) : Prop :=
  (∀ s ∈ Icc sb st, f (boxPoint tl s) = 0 ∧ f (boxPoint tr s) = 0) ∧
    (∀ t ∈ Icc tl tr, f (boxPoint t sb) = 0 ∧ f (boxPoint t st) = 0)

theorem boxPoint_mem {tl tr sb st t s : ℝ}
    (ht : t ∈ Icc tl tr) (hs : s ∈ Icc sb st) :
    boxPoint t s ∈ closedRectangle tl tr sb st := by
  simpa [boxPoint, closedRectangle] using And.intro ht hs

theorem boxPoint_hasDerivAt_t (t s : ℝ) :
    HasDerivAt (fun x => boxPoint x s) (Pi.single 0 (1 : ℝ) : Coord) t := by
  simpa [boxPoint] using
    ((hasDerivAt_id t).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add_const
      (s • (Pi.single 1 (1 : ℝ) : Coord))

theorem boxPoint_hasDerivAt_s (t s : ℝ) :
    HasDerivAt (boxPoint t) (Pi.single 1 (1 : ℝ) : Coord) s := by
  change HasDerivAt (fun x : ℝ => t • (Pi.single 0 (1 : ℝ) : Coord) +
    x • (Pi.single 1 (1 : ℝ) : Coord)) (Pi.single 1 (1 : ℝ) : Coord) s
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id s).smul_const (Pi.single 1 (1 : ℝ) : Coord)).const_add
      (t • (Pi.single 0 (1 : ℝ) : Coord))

variable {tl tr sb st : ℝ} {f g : Coord → ℝ}

theorem rectangle_area_integrable
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    IntegrableOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Ioc tl tr ×ˢ Ioc sb st) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Icc tl tr ×ˢ Icc sb st) :=
    hf.comp (by unfold boxPoint; fun_prop) (fun p hp => boxPoint_mem hp.1 hp.2)
  exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem rectangleIntegral_swap (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f =
      ∫ t in tl..tr, ∫ s in sb..st, f (boxPoint t s) := by
  have hi : IntegrableOn (Function.uncurry (fun t s => f (boxPoint t s)))
      (uIoc tl tr ×ˢ uIoc sb st) := by
    simpa only [uIoc_of_le ht, uIoc_of_le hs, Function.uncurry_def] using rectangle_area_integrable hf
  exact (intervalIntegral_intervalIntegral_swap hi).symm

theorem rectangleIntegral_eq_area (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f =
      ∫ p in Ioc tl tr ×ˢ Ioc sb st, f (boxPoint p.1 p.2) := by
  rw [rectangleIntegral_swap ht hs hf]
  simp_rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hs]
  have hi : IntegrableOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Ioc tl tr ×ˢ Ioc sb st) (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod] using rectangle_area_integrable hf
  simpa only [← Measure.volume_eq_prod] using
    (setIntegral_prod (fun p : ℝ × ℝ => f (boxPoint p.1 p.2)) hi).symm

theorem rectangleIntegral_congr (ht : tl ≤ tr) (hs : sb ≤ st)
    (heq : EqOn f g (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f = rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  apply intervalIntegral.integral_congr
  intro s hs'
  apply intervalIntegral.integral_congr
  intro t ht'
  exact heq (boxPoint_mem
    (by simpa only [uIcc_of_le ht] using ht')
    (by simpa only [uIcc_of_le hs] using hs'))

theorem rectangleIntegral_add (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st))
    (hg : ContinuousOn g (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st (fun p => f p + g p) =
      rectangleIntegral tl tr sb st f + rectangleIntegral tl tr sb st g := by
  have hfg : ContinuousOn (fun p => f p + g p) (closedRectangle tl tr sb st) := hf.add hg
  rw [rectangleIntegral_eq_area ht hs hfg,
    rectangleIntegral_eq_area ht hs hf, rectangleIntegral_eq_area ht hs hg]
  exact integral_add (rectangle_area_integrable hf) (rectangle_area_integrable hg)

variable {U : Set Coord}

theorem rectangleIntegral_partial_t_zero
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ s ∈ Icc sb st, f (boxPoint tl s) = 0 ∧ f (boxPoint tr s) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 0 f) = 0 := by
  have hinner (s : ℝ) (hs' : s ∈ Icc sb st) :
      (∫ t in tl..tr, coordPartial 0 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun t => coordPartial 0 f (boxPoint t s)) (uIcc tl tr) := by
      rw [uIcc_of_le ht]
      exact (partial_contDiffOn hf hU 0).continuousOn.comp
        (by unfold boxPoint; fun_prop) (fun t ht' => hbox (boxPoint_mem ht' hs'))
    have hderiv (t : ℝ) (ht' : t ∈ uIcc tl tr) :
        HasDerivAt (fun x => f (boxPoint x s)) (coordPartial 0 f (boxPoint t s)) t := by
      have hp : boxPoint t s ∈ U := hbox (boxPoint_mem
        (by simpa only [uIcc_of_le ht] using ht') hs')
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      exact hd.hasFDerivAt.comp_hasDerivAt t (boxPoint_hasDerivAt_t t s)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [(hedge s hs').1, (hedge s hs').2, sub_self] at he
    exact he
  unfold rectangleIntegral
  calc
    (∫ s in sb..st, ∫ t in tl..tr, coordPartial 0 f (boxPoint t s)) =
        ∫ _ in sb..st, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs'
      exact hinner s (by simpa only [uIcc_of_le hs] using hs')
    _ = 0 := intervalIntegral.integral_zero

theorem rectangleIntegral_partial_s_zero
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ t ∈ Icc tl tr, f (boxPoint t sb) = 0 ∧ f (boxPoint t st) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 1 f) = 0 := by
  rw [rectangleIntegral_swap ht hs ((partial_contDiffOn hf hU 1).continuousOn.mono hbox)]
  have hinner (t : ℝ) (ht' : t ∈ Icc tl tr) :
      (∫ s in sb..st, coordPartial 1 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun s => coordPartial 1 f (boxPoint t s)) (uIcc sb st) := by
      rw [uIcc_of_le hs]
      exact (partial_contDiffOn hf hU 1).continuousOn.comp
        (by unfold boxPoint; fun_prop) (fun s hs' => hbox (boxPoint_mem ht' hs'))
    have hderiv (s : ℝ) (hs' : s ∈ uIcc sb st) :
        HasDerivAt (fun y => f (boxPoint t y)) (coordPartial 1 f (boxPoint t s)) s := by
      have hp : boxPoint t s ∈ U := hbox (boxPoint_mem ht'
        (by simpa only [uIcc_of_le hs] using hs'))
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      exact hd.hasFDerivAt.comp_hasDerivAt s (boxPoint_hasDerivAt_s t s)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [(hedge t ht').1, (hedge t ht').2, sub_self] at he
    exact he
  calc
    (∫ t in tl..tr, ∫ s in sb..st, coordPartial 1 f (boxPoint t s)) =
        ∫ _ in tl..tr, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht'
      exact hinner t (by simpa only [uIcc_of_le ht] using ht')
    _ = 0 := intervalIntegral.integral_zero

def multiplierQuadratic (A B C m n u : Coord → ℝ) (p : Coord) : ℝ :=
  multiplierT B m n p * (coordPartial 0 u p) ^ 2 +
    multiplierS A C m n p * (coordPartial 1 u p) ^ 2 +
    multiplierJ A B C m n p * coordPartial 0 u p * coordPartial 1 u p

theorem multiplierTestProduct_contDiffOn
    {A B C m n u : Coord → ℝ} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hm : ContDiffOn ℝ ∞ m U)
    (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (fun p => multiplierOperator A B C u p * multiplierTest m n u p) U := by
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  have htt := partial_contDiffOn ht hU 0
  have hss := partial_contDiffOn hs hU 1
  have hL : ContDiffOn ℝ ∞ (multiplierOperator A B C u) U :=
    ((htt.add (hA.mul hss)).add (hB.mul ht)).add (hC.mul hs)
  have htest : ContDiffOn ℝ ∞ (multiplierTest m n u) U :=
    (hm.mul hs).add (hn.mul ht)
  exact hL.mul htest

theorem multiplierFluxes_contDiffOn
    {A m n u : Coord → ℝ} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hm : ContDiffOn ℝ ∞ m U)
    (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (multiplierFluxT A m n u) U ∧
      ContDiffOn ℝ ∞ (multiplierFluxS A m n u) U := by
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  constructor
  · exact (((hm.mul ht).mul hs).add
      (contDiffOn_const.mul (hn.mul (ht.pow 2)))).sub
      (contDiffOn_const.mul ((hA.mul hn).mul (hs.pow 2)))
  · exact ((contDiffOn_const.mul ((hA.mul hm).mul (hs.pow 2))).add
      (((hA.mul hn).mul ht).mul hs)).sub
      (contDiffOn_const.mul (hm.mul (ht.pow 2)))

theorem multiplierQuadratic_contDiffOn
    {A B C m n u : Coord → ℝ} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hm : ContDiffOn ℝ ∞ m U)
    (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (multiplierQuadratic A B C m n u) U := by
  have hhalf {v : Coord → ℝ} (hv : ContDiffOn ℝ ∞ v U) :
      ContDiffOn ℝ ∞ (fun p => v p / 2) U :=
    hv.div contDiffOn_const (fun _ _ => two_ne_zero)
  have hmt := partial_contDiffOn hm hU 0
  have hms := partial_contDiffOn hm hU 1
  have hnt := partial_contDiffOn hn hU 0
  have hAms := partial_contDiffOn (hA.mul hm) hU 1
  have hAnt := partial_contDiffOn (hA.mul hn) hU 0
  have hAns := partial_contDiffOn (hA.mul hn) hU 1
  have hT : ContDiffOn ℝ ∞ (multiplierT B m n) U :=
    (hhalf (hms.sub hnt)).add (hB.mul hn)
  have hS : ContDiffOn ℝ ∞ (multiplierS A C m n) U :=
    ((hhalf hAms.neg).add (hhalf hAnt)).add (hC.mul hm)
  have hJ : ContDiffOn ℝ ∞ (multiplierJ A B C m n) U :=
    ((hmt.neg.add (hB.mul hm)).sub hAns).add (hC.mul hn)
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  exact ((hT.mul (ht.pow 2)).add (hS.mul (hs.pow 2))).add ((hJ.mul ht).mul hs)

theorem multiplier_integrands_integrable
    {A B C m n u : Coord → ℝ} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hm : ContDiffOn ℝ ∞ m U)
    (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) :
    IntegrableOn (fun p : ℝ × ℝ =>
      multiplierOperator A B C u (boxPoint p.1 p.2) * multiplierTest m n u (boxPoint p.1 p.2))
      (Ioc tl tr ×ˢ Ioc sb st) ∧
    IntegrableOn (fun p : ℝ × ℝ => multiplierQuadratic A B C m n u (boxPoint p.1 p.2))
      (Ioc tl tr ×ˢ Ioc sb st) :=
  ⟨rectangle_area_integrable
      ((multiplierTestProduct_contDiffOn hU hA hB hC hm hn hu).continuousOn.mono hbox),
    rectangle_area_integrable
      ((multiplierQuadratic_contDiffOn hU hA hB hC hm hn hu).continuousOn.mono hbox)⟩

theorem integrated_multiplier_identity
    {A B C m n u : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hm : ContDiffOn ℝ ∞ m U)
    (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    (hmb : zeroRectangleBoundary tl tr sb st m)
    (hnb : zeroRectangleBoundary tl tr sb st n) :
    rectangleIntegral tl tr sb st (fun p =>
      multiplierOperator A B C u p * multiplierTest m n u p) =
        rectangleIntegral tl tr sb st (multiplierQuadratic A B C m n u) := by
  have hflux := multiplierFluxes_contDiffOn hU hA hm hn hu
  have hQ := multiplierQuadratic_contDiffOn hU hA hB hC hm hn hu
  have hFt0 : rectangleIntegral tl tr sb st (coordPartial 0 (multiplierFluxT A m n u)) = 0 := by
    apply rectangleIntegral_partial_t_zero ht hs hU hflux.1 hbox
    intro s hs'
    constructor <;> simp [multiplierFluxT, (hmb.1 s hs').1, (hmb.1 s hs').2,
      (hnb.1 s hs').1, (hnb.1 s hs').2]
  have hFs0 : rectangleIntegral tl tr sb st (coordPartial 1 (multiplierFluxS A m n u)) = 0 := by
    apply rectangleIntegral_partial_s_zero ht hs hU hflux.2 hbox
    intro t ht'
    constructor <;> simp [multiplierFluxS, (hmb.2 t ht').1, (hmb.2 t ht').2,
      (hnb.2 t ht').1, (hnb.2 t ht').2]
  have hFt := (partial_contDiffOn hflux.1 hU 0).continuousOn.mono hbox
  have hFs := (partial_contDiffOn hflux.2 hU 1).continuousOn.mono hbox
  calc
    rectangleIntegral tl tr sb st (fun p =>
        multiplierOperator A B C u p * multiplierTest m n u p) =
      rectangleIntegral tl tr sb st (fun p =>
        coordPartial 0 (multiplierFluxT A m n u) p +
          coordPartial 1 (multiplierFluxS A m n u) p + multiplierQuadratic A B C m n u p) := by
      apply rectangleIntegral_congr ht hs
      intro p hp
      have hpU := hbox hp
      have hd := multiplier_divergence_identity (B := B) (C := C)
        ((hA.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))
        ((hm.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))
        ((hn.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)) hu hU hpU
      dsimp only
      rw [hd]
      unfold multiplierQuadratic
      ring
    _ = rectangleIntegral tl tr sb st (coordPartial 0 (multiplierFluxT A m n u)) +
        rectangleIntegral tl tr sb st (coordPartial 1 (multiplierFluxS A m n u)) +
        rectangleIntegral tl tr sb st (multiplierQuadratic A B C m n u) := by
      have hsum : ContinuousOn (fun p => coordPartial 0 (multiplierFluxT A m n u) p +
          coordPartial 1 (multiplierFluxS A m n u) p) (closedRectangle tl tr sb st) :=
        hFt.add hFs
      rw [rectangleIntegral_add ht hs hsum (hQ.continuousOn.mono hbox),
        rectangleIntegral_add ht hs hFt hFs]
    _ = rectangleIntegral tl tr sb st (multiplierQuadratic A B C m n u) := by
      rw [hFt0, hFs0]
      ring

def cutoffM (chi : Coord → ℝ) (edge lambda : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  chi p * directedM edge lambda I p

def cutoffN (chi : Coord → ℝ) (edge lambda epsilon : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  chi p * directedN edge lambda epsilon I p

theorem cutoff_test_factor
    (chi I u : Coord → ℝ) (edge lambda epsilon : ℝ) (p : Coord) :
    multiplierTest (cutoffM chi edge lambda I) (cutoffN chi edge lambda epsilon I) u p =
      chi p * directedWeight edge lambda I p *
        (-coordPartial 1 u p + epsilon * p 0 * coordPartial 0 u p) := by
  unfold multiplierTest cutoffM cutoffN directedM directedN
  ring

theorem integrated_cutoff_directed_identity
    {A B C chi I u : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hchi : ContDiffOn ℝ ∞ chi U)
    (hI : ContDiffOn ℝ ∞ I U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    (hchiSides : ∀ s ∈ Icc sb st, chi (boxPoint tl s) = 0 ∧ chi (boxPoint tr s) = 0)
    (hchiBottom : ∀ t ∈ Icc tl tr, chi (boxPoint t sb) = 0)
    (lambda epsilon : ℝ) :
    rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p *
      multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p) =
        rectangleIntegral tl tr sb st
          (multiplierQuadratic A B C (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u) := by
  have hW := directedWeight_contDiffOn st lambda hI
  have hm : ContDiffOn ℝ ∞ (cutoffM chi st lambda I) U := hchi.mul hW.neg
  have htcoord : ContDiffOn ℝ ∞ (fun p : Coord => p 0) U := contDiffOn_apply ℝ ℝ 0 U
  have hn : ContDiffOn ℝ ∞ (cutoffN chi st lambda epsilon I) U :=
    hchi.mul ((contDiffOn_const.mul htcoord).mul hW)
  have hedge : zeroRectangleBoundary tl tr sb st (cutoffM chi st lambda I) ∧
      zeroRectangleBoundary tl tr sb st (cutoffN chi st lambda epsilon I) := by
    constructor
    · constructor
      · intro s hs'
        simp [cutoffM, (hchiSides s hs').1, (hchiSides s hs').2]
      · intro t ht'
        have hz := directed_mn_edge_zero st lambda epsilon I (boxPoint t st)
          (by simp [boxPoint])
        simp [cutoffM, hchiBottom t ht', hz.1]
    · constructor
      · intro s hs'
        simp [cutoffN, (hchiSides s hs').1, (hchiSides s hs').2]
      · intro t ht'
        have hz := directed_mn_edge_zero st lambda epsilon I (boxPoint t st)
          (by simp [boxPoint])
        simp [cutoffN, hchiBottom t ht', hz.2]
  exact integrated_multiplier_identity ht hs hU hA hB hC hm hn hu hbox hedge.1 hedge.2

end SmoothLocal.Weighted

end

end OAI
