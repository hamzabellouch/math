import OAI.Geometry.IsometricImmersion.Caps.EllipticAbsorption

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

variable {U : Set Coord} {f : Coord → ℝ}

theorem coordPartial_continuousOn_one (hf : ContDiffOn ℝ 1 f U)
    (hU : IsOpen U) (i : Fin 2) : ContinuousOn (coordPartial i f) U := by
  have hd : ContDiffOn ℝ 0 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  exact (hd.clm_apply contDiffOn_const).continuousOn

variable {tl tr sb st : ℝ}

theorem rectangleIntegral_partial_t_zero_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ s ∈ Icc sb st, f (boxPoint tl s) = 0 ∧ f (boxPoint tr s) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 0 f) = 0 := by
  have hinner (s : ℝ) (hs' : s ∈ Icc sb st) :
      (∫ t in tl..tr, coordPartial 0 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun t => coordPartial 0 f (boxPoint t s)) (uIcc tl tr) := by
      rw [uIcc_of_le ht]
      exact (coordPartial_continuousOn_one hf hU 0).comp
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

theorem rectangleIntegral_partial_s_zero_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ t ∈ Icc tl tr, f (boxPoint t sb) = 0 ∧ f (boxPoint t st) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 1 f) = 0 := by
  rw [rectangleIntegral_swap ht hs ((coordPartial_continuousOn_one hf hU 1).mono hbox)]
  have hinner (t : ℝ) (ht' : t ∈ Icc tl tr) :
      (∫ s in sb..st, coordPartial 1 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun s => coordPartial 1 f (boxPoint t s)) (uIcc sb st) := by
      rw [uIcc_of_le hs]
      exact (coordPartial_continuousOn_one hf hU 1).comp
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

variable {A B C v u : Coord → ℝ}

theorem elliptic_fields_C1
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ 1 v U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ 1 (ellipticFluxT v u) U ∧
    ContDiffOn ℝ 1 (ellipticFluxS A v u) U ∧
    ContinuousOn (ellipticEnergy A v u) U ∧
    ContinuousOn (ellipticError A B C v u) U := by
  have hA1 : ContDiffOn ℝ 1 A U := hA.of_le (by simp)
  have hu1 : ContDiffOn ℝ 1 u U := hu.of_le (by simp)
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  have ht1 : ContDiffOn ℝ 1 (coordPartial 0 u) U := ht.of_le (by simp)
  have hs1 : ContDiffOn ℝ 1 (coordPartial 1 u) U := hs.of_le (by simp)
  have hEt : ContinuousOn (ellipticErrorT B v) U :=
    (coordPartial_continuousOn_one hv hU 0).sub (hv.continuousOn.mul hB.continuousOn)
  have hEs : ContinuousOn (ellipticErrorS A C v) U :=
    (coordPartial_continuousOn_one (hA1.mul hv) hU 1).sub
      (hv.continuousOn.mul hC.continuousOn)
  exact ⟨((hv.mul hu1).mul ht1).neg, (((hA1.mul hv).mul hu1).mul hs1).neg,
    hv.continuousOn.mul ((ht.continuousOn.pow 2).add
      (hA.continuousOn.mul (hs.continuousOn.pow 2))),
    hu.continuousOn.mul ((hEt.mul ht.continuousOn).add (hEs.mul hs.continuousOn))⟩

theorem integrated_elliptic_identity_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ 1 v U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) (hboundary : zeroRectangleBoundary tl tr sb st v) :
    rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p * (-v p * u p)) =
      rectangleIntegral tl tr sb st (ellipticEnergy A v u) +
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
  obtain ⟨hFt, hFs, hE, hErr⟩ := elliptic_fields_C1 hU hA hB hC hv hu
  have htzero : rectangleIntegral tl tr sb st (coordPartial 0 (ellipticFluxT v u)) = 0 := by
    apply rectangleIntegral_partial_t_zero_C1 ht hs hU hFt hbox
    intro s hs'
    constructor <;> simp [ellipticFluxT, (hboundary.1 s hs').1, (hboundary.1 s hs').2]
  have hszero : rectangleIntegral tl tr sb st (coordPartial 1 (ellipticFluxS A v u)) = 0 := by
    apply rectangleIntegral_partial_s_zero_C1 ht hs hU hFs hbox
    intro t ht'
    constructor <;> simp [ellipticFluxS, (hboundary.2 t ht').1, (hboundary.2 t ht').2]
  have hdt := (coordPartial_continuousOn_one hFt hU 0).mono hbox
  have hds := (coordPartial_continuousOn_one hFs hU 1).mono hbox
  calc
    rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p * (-v p * u p)) =
        rectangleIntegral tl tr sb st (fun p => coordPartial 0 (ellipticFluxT v u) p +
          coordPartial 1 (ellipticFluxS A v u) p + ellipticEnergy A v u p +
          ellipticError A B C v u p) := by
      apply rectangleIntegral_congr ht hs
      intro p hp
      exact elliptic_divergence_identity (B := B) (C := C)
        ((hA.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by simp))
        ((hv.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by simp)) hu hU (hbox hp)
    _ = rectangleIntegral tl tr sb st (coordPartial 0 (ellipticFluxT v u)) +
        rectangleIntegral tl tr sb st (coordPartial 1 (ellipticFluxS A v u)) +
        rectangleIntegral tl tr sb st (ellipticEnergy A v u) +
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
      have hsum : ContinuousOn (fun p => coordPartial 0 (ellipticFluxT v u) p +
          coordPartial 1 (ellipticFluxS A v u) p) (closedRectangle tl tr sb st) :=
        hdt.add hds
      have hsumE : ContinuousOn (fun p => coordPartial 0 (ellipticFluxT v u) p +
          coordPartial 1 (ellipticFluxS A v u) p + ellipticEnergy A v u p)
          (closedRectangle tl tr sb st) := hsum.add (hE.mono hbox)
      rw [rectangleIntegral_add ht hs hsumE (hErr.mono hbox),
        rectangleIntegral_add ht hs hsum (hE.mono hbox),
        rectangleIntegral_add ht hs hdt hds]
    _ = rectangleIntegral tl tr sb st (ellipticEnergy A v u) +
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
      rw [htzero, hszero]
      ring

theorem integrated_elliptic_equation_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ 1 v U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) (hboundary : zeroRectangleBoundary tl tr sb st v)
    (hEq : ∀ p ∈ U, multiplierOperator A B C u p = f p) :
    rectangleIntegral tl tr sb st (ellipticEnergy A v u) =
      -rectangleIntegral tl tr sb st (fun p => v p * u p * f p) -
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
  have hid := integrated_elliptic_identity_C1 ht hs hU hA hB hC hv hu hbox hboundary
  have hsource : rectangleIntegral tl tr sb st
      (fun p => multiplierOperator A B C u p * (-v p * u p)) =
      -rectangleIntegral tl tr sb st (fun p => v p * u p * f p) := by
    calc
      rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p * (-v p * u p)) =
          rectangleIntegral tl tr sb st (fun p => -(v p * u p * f p)) := by
        apply rectangleIntegral_congr ht hs
        intro p hp
        dsimp only
        rw [hEq p (hbox hp)]
        ring
      _ = -rectangleIntegral tl tr sb st (fun p => v p * u p * f p) :=
        rectangleIntegral_neg tl tr sb st _
  linarith

theorem integrated_elliptic_energy_bound_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ 1 v U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) (hboundary : zeroRectangleBoundary tl tr sb st v)
    (hEq : ∀ p ∈ U, multiplierOperator A B C u p = f p)
    (V H : ℝ) (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hvn : ∀ p ∈ U, 0 ≤ v p)
    (hvV : ∀ p ∈ closedRectangle tl tr sb st, v p ≤ V)
    (hpos : ∀ p ∈ closedRectangle tl tr sb st, 0 < v p → 0 < A p)
    (hratio : ∀ p ∈ closedRectangle tl tr sb st, 0 < v p →
      (ellipticErrorT B v p) ^ 2 / v p + (ellipticErrorS A C v p) ^ 2 / (A p * v p) ≤ H) :
    rectangleIntegral tl tr sb st (ellipticEnergy A v u) ≤
      V * rectangleIntegral tl tr sb st (fun p => (f p) ^ 2) +
        (V + H) * rectangleIntegral tl tr sb st (fun p => (u p) ^ 2) := by
  have hf : ContDiffOn ℝ ∞ f U :=
    (ellipticOperator_contDiffOn hU hA hB hC hu).congr (fun p hp => (hEq p hp).symm)
  obtain ⟨_, _, hE, hErr⟩ := elliptic_fields_C1 hU hA hB hC hv hu
  have hSource : ContinuousOn (fun p => v p * u p * f p) U :=
    (hv.continuousOn.mul hu.continuousOn).mul hf.continuousOn
  have hpoint (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :
      -(v p * u p * f p) - ellipticError A B C v u p ≤
        (1 / 2 : ℝ) * ellipticEnergy A v u p +
          ((V + H) / 2) * (u p) ^ 2 + (V / 2) * (f p) ^ 2 := by
    have hpU := hbox hp
    have hErrBound := ellipticError_abs_bound (u := u) hU hpU
      ((hA.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))
      ((hv.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))
      hvn H hH (hpos p hp) (hratio p hp)
    have hyoung : -(u p * f p) ≤ ((u p) ^ 2 + (f p) ^ 2) / 2 := by
      nlinarith [sq_nonneg (u p + f p)]
    have hm := mul_le_mul_of_nonneg_left hyoung (hvn p hpU)
    have hcost := mul_le_mul (hvV p hp)
      (le_refl (((u p) ^ 2 + (f p) ^ 2) / 2))
      (div_nonneg (add_nonneg (sq_nonneg (u p)) (sq_nonneg (f p)))
        (by norm_num : (0 : ℝ) ≤ 2)) hV
    have hsource : -(v p * u p * f p) ≤ V * ((u p) ^ 2 + (f p) ^ 2) / 2 := by
      nlinarith [hm, hcost]
    nlinarith [hsource, neg_le_abs (ellipticError A B C v u p)]
  have hEhalf : ContinuousOn (fun p => (1 / 2 : ℝ) * ellipticEnergy A v u p)
      (closedRectangle tl tr sb st) := (continuousOn_const.mul hE).mono hbox
  have hUhalf : ContinuousOn (fun p => ((V + H) / 2) * (u p) ^ 2)
      (closedRectangle tl tr sb st) := (continuousOn_const.mul (hu.continuousOn.pow 2)).mono hbox
  have hFhalf : ContinuousOn (fun p => (V / 2) * (f p) ^ 2)
      (closedRectangle tl tr sb st) := (continuousOn_const.mul (hf.continuousOn.pow 2)).mono hbox
  have hNegSource : ContinuousOn (fun p => -(v p * u p * f p)) U := hSource.neg
  have hi := rectangleIntegral_mono ht hs
    ((hNegSource.sub hErr).mono hbox) ((hEhalf.add hUhalf).add hFhalf) hpoint
  simp only [Pi.add_def, Pi.sub_def] at hi
  have hsum : ContinuousOn (fun p => (1 / 2 : ℝ) * ellipticEnergy A v u p +
      ((V + H) / 2) * (u p) ^ 2) (closedRectangle tl tr sb st) := hEhalf.add hUhalf
  have heq := integrated_elliptic_equation_C1 ht hs hU hA hB hC hv hu hbox hboundary hEq
  have hleft : rectangleIntegral tl tr sb st
      (fun p => -(v p * u p * f p) - ellipticError A B C v u p) =
      rectangleIntegral tl tr sb st (ellipticEnergy A v u) := by
    rw [rectangleIntegral_sub ht hs (hNegSource.mono hbox) (hErr.mono hbox), rectangleIntegral_neg]
    exact heq.symm
  rw [hleft,
    rectangleIntegral_add ht hs hsum hFhalf,
    rectangleIntegral_add ht hs hEhalf hUhalf,
    rectangleIntegral_const_mul tl tr sb st (1 / 2 : ℝ) (ellipticEnergy A v u),
    rectangleIntegral_const_mul tl tr sb st ((V + H) / 2) (fun p => (u p) ^ 2),
    rectangleIntegral_const_mul tl tr sb st (V / 2) (fun p => (f p) ^ 2)] at hi
  nlinarith

end SmoothLocal.Weighted

end

end OAI
