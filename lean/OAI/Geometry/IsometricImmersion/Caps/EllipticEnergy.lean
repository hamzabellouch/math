import OAI.Geometry.IsometricImmersion.Energy.MultiplierIntegral

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def ellipticErrorT (B v : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 v p - v p * B p

def ellipticErrorS (A C v : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 1 (fun q => A q * v q) p - v p * C p

def ellipticEnergy (A v u : Coord → ℝ) (p : Coord) : ℝ :=
  v p * ((coordPartial 0 u p) ^ 2 + A p * (coordPartial 1 u p) ^ 2)

def ellipticError (A B C v u : Coord → ℝ) (p : Coord) : ℝ :=
  u p * (ellipticErrorT B v p * coordPartial 0 u p +
    ellipticErrorS A C v p * coordPartial 1 u p)

def ellipticFluxT (v u : Coord → ℝ) (p : Coord) : ℝ :=
  -(v p * u p * coordPartial 0 u p)

def ellipticFluxS (A v u : Coord → ℝ) (p : Coord) : ℝ :=
  -(A p * v p * u p * coordPartial 1 u p)

variable {A B C v u f : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem ellipticFluxT_partial_t
    (hv : DifferentiableAt ℝ v p) (hu : DifferentiableAt ℝ u p)
    (hut : DifferentiableAt ℝ (coordPartial 0 u) p) :
    coordPartial 0 (ellipticFluxT v u) p =
      -(coordPartial 0 v p * u p * coordPartial 0 u p +
        v p * (coordPartial 0 u p) ^ 2 +
        v p * u p * coordPartial 0 (coordPartial 0 u) p) := by
  have hd := ((hv.hasFDerivAt.fun_mul hu.hasFDerivAt).fun_mul hut.hasFDerivAt).neg
  change HasFDerivAt (fun x => -(v x * u x * coordPartial 0 u x)) _ p at hd
  simp only [coordPartial] at hd
  change coordPartial 0 (fun q => -(v q * u q * coordPartial 0 u q)) p = _
  simp only [coordPartial]
  rw [hd.fderiv]
  simp only [neg_apply, add_apply, smul_apply, smul_eq_mul]
  ring

theorem ellipticFluxS_partial_s
    (hA : DifferentiableAt ℝ A p) (hv : DifferentiableAt ℝ v p)
    (hu : DifferentiableAt ℝ u p) (hus : DifferentiableAt ℝ (coordPartial 1 u) p) :
    coordPartial 1 (ellipticFluxS A v u) p =
      -(coordPartial 1 (fun q => A q * v q) p * u p * coordPartial 1 u p +
        A p * v p * (coordPartial 1 u p) ^ 2 +
        A p * v p * u p * coordPartial 1 (coordPartial 1 u) p) := by
  have hAv : DifferentiableAt ℝ (fun q => A q * v q) p := hA.mul hv
  have hd := ((hAv.hasFDerivAt.fun_mul hu.hasFDerivAt).fun_mul hus.hasFDerivAt).neg
  change HasFDerivAt (fun x => -(A x * v x * u x * coordPartial 1 u x)) _ p at hd
  simp only [coordPartial] at hd
  change coordPartial 1 (fun q => -(A q * v q * u q * coordPartial 1 u q)) p = _
  simp only [coordPartial]
  rw [hd.fderiv]
  simp only [neg_apply, add_apply, smul_apply, smul_eq_mul]
  ring

theorem elliptic_divergence_identity
    (hA : DifferentiableAt ℝ A p) (hv : DifferentiableAt ℝ v p)
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U) (hp : p ∈ U) :
    multiplierOperator A B C u p * (-v p * u p) =
      coordPartial 0 (ellipticFluxT v u) p + coordPartial 1 (ellipticFluxS A v u) p +
        ellipticEnergy A v u p + ellipticError A B C v u p := by
  have hud : DifferentiableAt ℝ u p :=
    (hu.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdu (i : Fin 2) : DifferentiableAt ℝ (coordPartial i u) p :=
    ((partial_contDiffOn hu hU i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  rw [ellipticFluxT_partial_t hv hud (hdu 0), ellipticFluxS_partial_s hA hv hud (hdu 1)]
  unfold multiplierOperator ellipticEnergy ellipticError ellipticErrorT ellipticErrorS
  ring

theorem elliptic_fields_contDiffOn
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ ∞ v U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (ellipticFluxT v u) U ∧
    ContDiffOn ℝ ∞ (ellipticFluxS A v u) U ∧
    ContDiffOn ℝ ∞ (ellipticEnergy A v u) U ∧
    ContDiffOn ℝ ∞ (ellipticError A B C v u) U := by
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  have hEt := (partial_contDiffOn hv hU 0).sub (hv.mul hB)
  have hEs := (partial_contDiffOn (hA.mul hv) hU 1).sub (hv.mul hC)
  exact ⟨((hv.mul hu).mul ht).neg, (((hA.mul hv).mul hu).mul hs).neg,
    hv.mul ((ht.pow 2).add (hA.mul (hs.pow 2))),
    hu.mul ((hEt.mul ht).add (hEs.mul hs))⟩

theorem ellipticOperator_contDiffOn
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (multiplierOperator A B C u) U := by
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  exact (((partial_contDiffOn ht hU 0).add (hA.mul (partial_contDiffOn hs hU 1))).add
    (hB.mul ht)).add (hC.mul hs)

theorem rectangleIntegral_neg (tl tr sb st : ℝ) (g : Coord → ℝ) :
    rectangleIntegral tl tr sb st (fun p => -g p) = -rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  simp only [intervalIntegral.integral_neg]

theorem rectangleIntegral_const_mul (tl tr sb st c : ℝ) (g : Coord → ℝ) :
    rectangleIntegral tl tr sb st (fun p => c * g p) = c * rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  simp only [intervalIntegral.integral_const_mul]

variable {tl tr sb st : ℝ}

theorem integrated_elliptic_identity
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ ∞ v U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) (hboundary : zeroRectangleBoundary tl tr sb st v) :
    rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p * (-v p * u p)) =
      rectangleIntegral tl tr sb st (ellipticEnergy A v u) +
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
  obtain ⟨hFt, hFs, hE, hErr⟩ := elliptic_fields_contDiffOn hU hA hB hC hv hu
  have htzero : rectangleIntegral tl tr sb st (coordPartial 0 (ellipticFluxT v u)) = 0 := by
    apply rectangleIntegral_partial_t_zero ht hs hU hFt hbox
    intro s hs'
    constructor <;> simp [ellipticFluxT, (hboundary.1 s hs').1, (hboundary.1 s hs').2]
  have hszero : rectangleIntegral tl tr sb st (coordPartial 1 (ellipticFluxS A v u)) = 0 := by
    apply rectangleIntegral_partial_s_zero ht hs hU hFs hbox
    intro t ht'
    constructor <;> simp [ellipticFluxS, (hboundary.2 t ht').1, (hboundary.2 t ht').2]
  have hdt := (partial_contDiffOn hFt hU 0).continuousOn.mono hbox
  have hds := (partial_contDiffOn hFs hU 1).continuousOn.mono hbox
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
          (closedRectangle tl tr sb st) := hsum.add (hE.continuousOn.mono hbox)
      rw [rectangleIntegral_add ht hs hsumE
          (hErr.continuousOn.mono hbox),
        rectangleIntegral_add ht hs hsum (hE.continuousOn.mono hbox),
        rectangleIntegral_add ht hs hdt hds]
    _ = rectangleIntegral tl tr sb st (ellipticEnergy A v u) +
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
      rw [htzero, hszero]
      ring

theorem integrated_elliptic_equation
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ ∞ v U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) (hboundary : zeroRectangleBoundary tl tr sb st v)
    (hEq : ∀ p ∈ U, multiplierOperator A B C u p = f p) :
    rectangleIntegral tl tr sb st (ellipticEnergy A v u) =
      -rectangleIntegral tl tr sb st (fun p => v p * u p * f p) -
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
  have hid := integrated_elliptic_identity ht hs hU hA hB hC hv hu hbox hboundary
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

end SmoothLocal.Weighted

end

end OAI
