import OAI.Geometry.RCD.Coordinates.RegularBochnerFrameDefect
import OAI.Geometry.RCD.Sobolev.ScalarBochnerConstruction

namespace OAI

/-! # Quantitative frame energy on the actual regular core of an RCD space

The finite-dimensional inequality and common Bochner measure are
constructed from RCD. The only source data supplied below are the actual
weak Laplacians and their bounded local Sobolev representatives.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_core_frame_defect {K : ℝ} {n m : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0) (p : X)
    (u : Fin m → compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    {R : ℝ} (hR : 0<R)
    (w z : Fin (n+1) → Euclidean m) (F : Fin (n+1) → X →ᵇ ℝ)
    (hF : ∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic (fun j => (u j).val) (w i))
        =ᵐ[hausdorff n X] F i)
    (hz : ∀ i, sobolevColumnMap (hausdorff n X) hX.quadratic (fun j => (u j).val) (z i)=
      SobolevSpace.product (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic (fun j => (u j).val) (w i))
        (sobolevColumnMap (hausdorff n X) hX.quadratic (fun j => (u j).val) (w i)) ‖F i‖₊ ‖F i‖₊)
    (q : Fin (n+1) → Lp ℝ 2 (hausdorff n X))
    (hq : ∀ i, IsWeakLaplacian (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic (fun j => (u j).val) (w i)) (q i))
    (d : Fin (n+1) → SobolevSpace (hausdorff n X) hX.quadratic) (A : Fin (n+1) → ℝ≥0)
    (hd : ∀ i, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (d i) x|≤A i)
    (hqr : ∀ i, q i =ᵐ[(hausdorff n X).restrict (ball p R)]
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (d i))
    (δ : X → ℝ)
    (hδ : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (R/2)), 0≤δ x)
    (htrace : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (R/2)),
      |∑ i : Fin n, localGamma (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic (fun j => (u j).val) (w i.castSucc))
        (sobolevColumnMap (hausdorff n X) hX.quadratic (fun j => (u j).val) (w i.castSucc)) x-(n:ℝ)|≤δ x)
    (hsquare : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (R/2)),
      |∑ i : Fin n, ∑ j : Fin n, (localGamma (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic (fun k => (u k).val) (w i.castSucc))
        (sobolevColumnMap (hausdorff n X) hX.quadratic (fun k => (u k).val) (w j.castSucc)) x)^2-(n:ℝ)|≤δ x) :
    let U := sobolevColumnMap (hausdorff n X) hX.quadratic (fun j => (u j).val)
    ∀ᵐ x ∂(hausdorff n X).restrict (ball p (R/2)), δ x≤1 →
      |localGamma (hausdorff n X) hX.quadratic (U (w (Fin.last n))) (U (w (Fin.last n))) x-
        ∑ i : Fin n, (localGamma (hausdorff n X) hX.quadratic (U (w i.castSucc)) (U (w (Fin.last n))) x)^2|≤
      Real.sqrt (6*δ x)*|localGamma (hausdorff n X) hX.quadratic (U (w (Fin.last n))) (U (w (Fin.last n))) x| := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let U := sobolevColumnMap μ hQ (fun j => (u j).val)
  obtain ⟨D,H,L,hU,hc,hD,hH,hsym⟩ := hX.regular_finite_span hn p u
  obtain ⟨M,hM⟩ := hX.regular_span_bochner_sobolev_measure hn p hR U D H L hU hc hD
    (fun a => hH a a) hsym
  obtain ⟨χ,Cχ,hχ,hχc,hχs,hχb,hχ1⟩ :=
    exists_annular_lipschitz_cutoff p (a := R/2) (b := 3*R/4) (by linarith)
  have hχΩ : tsupport χ⊆ball p R := hχs.trans (closedBall_subset_ball (by linarith))
  have hχS (x : X) (hx : x∈ball p (R/2)) : χ x=1 := hχ1 x (ball_subset_closedBall hx)
  have hMs : ∀ (a : Euclidean m) (ψ : SobolevSpace μ hQ) (v : X →ᵇ ℝ),
      HasCompactSupport (v : X → ℝ) → tsupport v⊆ball p R →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      (∫ x, v x ∂M.measure a)=regularBochnerForm μ hQ K U D H v ψ L hU a a := by
    intro a ψ v hvc hvs hψ
    exact hM a ψ v v.continuous hvc hvs hψ
  have hBE := (hX.scalarBochner_nonpositive K n hn hK p).regular_density μ hQ
    U D H L hU hc hD (fun a => hH a a) M hMs measurableSet_ball
    χ hχ hχc hχΩ (fun x => (hχb x).1) hχS
  have hDr (i : Fin (n+1)) : D (w i) =ᵐ[μ.restrict (ball p R)] SobolevSpace.toLp μ hQ (d i) := by
    have he : D (w i)=q i := IsWeakLaplacian.unique μ hQ (hD (w i)) (hq i)
    rw [he]
    exact hqr i
  exact regularBochner_frame_defect μ hQ (by omega) K U D H L hU hD hH hsym
    measurableSet_ball M hMs w z F hF hz d A hd hDr measurableSet_ball
    (ball_subset_ball (by linarith)) χ hχ hχc hχΩ (fun x => (hχb x).1) hχS hBE δ hδ htrace hsquare

end RegularPointCoordinates

end

end OAI
