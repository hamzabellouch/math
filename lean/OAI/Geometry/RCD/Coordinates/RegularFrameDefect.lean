import OAI.Geometry.RCD.Coordinates.RegularCoreFrameDefect
import OAI.Geometry.RCD.Coordinates.RegularTestAlgebra

namespace OAI

/-! # Quantitative gradient expansion for an actual regular family

Only the original n+1 functions and their weak Laplacians are supplied.
Their squares, finite span, Bochner measure and dimensional inequality
are constructed internally.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_frame_defect {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0) (p : X)
    (f : Fin (n+1) → compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    {R : ℝ} (hR : 0<R) (F : Fin (n+1) → X →ᵇ ℝ)
    (hF : ∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (f i).val =ᵐ[hausdorff n X] F i)
    (q : Fin (n+1) → Lp ℝ 2 (hausdorff n X))
    (hq : ∀ i, IsWeakLaplacian (hausdorff n X) hX.quadratic (f i).val (q i))
    (d : Fin (n+1) → SobolevSpace (hausdorff n X) hX.quadratic) (A : Fin (n+1) → ℝ≥0)
    (hd : ∀ i, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (d i) x|≤A i)
    (hqr : ∀ i, q i =ᵐ[(hausdorff n X).restrict (ball p R)]
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (d i))
    (δ : X → ℝ)
    (hδ : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (R/2)), 0≤δ x)
    (htrace : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (R/2)),
      |∑ i : Fin n, localGamma (hausdorff n X) hX.quadratic
        (f i.castSucc).val (f i.castSucc).val x-(n:ℝ)|≤δ x)
    (hsquare : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (R/2)),
      |∑ i : Fin n, ∑ j : Fin n, (localGamma (hausdorff n X) hX.quadratic
        (f i.castSucc).val (f j.castSucc).val x)^2-(n:ℝ)|≤δ x) :
    ∀ᵐ x ∂(hausdorff n X).restrict (ball p (R/2)), δ x≤1 →
      |localGamma (hausdorff n X) hX.quadratic (f (Fin.last n)).val (f (Fin.last n)).val x-
        ∑ i : Fin n, (localGamma (hausdorff n X) hX.quadratic
          (f i.castSucc).val (f (Fin.last n)).val x)^2|≤
      Real.sqrt (6*δ x)*|localGamma (hausdorff n X) hX.quadratic
        (f (Fin.last n)).val (f (Fin.last n)).val x| := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let : IsFiniteMeasureOnCompacts μ :=
    ⟨fun {_s} hs => hX.finiteOnBounded _ hs.isBounded⟩
  have hb (i : Fin (n+1)) : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (f i).val x|≤‖F i‖₊ := by
    filter_upwards [hF i] with x hx
    rw [hx]
    exact (F i).norm_coe_le_norm x
  let sq (i : Fin (n+1)) : compactLaplacianCore μ hQ univ :=
    ⟨SobolevSpace.product μ hQ (f i).val (f i).val ‖F i‖₊ ‖F i‖₊,
      product_mem_compactLaplacianCore μ hQ (f i).property (f i).property _ _ (hb i) (hb i)⟩
  let u := Fin.append f sq
  let U := sobolevColumnMap μ hQ (fun i => (u i).val)
  let w (i : Fin (n+1)) : Euclidean ((n+1)+(n+1)) :=
    EuclideanSpace.single (Fin.castAdd (n+1) i) 1
  let z (i : Fin (n+1)) : Euclidean ((n+1)+(n+1)) :=
    EuclideanSpace.single (Fin.natAdd (n+1) i) 1
  have hUw (i : Fin (n+1)) : U (w i)=(f i).val := by
    simp [U,w,u,sobolevColumnMap_single]
  have hUz (i : Fin (n+1)) : U (z i)=
      SobolevSpace.product μ hQ (f i).val (f i).val ‖F i‖₊ ‖F i‖₊ := by
    change sobolevColumnMap μ hQ (fun j => (u j).val)
      (EuclideanSpace.single (Fin.natAdd (n+1) i) 1)=_
    rw [sobolevColumnMap_single]
    change (Fin.append f sq (Fin.natAdd (n+1) i)).val=_
    rw [Fin.append_right]
  have hF' (i : Fin (n+1)) : SobolevSpace.toLp μ hQ (U (w i)) =ᵐ[μ] F i := by
    rw [hUw]
    exact hF i
  have hz' (i : Fin (n+1)) : U (z i)=
      SobolevSpace.product μ hQ (U (w i)) (U (w i)) ‖F i‖₊ ‖F i‖₊ := by
    rw [hUz,hUw]
  have hq' (i : Fin (n+1)) : IsWeakLaplacian μ hQ (U (w i)) (q i) := by
    rw [hUw]
    exact hq i
  have ht : ∀ᵐ x ∂μ.restrict (ball p (R/2)),
      |∑ i : Fin n, localGamma μ hQ (U (w i.castSucc)) (U (w i.castSucc)) x-(n:ℝ)|≤δ x := by
    simpa only [hUw] using htrace
  have hs : ∀ᵐ x ∂μ.restrict (ball p (R/2)),
      |∑ i : Fin n, ∑ j : Fin n, (localGamma μ hQ (U (w i.castSucc)) (U (w j.castSucc)) x)^2-(n:ℝ)|≤δ x := by
    simpa only [hUw] using hsquare
  have hh := hX.regular_core_frame_defect hn hK p u hR w z F hF' hz' q hq' d A hd hqr δ hδ ht hs
  change (∀ᵐ x ∂μ.restrict (ball p (R/2)), δ x≤1 →
    |localGamma μ hQ (U (w (Fin.last n))) (U (w (Fin.last n))) x-
      ∑ i : Fin n, (localGamma μ hQ (U (w i.castSucc)) (U (w (Fin.last n))) x)^2|≤
    Real.sqrt (6*δ x)*|localGamma μ hQ (U (w (Fin.last n))) (U (w (Fin.last n))) x|) at hh
  simpa only [hUw] using hh

end RegularPointCoordinates

end

end OAI
