import OAI.Geometry.RCD.Coordinates.RegularBochnerSquareFamily
import OAI.Geometry.RCD.Coordinates.BochnerFrameDefect

namespace OAI

/-! # Quantitative frame energy for actual regular Bochner data -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m n : ℕ}

theorem regularBochner_frame_defect [μ.Regular] [SigmaFinite μ] [SecondCountableTopology X]
    (hn : 0<n) (K : ℝ) (U : Euclidean m →L[ℝ] SobolevSpace μ hQ)
    (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a)
    (hD : ∀ a, IsWeakLaplacian μ hQ (U a) (D a))
    (hH : ∀ a b, SobolevSpace.toLp μ hQ (H a b) =ᵐ[μ] localGamma μ hQ (U a) (U b))
    (hsym : ∀ a b, H a b=H b a)
    {Ω S : Set X} (hΩ : MeasurableSet Ω) (M : PositiveBilinearMeasure X (Euclidean m))
    (hM : ∀ (a : Euclidean m) (ψ : SobolevSpace μ hQ) (q : X →ᵇ ℝ),
      HasCompactSupport (q : X → ℝ) → tsupport q ⊆ Ω →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q →
      (∫ x, q x ∂M.measure a)=regularBochnerForm μ hQ K U D H q ψ L hU a a)
    (w z : Fin (n+1) → Euclidean m) (F : Fin (n+1) → X →ᵇ ℝ)
    (hF : ∀ i, SobolevSpace.toLp μ hQ (U (w i)) =ᵐ[μ] F i)
    (hz : ∀ i, U (z i)=SobolevSpace.product μ hQ (U (w i)) (U (w i)) ‖F i‖₊ ‖F i‖₊)
    (d : Fin (n+1) → SobolevSpace μ hQ) (A : Fin (n+1) → ℝ≥0)
    (hd : ∀ i, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (d i) x|≤A i)
    (hDr : ∀ i, D (w i) =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ (d i))
    (hS : MeasurableSet S) (hsub : S⊆Ω)
    (χ : X →ᵇ ℝ) {Cχ : ℝ≥0} (hχ : LipschitzWith Cχ χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ⊆Ω)
    (hχ0 : ∀ x, 0≤χ x) (hχ1 : ∀ x∈S, χ x=1)
    (hBE : ∀ a, ∀ᵐ x ∂μ.restrict S,
      (laplacianCoordinateForm μ D x a)^2≤(n:ℝ)*bochnerRadonDensity μ M x a a)
    (δ : X → ℝ) (hδ : ∀ᵐ x ∂μ.restrict S, 0≤δ x)
    (htrace : ∀ᵐ x ∂μ.restrict S,
      |∑ i : Fin n, localGamma μ hQ (U (w i.castSucc)) (U (w i.castSucc)) x-(n:ℝ)|≤δ x)
    (hsquare : ∀ᵐ x ∂μ.restrict S,
      |∑ i : Fin n, ∑ j : Fin n,
        (localGamma μ hQ (U (w i.castSucc)) (U (w j.castSucc)) x)^2-(n:ℝ)|≤δ x) :
    ∀ᵐ x ∂μ.restrict S, δ x≤1 →
      |localGamma μ hQ (U (w (Fin.last n))) (U (w (Fin.last n))) x-
        ∑ i : Fin n, (localGamma μ hQ (U (w i.castSucc)) (U (w (Fin.last n))) x)^2|≤
      Real.sqrt (6*δ x)*|localGamma μ hQ (U (w (Fin.last n))) (U (w (Fin.last n))) x| := by
  have hf := regularBochner_centered_square_family μ hQ K U D H L hU hD hH hsym
    hΩ M hM w z F hF hz d A hd hDr hS hsub χ hχ hχc hχΩ hχ0 hχ1 hBE
  filter_upwards [hf,hδ,htrace,hsquare] with x hx he ht hs
  intro he1
  let C (i : Fin (n+1)) := z i-(2*F i x) • w i
  exact bochner_frame_defect hn (bochnerRadonDensity μ M x) (laplacianCoordinateForm μ D x)
    (bochnerRadonDensity_symmetric μ M x) hx.2.2
    (fun i => C i.castSucc) (C (Fin.last n))
    (fun i j => localGamma μ hQ (U (w i.castSucc)) (U (w j.castSucc)) x)
    (localGamma μ hQ (U (w (Fin.last n))) (U (w (Fin.last n))) x)
    (fun i => localGamma μ hQ (U (w i.castSucc)) (U (w (Fin.last n))) x)
    he he1 (fun i => hx.1 i.castSucc) (fun i j => hx.2.1 i.castSucc j.castSucc)
    (hx.1 (Fin.last n)) (hx.2.1 (Fin.last n) (Fin.last n))
    (fun i => hx.2.1 i.castSucc (Fin.last n)) ht hs

end RegularPointCoordinates

end

end OAI
