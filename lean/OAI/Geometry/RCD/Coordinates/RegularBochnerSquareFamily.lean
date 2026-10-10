import OAI.Geometry.RCD.Coordinates.RegularBochnerFrame

namespace OAI

/-! # Common centered-square source and density data for a regular family -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m n : ℕ}

theorem regularBochner_centered_square_family [μ.Regular] [SigmaFinite μ] [SecondCountableTopology X]
    (K : ℝ) (U : Euclidean m →L[ℝ] SobolevSpace μ hQ)
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
      (laplacianCoordinateForm μ D x a)^2≤(n:ℝ)*bochnerRadonDensity μ M x a a) :
    ∀ᵐ x ∂μ.restrict S,
      (∀ i, laplacianCoordinateForm μ D x (z i-(2*F i x) • w i)=
        2*localGamma μ hQ (U (w i)) (U (w i)) x) ∧
      (∀ i j, bochnerRadonDensity μ M x (z i-(2*F i x) • w i)
        (z j-(2*F j x) • w j)=4*(localGamma μ hQ (U (w i)) (U (w j)) x)^2) ∧
      ∀ a, (laplacianCoordinateForm μ D x a)^2≤(n:ℝ)*bochnerRadonDensity μ M x a a := by
  let G (i j : Fin (n+1)) := localGamma μ hQ (U (w i)) (U (w j))
  let T (i j : Fin (n+1)) :=
    localHessianAction μ hQ (U (w i)) (U (w j)) (U (w j)) (H (w i) (w j))
      (H (w i) (w j)) (H (w j) (w j))
  have hgrad (i : Fin (n+1)) : ∀ᵐ x ∂μ, G i i x≤(L (w i):ℝ)^2 := by
    filter_upwards [localGamma_self μ hQ (U (w i)),hU (w i),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (U (w i)))] with x he hb h0
    change localGamma μ hQ (U (w i)) (U (w i)) x≤_
    rw [he]
    exact pow_le_pow_left₀ h0 hb 2
  have hfb (i : Fin (n+1)) : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (U (w i)) x|≤‖F i‖₊ := by
    filter_upwards [hF i] with x hx
    rw [hx]
    exact (F i).norm_coe_le_norm x
  have hsource (i : Fin (n+1)) := regular_square_source_data μ hQ U D H L hU hD hH
    (w i) (z i) (F i) (hF i) (hz i) (d i) (A i) (hd i) (hDr i)
  choose dz B hdz hDz using hsource
  have hlinear (i j : Fin (n+1)) : ∀ᵐ x ∂μ.restrict S,
      bochnerRadonDensity μ M x (w i) (z j)=
        2*F j x*bochnerRadonDensity μ M x (w i) (w j)+2*T i j x := by
    have hp := regularBochner_square_product μ hQ K U D H L hU hD hH hsym hΩ M hM
      (w i) (w j) (z j) (F j) (hF j) (hz j) (d i) (d j) (A i) (A j)
      (hd i) (hd j) (hDr i) (hDr j) hS χ hχ hχc hχΩ hχ0 hχ1
    have hh := signed_rnDeriv_local_product μ (M.bilinear (w i) (w j))
      (M.bilinear (w i) (w j)) (M.bilinear (w i) (z j)) (F j) (F j)
      (localHessianAction_integrable μ hQ _ _ _ _ _ _) hS hp
    filter_upwards [hh,ae_restrict_of_ae (bochnerRadonDensity_rep μ M (w i) (z j)),
      ae_restrict_of_ae (bochnerRadonDensity_rep μ M (w i) (w j))] with x hx he hf
    rw [he,hf] at hx
    change _=2*F j x*bochnerRadonDensity μ M x (w i) (w j)+2*
      localHessianAction μ hQ (U (w i)) (U (w j)) (U (w j))
        (H (w i) (w j)) (H (w i) (w j)) (H (w j) (w j)) x
    linarith only [hx]
  have hpairs (i j : Fin (n+1)) : ∀ᵐ x ∂μ.restrict S,
      bochnerRadonDensity μ M x (z i) (z j)=
        2*F j x*bochnerRadonDensity μ M x (z i) (w j)+4*F i x*T i j x+4*(G i j x)^2 :=
    regularBochner_square_pair μ hQ K U D H L hU hD hH hsym hΩ M hM
      (w i) (w j) (z i) (z j) (F i) (F j) (hF i) (hF j) (hz i) (hz j)
      (dz i) (d j) (B i) (A j) (hdz i) (hd j) (hDz i) (hDr j)
      hS hsub χ hχ hχc hχΩ hχ0 hχ1
  have hlap (i : Fin (n+1)) : ∀ᵐ x ∂μ.restrict S,
      laplacianCoordinateForm μ D x (z i)=
        2*F i x*laplacianCoordinateForm μ D x (w i)+2*G i i x := by
    have hh := laplacianCoordinateForm_square μ hQ U D hD (w i) (z i)
      ‖F i‖₊ (L (w i)) (hfb i) (hgrad i) (hz i)
    filter_upwards [ae_restrict_of_ae hh,ae_restrict_of_ae (hF i)] with x hx hf
    simpa only [hf] using hx
  have hfull := ae_finite_bochner_bound (μ.restrict S) (bochnerRadonDensity μ M)
    (laplacianCoordinateForm μ D) (n:ℝ) hBE
  filter_upwards [hfull,ae_all_iff.mpr hlap,
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hlinear i)),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hpairs i))] with x hbe hl hp hpp
  refine ⟨?_,?_,hbe⟩
  · intro i
    exact centered_square_source (laplacianCoordinateForm μ D x) (w i) (z i)
      (F i x) (G i i x) (hl i)
  · intro i j
    exact centered_square_bochner_pair (bochnerRadonDensity μ M x) (w i) (w j)
      (z i) (z j) (F i x) (F j x) (T i j x) (G i j x) (hpp i j) (hp i j)

end RegularPointCoordinates

end

end OAI
