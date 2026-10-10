import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates
import OAI.Geometry.RCD.Coordinates.RadialFitCoordinates
import OAI.Geometry.RCD.Harmonic.ColumnRepresentatives

namespace OAI

/-! # Centering the same normalized harmonic column

The constant is represented by a genuine local Sobolev cutoff. Centering
preserves all local Gram entries and the actual affine least-squares error.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def centeredColumn {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (c : Euclidean n) (η : SobolevSpace μ hQ) : Fin n → SobolevSpace μ hQ :=
  affineChangedColumn μ hQ u (ContinuousLinearMap.id ℝ (Euclidean n)) (-(innerSL ℝ c)) η

omit [BorelSpace X] [ProperSpace X] in
theorem centeredColumn_apply {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (c : Euclidean n) (η : SobolevSpace μ hQ) (i : Fin n) :
    centeredColumn μ hQ u c η i = u i + (-c i) • η := by
  simp only [centeredColumn, affineChangedColumn, ContinuousLinearMap.id_apply,
    sobolevColumnMap_single, neg_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul]

omit [BorelSpace X] [ProperSpace X] in
theorem centeredColumn_representative {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (v : X → Euclidean n) (c : Euclidean n) (η : SobolevSpace μ hQ)
    (hu : ∀ i, SobolevSpace.toLp μ hQ (u i) =ᵐ[μ.restrict s] fun x => v x i)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict s] fun _ => (1 : ℝ)) (i : Fin n) :
    SobolevSpace.toLp μ hQ (centeredColumn μ hQ u c η i) =ᵐ[μ.restrict s]
      fun x => (v x - c) i := by
  have hi := affineChangedColumn_representative μ hQ u s v hu
    (ContinuousLinearMap.id ℝ (Euclidean n)) (-(innerSL ℝ c)) η hη i
  filter_upwards [hi] with x hx
  change _ = (v x - c) i
  rw [PiLp.sub_apply]
  simpa only [centeredColumn, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply,
    neg_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    starRingEnd_apply, star_trivial, one_mul, sub_eq_add_neg] using hx

omit [BorelSpace X] [ProperSpace X] in
theorem centeredColumn_difference {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (c : Euclidean n) (η : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict s] fun _ => (1 : ℝ)) (i : Fin n) :
    SobolevSpace.toLp μ hQ (centeredColumn μ hQ u c η i - u i) =ᵐ[μ.restrict s]
      fun _ => -c i := by
  rw [centeredColumn_apply, add_sub_cancel_left]
  change SobolevSpace.toLpCLM μ hQ ((-c i) • η) =ᵐ[μ.restrict s] _
  rw [map_smul]
  filter_upwards [hη, ae_restrict_of_ae (Lp.coeFn_smul (-c i) (SobolevSpace.toLp μ hQ η))]
    with x hx hs
  change ((-c i) • SobolevSpace.toLp μ hQ η) x = -c i
  simp only [hs, Pi.smul_apply, smul_eq_mul, hx, mul_one]

theorem centeredColumn_gram {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (c : Euclidean n) (η : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict s] fun _ => (1 : ℝ)) (i j : Fin n) :
    localGamma μ hQ (centeredColumn μ hQ u c η i) (centeredColumn μ hQ u c η j)
      =ᵐ[μ.restrict s] localGamma μ hQ (u i) (u j) := by
  filter_upwards [localGamma_eq_of_constant_difference μ hQ s _ _ _ (-c i)
      (centeredColumn_difference μ hQ u s c η hη i),
    ae_restrict_of_ae (localGamma_comm μ hQ (u i) (centeredColumn μ hQ u c η j)),
    localGamma_eq_of_constant_difference μ hQ s _ _ (u i) (-c j)
      (centeredColumn_difference μ hQ u s c η hη j),
    ae_restrict_of_ae (localGamma_comm μ hQ (u j) (u i))] with x h₁ h₂ h₃ h₄
  exact h₁.trans (h₂.trans (h₃.trans h₄))

theorem FirstOrderSplittingOn.center {n : ℕ} {p : X} {r ε : ℝ}
    {u : Fin n → SobolevSpace μ hQ} {v : X → Euclidean n}
    (h : FirstOrderSplittingOn μ hQ p r ε u v)
    (c : Euclidean n) (η : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict (ball p r)] fun _ => (1 : ℝ)) :
    FirstOrderSplittingOn μ hQ p r ε (centeredColumn μ hQ u c η) (fun x => v x - c) := by
  have hc := isSobolevHarmonicOn_of_local_constant μ hQ _ measurableSet_ball η 1 hη
  refine ⟨centeredColumn_representative μ hQ u _ v c η h.representative hη,
    h.continuous.sub continuousOn_const, ?_, ?_, ?_⟩
  · intro i
    rw [centeredColumn_apply]
    exact IsSobolevHarmonicOn.add μ hQ (h.harmonic i) (hc.smul μ hQ (-c i))
  · intro i
    filter_upwards [centeredColumn_gram μ hQ u _ c η hη i i, h.gradient i] with x hx hg
    rwa [hx]
  · intro i j
    have he : (∫ x in ball p r,
        |localGamma μ hQ (centeredColumn μ hQ u c η i) (centeredColumn μ hQ u c η j) x -
          if i = j then 1 else 0| ∂μ) =
        ∫ x in ball p r, |localGamma μ hQ (u i) (u j) x - if i = j then 1 else 0| ∂μ := by
      apply integral_congr_ae
      filter_upwards [centeredColumn_gram μ hQ u _ c η hη i j] with x hx
      rw [hx]
    rw [he]
    exact h.gram i j

omit [BorelSpace X] [ProperSpace X] in
theorem centeredColumn_residual {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (hfin : μ s ≠ ∞) (c : Euclidean n) (η : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict s] fun _ => (1 : ℝ)) :
    affineResidual μ hQ (centeredColumn μ hQ u c η) s hfin = affineResidual μ hQ u s hfin := by
  exact affineChangedColumn_residual_eq μ hQ u (ContinuousLinearEquiv.refl ℝ (Euclidean n))
    (-(innerSL ℝ c)) η s hfin (restrictLp_eq_one_of_representative μ hQ η s hfin hη)

omit [BorelSpace X] [ProperSpace X] in
theorem centeredColumn_covector_difference {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (c b : Euclidean n) (η : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict s] fun _ => (1 : ℝ)) :
    SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ (centeredColumn μ hQ u c η) b -
      sobolevColumnMap μ hQ u b) =ᵐ[μ.restrict s] fun _ => -⟪c, b⟫_ℝ := by
  have he : sobolevColumnMap μ hQ (centeredColumn μ hQ u c η) b -
      sobolevColumnMap μ hQ u b = (-⟪c, b⟫_ℝ) • η := by
    rw [centeredColumn, sobolevColumnMap_affineChanged]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, neg_apply, innerSL_apply_apply, add_sub_cancel_left]
  rw [he]
  change SobolevSpace.toLpCLM μ hQ ((-⟪c, b⟫_ℝ) • η) =ᵐ[μ.restrict s] _
  rw [map_smul]
  filter_upwards [hη, ae_restrict_of_ae
    (Lp.coeFn_smul (-⟪c, b⟫_ℝ) (SobolevSpace.toLp μ hQ η))] with x hx hs
  change ((-⟪c, b⟫_ℝ) • SobolevSpace.toLp μ hQ η) x = -⟪c, b⟫_ℝ
  simp only [hs, Pi.smul_apply, smul_eq_mul, hx, mul_one]

/-- The raw derivative and its affine fit are unchanged by centering,
for every fixed covector and every admissible local gradient bound. -/
theorem centeredColumn_radial_fit {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (p : X) (r : ℝ) (hfin : μ (ball p r) ≠ ∞) (c b : Euclidean n)
    (η q : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict (ball p r)] fun _ => (1 : ℝ))
    {B B' : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict (ball p r),
      localGamma μ hQ (sobolevColumnMap μ hQ (centeredColumn μ hQ u c η) b)
        (sobolevColumnMap μ hQ (centeredColumn μ hQ u c η) b) x ≤ B)
    (ha' : ∀ᵐ x ∂μ.restrict (ball p r),
      localGamma μ hQ (sobolevColumnMap μ hQ u b) (sobolevColumnMap μ hQ u b) x ≤ B') :
    radialFitError μ hQ (centeredColumn μ hQ u c η) p r hfin q
      (sobolevColumnMap μ hQ (centeredColumn μ hQ u c η) b) ha =
    radialFitError μ hQ u p r hfin q (sobolevColumnMap μ hQ u b) ha' := by
  have he : localGamma μ hQ q (sobolevColumnMap μ hQ (centeredColumn μ hQ u c η) b)
      =ᵐ[μ.restrict (ball p r)] localGamma μ hQ q (sobolevColumnMap μ hQ u b) := by
    filter_upwards [localGamma_eq_of_constant_difference μ hQ (ball p r) _ _ q (-⟪c, b⟫_ℝ)
        (centeredColumn_covector_difference μ hQ u _ c b η hη),
      ae_restrict_of_ae (localGamma_comm μ hQ q
        (sobolevColumnMap μ hQ (centeredColumn μ hQ u c η) b)),
      ae_restrict_of_ae (localGamma_comm μ hQ q (sobolevColumnMap μ hQ u b))]
      with x h₁ h₂ h₃
    exact h₂.trans (h₁.trans h₃.symm)
  unfold radialFitError
  rw [centeredColumn_residual μ hQ u _ hfin c η hη,
    radialPairingLp_congr μ hQ _ _ _ _ _ ha ha' he]

end RegularPointCoordinates

end

end OAI
