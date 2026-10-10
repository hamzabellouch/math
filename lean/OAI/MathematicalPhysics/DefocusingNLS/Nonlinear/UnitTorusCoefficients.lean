import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPhysicalSampling

namespace OAI

/-! # Recovering the physical coefficients from the continuous Fourier series -/

open MeasureTheory
open scoped RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "T" => UnitAddTorus (Fin 12)

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def unitTorusCoefficient (n : Fin 12 → ℤ) : C(T, ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ (UnitAddTorus.mFourierLp 2 n)).comp
    (ContinuousMap.toLp 2 volume ℂ)

theorem unitTorusCoefficient_apply (n : Fin 12 → ℤ) (f : C(T, ℂ)) :
    unitTorusCoefficient n f = UnitAddTorus.mFourierCoeff f n := by
  change inner ℂ (UnitAddTorus.mFourierLp 2 n) (ContinuousMap.toLp 2 volume ℂ f) = _
  rw [← UnitAddTorus.coe_mFourierBasis]
  rw [← HilbertBasis.repr_apply_apply, UnitAddTorus.mFourierBasis_repr,
    UnitAddTorus.mFourierCoeff_toLp]

theorem unitTorusCoefficient_mFourier (n m : Fin 12 → ℤ) :
    unitTorusCoefficient n (UnitAddTorus.mFourier m) = if n = m then 1 else 0 := by
  change inner ℂ (UnitAddTorus.mFourierLp 2 n) (UnitAddTorus.mFourierLp 2 m) = _
  exact (orthonormal_iff_ite.mp UnitAddTorus.orthonormal_mFourier) n m

noncomputable def expandingUnitTorusTerm (a k L : ℝ) (f : FourierL2)
    (n : frequencyLattice) : C(T, ℂ) :=
  expandingFourierCoefficient a k L f n • UnitAddTorus.mFourier (frequencyCoordinates n)

theorem summable_expandingUnitTorusTerm (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    Summable (expandingUnitTorusTerm a k L f) := by
  apply Summable.of_norm
  simpa only [expandingUnitTorusTerm, norm_smul, UnitAddTorus.mFourier_norm, mul_one] using
    summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f

noncomputable def expandingUnitTorusFunction (a k L : ℝ) (f : FourierL2) : C(T, ℂ) :=
  ∑' n, expandingUnitTorusTerm a k L f n

theorem expandingUnitTorusFunction_coefficient (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (f : FourierL2) (n : frequencyLattice) :
    unitTorusCoefficient (frequencyCoordinates n) (expandingUnitTorusFunction a k L f) =
      expandingFourierCoefficient a k L f n := by
  classical
  have h := (summable_expandingUnitTorusTerm a k L ha ha1 hk hL f).hasSum.mapL
    (unitTorusCoefficient (frequencyCoordinates n))
  have he (m : frequencyLattice) :
      unitTorusCoefficient (frequencyCoordinates n) (expandingUnitTorusTerm a k L f m) =
        if m = n then expandingFourierCoefficient a k L f n else 0 := by
    simp only [expandingUnitTorusTerm, map_smul, unitTorusCoefficient_mFourier,
      smul_eq_mul]
    by_cases hmn : m = n
    · subst m
      simp
    · have hnm : frequencyCoordinates n ≠ frequencyCoordinates m := by
        intro heq
        exact hmn (frequencyCoordinatesEquiv.injective heq.symm)
      simp [hnm, hmn]
  simp_rw [he] at h
  simpa [expandingUnitTorusFunction] using h.tsum_eq.symm

theorem expandingUnitTorusFunction_projection (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (f : FourierL2) (x : E) :
    expandingUnitTorusFunction a k L f (unitTorusProjection x) =
      expandingTorusFunction a k L f (euclideanToTorus ((2 * Real.pi) • x)) := by
  have hs := (summable_expandingUnitTorusTerm a k L ha ha1 hk hL f).hasSum.mapL
    (ContinuousMap.evalCLM (R := ℂ) (unitTorusProjection x))
  have he (n : frequencyLattice) :
      UnitAddTorus.mFourier (frequencyCoordinates n) (unitTorusProjection x) =
        torusCharacter n (euclideanToTorus ((2 * Real.pi) • x)) := by
    change integerFourierCharacter n x = _
    rw [integerFourierCharacter_exp, torusCharacter_euclidean]
    simp only [spatialFourierCharacter, real_inner_smul_left]
  rw [expandingTorusFunction_apply a k L ha ha1 hk hL]
  exact hs.tsum_eq.symm.trans (tsum_congr fun n => by
    change expandingFourierCoefficient a k L f n *
      UnitAddTorus.mFourier (frequencyCoordinates n) (unitTorusProjection x) = _
    rw [he])

theorem expandingFourierCoefficient_eq_of_torus_eq (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (f g : FourierL2)
    (hfg : ∀ x : E, expandingTorusFunction a k L f (euclideanToTorus x) =
      expandingTorusFunction a k L g (euclideanToTorus x)) (n : frequencyLattice) :
    expandingFourierCoefficient a k L f n = expandingFourierCoefficient a k L g n := by
  have he : expandingUnitTorusFunction a k L f = expandingUnitTorusFunction a k L g := by
    ext y
    obtain ⟨x, rfl⟩ := unitTorusProjection_isOpenQuotientMap.surjective y
    rw [expandingUnitTorusFunction_projection a k L ha ha1 hk hL,
      expandingUnitTorusFunction_projection a k L ha ha1 hk hL]
    exact hfg _
  rw [← expandingUnitTorusFunction_coefficient a k L ha ha1 hk hL f n,
    ← expandingUnitTorusFunction_coefficient a k L ha ha1 hk hL g n, he]

end DefocusingNLS

end OAI
