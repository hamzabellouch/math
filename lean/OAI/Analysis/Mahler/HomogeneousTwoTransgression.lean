import OAI.Analysis.Mahler.PairTransgression
import OAI.Analysis.Mahler.WedgeUnit
import OAI.Analysis.Mahler.HomogeneousVariationCoefficient
import OAI.Analysis.Mahler.HomogeneousSmoothForms

namespace OAI

open Complex

namespace Mahler

lemma boundaryResidualFin_two
    (a b : ComplexEuclidean 2 → ComplexEuclidean 2 →L[ℝ] ℂ)
    (x : ComplexEuclidean 2) :
    boundaryResidualFin (k := 1) a b x =
      (wedge (oneForm a x).toAlternatingMap
        (extDeriv (oneForm b) x).toAlternatingMap).domDomCongr (prependFinEquiv 2) := by
  rw [boundaryResidualFin_succ (k := 0)]
  simp only [Nat.zero_add, Nat.cast_one, one_smul]
  exact wedge_power_one_boundary (sphereFrame 1).toBasis _ _

/-- The transgression primitive in complex dimension two. -/
noncomputable def homogeneousTwoPrimitive {N m : ℕ}
    (G : Fin N → MvPolynomial (Fin 2) ℂ) (t : ℝ) (x : ComplexEuclidean 2) :
    ComplexEuclidean 2 [⋀^Fin 2]→L[ℝ] ℂ :=
  pairExterior (alphaPath (polynomialMap G) (coordinateMap 2) m t x)
    (betaLinear (polynomialMap G) (coordinateMap 2) m x)

/-- Exact negative-sign transgression on actual sphere tangents in complex
dimension two. The residual is an exterior derivative, not pointwise zero. -/
theorem MassHypotheses.sphere_residual_two_transgression {N m : ℕ}
    {U : Set (ComplexEuclidean 2)} {f : Fin N → ComplexEuclidean 2 → ℂ}
    {G : Fin N → MvPolynomial (Fin 2) ℂ} (h : MassHypotheses 2 N m U f G)
    {x : ComplexEuclidean 2} (hx : x ≠ 0) (t : ℝ)
    (v : Fin 3 → ComplexEuclidean 2) (hv : ∀ i, inner ℝ x (v i) = 0) :
    boundaryResidualFin (k := 1)
      (alphaPath (polynomialMap G) (coordinateMap 2) m t)
      (betaLinear (polynomialMap G) (coordinateMap 2) m) x v =
      -(extDeriv (homogeneousTwoPrimitive (m := m) G t) x v) := by
  let a := alphaPath (polynomialMap G) (coordinateMap 2) m t
  let b := betaLinear (polynomialMap G) (coordinateMap 2) m
  have hs := h.alpha_beta_contDiffAt hx t 1
  have ha : DifferentiableAt ℝ a x := hs.1.differentiableAt (by norm_num)
  have hb : DifferentiableAt ℝ b x := hs.2.differentiableAt (by norm_num)
  have hzero : (wedge (oneForm b x).toAlternatingMap
      (extDeriv (oneForm a) x).toAlternatingMap).domDomCongr (prependFinEquiv 2) v = 0 := by
    rw [← wedge_power_one_boundary (sphereFrame 1).toBasis]
    let w : Fin 1 ⊕ WedgePowerSlots 1 → sphereTangent x := fun i =>
      ⟨v (boundaryFinEquiv 1 i), Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hv _)⟩
    have hz := congrArg (fun B => B w) (h.sphere_beta_wedge_power_zero hx t)
    simpa only [Nat.reduceSub, tangentForm, ← wedgePower_compLinearMap,
      ← wedge_compLinearMap, AlternatingMap.compLinearMap_apply,
      AlternatingMap.domDomCongr_apply, Submodule.subtype_apply,
      AlternatingMap.zero_apply, w, a, b, Function.comp_def] using hz
  have he := congrArg (fun B => B v) (extDeriv_pairExterior (sphereFrame 1).toBasis ha hb)
  simp only [AlternatingMap.sub_apply, hzero, zero_sub,
    ContinuousAlternatingMap.coe_toAlternatingMap] at he
  rw [boundaryResidualFin_two]
  change _ = -(extDeriv (fun y => pairExterior (a y) (b y)) x v)
  rw [he]
  exact (neg_neg _).symm

/-- The actual density derivative with its residual replaced by the negative
exterior derivative. -/
theorem MassHypotheses.sphere_density_two_transgression {N m : ℕ}
    {U : Set (ComplexEuclidean 2)} {f : Fin N → ComplexEuclidean 2 → ℂ}
    {G : Fin N → MvPolynomial (Fin 2) ℂ} (h : MassHypotheses 2 N m U f G)
    {x : ComplexEuclidean 2} (hx : ‖x‖ = 1) (t : ℝ) :
    HasDerivAt
      (fun s => orientedDensity (sphereFrame 1) (sphereVolume 1)
        (boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap 2) m s) x) x)
      (orientedDensity (sphereFrame 1) (sphereVolume 1)
        (- (extDeriv (homogeneousTwoPrimitive (m := m) G t) x).toAlternatingMap) x) t := by
  have hxn : x ≠ 0 := by intro he; simp [he] at hx
  have hd := h.sphere_density_derivative hx t
  have he := orientedDensity_congr_on_tangent (k := 1) hx
    (B := boundaryResidualFin
      (alphaPath (polynomialMap G) (coordinateMap 2) m t)
      (betaLinear (polynomialMap G) (coordinateMap 2) m) x)
    (C := -(extDeriv (homogeneousTwoPrimitive (m := m) G t) x).toAlternatingMap)
    (fun v hv => h.sphere_residual_two_transgression hxn t v hv)
  exact he ▸ hd

/-- The primitive has every finite order of local regularity off the origin,
and in particular is C1 at the entire unit sphere. -/
theorem MassHypotheses.homogeneousTwoPrimitive_contDiffAt {N m : ℕ}
    {U : Set (ComplexEuclidean 2)} {f : Fin N → ComplexEuclidean 2 → ℂ}
    {G : Fin N → MvPolynomial (Fin 2) ℂ} (h : MassHypotheses 2 N m U f G)
    {x : ComplexEuclidean 2} (hx : x ≠ 0) (t : ℝ) (q : ℕ) :
    ContDiffAt ℝ q (homogeneousTwoPrimitive (m := m) G t) x := by
  exact contDiffAt_pairExterior q (h.alpha_beta_contDiffAt hx t q).1
    (h.alpha_beta_contDiffAt hx t q).2

/-- The actual boundary form derivative itself, with no residual placeholder,
on arbitrary sphere tangent tuples in complex dimension two. -/
theorem MassHypotheses.sphere_boundaryForm_two_transgression {N m : ℕ}
    {U : Set (ComplexEuclidean 2)} {f : Fin N → ComplexEuclidean 2 → ℂ}
    {G : Fin N → MvPolynomial (Fin 2) ℂ} (h : MassHypotheses 2 N m U f G)
    {x : ComplexEuclidean 2} (hx : x ≠ 0) (t : ℝ)
    (v : Fin 3 → ComplexEuclidean 2) (hv : ∀ i, inner ℝ x (v i) = 0) :
    HasDerivAt
      (fun s => boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap 2) m s) x v)
      (-(extDeriv (homogeneousTwoPrimitive (m := m) G t) x v)) t := by
  let w : Fin 1 ⊕ WedgePowerSlots 1 → sphereTangent x := fun i =>
    ⟨v (boundaryFinEquiv 1 i), Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hv _)⟩
  have hd := h.sphere_boundaryForm_derivative hx t w
  have he : HasDerivAt
      (fun s => boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap 2) m s) x v)
      (boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap 2) m t)
        (betaLinear (polynomialMap G) (coordinateMap 2) m) x v) t := by
    simpa only [Nat.reduceSub, boundaryFormFin, boundaryResidualFin,
      AlternatingMap.domDomCongr_apply, tangentForm, ← wedgePower_compLinearMap,
      ← wedgePowerVariation_compLinearMap, ← wedge_compLinearMap,
      AlternatingMap.compLinearMap_apply, Submodule.subtype_apply, w, Function.comp_def] using hd
  exact h.sphere_residual_two_transgression hx t v hv ▸ he

end Mahler

end OAI
