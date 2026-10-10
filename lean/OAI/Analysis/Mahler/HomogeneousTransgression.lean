import OAI.Analysis.Mahler.PowerTransgression

namespace OAI

open Complex

namespace Mahler

/-- The transgression primitive in every complex dimension k+2. -/
noncomputable def homogeneousPrimitive {k N m : ℕ}
    (G : Fin N → MvPolynomial (Fin (k+2)) ℂ) (t : ℝ) :=
  powerTransgressionPrimitive (sphereFrame (k+1)).toBasis
    (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
    (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) k

lemma homogeneousPrimitive_is_wedge {k N m : ℕ}
    (G : Fin N → MvPolynomial (Fin (k+2)) ℂ) (t : ℝ)
    (x : ComplexEuclidean (k+2)) :
    (homogeneousPrimitive (m := m) G t x).toAlternatingMap =
      (wedge (oneForm (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t) x).toAlternatingMap
        (wedge (oneForm (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x).toAlternatingMap
          (wedgePower (extDeriv (oneForm (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)) x).toAlternatingMap k))).domDomCongr
        (primitiveFinEquiv k) :=
  powerTransgressionPrimitive_is_wedge (sphereFrame (k+1)).toBasis _ _ k x

/-- The full ambient identity; the horizontal term has not been discarded. -/
theorem MassHypotheses.homogeneousPrimitive_extDeriv {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    {x : ComplexEuclidean (k+2)} (hx : x ≠ 0) (t : ℝ) :
    (extDeriv (homogeneousPrimitive (m := m) G t) x).toAlternatingMap =
      (wedge (oneForm (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x).toAlternatingMap
        (wedgePower (extDeriv (oneForm
          (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)) x).toAlternatingMap
          (k+1))).domDomCongr (boundaryFinEquiv (k+1)) -
      boundarySingleResidualFin
        (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x := by
  have hs := h.alpha_beta_contDiffAt hx t 1
  have hda := (contDiffAt_extDeriv_power_order 1
      (contDiffAt_oneForm_order 2 (h.alpha_beta_contDiffAt hx t 2).1)).differentiableAt
      (by norm_num)
  have he := extDeriv_powerTransgressionPrimitive (sphereFrame (k+1)).toBasis k
    (hs.1.differentiableAt (by norm_num)) (hs.2.differentiableAt (by norm_num))
    hda (h.alphaPath_extDeriv_extDeriv hx t)
  unfold homogeneousPrimitive boundarySingleResidualFin
  have hdec : wedgePowerSlotsDecidableEq (k+1) =
      (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) := Subsingleton.elim _ _
  have hfin : wedgePowerSlotsFintype (k+1) =
      (inferInstance : Fintype (Fin 2 ⊕ WedgePowerSlots k)) := Subsingleton.elim _ _
  rw [hdec, hfin] at he ⊢
  exact he

/-- Every required smoothness order follows from MassHypotheses. -/
theorem MassHypotheses.homogeneousPrimitive_contDiffAt {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    {x : ComplexEuclidean (k+2)} (hx : x ≠ 0) (t : ℝ) (q : ℕ) :
    ContDiffAt ℝ q (homogeneousPrimitive (m := m) G t) x :=
  contDiffAt_powerTransgressionPrimitive (sphereFrame (k+1)).toBasis k q
    (h.alpha_beta_contDiffAt hx t (q+1)).1 (h.alpha_beta_contDiffAt hx t q).2

/-- Exact negative-sign residual transgression on sphere tangents, with the
actual multiplicity n-1, in all complex dimensions n=k+2. -/
theorem MassHypotheses.sphere_residual_transgression {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    {x : ComplexEuclidean (k+2)} (hx : x ≠ 0) (t : ℝ)
    (v : Fin (2*(k+1)+1) → ComplexEuclidean (k+2))
    (hv : ∀ i, inner ℝ x (v i) = 0) :
    boundaryResidualFin (k := k+1)
      (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
      (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x v =
      -((k+1 : ℕ) : ℂ) * extDeriv (homogeneousPrimitive (m := m) G t) x v := by
  let a := alphaPath (polynomialMap G) (coordinateMap (k+2)) m t
  let b := betaLinear (polynomialMap G) (coordinateMap (k+2)) m
  have hzero : (wedge (oneForm b x).toAlternatingMap
      (wedgePower (extDeriv (oneForm a) x).toAlternatingMap (k+1))).domDomCongr
        (boundaryFinEquiv (k+1)) v = 0 := by
    let w : Fin 1 ⊕ WedgePowerSlots (k+1) → sphereTangent x := fun i =>
      ⟨v (boundaryFinEquiv (k+1) i), Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hv _)⟩
    have hz0 := h.sphere_beta_wedge_power_zero hx t
    rw [show k+2-1=k+1 by omega] at hz0
    have hz := congrArg (fun B => B w) hz0
    simpa only [show k+2-1 = k+1 by omega, tangentForm, ← wedgePower_compLinearMap,
      ← wedge_compLinearMap, AlternatingMap.compLinearMap_apply,
      AlternatingMap.domDomCongr_apply, Submodule.subtype_apply,
      AlternatingMap.zero_apply, w, a, b, Function.comp_def] using hz
  have he := congrArg (fun B => B v) (h.homogeneousPrimitive_extDeriv hx t)
  change extDeriv (homogeneousPrimitive (m := m) G t) x v =
    (wedge (oneForm b x).toAlternatingMap
      (wedgePower (extDeriv (oneForm a) x).toAlternatingMap (k+1))).domDomCongr
        (boundaryFinEquiv (k+1)) v - boundarySingleResidualFin a b x v at he
  rw [hzero, zero_sub] at he
  rw [boundaryResidualFin_succ, AlternatingMap.smul_apply, he]
  change _ * _ = _ * _
  ring

theorem MassHypotheses.sphere_density_transgression {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    {x : ComplexEuclidean (k+2)} (hx : ‖x‖ = 1) (t : ℝ) :
    HasDerivAt
      (fun s => orientedDensity (sphereFrame (k+1)) (sphereVolume (k+1))
        (boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m s) x) x)
      (orientedDensity (sphereFrame (k+1)) (sphereVolume (k+1))
        (-((k+1 : ℕ) : ℂ) •
          (extDeriv (homogeneousPrimitive (m := m) G t) x).toAlternatingMap) x) t := by
  have hxn : x ≠ 0 := by intro he; simp [he] at hx
  have hd := h.sphere_density_derivative hx t
  have he := orientedDensity_congr_on_tangent (k := k+1) hx
    (B := boundaryResidualFin
      (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
      (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x)
    (C := -((k+1 : ℕ) : ℂ) •
      (extDeriv (homogeneousPrimitive (m := m) G t) x).toAlternatingMap)
    (fun v hv => h.sphere_residual_transgression hxn t v hv)
  exact he ▸ hd

/-- The actual boundary-form derivative on every tangent tuple. -/
theorem MassHypotheses.sphere_boundaryForm_transgression {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    {x : ComplexEuclidean (k+2)} (hx : x ≠ 0) (t : ℝ)
    (v : Fin (2*(k+1)+1) → ComplexEuclidean (k+2))
    (hv : ∀ i, inner ℝ x (v i) = 0) :
    HasDerivAt
      (fun s => boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m s) x v)
      (-((k+1 : ℕ) : ℂ) * extDeriv (homogeneousPrimitive (m := m) G t) x v) t := by
  let w : Fin 1 ⊕ WedgePowerSlots (k+1) → sphereTangent x := fun i =>
    ⟨v (boundaryFinEquiv (k+1) i), Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hv _)⟩
  have hd0 := h.sphere_boundaryForm_derivative hx t
  rw [show k+2-1=k+1 by omega] at hd0
  have hd := hd0 w
  have he : HasDerivAt
      (fun s => boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m s) x v)
      (boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x v) t := by
    simpa only [show k+2-1=k+1 by omega, boundaryFormFin, boundaryResidualFin,
      AlternatingMap.domDomCongr_apply, tangentForm, ← wedgePower_compLinearMap,
      ← wedgePowerVariation_compLinearMap, ← wedge_compLinearMap,
      AlternatingMap.compLinearMap_apply, Submodule.subtype_apply, w, Function.comp_def] using hd
  exact h.sphere_residual_transgression hx t v hv ▸ he

end Mahler

end OAI
