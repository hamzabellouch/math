import OAI.Analysis.Mahler.HomogeneousSphereIntegral

namespace OAI

open Complex

namespace Mahler

lemma wedgePowerVariation_compLinearMap {T S : Type*}
    [AddCommGroup T] [Module ℝ T] [AddCommGroup S] [Module ℝ S]
    (L : S →ₗ[ℝ] T) (a da : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (k : ℕ) :
    (wedgePowerVariation a da k).compLinearMap L =
      wedgePowerVariation (a.compLinearMap L) (da.compLinearMap L) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hadd {ι : Type} (A C : T [⋀^ι]→ₗ[ℝ] ℂ) :
        (A+C).compLinearMap L = A.compLinearMap L + C.compLinearMap L := by ext v; rfl
    simp only [wedgePowerVariation]
    have h1 := wedge_compLinearMap L da (wedgePower a k)
    have h2 := wedge_compLinearMap L a (wedgePowerVariation a da k)
    rw [wedgePower_compLinearMap] at h1
    rw [ih] at h2
    exact congrArg₂ (fun A B => A+B) h1 h2

/-- The residual variation, retaining all terms and the actual exterior
spatial derivatives. Its sphere integral has not been asserted to vanish. -/
noncomputable def boundaryResidualFin {k : ℕ}
    (a b : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ)
    (x : ComplexEuclidean (k+1)) :
    ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ :=
  (wedge (oneForm a x).toAlternatingMap
    (wedgePowerVariation (extDeriv (oneForm a) x).toAlternatingMap
      (extDeriv (oneForm b) x).toAlternatingMap k)).domDomCongr (boundaryFinEquiv k)

/-- Pointwise parameter derivative of the actual oriented sphere density.
The horizontal term is eliminated; the residual is kept explicit. -/
theorem MassHypotheses.sphere_density_derivative {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G)
    {x : ComplexEuclidean (k+1)} (hx : ‖x‖ = 1) (t : ℝ) :
    HasDerivAt
      (fun s => orientedDensity (sphereFrame k) (sphereVolume k)
        (boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap (k+1)) m s) x) x)
      (orientedDensity (sphereFrame k) (sphereVolume k)
        (boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t)
          (betaLinear (polynomialMap G) (coordinateMap (k+1)) m) x) x) t := by
  obtain ⟨v,hv,hvol⟩ := exists_outward_tangent_frame hx
  let w : Fin 1 ⊕ WedgePowerSlots k → sphereTangent x := fun s =>
    ⟨v (boundaryFinEquiv k s), Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hv _)⟩
  have hxn : x ≠ 0 := by intro he; simp [he] at hx
  have hd := h.sphere_boundaryForm_derivative hxn t w
  have hval (B : ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ) :
      B v = orientedDensity (sphereFrame k) (sphereVolume k) B x := by
    simpa only [hvol, mul_one] using orientedDensity_spec (sphereFrame k)
      (sphereVolume k) (sphereVolume_frame_ne_zero k) B hx v hv
  have he : HasDerivAt
      (fun s => boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap (k+1)) m s) x v)
      (boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+1)) m) x v) t := by
    simp only [boundaryFormFin, boundaryResidualFin,
      AlternatingMap.domDomCongr_apply, tangentForm, ← wedgePower_compLinearMap,
      ← wedgePowerVariation_compLinearMap, ← wedge_compLinearMap,
      AlternatingMap.compLinearMap_apply, Submodule.subtype_apply, w, Function.comp_def] at hd ⊢
    convert hd using 1 <;> rfl
  simpa only [hval] using he

end Mahler

end OAI
