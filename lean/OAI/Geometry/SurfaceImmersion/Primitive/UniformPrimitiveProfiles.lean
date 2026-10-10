import OAI.Geometry.SurfaceImmersion.Primitive.UniformPrimitiveNormal
import OAI.Geometry.SurfaceImmersion.Primitive.UniformMixedProfile
import OAI.Geometry.SurfaceImmersion.Primitive.UniformScaledLongitudinalProfile

namespace OAI

/-! All five actual derivative profiles share a loss fixed before the slow
map. The leading profiles are the geometric velocity and its derivatives. -/
noncomputable section
open Set
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

def primitiveJetProfile (f : JetPolynomial.Base → Euclidean) (z : ℝ)
    (p : JetPolynomial.Base) : Fin 5 → Euclidean :=
  ![PeriodicExpansion.directionalMap f (coordinateVector 0) p,
    PeriodicExpansion.directionalMap f (coordinateVector 1) p,
    PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 1))
      (coordinateVector 1) p,
    PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 0))
      (coordinateVector 1) p,
    z • PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 0))
      (coordinateVector 0) p]

theorem uniform_primitive_five_profiles {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hx : ℓ (coordinateVector 0) = 1) (hy : ℓ (coordinateVector 1) = 0) :
    ∃ loss : ℕ, ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGQ : MapsTo (lowJet G) S Q),
      ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s ((2*n+2)+2) B (lowJet G) →
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        U 0 = (l.geometry G hG (fun _ hp => hQO (hGQ hp))).initial →
      ∀ p ∈ S,
        let g := l.geometry G hG (fun _ hp => hQO (hGQ hp))
        let t : Period := ((ℓ p/z : ℝ) : Period)
        ‖primitiveJetProfile (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
            U ℓ (n+1) z) z p-
          ![g.longitudinal.val p t,g.Y p,g.C p,
            (g.longitudinal.slow (coordinateVector 1)).val p t,g.V.angle.val p t]‖ ≤ D*z/s^loss := by
  obtain ⟨lx,hxb⟩ := l.uniform_longitudinal_profile (S := S) hQ hQO n ℓ hx
  obtain ⟨ly,hyb⟩ := l.uniform_transverse_profiles (S := S) hQ hQO n ℓ hy
  obtain ⟨lm,hmb⟩ := l.uniform_mixed_profile (S := S) hQ hQO n ℓ hx hy
  obtain ⟨la,hab⟩ := l.uniform_scaled_longitudinal_profile (S := S) hQ hQO n ℓ hx
  let loss := max (max lx ly) (max lm la)
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨Dx,hDx,hxbound⟩ := hxb B hB
  obtain ⟨Dy,hDy,hybound⟩ := hyb B hB
  obtain ⟨Dm,hDm,hmbound⟩ := hmb B hB
  obtain ⟨Da,hDa,habound⟩ := hab B hB
  let D := Dx+Dy+Dm+Da
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro G hG hGQ s z hz hzs hs1 hb U hU hrep hinit p hp
  have hs : 0 < s := hz.trans_le hzs
  have hbound (C : ℝ) (hC : 0 ≤ C) (hCD : C ≤ D) (d : ℕ) (hd : d ≤ loss) :
      C*z/s^d ≤ D*z/s^loss := by
    exact (div_le_div_of_nonneg_left (mul_nonneg hC hz.le) (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 hd)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCD hz.le) (pow_nonneg hs.le _))
  have hxd : lx ≤ loss := (le_max_left lx ly).trans (le_max_left _ _)
  have hyd : ly ≤ loss := (le_max_right lx ly).trans (le_max_left _ _)
  have hmd : lm ≤ loss := (le_max_left lm la).trans (le_max_right _ _)
  have had : la ≤ loss := (le_max_right lm la).trans (le_max_right _ _)
  have hxerr := (hxbound G hG hGQ s z hz hzs hs1 hb U hU hrep p hp).trans
    (hbound Dx hDx (by dsimp [D]; linarith) lx hxd)
  obtain ⟨hyerr,hyyerr⟩ := hybound G hG hGQ s z hz hzs hs1 hb U hU hrep p hp
  have hdy := hbound Dy hDy (by dsimp [D]; linarith) ly hyd
  replace hyerr := hyerr.trans hdy
  replace hyyerr := hyyerr.trans hdy
  have hmerr := (hmbound G hG hGQ s z hz hzs hs1 hb U hU hrep p hp).trans
    (hbound Dm hDm (by dsimp [D]; linarith) lm hmd)
  have haerr := (habound G hG hGQ s z hz hzs hs1 hb U hU hrep p hp).trans
    (hbound Da hDa (by dsimp [D]; linarith) la had)
  let F := fun q => JetVelocityCoordinates.toEuclidean (G q)
  have hFs : ContDiff ℝ ∞ F := JetVelocityCoordinates.toEuclidean.contDiff.comp hG
  have hGO : MapsTo (lowJet G) S O := fun _ hq => hQO (hGQ hq)
  let g := l.geometry G hG hGO
  let W := globalCoefficients U hU
  have hW : (W 0).val = g.initial.val := by
    change (U 0).val = g.initial.val
    rw [hinit]
  have hx0 := g.initial_global_longitudinal (W 0) hW (coordinateVector 0)
    (fun q hq => l.geometry_dx hG hGO hq) hp ((ℓ p/z : ℝ) : Period)
  rw [global_angle_eq_local (W 0) (U 0) rfl hp] at hx0
  change PeriodicExpansion.directionalMap F (coordinateVector 0) p+
    (U 0).angle.fastValue ℓ z p = g.longitudinal.val p ((ℓ p/z : ℝ) : Period) at hx0
  rw [hx0] at hxerr
  have hy0 : PeriodicExpansion.directionalMap F (coordinateVector 1) =ᶠ[𝓝 p] g.Y := by
    filter_upwards [S.isOpen.mem_nhds hp] with q hq
    exact l.geometry_dy hG hGO q
  have hyy0 : PeriodicExpansion.directionalMap
      (PeriodicExpansion.directionalMap F (coordinateVector 1)) (coordinateVector 1) p = g.C p :=
    (congrArg (fun L : JetPolynomial.Base →L[ℝ] Euclidean => L (coordinateVector 1))
      hy0.fderiv_eq).trans (g.derivativeY p hp)
  rw [hy0.eq_of_nhds] at hyerr
  rw [hyy0] at hyyerr
  have hm0 := g.initial_global_longitudinal_slow hFs (W 0) hW (coordinateVector 0)
    (fun q hq => l.geometry_dx hG hGO hq) hp (ℓ p/z)
  rw [global_slow_eq_local_of_eqOn (W 0).angle (U 0).angle
    (fun q hq t => global_angle_eq_local (W 0) (U 0) rfl hq t) (coordinateVector 1) hp] at hm0
  change PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap F (coordinateVector 0))
    (coordinateVector 1) p+((U 0).angle.slow (coordinateVector 1)).fastValue ℓ z p = _ at hm0
  rw [hm0] at hmerr
  have ha0 := g.initial_global_angle_angle (W 0) hW hp ((ℓ p/z : ℝ) : Period)
  have haLocal : (W 0).angle.angle.val p ((ℓ p/z : ℝ) : Period) =
      (U 0).angle.angle.val p ((ℓ p/z : ℝ) : Period) :=
    global_second_coefficientDerivative_eq_local (W 0) (U 0) rfl 2 2 hp _
  rw [haLocal] at ha0
  change (U 0).angle.angle.fastValue ℓ z p = _ at ha0
  rw [ha0] at haerr
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (mul_nonneg hD hz.le) (pow_nonneg hs.le _))).mpr
  intro k
  fin_cases k
  · exact hxerr
  · exact hyerr
  · exact hyyerr
  · exact hmerr
  · exact haerr

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
