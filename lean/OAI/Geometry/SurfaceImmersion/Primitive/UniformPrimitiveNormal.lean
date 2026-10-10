import OAI.Geometry.SurfaceImmersion.Primitive.UniformLongitudinalProfile
import OAI.Geometry.SurfaceImmersion.Primitive.UniformTransverseProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.LoopCompactNormalMargin
import OAI.Geometry.SurfaceImmersion.Primitive.LocalAnsatzProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceVelocityIdentities

namespace OAI

/-! The same finite coefficients used for the metric expansion preserve
transverse normal acceleration uniformly over a compact low-jet family. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector
open WeightedEstimates NormalFrame
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

def primitiveNormalTriple (f : JetPolynomial.Base → Euclidean) (p : JetPolynomial.Base) :
    VelocityFrame.NormalTriple :=
  ![spaceCoordinates (fderiv ℝ f p (coordinateVector 0)),
    spaceCoordinates (fderiv ℝ f p (coordinateVector 1)),
    spaceCoordinates (fderiv ℝ (fun q => fderiv ℝ f q (coordinateVector 1))
      p (coordinateVector 1))]

lemma geometry_longitudinal_coordinates {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    spaceCoordinates ((l.geometry G hG hGO).longitudinal.val p (t : Period)) =
      VelocityFrame.leadingTangent (slot 1 (lowJet G p)) (slot 2 (lowJet G p))
        (slot 6 (lowJet G p)) (l.velocity (lowJet G p,t)) := by
  rw [LocalPeriodicExpansion.Geometry.longitudinal,Family.add_apply,
    Family.constant_apply _ _ hp,map_add,l.geometry_velocity hG hGO hp,
    l.euclideanVelocity_apply (hGO hp)]
  change spaceCoordinates (JetVelocityCoordinates.toEuclidean (tangent (lowJet G p)))+
    l.velocity (lowJet G p,t) = _
  simp only [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply,
    tangent,normal,VelocityFrame.leadingTangent]

theorem uniform_primitive_normal_triple {S : TopologicalSpace.Opens JetPolynomial.Base}
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
        ‖primitiveNormalTriple (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
            U ℓ (n+1) z) p-
          ![VelocityFrame.leadingTangent (slot 1 (lowJet G p)) (slot 2 (lowJet G p))
            (slot 6 (lowJet G p)) (l.velocity (lowJet G p,ℓ p/z)),
            slot 2 (lowJet G p),slot 6 (lowJet G p)]‖ ≤ D*z/s^loss := by
  obtain ⟨lx,hxb⟩ := l.uniform_longitudinal_profile (S := S) hQ hQO n ℓ hx
  obtain ⟨ly,hyb⟩ := l.uniform_transverse_profiles (S := S) hQ hQO n ℓ hy
  refine ⟨max lx ly,?_⟩
  intro B hB
  obtain ⟨Dx,hDx,hxb⟩ := hxb B hB
  obtain ⟨Dy,hDy,hyb⟩ := hyb B hB
  let D := ‖spaceCoordinates.toContinuousLinearMap‖*(Dx+Dy)
  refine ⟨D,mul_nonneg (norm_nonneg _) (add_nonneg hDx hDy),?_⟩
  intro G hG hGQ s z hz hzs hs1 hb U hU hrep hinit p hp
  have hs : 0 < s := hz.trans_le hzs
  have hGO : MapsTo (lowJet G) S O := fun _ hq => hQO (hGQ hq)
  let F := fun q => JetVelocityCoordinates.toEuclidean (G q)
  let f := finiteAnsatz F U ℓ (n+1) z
  let g := l.geometry G hG hGO
  have hbound (C : ℝ) (hC : 0 ≤ C) (hC' : C ≤ Dx+Dy)
      (d : ℕ) (hd : d ≤ max lx ly) : C*z/s^d ≤ (Dx+Dy)*z/s^(max lx ly) := by
    calc
      _ ≤ C*z/s^(max lx ly) := div_le_div_of_nonneg_left (mul_nonneg hC hz.le)
        (pow_pos hs _) (pow_le_pow_of_le_one hs.le hs1 hd)
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hz.le)
        (pow_nonneg hs.le _)
  have hxerr := (hxb G hG hGQ s z hz hzs hs1 hb U hU hrep p hp).trans
    (hbound Dx hDx (by linarith) lx (le_max_left _ _))
  obtain ⟨hyerr,hyyerr⟩ := hyb G hG hGQ s z hz hzs hs1 hb U hU hrep p hp
  have hdy := hbound Dy hDy (by linarith) ly (le_max_right _ _)
  replace hyerr := hyerr.trans hdy
  replace hyyerr := hyyerr.trans hdy
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
  have hy0 : PeriodicExpansion.directionalMap F (coordinateVector 1) =
      fun q => JetVelocityCoordinates.toEuclidean (slot 2 (lowJet G q)) := by
    funext q
    exact euclidean_first_derivative hG 1 q
  rw [hy0] at hyerr hyyerr
  change ‖PeriodicExpansion.directionalMap f (coordinateVector 1) p-
    JetVelocityCoordinates.toEuclidean (slot 2 (lowJet G p))‖ ≤ _ at hyerr
  change ‖PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 1))
    (coordinateVector 1) p-fderiv ℝ (fun q =>
      JetVelocityCoordinates.toEuclidean (slot 2 (lowJet G q))) p (coordinateVector 1)‖ ≤ _ at hyyerr
  rw [euclidean_y_derivative hG] at hyyerr
  have hcoord {u v : Euclidean} (he : ‖u-v‖ ≤ (Dx+Dy)*z/s^(max lx ly)) :
      ‖spaceCoordinates u-spaceCoordinates v‖ ≤ D*z/s^(max lx ly) := by
    calc
      _ = ‖spaceCoordinates (u-v)‖ := by rw [map_sub]
      _ ≤ ‖spaceCoordinates.toContinuousLinearMap‖*‖u-v‖ :=
        spaceCoordinates.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖spaceCoordinates.toContinuousLinearMap‖*((Dx+Dy)*z/s^(max lx ly)) :=
        mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = _ := by dsimp [D]; ring
  have hxc := hcoord hxerr
  rw [l.geometry_longitudinal_coordinates hG hGO hp] at hxc
  have hyc := hcoord hyerr
  have hyyc := hcoord hyyerr
  simp only [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply] at hyc hyyc
  refine (pi_norm_le_iff_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _)
    (add_nonneg hDx hDy)) hz.le) (pow_nonneg hs.le _))).mpr ?_
  intro k
  fin_cases k
  · exact hxc
  · exact hyc
  · exact hyyc

theorem uniform_primitive_normal_geometry {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hx : ℓ (coordinateVector 0) = 1) (hy : ℓ (coordinateVector 1) = 0) :
    ∃ loss : ℕ, ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGQ : MapsTo (lowJet G) S Q),
      ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s ((2*n+2)+2) B (lowJet G) → D*z/s^loss < ε →
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        U 0 = (l.geometry G hG (fun _ hp => hQO (hGQ hp))).initial →
      ∀ p ∈ S,
        let H := primitiveNormalTriple (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
          U ℓ (n+1) z) p
        gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖realNormalPart (H 0) (H 1) (H 2)‖ := by
  obtain ⟨loss,hb⟩ := l.uniform_primitive_normal_triple (S := S) hQ hQO n ℓ hx hy
  obtain ⟨ε,c,hε,hc,hn⟩ := l.compact_normal_margin hQ hQO
  refine ⟨loss,ε,c,hε,hc,?_⟩
  intro B hB
  obtain ⟨D,hD,hd⟩ := hb B hB
  refine ⟨D,hD,?_⟩
  intro G hG hGQ s z hz hzs hs1 hbound hsmall U hU hrep hinit p hp
  exact hn _ (hGQ hp) (ℓ p/z) _
    ((hd G hG hGQ s z hz hzs hs1 hbound U hU hrep hinit p hp).trans_lt hsmall)

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
