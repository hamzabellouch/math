import OAI.Geometry.SurfaceImmersion.Primitive.LocalAnsatzProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceVelocityIdentities
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicNormalStability

namespace OAI

/-! Nonzero normal geometry for the actual supported finite periodic ansatz. -/

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion NormalFrame
local notation "ι" => JetVelocityCoordinates.toEuclidean

private lemma coordinate_sub_bound (u v : Euclidean) :
    ‖spaceCoordinates u-spaceCoordinates v‖ ≤
      ‖spaceCoordinates.toContinuousLinearMap‖*‖u-v‖ := by
  rw [← map_sub]
  exact spaceCoordinates.toContinuousLinearMap.le_opNorm _

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)
  {S : TopologicalSpace.Opens JetPolynomial.Base}
  {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
  (hGO : MapsTo (lowJet G) S O)

private lemma geometry_leading_tangent {p : JetPolynomial.Base} (hp : p ∈ S)
    (t : Period) :
    spaceCoordinates ((l.geometry G hG hGO).longitudinal.val p t) =
      VelocityFrame.leadingTangent (slot 1 (lowJet G p)) (slot 2 (lowJet G p))
        (slot 6 (lowJet G p))
        (spaceCoordinates ((l.geometry G hG hGO).V.val p t)) := by
  rw [LocalPeriodicExpansion.Geometry.longitudinal,Family.add_apply,
    Family.constant_apply _ _ hp,map_add]
  change spaceCoordinates (ι (tangent (lowJet G p)))+
    spaceCoordinates ((l.geometry G hG hGO).V.val p t) = _
  simp only [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply,
    tangent,normal,VelocityFrame.leadingTangent]

/-- The compact normal margin applies to the same finite ansatz whose
coefficients and metric were constructed. Its fast xx derivative need not be
bounded: the geometry is already detected by x, y and yy. -/
theorem compact_ansatz_normal_geometry
    (U : ℕ → Family S Euclidean)
    (hU : ∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ =>
      (U i).val y.1 (y.2 : Period)))
    (hinit : U 0 = (l.geometry G hG hGO).initial)
    {Q : Set JetPolynomial.Base} (hQ : IsCompact Q) (hQS : Q ⊆ S)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hx : ℓ (coordinateVector 0) = 1) (hy : ℓ (coordinateVector 1) = 0) (n : ℕ) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ z : ℝ, 0 < z → z < η → ∀ p ∈ Q,
      let f := finiteAnsatz (fun q => ι (G q)) U ℓ (n+1) z
      let x := spaceCoordinates (fderiv ℝ f p (coordinateVector 0))
      let y := spaceCoordinates (fderiv ℝ f p (coordinateVector 1))
      let b := spaceCoordinates (fderiv ℝ
        (fun q => fderiv ℝ f q (coordinateVector 1)) p (coordinateVector 1))
      NormalFrame.gramDet x y ≠ 0 ∧ c < ‖realNormalPart x y b‖ := by
  let g := l.geometry G hG hGO
  let F : JetPolynomial.Base → Euclidean := fun p => ι (G p)
  have hF : ContDiff ℝ ∞ F := JetVelocityCoordinates.toEuclidean.contDiff.comp hG
  obtain ⟨N,hN,hn⟩ := g.compact_initial_ansatz_profiles hF U hU hinit hQ hQS
    ℓ (coordinateVector 0) hx hy
    (fun p hp => l.geometry_dx hG hGO hp)
    (fun p _ => l.geometry_dy hG hGO p) n
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let X : Q → NormalFrame.Vec := fun p => slot 1 (lowJet G p)
  let Y : Q → NormalFrame.Vec := fun p => slot 2 (lowJet G p)
  let C : Q → NormalFrame.Vec := fun p => slot 6 (lowJet G p)
  let V : Q → C(Period,NormalFrame.Vec) := fun p =>
    ⟨fun t => spaceCoordinates (g.V.val p t),
      spaceCoordinates.continuous.comp (g.V.val p).continuous⟩
  have hX : Continuous X :=
    ((slot_smooth 1).comp (lowJet_smooth hG)).continuous.comp continuous_subtype_val
  have hY : Continuous Y :=
    ((slot_smooth 2).comp (lowJet_smooth hG)).continuous.comp continuous_subtype_val
  have hC : Continuous C :=
    ((slot_smooth 6).comp (lowJet_smooth hG)).continuous.comp continuous_subtype_val
  have hYval (p : Q) : Y p = spaceCoordinates (g.Y p) := by
    change slot 2 (lowJet G p) = spaceCoordinates (ι (slot 2 (lowJet G p)))
    simp only [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
  have hCval (p : Q) : C p = spaceCoordinates (g.C p) := by
    change slot 6 (lowJet G p) = spaceCoordinates (ι (slot 6 (lowJet G p)))
    simp only [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
  have hV : Continuous (fun p : Q × ℝ => V p.1 (p.2 : Period)) := by
    have hi : Continuous (fun p : Q × ℝ => ((p.1 : JetPolynomial.Base),p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hm : ∀ p : Q × ℝ, ((p.1 : JetPolynomial.Base),p.2) ∈
        (S : Set JetPolynomial.Base) ×ˢ (univ : Set ℝ) :=
      fun p => ⟨hQS p.1.property,mem_univ _⟩
    exact spaceCoordinates.continuous.comp (g.V.smooth.continuousOn.comp_continuous hi hm)
  have hD : ∀ p ∈ (univ : Set Q), NormalFrame.gramDet (Y p) (C p) ≠ 0 := by
    intro p _
    exact l.gram_ne _ (hGO (hQS p.property))
  have hYV : ∀ p ∈ (univ : Set Q), ∀ t : Period, Y p ⬝ᵥ V p t = 0 := by
    intro p _ t
    rw [hYval p]
    change spaceCoordinates (g.Y p) ⬝ᵥ spaceCoordinates (g.V.val p t) = 0
    rw [spaceCoordinates_dot]
    exact g.perpY p (hQS p.property) _ (g.V_mem p (hQS p.property) t)
  have hCV : ∀ p ∈ (univ : Set Q), ∀ t : Period, C p ⬝ᵥ V p t = 0 := by
    intro p _ t
    rw [hCval p]
    change spaceCoordinates (g.C p) ⬝ᵥ spaceCoordinates (g.V.val p t) = 0
    rw [spaceCoordinates_dot]
    exact g.perpC p (hQS p.property) _ (g.V_mem p (hQS p.property) t)
  have hV0 : ∀ p ∈ (univ : Set Q), ∀ t : Period, V p t ≠ 0 := by
    intro p _ t hz
    change spaceCoordinates (g.V.val p t) = 0 at hz
    have hv : g.V.val p t = 0 := spaceCoordinates.injective (by simpa only [map_zero] using hz)
    have he := g.circle p (hQS p.property) t
    rw [hv,inner_zero_left] at he
    exact (ne_of_gt (g.q_pos p (hQS p.property))) he.symm
  let D : ℝ := ‖spaceCoordinates.toContinuousLinearMap‖*N
  have hD0 : 0 ≤ D := mul_nonneg (norm_nonneg _) hN
  obtain ⟨η,c,hη,hc,hh⟩ := VelocityFrame.periodic_normal_stability_of_linear_error
    (isCompact_univ : IsCompact (univ : Set Q)) hX hY hC V hV hD hYV hCV hV0 D hD0
  refine ⟨min 1 η,c,lt_min zero_lt_one hη,hc,?_⟩
  intro z hz hzsmall p hp
  let pQ : Q := ⟨p,hp⟩
  have hz1 : z ≤ 1 := (lt_of_lt_of_le hzsmall (min_le_left _ _)).le
  obtain ⟨hyerr,hberr,hxerr,_,_⟩ := hn z hz hz1 p hp
  let f := finiteAnsatz F U ℓ (n+1) z
  let x := spaceCoordinates (fderiv ℝ f p (coordinateVector 0))
  let y := spaceCoordinates (fderiv ℝ f p (coordinateVector 1))
  let b := spaceCoordinates (fderiv ℝ
    (fun q => fderiv ℝ f q (coordinateVector 1)) p (coordinateVector 1))
  have hbnd {u v : Euclidean} (huv : ‖u-v‖ ≤ N*z) :
      ‖spaceCoordinates u-spaceCoordinates v‖ ≤ D*z := by
    exact (coordinate_sub_bound u v).trans
      ((mul_le_mul_of_nonneg_left huv (norm_nonneg _)).trans_eq (by dsimp [D]; ring))
  have hx' : ‖x-VelocityFrame.leadingTangent (X pQ) (Y pQ) (C pQ)
      (V pQ ((ℓ p/z : ℝ) : Period))‖ ≤ D*z := by
    change ‖x-VelocityFrame.leadingTangent (slot 1 (lowJet G p))
      (slot 2 (lowJet G p)) (slot 6 (lowJet G p))
      (spaceCoordinates ((l.geometry G hG hGO).V.val p ((ℓ p/z : ℝ) : Period)))‖ ≤ D*z
    rw [← l.geometry_leading_tangent hG hGO (hQS hp)]
    exact hbnd hxerr
  have hy' : ‖y-Y pQ‖ ≤ D*z := by
    rw [hYval]
    exact hbnd hyerr
  have hb' : ‖b-C pQ‖ ≤ D*z := by
    rw [hCval]
    exact hbnd hberr
  exact hh z hz (lt_of_lt_of_le hzsmall (min_le_right _ _)) pQ (mem_univ _)
    (ℓ p/z) x y b hx' hy' hb'

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
