import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceCircularThreshold
import OAI.Geometry.SurfaceImmersion.Primitive.CircularSectionProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.SpatialLoopAmplitude

namespace OAI

/-! The constructed real surface profile is exactly the analytic loop's
five-profile map, including its transverse mixed derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation SurfaceJetCoordinates
open JetVelocityCoordinates

lemma actual_circular_geometric_profile {F : SmallModes.Base → Vec} (hF : ContDiff ℝ ∞ F)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {Z : TopologicalSpace.Opens GeometricJet} {O : TopologicalSpace.Opens JetPolynomial.LowJet}
    (hOZ : (O : Set JetPolynomial.LowJet) ⊆ jetDomain Z) (l : Loop O)
    (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    (hGO : MapsTo (JetPolynomial.lowJet (F ∘ baseEquiv)) S O)
    {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    boundaryProfileMap (l.geometricLeadingProfile (F ∘ baseEquiv) (hF.comp baseEquiv.contDiff)
      hGO p (t : CovarianceCorrector.Period)) =
      surfaceCircularProfile F a e₁ e₂ α (baseEquiv p,t) := by
  let σ := JetPolynomial.lowJet (F ∘ baseEquiv)
  let R₀ : JetPolynomial.LowJet → ℝ := fun J => velocityRadius (normal J) (a (decode J).1)
  have hA : ContDiff ℝ ∞ (fun J : JetPolynomial.LowJet => a (decode J).1) :=
    ha.comp (contDiff_fst.comp decode_smooth)
  have hR₀ : ContDiffOn ℝ ∞ R₀ O := velocityRadius_smoothOn l.smoothNormal hA.contDiffOn (by
    intro J hJ
    have hh := l.nonzero J hJ
    rw [hamp J hJ] at hh
    exact hh)
  have he₁ := h₁.comp decode_smooth.contDiffOn hOZ
  have he₂ := h₂.comp decode_smooth.contDiffOn hOZ
  have hα₀ : ContDiffOn ℝ ∞ (fun z : JetPolynomial.LowJet × ℝ => α (decode z.1,z.2))
      (O ×ˢ univ) := hα.comp ((decode_smooth.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
        (fun _ hz => ⟨hOZ hz.1,hz.2⟩)
  rw [l.circular_geometricLeadingProfile hR₀ he₁ he₂ hα₀ hvel
    (hF.comp baseEquiv.contDiff) hGO hp t]
  let X := coordDeriv dx F
  let Y := coordDeriv dy F
  let C := coordDeriv dy (coordDeriv dy F)
  let v : SmallModes.Base → Vec := fun x => jetNormal (CollarVelocity.jetSection F x)
  let Q := X-v
  let R : SmallModes.Base → ℝ := fun x => velocityRadius (v x) (a x)
  let E₁ := e₁ ∘ CollarVelocity.jetSection F
  let E₂ := e₂ ∘ CollarVelocity.jetSection F
  let β : SmallModes.Base × ℝ → ℝ := fun z => α (CollarVelocity.jetSection F z.1,z.2)
  have hq : tangent ∘ σ = Q ∘ baseEquiv := by
    funext x
    change (decode (σ x)).2 0 - jetNormal (decode (σ x)) = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have hx : (slot 1) ∘ σ = X ∘ baseEquiv := by
    funext x
    change (decode (σ x)).2 0 = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have hy : (slot 2) ∘ σ = Y ∘ baseEquiv := by
    funext x
    change (decode (σ x)).2 1 = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have hc : (slot 6) ∘ σ = C ∘ baseEquiv := by
    funext x
    change (decode (σ x)).2 4 = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have hr : R₀ ∘ σ = R ∘ baseEquiv := by
    funext x
    change velocityRadius (jetNormal (decode (σ x))) (a (decode (σ x)).1) = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have he1 : (e₁ ∘ decode) ∘ σ = E₁ ∘ baseEquiv := by
    funext x
    exact congrArg e₁ (decode_lowJet hF x)
  have he2 : (e₂ ∘ decode) ∘ σ = E₂ ∘ baseEquiv := by
    funext x
    exact congrArg e₂ (decode_lowJet hF x)
  have hb : (fun z : JetPolynomial.Base × ℝ => α (decode (σ z.1),z.2)) =
      fun z => β (baseEquiv z.1,z.2) := by
    funext z
    rw [show decode (σ z.1) = CollarVelocity.jetSection F (baseEquiv z.1) from decode_lowJet hF z.1]
  change circularFamilyProfile (tangent ∘ σ) ((slot 1) ∘ σ) ((slot 2) ∘ σ) ((slot 6) ∘ σ)
    (R₀ ∘ σ) ((e₁ ∘ decode) ∘ σ) ((e₂ ∘ decode) ∘ σ)
    (fun z => α (decode (σ z.1),z.2)) (JetPolynomial.coordinateVector 1) (p,t) = _
  rw [hq,hx,hy,hc,hr,he1,he2,hb]
  have hJ := hGO hp
  have hZp : CollarVelocity.jetSection F (baseEquiv p) ∈ Z := by
    rw [← decode_lowJet hF p]
    exact hOZ hJ
  have hD : gramDet (Y (baseEquiv p)) (C (baseEquiv p)) ≠ 0 := by
    have hh := l.gram_ne _ hJ
    change gramDet ((decode (σ p)).2 1) ((decode (σ p)).2 4) ≠ 0 at hh
    rw [show decode (σ p) = CollarVelocity.jetSection F (baseEquiv p) from decode_lowJet hF p] at hh
    exact hh
  have hv : ContDiffAt ℝ ∞ v (baseEquiv p) :=
    contDiffAt_realNormalPart (contDiff_real_coordDeriv hF dy).contDiffAt
      (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy).contDiffAt
      (contDiff_real_coordDeriv hF dx).contDiffAt hD
  have hn : v (baseEquiv p) ≠ 0 ∨ a (baseEquiv p) ≠ 0 := by
    have hh := l.nonzero _ hJ
    rw [hamp _ hJ] at hh
    change jetNormal (decode (σ p)) ≠ 0 ∨ a (baseEquiv p) ≠ 0 at hh
    rw [show decode (σ p) = CollarVelocity.jetSection F (baseEquiv p) from decode_lowJet hF p] at hh
    exact hh
  have hdot : ContDiffAt ℝ ∞ (fun x => v x ⬝ᵥ v x) (baseEquiv p) :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hR : ContDiffAt ℝ ∞ R (baseEquiv p) :=
    (hdot.add (ha.contDiffAt.pow 2)).sqrt (Real.sqrt_pos.mp (velocityRadius_pos hn)).ne'
  have hσ := CollarVelocity.jetSection_smooth hF
  have hE1 := (h₁.contDiffAt (Z.isOpen.mem_nhds hZp)).comp _ hσ.contDiffAt
  have hE2 := (h₂.contDiffAt (Z.isOpen.mem_nhds hZp)).comp _ hσ.contDiffAt
  have hβ : ContDiffAt ℝ ∞ β (baseEquiv p,t) :=
    (hα.contDiffAt ((Z.isOpen.prod isOpen_univ).mem_nhds ⟨hZp,mem_univ t⟩)).comp _
      ((hσ.comp contDiff_fst).prodMk contDiff_snd).contDiffAt
  rw [circularFamilyProfile_comp (Q := Q) (X := X) (Y := Y) (C := C) (R := R)
    (e₁ := E₁) (e₂ := E₂) (α := β) baseEquiv.differentiableAt
    (((contDiff_real_coordDeriv hF dx).contDiffAt.sub hv).differentiableAt (by simp))
    (hR.differentiableAt (by simp)) (hE1.differentiableAt (by simp))
    (hE2.differentiableAt (by simp)) (hβ.differentiableAt (by simp)),baseEquiv.fderiv]
  have hd : baseEquiv.toContinuousLinearMap (JetPolynomial.coordinateVector 1) = dy := baseEquiv_one
  rw [hd]
  rfl

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
