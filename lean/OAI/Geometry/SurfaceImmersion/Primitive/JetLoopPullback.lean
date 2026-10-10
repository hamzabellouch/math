import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceVelocityFamily
import OAI.Geometry.SurfaceImmersion.Primitive.GeometricJetVelocity

namespace OAI

/-! Transfer the constructed geometric loop to the ordered coordinate jets
used by the quantitative finite correction. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates SurfaceJetCoordinates

def jetDomain (Ω : TopologicalSpace.Opens CollarVelocity.JetBase) :
    TopologicalSpace.Opens LowJet :=
  ⟨decode ⁻¹' Ω, Ω.isOpen.preimage decode_smooth.continuous⟩

/-- The velocity supplied by the geometric construction, expressed in the
analytic second-jet coordinates. All its identities survive this pullback. -/
def Loop.ofGeometric {Ω : TopologicalSpace.Opens CollarVelocity.JetBase}
    {a : CollarVelocity.JetBase → ℝ} {V : CollarVelocity.JetBase × ℝ → RVec 4}
    (ha : ContDiffOn ℝ ∞ a Ω) (hV : ContDiffOn ℝ ∞ V (Ω ×ˢ univ))
    (hper : ∀ j ∈ Ω, Function.Periodic (fun t => V (j, t)) 1)
    (hD : ∀ j ∈ Ω, NormalFrame.gramDet (j.2 1) (j.2 4) ≠ 0)
    (hn : ∀ j ∈ Ω, realNormalPart (j.2 1) (j.2 4) (j.2 0) ≠ 0 ∨ a j ≠ 0)
    (hy : ∀ j ∈ Ω, ∀ t, j.2 1 ⬝ᵥ V (j, t) = 0)
    (hc : ∀ j ∈ Ω, ∀ t, j.2 4 ⬝ᵥ V (j, t) = 0)
    (hlen : ∀ j ∈ Ω, ∀ t, V (j, t) ⬝ᵥ V (j, t) =
      realNormalPart (j.2 1) (j.2 4) (j.2 0) ⬝ᵥ
        realNormalPart (j.2 1) (j.2 4) (j.2 0) + a j ^ 2)
    (hm : ∀ j ∈ Ω, (∫ t in 0..1, V (j, t)) = realNormalPart (j.2 1) (j.2 4) (j.2 0)) :
    Loop (jetDomain Ω) where
  amplitude := a ∘ decode
  smoothAmplitude := ha.comp decode_smooth.contDiffOn (fun _ hJ => hJ)
  velocity z := V (decode z.1, z.2)
  smoothVelocity := hV.comp
    ((decode_smooth.contDiffOn.comp contDiffOn_fst (fun z _ => mem_univ z.1)).prodMk
      contDiffOn_snd) (fun _ hz => ⟨hz.1, hz.2⟩)
  periodic J hJ := hper (decode J) hJ
  gram_ne J hJ := hD (decode J) hJ
  nonzero J hJ := hn (decode J) hJ
  perpY J hJ := hy (decode J) hJ
  perpC J hJ := hc (decode J) hJ
  length J hJ := hlen (decode J) hJ
  mean J hJ := hm (decode J) hJ

lemma actual_jet_mem {Ω : TopologicalSpace.Opens CollarVelocity.JetBase}
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {p : JetPolynomial.Base}
    (hp : CollarVelocity.jetSection F (baseEquiv p) ∈ Ω) :
    lowJet (F ∘ baseEquiv) p ∈ jetDomain Ω := by
  change decode (lowJet (F ∘ baseEquiv) p) ∈ Ω
  rwa [decode_lowJet hF]

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
