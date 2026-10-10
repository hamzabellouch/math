import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure
import OAI.Probability.CriticalPercolation.GraphGeometry.EuclideanEllipse
import OAI.Probability.CriticalPercolation.GraphGeometry.MovingStrips
import OAI.Probability.CriticalPercolation.Gluing.EllipseMoves
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseOrigin
import OAI.Probability.CriticalPercolation.Gluing.ApproximateMoveEndgame
import OAI.Probability.CriticalPercolation.Modular.MoveTransport

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma ellipse_aut_differences (pi : V → ℂ) (R W : ℝ) (c d e : Circle) (phi : G.Aut)
    (hphi : ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y) :
    (∀ x y, ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex x)-
      ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex y)=
      ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e x-
      ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e y) ∧
    (∀ x y, ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex x)-
      ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex y)=
      ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e x-
      ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e y) := by
  have hPsi : ∀ x y,
      EuclideanEllipse.normalize R W c (pi (phi.vertex x))-EuclideanEllipse.normalize R W c (pi (phi.vertex y))=
      EuclideanEllipse.normalize R W c (pi x)-EuclideanEllipse.normalize R W c (pi y) := by
    intro x y
    rw [←EuclideanEllipse.normalize_sub,←EuclideanEllipse.normalize_sub,hphi]
  constructor
  · intro x y
    rw [(ellipse_coordinates_sub _ d e (phi.vertex x) (phi.vertex y)).1,
      (ellipse_coordinates_sub _ d e x y).1]
    exact congrArg (fun z : ℂ => EllipseLinear.time (d : ℂ).re (d : ℂ).im (e : ℂ).re (e : ℂ).im z.re z.im) (hPsi x y)
  · intro x y
    rw [(ellipse_coordinates_sub _ d e (phi.vertex x) (phi.vertex y)).2,
      (ellipse_coordinates_sub _ d e x y).2]
    exact congrArg (fun z : ℂ => EllipseLinear.height (d : ℂ).re (d : ℂ).im (e : ℂ).re (e : ℂ).im z.re z.im) (hPsi x y)

theorem ellipse_uniform_moves [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (pi : V → ℂ) (o : V) (c : ℕ) (D : ℝ) (pc : unitInterval)
    (hD : 0≤D) (hpc : 0<pc) (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (hdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
      ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y)
    (hone : BernoulliProduct.law (fun _ : E => pc) G.percolates=1)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => pc), ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      BernoulliProduct.law (fun _ : E => pc)
        (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0<rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
      (pc : ℝ)/2≤p ∧ p<pc ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y → |t x-t y|≤rho) ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y → |z x-z y|≤rho) ∧
      ∀ y s, |s|=1 → 1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
        (G.coordinateMove t z m eps y s) := by
  obtain ⟨m,hm⟩ := G.ellipse_origin_moves hc hl pi o D pc hD hpo hpi hone hbox hnull eps eta heps heps' heta
  refine ⟨m+c,?_⟩
  intro rho hrho
  let r := min rho (eps/(8*((c : ℝ)+1)))
  have hr : 0<r := lt_min hrho (div_pos heps (by positivity))
  have hrrho : r≤rho := min_le_left _ _
  have hrs : r≤eps/(8*((c : ℝ)+1)) := min_le_right _ _
  have hmesh : (c : ℝ)*r≤eps/8 := by
    have hh := (le_div_iff₀ (by positivity : 0<8*((c : ℝ)+1))).mp hrs
    nlinarith
  obtain ⟨R,W,a,b,d,ht,hz,hmoves⟩ := hm r hr
  let t := ellipseTime (EuclideanEllipse.normalize R W a ∘ pi) b d
  let z := ellipseHeight (EuclideanEllipse.normalize R W a ∘ pi) b d
  have htdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
      (∀ x y, t (phi.vertex x)-t (phi.vertex y)=t x-t y) ∧
      (∀ x y, z (phi.vertex x)-z (phi.vertex y)=z x-z y) := by
    intro y
    obtain ⟨phi,hphi,hphiP⟩ := hdense y
    exact ⟨phi,hphi,G.ellipse_aut_differences pi R W a b d phi hphiP⟩
  obtain ⟨p,hpl,hpu,hp⟩ := G.uniform_moves_of_origin t z o m c eps eta r heps' hr.le hmesh ht hz htdense pc hpc hmoves
  exact ⟨t,z,p,hpl,hpu,fun {_ _} h => (ht h).trans hrrho,fun {_ _} h => (hz h).trans hrrho,hp⟩

theorem ellipse_critical_contradiction [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (pi : V → ℂ) (o : V) (c : ℕ) (D : ℝ)
    (hD : 0≤D) (hpc : 0<(G.criticalProbability : ℝ)) (hpc1 : (G.criticalProbability : ℝ)<1)
    (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (hdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
      ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y)
    (hone : BernoulliProduct.law (fun _ : E => G.criticalProbability) G.percolates=1)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability), ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      BernoulliProduct.law (fun _ : E => G.criticalProbability)
        (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0) : False := by
  apply G.approximate_moves_contradiction hc hl hq hpc hpc1
  intro eps eta he he' heta _heta'
  exact G.ellipse_uniform_moves hc hl pi o c D G.criticalProbability hD hpc hpo hpi hdense hone hbox hnull eps eta he he' heta

end CriticalPercolation.BondGraph
end
end
end

end OAI
