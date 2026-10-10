import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.StripOrigin
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseExit
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseSeparation
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseSeed
import OAI.Probability.CriticalPercolation.Gluing.EllipseMoves
import OAI.Probability.CriticalPercolation.ProductMeasure.EllipseProbability

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem ellipse_origin_moves [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (pi : V → ℂ) (o : V) (D : ℝ) (pc : unitInterval)
    (hD : 0≤D) (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (hone : BernoulliProduct.law (fun _ : E => pc) G.percolates=1)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => pc), ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      BernoulliProduct.law (fun _ : E => pc)
        (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0<rho → ∃ R W : ℝ, ∃ c d e : Circle,
      (∀ ⦃x y⦄, G.fullGraph.Adj x y →
        |ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e x-
          ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e y|≤rho) ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y →
        |ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e x-
          ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e y|≤rho) ∧
      ∀ b : Bool, 1-eta<(BernoulliProduct.law (fun _ : E => pc)).real
        (G.boxMove (ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e)
          (ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e) m (eps/8) 30 o (Corridor.sign b)) := by
  let zeta := eps/1000
  have hzeta : 0<zeta := by dsimp [zeta]; positivity
  have hzeta' : zeta≤1/10000 := by dsimp [zeta]; linarith
  let a := min (eta/2) (1/2)
  have ha : 0<a := lt_min (by positivity) (by norm_num)
  have haeta : a<eta := (min_le_left _ _).trans_lt (by linarith)
  have haone : a<1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨S,hS⟩ := EuclideanEllipse.finite_circle_cover zeta hzeta
  obtain ⟨m,hm⟩ := G.exists_seed_infinite_probability hc o (fun _ : E => pc) hone (a^S.card) (pow_pos ha _)
  have hAfin := G.vertexBall_finite hl o m
  obtain ⟨B,hB⟩ := (hAfin.image (fun x => ‖pi x‖)).bddAbove
  have hAB : ∀ x∈G.vertexBall o m, ‖pi x‖≤B := fun x hx => hB ⟨x,hx,rfl⟩
  refine ⟨m,?_⟩
  intro rho hrho
  obtain ⟨W,hW,hBW,hmesh⟩ := exists_strip_scale B D (min zeta (rho/16)) (lt_min hzeta (by positivity))
  have hDz : D/W≤zeta := hmesh.le.trans (min_le_left _ _)
  have hDrho : 16*(D/W)≤rho := by have := hmesh.trans_le (min_le_right _ _); linarith
  have hfav := G.all_ellipses_favored pi (G.vertexBall o m) W B D zeta hD hW hBW hDz hpi hAB
    S hS (fun _ : E => pc) a ha.le hm hbox
  let chooseCenter : (ℂ → ℂ) → Circle := fun f => Classical.epsilon
    (fun c => c∈S ∧ 1-a<(BernoulliProduct.law (fun _ : E => pc)).real
      (G.ellipseExit (f ∘ pi) (G.vertexBall o m) zeta c))
  have hselect : ∀ R : ℝ, W≤R → ∀ c : Circle,
      1-a<(BernoulliProduct.law (fun _ : E => pc)).real
        (G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) (G.vertexBall o m) zeta
          (chooseCenter (EuclideanEllipse.normalize R W c))) := by
    intro R hWR c
    exact (Classical.epsilon_spec (hfav R hWR c)).2
  obtain ⟨N,hN⟩ := G.favored_boundary_major_small hl (BernoulliProduct.law (fun _ : E => pc))
    pi (G.vertexBall o m) hAfin W zeta (1-a) hW hzeta.le hzeta' (by linarith) hnull
  let U := max W (10*(N : ℝ))
  have hWU : W≤U := le_max_left _ _
  have hU : 0<U := hW.trans_le hWU
  have hboundary : ∀ phi : ℝ,
      |((Circle.exp phi : ℂ)⁻¹*(chooseCenter (EuclideanEllipse.normalize U W (Circle.exp phi)) : ℂ)).re|<1/8 := by
    intro phi
    exact hN U hU (le_max_right _ _) _ _ (hselect U hWU _).le
  obtain ⟨p,hp,q,hq,hcomp,hdet⟩ := EuclideanEllipse.separated_neighboring_ellipses W U zeta hW hWU hzeta chooseCenter hboundary
  have hpR := EuclideanEllipse.diskRadius_bounds W U hWU hp
  have hqR := EuclideanEllipse.diskRadius_bounds W U hWU hq
  let R := EuclideanEllipse.diskRadius W U p
  let c := Circle.exp p.2
  let Psi := EuclideanEllipse.diskNormalize W U p ∘ pi
  let Psi' := EuclideanEllipse.diskNormalize W U q ∘ pi
  let d := chooseCenter (EuclideanEllipse.diskNormalize W U p)
  let e := chooseCenter (EuclideanEllipse.diskNormalize W U q)
  have hstep := G.ellipse_coordinates_step Psi d e hdet (D/W)
    (G.normalized_edge_bound pi R W D hW hpR.1 c hpi)
  have hpert : ∀ x, ‖Psi x-Psi' x‖≤zeta*‖Psi' x‖ := by
    intro x
    have hh := hcomp (Psi' x)
    have he : EuclideanEllipse.diskExpand W U q (Psi' x)=pi x :=
      EuclideanEllipse.expand_normalize _ W (ne_of_gt (hW.trans_le hqR.1)) hW.ne' _ (pi x)
    rwa [he] at hh
  have hPsi0 : Psi o=0 := by
    change EuclideanEllipse.normalize R W c (pi o)=0
    rw [hpo,EuclideanEllipse.normalize_origin]
  refine ⟨R,W,c,d,e,(fun {_ _} h => (hstep.1 h).trans hDrho),
    (fun {_ _} h => (hstep.2 h).trans hDrho),?_⟩
  intro b
  cases b
  · have hfavored := hselect (EuclideanEllipse.diskRadius W U q) hqR.1 (Circle.exp q.2)
    have hmono := ENNReal.toReal_mono (measure_ne_top (BernoulliProduct.law (fun _ : E => pc)) _)
      (measure_mono (G.ellipseExit_boxMove Psi Psi' o m d e hdet eps heps heps' hPsi0 hpert false))
    exact (by linarith : 1-eta<1-a).trans (hfavored.trans_le hmono)
  · have hfavored := hselect (EuclideanEllipse.diskRadius W U p) hpR.1 (Circle.exp p.2)
    have hsame : ∀ x, ‖Psi x-Psi x‖≤(eps/1000)*‖Psi x‖ := by intro x; simp only [sub_self,norm_zero]; positivity
    have hmono := ENNReal.toReal_mono (measure_ne_top (BernoulliProduct.law (fun _ : E => pc)) _)
      (measure_mono (G.ellipseExit_boxMove Psi Psi o m d e hdet eps heps heps' hPsi0 hsame true))
    exact (by linarith : 1-eta<1-a).trans (hfavored.trans_le hmono)

end CriticalPercolation.BondGraph
end
end
end

end OAI
