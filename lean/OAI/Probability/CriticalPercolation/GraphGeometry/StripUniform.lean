import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure
import OAI.Probability.CriticalPercolation.GraphGeometry.StripLinear
import OAI.Probability.CriticalPercolation.GraphGeometry.StripOrigin
import OAI.Probability.CriticalPercolation.Gluing.ApproximateMoveEndgame
import OAI.Probability.CriticalPercolation.Gluing.StripMoves
import OAI.Probability.CriticalPercolation.Modular.MoveTransport

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma strip_aut_differences (u v : V → ℝ) (U Q : ℝ) (a b : Bool) (φ : G.Aut)
    (hu : ∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y)
    (hv : ∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y) :
    (∀ x y, stripTime u v U Q a b (φ.vertex x)-stripTime u v U Q a b (φ.vertex y)=
      stripTime u v U Q a b x-stripTime u v U Q a b y) ∧
    (∀ x y, stripHeight u v U Q a b (φ.vertex x)-stripHeight u v U Q a b (φ.vertex y)=
      stripHeight u v U Q a b x-stripHeight u v U Q a b y) := by
  constructor
  · intro x y
    calc
      _ = Corridor.sign a*(u (φ.vertex x)-u (φ.vertex y))/U+
        Corridor.sign b*(v (φ.vertex x)-v (φ.vertex y))/Q := by unfold stripTime; ring
      _ = _ := by rw [hu,hv]; unfold stripTime; ring
  · intro x y
    calc
      _ = Corridor.sign a*(u (φ.vertex x)-u (φ.vertex y))/U-
        Corridor.sign b*(v (φ.vertex x)-v (φ.vertex y))/Q := by unfold stripHeight; ring
      _ = _ := by rw [hu,hv]; unfold stripHeight; ring

theorem strip_uniform_moves [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (u v : V → ℝ) (o : V) (c : ℕ) (D : ℝ) (pc : unitInterval)
    (hD : 0≤D) (hpc : 0<pc) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
      (∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y) ∧
      (∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y))
    (hstrip : 0<(BernoulliProduct.law (fun _ : E => pc)) (G.someStripPercolates v))
    (hdir : ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => pc),
      ∀ a, (G.cluster ω a).Infinite → ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => pc), ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0<rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
      (pc : ℝ)/2≤p ∧ p<pc ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y → |t x-t y|≤rho) ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y → |z x-z y|≤rho) ∧
      ∀ y s, |s|=1 → 1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
        (G.coordinateMove t z m eps y s) := by
  obtain ⟨m,hm⟩ := G.strip_origin_moves hc hl u v o D pc hD huo hvo hu hv
    hstrip hdir hbox eps eta heps heps' heta
  refine ⟨m+c,?_⟩
  intro rho hrho
  let r := min rho (eps/(8*((c : ℝ)+1)))
  have hcpos : 0<(c : ℝ)+1 := by positivity
  have hr : 0<r := lt_min hrho (div_pos heps (by positivity))
  have hrrho : r≤rho := min_le_left _ _
  have hrs : r≤eps/(8*((c : ℝ)+1)) := min_le_right _ _
  have hmesh : (c : ℝ)*r≤eps/8 := by
    have hh := (le_div_iff₀ (by positivity : 0<8*((c : ℝ)+1))).mp hrs
    nlinarith
  obtain ⟨U,Q,a,b,_hU,_hQ,ht,hz,hmoves⟩ := hm r hr
  have htdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
      (∀ x y, stripTime u v U Q a b (φ.vertex x)-stripTime u v U Q a b (φ.vertex y)=
        stripTime u v U Q a b x-stripTime u v U Q a b y) ∧
      (∀ x y, stripHeight u v U Q a b (φ.vertex x)-stripHeight u v U Q a b (φ.vertex y)=
        stripHeight u v U Q a b x-stripHeight u v U Q a b y) := by
    intro y
    obtain ⟨φ,hφ,hφu,hφv⟩ := hdense y
    exact ⟨φ,hφ,G.strip_aut_differences u v U Q a b φ hφu hφv⟩
  obtain ⟨p,hpl,hpu,hp⟩ := G.uniform_moves_of_origin (stripTime u v U Q a b)
    (stripHeight u v U Q a b) o m c eps eta r heps' hr.le hmesh ht hz htdense pc hpc hmoves
  exact ⟨stripTime u v U Q a b,stripHeight u v U Q a b,p,hpl,hpu,
    fun {_ _} h => (ht h).trans hrrho,fun {_ _} h => (hz h).trans hrrho,hp⟩

theorem strip_critical_contradiction [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (u v : V → ℝ) (o : V) (c : ℕ) (D : ℝ)
    (hD : 0≤D) (hpc : 0<(G.criticalProbability : ℝ))
    (hpc1 : (G.criticalProbability : ℝ)<1) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
      (∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y) ∧
      (∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y))
    (hstrip : 0<(BernoulliProduct.law (fun _ : E => G.criticalProbability)) (G.someStripPercolates v))
    (hdir : ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability),
      ∀ a, (G.cluster ω a).Infinite → ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability), ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite) : False := by
  apply G.approximate_moves_contradiction hc hl hq hpc hpc1
  intro eps eta he he' heta _heta'
  exact G.strip_uniform_moves hc hl u v o c D G.criticalProbability hD hpc huo hvo hu hv hdense
    hstrip hdir hbox eps eta he he' heta

end CriticalPercolation.BondGraph
end
end
end

end OAI
