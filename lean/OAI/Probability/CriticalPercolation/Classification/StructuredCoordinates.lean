import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.EquivariantCoordinates
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphActionCoordinates
import OAI.Probability.CriticalPercolation.GraphGeometry.ActionCoordinates
import OAI.Probability.CriticalPercolation.GraphGeometry.CriticalCoordinates

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E Λ N : Type*} (G : BondGraph V E)
  [Group Λ] [Group N] [MulAction Λ V] [MulAction Λ E]

def integerPairComplex (z : ℤ×ℤ) : ℂ := (z.1 : ℂ)+(z.2 : ℂ)*Complex.I

lemma integerPairComplex_add (a b : ℤ×ℤ) :
    integerPairComplex (a+b)=integerPairComplex a+integerPairComplex b := by
  simp only [integerPairComplex,Prod.fst_add,Prod.snd_add,Int.cast_add]
  ring

lemma integerPairComplex_re (z : ℤ×ℤ) : (integerPairComplex z).re=z.1 := by
  simp [integerPairComplex]

lemma integerPairComplex_im (z : ℤ×ℤ) : (integerPairComplex z).im=z.2 := by
  simp [integerPairComplex]

theorem exists_integer_pair_coordinates
    (ρ : Λ →* N) (hρ : Surjective ρ)
    (φ : N →* Multiplicative (ℤ×ℤ)) (hφ : Surjective φ)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite)
    [Nonempty V] :
    ∃ z : V → ℤ×ℤ, Surjective z ∧
      ∀ g v, z (g • v)=(φ (ρ g)).toAdd+z v := by
  obtain ⟨π,hπ⟩ := EquivariantCoordinates.exists_equivariant (φ.comp ρ)
    (EquivariantCoordinates.stabilizer_killed ρ φ hstab)
  refine ⟨fun v => (π v).toAdd,?_,?_⟩
  · intro t
    obtain ⟨v,hv⟩ := EquivariantCoordinates.surjective_of_equivariant
      (φ.comp ρ) (hφ.comp hρ) π hπ (Multiplicative.ofAdd t)
    exact ⟨v,congrArg Multiplicative.toAdd hv⟩
  · intro g v
    exact congrArg Multiplicative.toAdd (hπ g v)

lemma integer_pair_coordinate_geometry
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (a : Λ → ℤ×ℤ) (z : V → ℤ×ℤ) (honto : Surjective z)
    (hz : ∀ g v, z (g • v)=a g+z v) :
    ∃ (o : V) (c : ℕ) (D : ℝ), 0≤D ∧ integerPairComplex (z o)=0 ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y →
        ‖integerPairComplex (z x)-integerPairComplex (z y)‖≤D) ∧
      (∀ m n : ℤ, ∃ x, (integerPairComplex (z x)).re=m ∧
        (integerPairComplex (z x)).im=n) ∧
      (∀ y, ∃ psi : G.Aut, psi.vertex o∈G.vertexBall y c ∧
        ∀ x y, integerPairComplex (z (psi.vertex x))-integerPairComplex (z (psi.vertex y))=
          integerPairComplex (z x)-integerPairComplex (z y)) := by
  let pi : V → ℂ := fun v => integerPairComplex (z v)
  have hpi : ∀ g v, pi (g • v)=integerPairComplex (a g)+pi v := by
    intro g v
    exact (congrArg integerPairComplex (hz g v)).trans (integerPairComplex_add _ _)
  obtain ⟨o,ho⟩ := honto 0
  obtain ⟨c,hc'⟩ := G.action_orbit_dense (fun g => G.smulAut ha g) (fun _ _ => rfl)
    hc S hS hcover o
  obtain ⟨D,hD,hj⟩ := G.bounded_coordinate_jumps hl ha S hS hcover
    (fun g => integerPairComplex (a g)) pi hpi
  refine ⟨o,c,D,hD,?_,?_,?_,?_⟩
  · simp [ho,integerPairComplex]
  · intro x y hxy
    obtain ⟨⟨e,_,he⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
    exact hj e x y he
  · intro m n
    obtain ⟨x,hx⟩ := honto (m,n)
    exact ⟨x,by rw [hx,integerPairComplex_re],by rw [hx,integerPairComplex_im]⟩
  · intro y
    obtain ⟨g,hg⟩ := hc' y
    refine ⟨G.smulAut ha g,hg,?_⟩
    intro x y
    change pi (g • x)-pi (g • y)=pi x-pi y
    rw [hpi,hpi]
    abel

theorem critical_null_of_action_coordinates
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (hg : G.SubexponentialGrowth) (hpc : G.criticalProbability<1)
    (a : Λ → ℤ×ℤ) (z : V → ℤ×ℤ) (honto : Surjective z)
    (hz : ∀ g v, z (g • v)=a g+z v)
    (hnoray : ∀ᵐ ω ∂G.law G.criticalProbability,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n,
        |(z (r.vertex n)).1|≤U ∧ |(z (r.vertex n)).2|≤W) :
    G.law G.criticalProbability G.percolates=0 := by
  obtain ⟨o,c,D,hD,ho,hjump,honto',hdense⟩ :=
    G.integer_pair_coordinate_geometry hc hl ha S hS hcover a z honto hz
  apply G.critical_null_of_unbounded_projection hc hl
    (G.quasiTransitive_of_action ha S hS hcover) hg hpc
    (fun v => integerPairComplex (z v)) o c D hD ho hjump honto' hdense
  simpa only [integerPairComplex_re,integerPairComplex_im,Int.cast_abs] using hnoray

end CriticalPercolation.BondGraph
end
end
end

end OAI
