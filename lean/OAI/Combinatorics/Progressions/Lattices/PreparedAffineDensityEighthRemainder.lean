import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceRelativeInitializerBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G V : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

include hσ1 hC hchart

theorem allocatedAffineDensity_eighth_integer_remainder_of_earlyRadius
    {Pchart Bstruct : ℝ}
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (hbudget : ∀ C' : Fin m → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Bstruct) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hchartBound : ∀ j, C j ≤ Real.exp Pchart)
    (hallow : Pchart + 1 ≤ Bstruct)
    (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))
    (center : ∀ j, U j)
    (frame : Option (LayerSamplerVariables G I n B) → V → ℝ)
    (hframe : allocatedAffineDensity B U b hb o hR hσ S p hm center frame ≠ 0) :
    ∃ β : ∀ j, J j → MvPolynomial (LayerSamplerVariables G I n B) ℤ,
      (∀ j i, (β j i).totalDegree ≤ j.val + 1) ∧
      ∀ (x : LayerSamplerVariables G I n B → ℝ), (∀ v, |x v| ≤ layerSamplerBox B U b S v) →
        ∀ j i,
          |eval (fun v => frame none v + ∑ k, frame (some k) v * x k) (p j) i - (center j).val i -
            MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β j i))| ≤ 1 / 8 := by
  have heighth := preparedEarlyRadius_eighth_of_universal hbudget C hC hchartBound hallow
  have hsmall (j : Fin m) : C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4 :=
    (heighth j).trans (by norm_num)
  obtain ⟨β, hβ, hremainder⟩ := allocatedAffineDensity_small_integer_remainder
    B U b o hR hσ S hσ1 C hC hchart hb hsmall p hm hp center frame hframe
  refine ⟨β, hβ, ?_⟩
  intro x hx j i
  exact (hremainder x hx j i).trans (by simpa only [mul_assoc] using heighth j)

end Erdos3.VectorPolynomial

end

end OAI
