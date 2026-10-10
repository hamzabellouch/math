import OAI.Combinatorics.Progressions.Lattices.AllocatedOriginalSampleResidueMixtureForecast
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveProduct

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite

theorem exists_forecast_inactive_residue_site
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    (q : ℕ) [NeZero q]
    (coefficient : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q) → ℂ)
    (hcoefficient : ∀ r, ‖coefficient r‖ ≤ 1)
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E)
    (hδE : δ⁻¹ ≤ Real.exp E)
    (hsize : q ≤ S.value) (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 q ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Pos := {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q //
      0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))}
    let scale := fun a => allocatedPrincipalGridScale (G := G) B U b (R := R)
      (selected a).1 (selected a).2
    let O := allocatedInactiveJointSiteLog m D p v E
    ∃ e : Pos → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ r a, (e r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      (∑ t : Σ r, ∀ a, (e r a).Term, ‖forecastSiteMixtureCoefficient e
        (fun r => (law.mass (Finset.univ.filter
          (fun y => principalResidueLabel q y = r.val)) : ℂ) * coefficient r.val) t‖)
        ≤ Real.exp (Fintype.card A * O) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ),
        ‖((∏ a, (scale a : ℝ)) : ℂ) *
          law.complexMean (fun y => coefficient (principalResidueLabel q y) *
            ((forecastInactivePhysicalJointKernel B U b hR hσ S selected
              (fun _ => Finset.univ) x y (fun a _ => z a)).toReal : ℂ)) -
          (∑ r : Pos, (law.mass (Finset.univ.filter
            (fun y => principalResidueLabel q y = r.val)) : ℂ) * coefficient r.val *
            siteFamilyEval (e r) (fun _ => z) (fun _ a => (z a : ℝ) / scale a))‖ ≤ δ := by
  intro law Pos scale O
  have heach (r : Pos) := exists_forecast_inactive_product_site B U b S hR hσ
    selected hselected q (NeZero.pos q) r.val hD hP hp hv hPp hqv hδ hE hδE
    hsize hR1 hsmall r.property hgrid hσ1 L hL hprimitive hB
  choose e he herr using heach
  have hmass : (∑ r : Pos, law.mass (Finset.univ.filter
      (fun y => principalResidueLabel q y = r.val))) ≤ 1 :=
    (forecastInactive_positiveResidue_mass_sum law (principalResidueLabel q)).le
  let w (r : Pos) := law.mass (Finset.univ.filter
    (fun y => principalResidueLabel q y = r.val))
  have hw (r : Pos) : 0 ≤ w r := law.mass_nonneg _
  refine ⟨e, he, ?_, ?_⟩
  · have hm := forecastSiteMixture_weighted_mass e he
      (fun _ => Real.exp_nonneg O) w (fun r => coefficient r.val) hw hmass
      (fun r => hcoefficient r.val)
    simpa only [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul] using hm
  · intro x z
    let μ (r : Pos) : ℂ := (((∏ a, (scale a : ℝ)) *
      (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r.val r.property selected
        (fun _ => Finset.univ) x (fun a _ => z a)).toReal : ℝ) : ℂ)
    have herr' := forecastSiteMixture_weighted_error e w (fun r => coefficient r.val) μ
      hw hmass (fun r => hcoefficient r.val) (fun _ => z)
      (fun _ a => (z a : ℝ) / scale a) hδ.le (fun r => herr r x z)
    have hdis := forecastInactive_physical_kernel_disintegration B U b hR hσ S selected
      (fun _ => (Finset.univ : Finset (Finset Empty))) x q coefficient (fun a _ => z a)
    change law.complexMean _ = _ at hdis
    rw [hdis, Finset.mul_sum]
    have heq : (∑ r : Pos, ((∏ a, (scale a : ℝ)) : ℂ) *
        ((w r : ℂ) * coefficient r.val *
          ((allocatedSupportedPhysicalJointPMF B U b hR hσ S q r.val r.property selected
            (fun _ => Finset.univ) x (fun a _ => z a)).toReal : ℂ))) =
        ∑ r : Pos, (w r : ℂ) * coefficient r.val * μ r := by
      apply Finset.sum_congr rfl
      intro r _
      dsimp only [μ]
      push_cast
      ring
    rw [heq]
    exact herr'

end Erdos3.VectorPolynomial

end

end OAI
