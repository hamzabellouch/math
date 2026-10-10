import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateDenseSliceInput
import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}
    (out : P.Conclusion outputCost outputMass outputScore)

noncomputable def retainedForecastSelect {Forecast : Type}
    (member : out.retained → Forecast) (z : A.Path) : Option Forecast :=
  if hz : z ∈ out.retained then some (member ⟨z, hz⟩) else none

@[simp] theorem retainedForecastSelect_coe {Forecast : Type}
    (member : out.retained → Forecast) (z : out.retained) :
    out.retainedForecastSelect member z.val = some (member z) := by
  classical
  simp only [retainedForecastSelect, dite_eq_left z.property]

variable [DecidableEq X]
    {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
    {Dmod Lrank : ℕ} {Selection : Type} [Fintype Selection]
    {selected : Selection → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    {spatial : Fin Lrank ↪ G}
    {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
    {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
    {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
    {Wsp Lsp : ℝ}
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod selected τ δslice)
    (qnum : ActualFixedSpatialSlicedForecastNumerics s)
    {δbase PpresBase : ℝ}
    (paths : out.retained → ActualFixedSpatialForecastPath (Eout := Eout)
      B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp N
      τ δbase s.P s.Pbad PpresBase)
    (hkeep : ∀ z : out.retained, ∀ k,
      (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔ qnum.Hchild ≤ A.sides k)
    (hkernel : Nonempty G)
    (hcutoff : qnum.Hchild ≤ S.value)
    (hlate : 2 ≤ Real.exp (-outputCost) * (S.value : ℝ))
    (hdensity : qnum.δ ≤ Real.exp (-outputCost))
    (hactive : δslice ≤ Real.exp (-outputCost) / 2)
    (hlog : outputCost + 1 ≤ qnum.v)
    (hprescribed : outputCost + 1 ≤ s.Ppres)
    (hstride : 2 * Real.exp outputCost ≤ qnum.Ptail)

noncomputable def denseForecastMember (z : out.retained) :
    ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := N) s qnum :=
  (paths z).toDenseSliceMember (out.denseSliceInput s qnum z (hkeep z)
    (paths z).commonTuple hkernel hcutoff hlate hdensity hactive hlog hprescribed hstride)

omit [Fintype Tsp] in
@[simp] theorem denseForecastMember_center (z : out.retained) :
    (out.denseForecastMember s qnum paths hkeep hkernel hcutoff hlate hdensity
      hactive hlog hprescribed hstride z).slice.path.center = (paths z).center := rfl

theorem exists_denseForecastData
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    let Member := ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := N) s qnum
    let member : out.retained → Member := out.denseForecastMember s qnum paths hkeep
      hkernel hcutoff hlate hdensity hactive hlog hprescribed hstride
    let select := out.retainedForecastSelect member
    ∃ data : Option Member → ActualForecastData N poly
        qnum.Pnative qnum.massLog qnum.capLog qnum.E,
      (∀ path, (data (some path)).target =
        path.slice.target selected s.hBactive o bW hb poly hm s.κ ∧
        (data (some path)).centerConstant = fun j => (path.slice.path.center j).val) ∧
      (∀ z : out.retained,
        (data (select z.val)).target =
          (member z).slice.target selected s.hBactive o bW hb poly hm s.κ ∧
        (data (select z.val)).centerConstant = fun j => ((paths z).center j).val) ∧
      (∀ forecast x, (((data forecast).target x).re : ℂ) = (data forecast).target x) ∧
      (data none).target = (fun _ => 0) ∧
      (data none).centerConstant = (fun _ _ => 0) := by
  classical
  intro Member member select
  obtain ⟨data, hdata, hnone, hnoneCenter, _hcap, _hmass, _happrox⟩ :=
    exists_actualFixedSpatialSlicedForecastFamily_option_of_numerics
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := N)
      s qnum o bW hb poly hm
  refine ⟨data, hdata, ?_, ?_, hnone, hnoneCenter⟩
  · intro z
    change (data (out.retainedForecastSelect member z.val)).target = _ ∧
      (data (out.retainedForecastSelect member z.val)).centerConstant = _
    rw [out.retainedForecastSelect_coe member z]
    exact hdata (member z)
  · intro forecast x
    cases forecast with
    | none => simp only [hnone, Complex.zero_re, Complex.ofReal_zero]
    | some path =>
      rw [(hdata path).1]
      exact path.slice.target_real selected s.hBactive o bW hb s.κ poly hm x

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
