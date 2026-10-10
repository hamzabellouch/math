import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAlternatingComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSeparatedTuples
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorLogVolume
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceTupleVolume
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChronologicalAlternatingHaar
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BundleParameterCharts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalExponentialMeasure

namespace OAI

/-! # Separated target tuples supply the alternating increment volume

The auxiliary Cartan volume is subexponential. Thus the finite separated
count supplies the full correlated Haar lower bound needed by the product
comparison; this lower bound is not assumed independently.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]

def alternatingCoordinateFamily {A : Type*} (h : ℕ) (v₁ v₂ : A) (i : Fin (h * 2)) : A :=
  if (finProdFinEquiv.symm i).2 = 0 then v₁ else v₂

@[simp] theorem alternatingCoordinateFamily_left {A : Type*} (h : ℕ) (v₁ v₂ : A) (j : Fin h) :
    alternatingCoordinateFamily h v₁ v₂ (finProdFinEquiv (j, (0 : Fin 2))) = v₁ := by
  simp [alternatingCoordinateFamily]

@[simp] theorem alternatingCoordinateFamily_right {A : Type*} (h : ℕ) (v₁ v₂ : A) (j : Fin h) :
    alternatingCoordinateFamily h v₁ v₂ (finProdFinEquiv (j, (1 : Fin 2))) = v₂ := by
  simp [alternatingCoordinateFamily]

theorem separated_alternating_product_exponent_le
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β β₁ β₂ : M.Bases) (E E₁ E₂ : Set W)
    {h cN : ℕ} (hh : 0 < h) (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hn : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale RH R η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 < scale n) (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) (hη : Tendsto η atTop (𝓝 0))
    (p₀ : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun n =>
      let b := M.boxBasis T hunimod eW E β (scale n)
      let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale n)
      let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale n)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂)) atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hsub : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct aN p₀.1 p₀.2.1 p₀.2.2) z₀))
    (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂) (h01 : (0 : W) ∈ E₁) (h02 : (0 : W) ∈ E₂)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
    (s : ℕ → Finset (Fin (h * 2) → G))
    (p : ℕ → (Fin (h * 2) → G) → (Fin (h * 2) → F.N.carrier) × (Fin (h * 2) → F.D.carrier))
    (U : Set ((Fin (h * 2) → F.N.carrier) × (Fin (h * 2) → F.D.carrier))) (hU : IsCompact U)
    (hUpos : ((Measure.pi fun _ : Fin (h * 2) =>
      Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume).prod
        (Measure.pi fun _ : Fin (h * 2) => ν)) U ≠ 0)
    (t : ℕ → Finset G) {ρ Rc q : ℝ}
    (hp : ∀ n x, x ∈ s n → ∀ i,
      F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i)
    (hsmall : ∀ z ∈ U, dist (1 : Fin (h * 2) → G)
      (fun i => F.inclusionN (z.1 i) * F.inclusionD (z.2 i)) < ρ / 2)
    (hsep : ∀ n x, x ∈ s n → ∀ y, y ∈ s n → x ≠ y → ρ ≤ dist x y)
    (hd : ∀ n x, x ∈ s n → ∀ i,
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n)
    (hhgt : ∀ n x, x ∈ s n → ∀ i,
      ‖eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
          η n * scale n)
    (hinc : ∀ n x, x ∈ s n → ∀ i, (prefixCoordinateEquiv (h * 2)).symm (p n x).1 i ∈
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        (alternatingCoordinateFamily h E₁ E₂ i) (alternatingCoordinateFamily h β₁ β₂ i)
        (scale n) (R n))
    (hnum : HasSubexponentialLowerBoundSeq scale (fun n => ((s n).card : ℝ) /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))))
    (hcover : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ y ∈ t n,
      dist (x ⟨h * 2 - 1, Nat.sub_lt (by omega) (by decide)⟩) y ≤ Rc)
    (hcount : HasSubexponentialUpperBoundSeq scale
      (fun n => ((t n).card : ℝ) / Real.exp (scale n * q))) :
    columnBasisWeight (M.boxCost T hunimod eW E) β.val ≤ q := by
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  let : LocallyCompactSpace F.N.carrier := F.closedN.locallyCompactSpace
  let : LocallyCompactSpace F.D.carrier := F.closedD.locallyCompactSpace
  let : SigmaFinite μ := inferInstance
  have hEc (i : Fin (h * 2)) : IsCompact (alternatingCoordinateFamily h E₁ E₂ i) := by
    unfold alternatingCoordinateFamily
    split_ifs <;> assumption
  have hE0 (i : Fin (h * 2)) : (0 : W) ∈ alternatingCoordinateFamily h E₁ E₂ i := by
    unfold alternatingCoordinateFamily
    split_ifs <;> assumption
  have hβ (i : Fin (h * 2)) : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (alternatingCoordinateFamily h E₁ E₂ i))
      (alternatingCoordinateFamily h β₁ β₂ i).val := by
    unfold alternatingCoordinateFamily
    split_ifs <;> assumption
  obtain ⟨Q, RD, hQ0, hQ, hRD0, hRD, hex⟩ := M.exists_controlled_increment_volume T F hunimod eW
    hExpG realize chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD μ ν b₀ β
    (h * 2) (alternatingCoordinateFamily h E₁ E₂) hEc hE0 (alternatingCoordinateFamily h β₁ β₂) hβ
    scale RH R η hs (fun n => (hscale n).le) hRH0 hR0 hRH hR hη s p U hU hp hsmall hsep hd hhgt hinc
  choose I hIc hIm hmass hbox hreach using hex
  obtain ⟨RQ, hRQ0, hRQ, hQle⟩ := finite_subexponential_envelope hs Q hQ0 hQ
  obtain ⟨hDfinite, hDvol⟩ := F.log_regions_volume haarD hbijD ν scale RD hs hRD0 hRD
  obtain ⟨hDpiFinite, hDpiVol⟩ := tuple_region_volume_subexponential ν hs _ hDfinite hDvol (h * 2)
  have hIlower := lower_volume_rate_of_tuple_count hs (fun n => (s n).card)
    (fun n => (Measure.pi fun _ : Fin (h * 2) => μ) (I n))
    (fun n => (Measure.pi fun _ : Fin (h * 2) => ν)
      {d | ∀ i, ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (d i))‖ ≤ RD n})
    (((Measure.pi fun _ : Fin (h * 2) => μ).prod (Measure.pi fun _ : Fin (h * 2) => ν)) U)
    hUpos hU.measure_lt_top.ne (fun n => (hIc n).measure_lt_top.ne) hDpiFinite hDpiVol hnum hmass
  have hbox' (n : ℕ) (u : Fin (h * 2) → F.N.carrier) (hu : u ∈ I n) (i : Fin (h * 2)) :
      u i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        (alternatingCoordinateFamily h E₁ E₂ i) (alternatingCoordinateFamily h β₁ β₂ i)
        (scale n) (RQ n) := by
    obtain ⟨v, hv, hb⟩ := hbox n u hu i
    exact ⟨v, hv, hb.trans (hQle i n)⟩
  exact M.alternating_product_exponent_le T F hunimod eW hExpG hinjG realize rem π hπ hπExp
    chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN b₀ β β₁ β₂ E E₁ E₂
    hh aN hm hn scale RH RQ η hs hscale hRH0 hRQ0 hRH hRQ hη p₀ hlim z₀ hsub I hIc
    (fun n u hu j => by
      simpa only [alternatingCoordinateFamily_left] using hbox' n u hu (finProdFinEquiv (j, (0 : Fin 2))))
    (fun n u hu j => by
      simpa only [alternatingCoordinateFamily_right] using hbox' n u hu (finProdFinEquiv (j, (1 : Fin 2))))
    hIlower s p U hU t hp hsmall hd hhgt hreach hcover hcount

end PolycyclicRecognition.CartanWordModel

end

end OAI
