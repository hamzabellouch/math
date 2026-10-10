import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTerminalCorrections
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLiftMultiplicity
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TerminalTupleProjection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.EventualLiftVolumeCover

namespace OAI

/-! # Closing the terminal-volume comparison in the actual Cartan factors

Compact thickening errors are absorbed into the logarithmic and height
bounds before applying the noncentral lift-multiplicity estimate.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set Metric
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
  [SecondCountableTopology F.N.carrier]

include hunimod in
theorem terminal_product_exponent_le
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
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
    (μ : Measure F.N.carrier) [μ.IsHaarMeasure]
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) {h : ℕ} (hh : 0 < h)
    (scale RH η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 < scale n) (hRH0 : ∀ n, 0 ≤ RH n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH) (hη : Tendsto η atTop (𝓝 0))
    (s : ℕ → Finset (Fin h → G))
    (p : ℕ → (Fin h → G) → (Fin h → F.N.carrier) × (Fin h → F.D.carrier))
    (U : Set ((Fin h → F.N.carrier) × (Fin h → F.D.carrier))) (hU : IsCompact U)
    (I : ℕ → Set (Fin h → F.N.carrier)) (C : ℕ → Set F.N.carrier)
    (t : ℕ → Finset G) {ρ R b c : ℝ}
    (hp : ∀ n x, x ∈ s n → ∀ i,
      F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i)
    (hsmall : ∀ z ∈ U, dist (1 : Fin h → G)
      (fun i => F.inclusionN (z.1 i) * F.inclusionD (z.2 i)) < ρ)
    (hd : ∀ n x, x ∈ s n → ∀ i,
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n)
    (hhgt : ∀ n x, x ∈ s n → ∀ i,
      ‖eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
          η n * scale n)
    (hI : ∀ n u, u ∈ I n → ∃ x ∈ s n, ∃ z ∈ U,
      prefixCoordinateEquiv h u = fun i => (p n x).1 i * F.action ((p n x).2 i) (z.1 i))
    (hC : ∀ᶠ n in atTop, C n ⊆ (fun u : Fin h → F.N.carrier => (List.ofFn u).prod) '' I n)
    (hlower : HasSubexponentialLowerBoundSeq scale
      (fun n => (μ (C n)).toReal / Real.exp (scale n * b)))
    (hcover : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ y ∈ t n,
      dist (x ⟨h - 1, Nat.sub_lt hh (by decide)⟩) y ≤ R)
    (hcount : HasSubexponentialUpperBoundSeq scale
      (fun n => ((t n).card : ℝ) / Real.exp (scale n * c))) : b ≤ c := by
  let KD := (fun z : (Fin h → F.N.carrier) × (Fin h → F.D.carrier) =>
    z.2 ⟨h - 1, Nat.sub_lt hh (by decide)⟩) '' U
  have hKD : IsCompact KD := hU.image ((continuous_apply _).comp continuous_snd)
  obtain ⟨RC, ε, hRC0, hRC, hε, hcorrect⟩ := F.exists_terminal_correction_bounds T eW π hπ
    hπExp chartD hchartD hbijD dynkinD hKD scale RH η hs hscale hRH0 hRH hη
  let A := fun n => {d : F.D.carrier |
    ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RC n ∧
    ‖eW (heightProjection T.character
      (cartanLog H F.D.equiv F.ExpD hbijD d : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤ ε n * scale n}
  obtain ⟨V, hV0, hV, hball⟩ := M.exists_subexponential_lift_multiplicity T F hunimod eW
    hExpG hinjG realize chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN
    μ b₀ γ scale RC ε hs (fun n => (hscale n).le) hRC0 hRC hε (ρ + R)
  apply exponent_le_of_lifted_volume_covers_eventually μ
    (fun u d => F.inclusionN u * F.inclusionD d) A C t (ρ + R) V hV0 hs hV hlower hcount
  · exact Eventually.of_forall (fun n y _ => by simpa only [A, mem_ofPred_eq, and_assoc] using hball n y)
  · filter_upwards [hC, hcover] with n hCn hcovern
    apply terminal_tuple_product_cover_pos hh F.inclusionN F.inclusionD F.action F.conjugation
      (s n) (p n) U (I n) (C n) (A n) (t n) (hp n) (hI n) hsmall ?_ hcovern hCn
    intro x hx z hz
    exact hcorrect n _ _ ⟨z, hz, rfl⟩
      (hd n x hx ⟨h - 1, Nat.sub_lt hh (by decide)⟩)
      (hhgt n x hx ⟨h - 1, Nat.sub_lt hh (by decide)⟩)

end PolycyclicRecognition.CartanWordModel

end

end OAI
