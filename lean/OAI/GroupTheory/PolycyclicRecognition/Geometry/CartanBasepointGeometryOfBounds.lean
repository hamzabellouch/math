import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBasepointFactorCover
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveWidthSmallLog
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartLogBound
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMetricLogChartShift

namespace OAI

/-! # Assembling basepoint geometry from proved quantitative factor bounds -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Pointwise Topology

variable {EG G I : Type*} [Fintype I] [DecidableEq I] [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  [IsTopologicalGroup F.D.carrier]

omit [SimplyConnectedSpace G] [IsIsometricSMul G G] [ProperSpace G] in
include hunimod hπExp hchartN dynkinN in
/-- Quantitative factor bounds imply the required two box inclusions.
This assembly lemma is used with the already proved metric factor theorem. -/
theorem exists_basepoint_geometry_of_factor_bounds
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ h : H, F.action (F.ExpD (F.D.equiv h)) =
      M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
        (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN h)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (X : I → H) (d : ℕ) (βD : WordBasisSelections X (boundedBracketWords d))
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {lo : ℝ} (hlo : 0 < lo)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW E w)
    {α t : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α < 1) (ht : 1 < t)
    {R : ℝ} (hR : 0 < R)
    (L : ℝ)
    (hprod : ∀ r : ℝ, 0 ≤ r → ∀ x u a : F.N.carrier,
      x ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1 →
      u ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1 →
      a ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1 →
      x⁻¹ * u⁻¹ * a ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r L)
    (hL : 1 ≤ L)
    (C A : ℝ) (q : ℕ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hmetric :
      ∀ R : ℝ, 0 < R → ∃ (ρ η S D : ℝ) (p : ℕ),
      0 < ρ ∧ 0 < η ∧ 1 ≤ S ∧ 0 ≤ D ∧
      ∀ r s : ℝ, S ≤ r → 0 < s → r ≤ 2 * s → s ≤ r →
      ∀ g : G, dist 1 g ≤ η * r →
      ∃ (n : F.N.carrier) (k : F.D.carrier) (h : H),
        F.inclusionN n * F.inclusionD k = g ∧
        (π (F.inclusionD k)).toAdd = (π g).toAdd ∧
        (∃ v : cartanRootIdeal H, F.ExpN (F.N.equiv v) = n ∧
          ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖ ≤ C * (3 + dist 1 g) ^ q * Real.exp (A * (dist 1 g + 1))) ∧
        F.ExpD (F.D.equiv h) = k ∧
        ‖(finBasis ℝ H).equivFun h‖ ≤ D * (1 + r) ^ p ∧
        let b := WordBasisSelections.basis X (boundedBracketWords d) βD
        let br := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log r)
        let bs := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log s)
        ∀ z : Fin (finrank ℝ H) → ℝ, ‖z‖ ≤ ρ →
          ‖wordChartLeftShift F.D.equiv chartD br bs k z‖ ≤ R) :
    ∃ ρ η : ℝ, 0 < ρ ∧ 0 < η ∧
      ∀ scale : ℕ → ℝ, Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
      ∀ᶠ n in atTop, ∀ g : G, dist 1 g ≤ η * scale n →
      ∃ (u : F.N.carrier) (k : F.D.carrier),
        F.inclusionN u * F.inclusionD k = g ∧
        (π (F.inclusionD k)).toAdd = (π g).toAdd ∧
        (∀ a₀ ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (α * scale n) 1,
          ∀ a ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1,
          (F.action k a₀)⁻¹ * u⁻¹ * a ∈
            M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) L) ∧
        ((F.action k) ⁻¹' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) L ⊆
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (t * scale n) 1) ∧
        let b := WordBasisSelections.basis X (boundedBracketWords d) βD
        let br := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
        let bs := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (α * scale n))
        ∀ z : Fin (finrank ℝ H) → ℝ, ‖z‖ ≤ ρ →
          ‖wordChartLeftShift F.D.equiv chartD br bs k z‖ ≤ R := by
  have hα0 : 0 < α := by linarith only [hα]
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  let bN := WordBasisSelections.basis M.letter M.wordList β
  obtain ⟨ηN, SN, hηN, _, hSN, hsmallN⟩ := exists_small_distance_exponential_box bN
    (fun j => M.boxCost T hunimod eW E (β.val j)) (F.ExpN ∘ F.N.equiv)
    hlo (fun j => hcost (β.val j)) hC hA q
  obtain ⟨ηB, hηB, hboxes⟩ := M.exists_small_height_two_scale_inclusions T hunimod eW
    F.N.equiv F.ExpN F.isExpN hbijN dynkinN b₀ hE hne β hβ hlo hcost hα0 hα1 ht
  obtain ⟨ρ, ηC, SC, D, p, hρ, hηC, hSC, hD, hshift⟩ := hmetric R hR
  let η := min ηC (min ηN (ηB / (K + 1)))
  have hη : 0 < η := lt_min hηC (lt_min hηN (div_pos hηB (by linarith only [hK])))
  have hηC' : η ≤ ηC := min_le_left _ _
  have hηN' : η ≤ ηN := (min_le_right _ _).trans (min_le_left _ _)
  have hηB' : K * η ≤ ηB := by
    have hh : η ≤ ηB / (K + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by linarith only [hK] : 0 < K + 1)).mp hh
    nlinarith only [hh', hη]
  refine ⟨ρ, η, hρ, hη, ?_⟩
  intro scale hs hs1
  let RH := fun n => D * (1 + scale n) ^ p
  have hRH0 : ∀ n, 0 ≤ RH n := fun n =>
    mul_nonneg hD (pow_nonneg (by linarith only [hs1 n]) p)
  have hRH : HasSubexponentialUpperBoundSeq scale RH := by
    intro ε hε
    filter_upwards [((subexponential_upper_polynomial
      (by linarith only [hD] : 0 < D + 1) p).along_sequence hs) ε hε] with n hn
    exact (mul_le_mul_of_nonneg_right (by linarith only : D ≤ D + 1)
      (pow_nonneg (by linarith only [hs1 n]) p)).trans hn
  have hb := hboxes scale RH (fun _ => L) hs hRH0 (fun _ => le_trans zero_le_one hL)
    hRH (sequence_subexponential_upper_const hs L)
  have hαs : ∀ᶠ n in atTop, 1 ≤ α * scale n :=
    (hs.const_mul_atTop hα0).eventually (eventually_ge_atTop 1)
  filter_upwards [hb, hαs, hs.eventually (eventually_ge_atTop SN),
    hs.eventually (eventually_ge_atTop SC)] with n hn hαsn hsn hscn g hg
  have hsn0 : 0 ≤ scale n := (by linarith only [hs1 n])
  have hrs : scale n ≤ 2 * (α * scale n) := by nlinarith only [hα, hsn0]
  obtain ⟨u, k, h, huk, hkheight, hu, he, hh, hkshift⟩ := hshift (scale n) (α * scale n) hscn
    (mul_pos hα0 (zero_lt_one.trans_le (hs1 n))) hrs
    (mul_le_of_le_one_left hsn0 hα1.le) g (hg.trans (mul_le_mul_of_nonneg_right hηC' hsn0))
  have huBox : u ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 := by
    obtain ⟨v, hv, hbound⟩ := hu
    rw [← hv]
    exact hsmallN (scale n) hsn (dist 1 g) dist_nonneg
      (hg.trans (mul_le_mul_of_nonneg_right hηN' hsn0)) v hbound
  have hsmall : K * dist 1 g ≤ ηB * scale n :=
    (mul_le_mul_of_nonneg_left hg hK).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hηB' hsn0)
  have hcover := M.basepoint_factor_cover T F eW π hπExp hbijN dynkinN hφ hLip
    _ _ _ _ hn
    (fun x hx u hu a ha => hprod (scale n) hsn0 x u a hx hu ha)
    g u k h he hkheight hh hsmall huBox
  exact ⟨u, k, huk, hkheight, hcover.1, hcover.2, hkshift⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
