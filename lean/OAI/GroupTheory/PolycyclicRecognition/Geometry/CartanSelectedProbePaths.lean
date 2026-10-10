import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanThreeTemplatePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxProbeChains

namespace OAI

/-! # Image paths for the selected actual probe chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

omit [SimplyConnectedSpace G] [IsIsometricSMul G G] [Fintype I] [DecidableEq I]
    [FiniteDimensional ℝ W] [Nonempty (Fin M.letterCount)] in
/-- Inclusion into the ambient group retains the exact generator edge of
the measured box chain, also after left translation by an anchor. -/
theorem BoxProbeChains.ambient_step
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : ∀ n, Y n → F.N.carrier)
    (P : M.BoxProbeChains T F hunimod eW b₀ E γ t scale probe)
    (n : ℕ) (y : Y n) (g : G) (j : Fin P.length) :
    g * F.inclusionN (F.ExpN (F.N.equiv (P.vertex n y j.succ))) =
      (g * F.inclusionN (F.ExpN (F.N.equiv (P.vertex n y j.castSucc)))) *
        Exp (P.coefficient n y j • (M.letter (P.mode n j) :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
  have h := congrArg F.inclusionN (P.vertex_step n y j)
  rw [map_mul, F.compatibleN (P.coefficient n y j • M.letter (P.mode n j))] at h
  exact (congrArg (g * ·) h).trans (mul_assoc _ _ _).symm

/-- One compact profile domain works for all three actual box chains and
for arbitrary measurable anchor choices. On a retained good probe, the
paths start at the corresponding anchors and end at the actual samplers.
The only profile premise is the prefix estimate supplied by selection. -/
theorem exists_selected_probe_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g : G => (π g).toAdd))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (pivot : H) (E : Fin 3 → Set W) (V : Set W) (hEc : ∀ k, IsCompact (E k))
    (hE : ∀ k, Convex ℝ (E k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ E k)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : ∀ k, E k ⊆ V)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) (t : Fin M.letterCount → ℝ)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (Λ : ℝ≥0) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ (k : Fin 3) (y : Y n) (x anchor : G)
        (f : G → G), LipschitzWith Λ f →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ j z, z ∈ Q →
          ‖rescaledMapProfile (fun g => (π (f g)).toAdd) x
              (anchor * F.inclusionN (F.ExpN (F.N.equiv ((P k).vertex n y j))))
              (Real.log (scale n)) (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (h (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        ∃ path : Path (1 : G) (basedImage f
            (x * anchor * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
            (x * (anchor * F.inclusionN (probe k n y)) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))),
          PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
          ∀ s, ∃ z ∈ (fun w => A (w - h pivot)) '' E k,
            ‖(π (path s)).toAdd - scale n • z‖ ≤
              2 * scale n * ε + C * (1 + Real.log (2 + scale n)) := by
  classical
  dsimp only
  let B := ∑ k : Fin 3, (P k).amplitude
  let N₀ := ∑ k : Fin 3, (P k).length
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ => le_trans zero_le_one (P k).amplitude_ge_one)
  have hBk (k : Fin 3) : (P k).amplitude ≤ B :=
    Finset.single_le_sum (fun j _ => le_trans zero_le_one (P j).amplitude_ge_one)
      (Finset.mem_univ k)
  have hNk (k : Fin 3) : (P k).length ≤ N₀ :=
    Finset.single_le_sum (f := fun k : Fin 3 => (P k).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  obtain ⟨Q, C, hQ, hQV, hC, he⟩ := M.exists_three_template_profile_paths T F eW
    hExp realize haarD dynkinD π hπ hLip X hDnil bD₀ βD hβD scale hscale hscale0
    hunimod pivot E V hEc hE hpivot hV hVconv hEV hB N₀ Λ
  refine ⟨Q, C, hQ, hQV, hC, he.mono ?_⟩
  intro n hn k y x anchor f hf A offset ε hgood
  let vertex := fun j => anchor * F.inclusionN (F.ExpN (F.N.equiv ((P k).vertex n y j)))
  have hamp (j) : |(P k).coefficient n y j| ≤ B * Real.exp (scale n *
      (M.supportIn T hunimod eW).weightSupport (E k) ((P k).mode n j)) :=
    ((P k).coefficient_bound n y j).trans
      (mul_le_mul_of_nonneg_right (hBk k) (Real.exp_pos _).le)
  have hz : vertex 0 = anchor := by
    simp only [vertex, (P k).vertex_zero, map_zero, F.isExpN.map_zero, map_one, mul_one]
  have hend : vertex (Fin.last (P k).length) = anchor * F.inclusionN (probe k n y) :=
    congrArg (fun z => anchor * F.inclusionN z) ((P k).vertex_last n y)
  have hp := hn k (P k).length (hNk k) x vertex ((P k).mode n)
    ((P k).coefficient n y) (BoxProbeChains.ambient_step T M F hunimod eW b₀ (E k) γ t scale
      (probe k) (P k) n y anchor) hamp f hf A offset ε hgood
  obtain ⟨path, hm, hh⟩ := hp
  have he : basedImage f
      (x * anchor * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
      (x * (anchor * F.inclusionN (probe k n y)) *
        Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) =
      basedImage f (x * vertex 0 * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (x * vertex (Fin.last (P k).length) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) := by
    rw [hz, hend]
  exact ⟨path.cast rfl he, hm.cast rfl he, hh⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
