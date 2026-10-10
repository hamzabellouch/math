import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborSuffixRate
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxScaling

namespace OAI

/-! # Linked probe chains based at the original neighboring cells -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Original enlarged-box membership supplies both logarithmic base points
and their common vanishing error. Thus linking the actual probes requires
no separate logarithm or product-suffix estimate. -/
theorem exists_linked_probe_chains_of_neighbor_boxes
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW E) β.val)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop) (hs1 : ∀ n, 1 ≤ scale n)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (base step : ℕ → F.N.carrier)
    (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (Eprobe : Fin 3 → Set W) (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW bN (Eprobe k) β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i) scale (probe k)) :
    ∃ (origin finish : ℕ → cartanRootIdeal H) (ε : ℕ → ℝ),
      (∀ n, F.ExpN (F.N.equiv (origin n)) = base n) ∧
      (∀ n, F.ExpN (F.N.equiv (finish n)) = base n * step n) ∧
      (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      Nonempty (M.LinkedProbeChains T F hunimod eW bN Eprobe β
        (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
        scale probe P (fun n _ => origin n) (fun n _ => finish n) ε) := by
  let E' := (fun w => (1 + δ) • w) '' E
  have hcost (w : M.wordList) : M.boxCost T hunimod eW E' w =
      (1 + δ) * M.boxCost T hunimod eW E w :=
    M.boxCost_image_smul T hunimod eW hE hne (by linarith) w
  have hβ' : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW E') β.val := by
    refine ⟨hβ.1, ?_⟩
    intro γ hγ
    simp only [columnBasisWeight, hcost, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hβ.2 γ hγ) (by linarith)
  obtain ⟨v₀, v₁, η, hv₀, hv₁, hη0, hη, hb⟩ :=
    M.exists_neighbor_suffix_coordinate_rate T F hunimod eW dynkinN bN E' β hβ'
      scale R hs (fun n => zero_lt_one.trans_le (hs1 n)) hR0 hR base step hbase hstep
  let t := fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i
  have hβt : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (fun w => bracketWordExponent t w) β.val := by
    refine ⟨hβ.1, ?_⟩
    intro γ hγ
    simp only [t, columnBasisWeight, bracketWordExponent_const_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hβ.2 γ hγ) (by linarith)
  have hwidth : (M.supportIn T hunimod eW).weightSupport E' = t := by
    funext i
    exact (M.supportIn T hunimod eW).weightSupport_image_smul hE hne
      (show 0 ≤ 1 + δ by linarith) i
  have hb₀ : ∀ n (y : Y n),
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent t (β.val j)) (scale n)).equivFun (v₀ n)‖ ≤
          Real.exp (scale n * η n) := by
    intro n _
    simpa only [boxBasis, boxCost, hwidth] using (hb n).1
  have hb₁ : ∀ n (y : Y n),
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent t (β.val j)) (scale n)).equivFun (v₁ n)‖ ≤
          Real.exp (scale n * η n) := by
    intro n _
    simpa only [boxBasis, boxCost, hwidth] using (hb n).2
  obtain ⟨ε, hε0, hε, hL⟩ := M.exists_linked_probe_chains T F hunimod eW haarN dynkinN
    bN Eprobe β t hβt scale hs hs1 probe P (fun n _ => v₀ n) (fun n _ => v₁ n)
    (fun _ => measurable_const) (fun _ => measurable_const) η hη0 hη hb₀ hb₁
  exact ⟨v₀, v₁, ε, hv₀, hv₁, hε0, hε, hL⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
