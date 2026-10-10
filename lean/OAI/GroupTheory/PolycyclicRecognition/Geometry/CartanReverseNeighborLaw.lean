import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellPairLaws
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborSuffixRate

namespace OAI

/-! # Reversing the actual neighboring pair for the opposite offset inequality -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Reversing the deterministic root step replaces the joint law by its
coordinate swap, using exactly the Haar cell based at `base * step`. -/
theorem reversed_neighbor_cell_limit
    [IsTopologicalGroup F.N.carrier]
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (scale : ℕ → ℝ) (base step : ℕ → F.N.carrier)
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β (scale n) (base n))
      (fun q => (profile n q, profile n (q * step n)))) atTop (𝓝 ν)) :
    Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (base n * step n))
      (fun q => (profile n q, profile n (q * (step n)⁻¹)))) atTop
      (𝓝 (ProbabilityMeasure.map ν Prod.swap)) := by
  let μ := fun n => M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
    E β (scale n) (base n)
  let pair := fun n q => (profile n q, profile n (q * step n))
  have hp' n : Measurable (pair n) :=
    (hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)
  have he := sampled_projection_tendsto μ pair hp' ν hν Prod.swap continuous_swap
  convert he using 1
  funext n
  have hr := M.translated_groupBox_profile_law_mul_right T F hunimod eW
    haarN chartN hchartN b₀ E β (scale n) (base n) (step n)
    (fun q => (profile n q, profile n (q * (step n)⁻¹)))
    ((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable))
  simpa only [μ, pair, Function.comp_def, Prod.swap_prod_mk, mul_inv_cancel_right] using hr.symm

/-- Swapped supported profiles remain supported in the reversed law. -/
theorem swapped_pair_mem_support
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (ν : ProbabilityMeasure (S × S)) {f : S × S} (hf : f ∈ (ν : Measure (S × S)).support) :
    f.swap ∈ (ProbabilityMeasure.map ν Prod.swap : Measure (S × S)).support :=
  mem_support_map_of_continuous ν Prod.swap continuous_swap hf

/-- The inverse of an actual root step has the same generator and negated
parameter; the allowed amplitude is unchanged. -/
theorem inverse_root_step (hExp : IsGroupExponential Exp)
    (i : Fin M.letterCount) (step : F.N.carrier) (time : ℝ)
    (hstep : F.inclusionN step = Exp (time • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) :
    F.inclusionN step⁻¹ = Exp ((-time) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
  rw [map_inv, hstep, neg_smul, hExp.map_neg]

/-- The new base and the inverse step lie in the same enlarged box with
one common subexponential radius. This supplies the original box hypotheses
when the offset volume comparison is applied in reverse. -/
theorem exists_reverse_neighbor_radius
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop) (hs0 : ∀ n, 0 ≤ scale n)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (base step : ℕ → F.N.carrier)
    (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n)) :
    ∃ R' : ℕ → ℝ, (∀ n, R n ≤ R' n) ∧ (∀ n, 0 ≤ R' n) ∧
      HasSubexponentialUpperBoundSeq scale R' ∧ ∀ n,
      base n * step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R' n) ∧
      (step n)⁻¹ ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R' n) := by
  obtain ⟨C, hC, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW
    F.N.equiv F.ExpN F.isExpN dynkinN b₀
  let P := fun n => C * (1 + (2 : ℝ)) ^ M.bound * (1 + R n) ^ M.bound
  have hP0 n : 0 ≤ P n := by
    have := hR0 n
    dsimp only [P]
    positivity
  have hP : HasSubexponentialUpperBoundSeq scale P := by
    apply (sequence_subexponential_upper_const hs (C * (1 + (2 : ℝ)) ^ M.bound)).mul
      (((sequence_subexponential_upper_const hs 1).add hR hs).pow hs
        (Eventually.of_forall (fun n => by linarith [hR0 n])) M.bound)
    exact Eventually.of_forall (fun _ => mul_nonneg hC (by positivity))
  refine ⟨fun n => R n + P n, fun n => le_add_of_nonneg_right (hP0 n),
    fun n => add_nonneg (hR0 n) (hP0 n), hR.add hP hs, ?_⟩
  intro n
  have hpair : ∀ i : Fin 2, ![base n, step n] i ∈
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) (R n) := by
    intro i
    fin_cases i
    · exact hbase n
    · exact hstep n
  have hm : base n * step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      E β (scale n) (P n) := by
    simpa [P, List.ofFn_succ] using hprod E β hβ (scale n) (hs0 n) 2 (R n) (hR0 n) _ hpair
  constructor
  · obtain ⟨v, hv, hb⟩ := hm
    exact ⟨v, hv, hb.trans (le_add_of_nonneg_left (hR0 n))⟩
  · obtain ⟨v, hv, hb⟩ := M.groupBox_inv_mem T hunimod eW F.N.equiv F.ExpN
      F.isExpN E β (scale n) (R n) (hstep n)
    exact ⟨v, hv, hb.trans (le_add_of_nonneg_right (hP0 n))⟩

/-- Reversal preserves every original input needed by the opposite volume
test, after enlarging only the subexponential radius. The limiting law is
the coordinate swap of the original law, with the original supported pair
swapped as well. -/
theorem exists_reversed_neighbor_data
    [IsTopologicalGroup F.N.carrier]
    (hExp : IsGroupExponential Exp)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop) (hs0 : ∀ n, 0 ≤ scale n)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (base step : ℕ → F.N.carrier)
    (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      E β (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      E β (scale n) (R n))
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [BorelSpace S] [BorelSpace (S × S)]
    (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        E β (scale n) (base n))
      (fun q => (profile n q, profile n (q * step n)))) atTop (𝓝 ν))
    (f : S × S) (hf : f ∈ (ν : Measure (S × S)).support)
    (i : Fin M.letterCount) (time : ℕ → ℝ) (q : ℝ)
    (htime : ∀ n, |time n| ≤ R n * Real.exp (q * scale n))
    (hroot : ∀ n, F.inclusionN (step n) =
      Exp (time n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) :
    ∃ R' : ℕ → ℝ, (∀ n, R n ≤ R' n) ∧ (∀ n, 0 ≤ R' n) ∧
      HasSubexponentialUpperBoundSeq scale R' ∧
      (∀ n,
        base n * step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
          E β (scale n) (R' n) ∧
        (step n)⁻¹ ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
          E β (scale n) (R' n) ∧
        |-time n| ≤ R' n * Real.exp (q * scale n) ∧
        F.inclusionN (step n)⁻¹ =
          Exp ((-time n) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ∧
      Tendsto (fun n => ProbabilityMeasure.map
        (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
          E β (scale n) (base n * step n))
        (fun q => (profile n q, profile n (q * (step n)⁻¹)))) atTop
        (𝓝 (ProbabilityMeasure.map ν Prod.swap)) ∧
      f.swap ∈ (ProbabilityMeasure.map ν Prod.swap : Measure (S × S)).support := by
  obtain ⟨R', hRR', hR'0, hR', hb⟩ :=
    M.exists_reverse_neighbor_radius T F hunimod eW dynkinN b₀ E β hβ scale R
      hs hs0 hR0 hR base step hbase hstep
  refine ⟨R', hRR', hR'0, hR', ?_, ?_, swapped_pair_mem_support ν hf⟩
  · intro n
    refine ⟨(hb n).1, (hb n).2, ?_, M.inverse_root_step F hExp i (step n) (time n) (hroot n)⟩
    rw [abs_neg]
    exact (htime n).trans
      (mul_le_mul_of_nonneg_right (hRR' n) (Real.exp_pos _).le)
  · exact M.reversed_neighbor_cell_limit T F hunimod eW haarN chartN hchartN b₀
      E β scale base step profile hp ν hν

end PolycyclicRecognition.CartanWordModel

end

end OAI
