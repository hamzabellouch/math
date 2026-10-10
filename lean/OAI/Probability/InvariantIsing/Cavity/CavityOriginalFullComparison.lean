import OAI.Probability.InvariantIsing.Cavity.CavityOriginalTreeLimit
import OAI.Probability.InvariantIsing.Cavity.CavityFullTreeCutoff

namespace OAI

/-! The full original Gibbs law converges, through the proved geometric
cutoff, to the actual fresh-Haar restricted law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_original_full_haar_comparison {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (η : (j : ℕ) → Measure ((a : Fin m) → Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j, IsProbabilityMeasure (η j)]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : (j : ℕ) → Measure (LabeledTree (depth j))) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2) (t : ℝ)
    (good : (j : ℕ) → Set (SpecialOrthogonal (N j+n)))
    (hgood : ∀ j, MeasurableSet (good j))
    (hp : Tendsto (fun j => ((μ j).map (cavityOrientationLift
      (Nat.add_pos_left (hN j) n))).real (good j)) atTop (𝓝 1))
    {L M : ℝ} (hL : 0 < L)
    (hbound : ∀ j U, U ∈ good j → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g j) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
    (hM : 0 ≤ M)
    (F : (j : ℕ) → (Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) → ℝ)
    (hF : ∀ j σ, |F j σ| ≤ M) (A : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0))
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop) :
    let E := fun j => cavityBaseGroupEquiv (k j) (e j) a₀
    let eig := fun j => diagonalPerturbedEigenvalues (fun i => lam ((E j).symm i).1)
      (cavitySpectralGroup (fun i => ((E j).symm i).1)) (v j) t
    let τ := fun j => cavityFactorSize (t • A.1) (t • A.2.1) (t • A.2.2) * (1+(b j)^2)
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ r in atTop,
      |(∫ T, cavityFullTest ((μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))) T
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) t)
        (cavitySpectralGroup (g r)) (u r)
        (fun σ => F r (fun i => (((cavitySpinSplit (N r) n (σ i).1).1,(σ i).2),
          (cavitySpinSplit (N r) n (σ i).1).2))) ∂θ r) -
      ∫ p, cavityWeightedReplicaMean ((cavityRotationProbability (eig r)
          (cavitySpectralGroup (fun i => ((E r).symm i).1)) (u r) p.1).prod (uniformSpinPrior n))
        (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
          (cavityRotationVectors (cavityBaseGroupDimension (k r) a₀) (E r))
          (cavityCanonicalGroupFrame (k r) (e r) a₀ (hk r))
          (t • A.1) (t • A.2.1) (t • A.2.2) (τ j) (b j) (p,x)) (F r)
        ∂((((ν r).prod (θ r)).prod gaussianCoordinates).prod (η r))| < ε := by
  intro E eig τ
  let μO := fun j => (μ j).map (cavityOrientationLift (Nat.add_pos_left (hN j) n))
  let (j : ℕ) : IsProbabilityMeasure (μO j) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_cavityOrientationLift _).aemeasurable).mpr inferInstance
  let (j : ℕ) : (μO j).IsMulRightInvariant := cavityOrientationLift_measure_rightInvariant _ _
  let eigFull := fun j => diagonalPerturbedEigenvalues (fun i => lam (g j i))
    (cavitySpectralGroup (g j)) (v j) t
  let test := fun j (σ : Fin 2 → Spin (N j+n) × LabeledLeaf (depth j)) =>
    F j (fun i => (((cavitySpinSplit (N j) n (σ i).1).1,(σ i).2),
      (cavitySpinSplit (N j) n (σ i).1).2))
  let B := fun j (U : SpecialOrthogonal (N j+n)) =>
    cavityConcreteComplement es B₀ (cavityCompressionGrams (g j) (cavitySpecialOrthogonal U))
  have hmB : ∀ j, Measurable (B j) := fun j =>
    (measurable_cavityConcreteComplement es B₀).comp
      ((measurable_cavityCompressionGrams (g j)).comp
        (show Measurable (cavitySpecialOrthogonal (N := N j+n)) from
          measurable_subtype_coe.subtype_mk))
  have hcut := cavity_full_tree_cutoff_sequence N depth
    (fun j => Nat.add_pos_left (hN j) n) μO θ eigFull g u hu B hmB
    (fun j U => cavityConcreteComplement_gram (g j) es B₀ (cavitySpecialOrthogonal U))
    good hgood hp hL hbound test hM (fun j σ => hF j _) b hb hblim
  intro ε hε
  filter_upwards [hcut (ε/2) (by positivity)] with j hj
  have hmatch := cavity_original_restricted_tree_limit N depth hN hNlim g k ek e es B₀ a₀ hk η
    l w hg hln hw μ ν θ lam v hv u hu t (hb j).le hM F hF A hprob
  have hmatch' := hmatch.eventually
    (Metric.ball_mem_nhds 0 (show 0 < ε/2 by positivity))
  filter_upwards [hj,hmatch'] with r hr hr'
  rw [Real.dist_eq,sub_zero] at hr'
  have heq :
      (∫ T, ∫ U, cavityOriginalGeometricMean (g r) (cavityConcreteComplement es B₀) T
        (eigFull r) (u r) (1+(b j)^2)
        (fun σ => F r (fun i => (((σ i).1.1,(σ i).2),(σ i).1.2)))
        (cavityOrientationLift (Nat.add_pos_left (hN r) n) U) ∂μ r ∂θ r) =
      ∫ T, cavityFullCutoffDisorderTest (μO r) T (eigFull r) (cavitySpectralGroup (g r)) (u r)
        (cavitySpecialCutoff (g r) (B r) (b j)) (fun _ => test r) ∂θ r := by
    apply integral_congr_ae
    filter_upwards [] with T
    exact cavity_original_radial_cutoff (μ r) (Nat.add_pos_left (hN r) n) (g r)
      (cavityConcreteComplement es B₀) (measurable_cavityConcreteComplement es B₀) T
      (eigFull r) (u r) (hb j).le _
  change |(∫ T, cavityFullTest (μO r) T (eigFull r) (cavitySpectralGroup (g r)) (u r)
    (test r) ∂θ r) - _| < ε
  rw [heq] at hr'
  exact (abs_sub_le _ _ _).trans_lt (add_lt_add hr hr') |>.trans_eq (by ring)

end InvariantIsing

end

end OAI
