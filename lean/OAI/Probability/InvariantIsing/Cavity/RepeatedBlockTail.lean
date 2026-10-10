import OAI.Probability.InvariantIsing.Cavity.RepeatedBlockProjection
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFullTail
import OAI.Probability.InvariantIsing.Cavity.CavityFullTightness

namespace OAI

/-! Projection-based radial tails for the physical model on repeated
constrained blocks, uniformly in the number of blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

theorem repeated_block_projection_axes_mean {n K m depth : ℕ}
    (hn : 0 < n) (hK : 3 ≤ K) (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (n*K))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (n*K) → ℝ)
    (I : Fin m → Finset (Fin (n*K))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (b₀ : Fin K) :
    restrictedCavityFullDisorderTest (spinBlockConstraint n K C) (spinBlockConstraint_nonempty C hC)
      μ T eig I u (cavityProjectionAxesTest I (fun i => finProdFinEquiv (i,b₀))) ≤
        (m : ℝ) * n * n := by
  change restrictedCavityFullDisorderTest _ _ μ T eig I u
    (fun U σ => ∑ t : Fin m × Fin n,
      cavityProjectionSiteTest (I t.1) (finProdFinEquiv (t.2,b₀)) U σ) ≤ _
  rw [restrictedCavityFullDisorderTest_sum _ _ μ T eig I u
    (fun t : Fin m × Fin n => cavityProjectionSiteTest (I t.1) (finProdFinEquiv (t.2,b₀)))
    (fun t => measurable_cavityProjectionSiteTest _ _)
    (Nat.cast_nonneg (n*K)) (fun t => cavityProjectionSiteTest_bound _ _)]
  calc
    _ ≤ ∑ _ : Fin m × Fin n, (n : ℝ) := Finset.sum_le_sum fun t _ =>
      repeated_block_projection_mean_le hn hK C hC μ T eig I u hu (I t.1) t.2 b₀
    _ = _ := by simp [Fintype.card_prod, Nat.cast_mul, mul_assoc]

theorem repeated_block_tail_probability {n K m d depth : ℕ}
    (hn : 0 < n) (hK : 3 ≤ K) (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (n*K))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (n*K) → ℝ)
    (I : Fin m → Finset (Fin (n*K))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (b₀ : Fin K) (good : Set (SpecialOrthogonal (n*K))) (hgood : MeasurableSet good)
    (y : SpecialOrthogonal (n*K) → (Fin 2 → Spin (n*K) × LabeledLeaf depth) →
      EuclideanSpace ℝ (Fin d)) (hmy : Measurable (Function.uncurry y))
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hgeometry : ∀ U ∈ good, ∀ σ, c * ‖y U σ‖ ^ 2 ≤
      cavityProjectionAxesTest I (fun i => finProdFinEquiv (i,b₀)) U σ) :
    restrictedCavityFullDisorderTest (spinBlockConstraint n K C) (spinBlockConstraint_nonempty C hC)
      μ T eig I u (fun U σ => if R < ‖y U σ‖ then 1 else 0) ≤
        μ.real goodᶜ + ((m : ℝ) * n * n) / (c * R ^ 2) :=
  restricted_full_tail_probability _ _ μ T eig I u _
    (repeated_block_projection_axes_mean hn hK C hC μ T eig I u hu b₀)
    good hgood y hmy hc hR hgeometry

theorem repeated_block_tightness {n m d depth : ℕ} (hn : 0 < n)
    (K : ℕ → ℕ) (hK : ∀ r, 3 ≤ K r) (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : (r : ℕ) → Measure (SpecialOrthogonal (n*K r)))
    [∀ r, IsProbabilityMeasure (μ r)] [∀ r, (μ r).IsMulRightInvariant]
    (T : ℕ → LabeledTree depth) (eig : (r : ℕ) → Fin (n*K r) → ℝ)
    (I : (r : ℕ) → Fin m → Finset (Fin (n*K r)))
    (u : ℕ → ℕ → ℝ) (hu : ∀ r k, |u r k| ≤ 2) (b₀ : (r : ℕ) → Fin (K r))
    (good : (r : ℕ) → Set (SpecialOrthogonal (n*K r)))
    (hgood : ∀ r, MeasurableSet (good r))
    (hp : Tendsto (fun r => (μ r).real (good r)) atTop (𝓝 1))
    (y : (r : ℕ) → SpecialOrthogonal (n*K r) →
      (Fin 2 → Spin (n*K r) × LabeledLeaf depth) → EuclideanSpace ℝ (Fin d))
    (hmy : ∀ r, Measurable (Function.uncurry (y r))) {c : ℝ} (hc : 0 < c)
    (hgeometry : ∀ r U, U ∈ good r → ∀ σ, c * ‖y r U σ‖ ^ 2 ≤
      cavityProjectionAxesTest (I r) (fun i => finProdFinEquiv (i,b₀ r)) U σ) :
    ∀ ε > 0, ∃ R > 0, ∀ᶠ r in atTop,
      restrictedCavityFullDisorderTest (spinBlockConstraint n (K r) C)
        (spinBlockConstraint_nonempty C hC) (μ r) (T r) (eig r) (I r) (u r)
        (fun U σ => if R < ‖y r U σ‖ then 1 else 0) < ε := by
  have he : Tendsto (fun r => (μ r).real (good r)ᶜ) atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp
    simpa only [measureReal_compl (hgood _), probReal_univ, sub_self] using ht
  apply cavity_tightness_of_square_tail (C := (m : ℝ) * n * n / c) _ _ he
  intro r R hR
  have ht := repeated_block_tail_probability hn (hK r) C hC (μ r) (T r) (eig r) (I r)
    (u r) (hu r) (b₀ r) (good r) (hgood r) (y r) (hmy r) hc hR (hgeometry r)
  convert ht using 1
  ring

end InvariantIsing

end

end OAI
