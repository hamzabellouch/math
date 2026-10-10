import OAI.Probability.InvariantIsing.Cavity.RepeatedBlockRemainderProjection
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFullTail
import OAI.Probability.InvariantIsing.Cavity.CavityFullTightness

namespace OAI

/-! Uniform physical projection tails for repeated constrained blocks
and a bounded number of remainder sites. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

theorem repeated_block_remainder_projection_uniform {n K r m depth rMax : ℕ}
    (hn : 0 < n) (hK : 3 ≤ K) (hr : r ≤ rMax)
    (C : Finset (Spin n)) (hC : C.Nonempty) (R : Finset (Spin r)) (hR : R.Nonempty)
    (μ : Measure (SpecialOrthogonal (n*K+r))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (n*K+r) → ℝ)
    (I : Fin m → Finset (Fin (n*K+r))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (J : Finset (Fin (n*K+r))) (i : Fin n) (b₀ : Fin K) :
    restrictedCavityFullDisorderTest (cavityProductSlice (spinBlockConstraint n K C) R)
      (cavityProductSlice_nonempty _ (spinBlockConstraint_nonempty C hC) R hR)
      μ T eig I u (cavityProjectionSiteTest J (Fin.castAdd r (finProdFinEquiv (i,b₀)))) ≤
        (n : ℝ) + rMax := by
  apply (repeated_block_remainder_projection_mean_le hn hK C hC R hR μ T eig I u hu J i b₀).trans
  have hk : (0:ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hk1 : (1:ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hr' : (r:ℝ) ≤ rMax := Nat.cast_le.mpr hr
  apply (div_le_iff₀ hk).mpr
  simp only [Nat.cast_add, Nat.cast_mul]
  nlinarith [mul_le_mul_of_nonneg_left hk1 (Nat.cast_nonneg rMax)]

theorem repeated_block_remainder_axes_mean {n K r m depth rMax : ℕ}
    (hn : 0 < n) (hK : 3 ≤ K) (hr : r ≤ rMax)
    (C : Finset (Spin n)) (hC : C.Nonempty) (R : Finset (Spin r)) (hR : R.Nonempty)
    (μ : Measure (SpecialOrthogonal (n*K+r))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (n*K+r) → ℝ)
    (I : Fin m → Finset (Fin (n*K+r))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (b₀ : Fin K) :
    restrictedCavityFullDisorderTest (cavityProductSlice (spinBlockConstraint n K C) R)
      (cavityProductSlice_nonempty _ (spinBlockConstraint_nonempty C hC) R hR)
      μ T eig I u (cavityProjectionAxesTest I (fun i => Fin.castAdd r (finProdFinEquiv (i,b₀)))) ≤
        (m : ℝ) * n * (n+rMax) := by
  change restrictedCavityFullDisorderTest _ _ μ T eig I u
    (fun U σ => ∑ t : Fin m × Fin n,
      cavityProjectionSiteTest (I t.1) (Fin.castAdd r (finProdFinEquiv (t.2,b₀))) U σ) ≤ _
  rw [restrictedCavityFullDisorderTest_sum _ _ μ T eig I u
    (fun t : Fin m × Fin n => cavityProjectionSiteTest (I t.1) (Fin.castAdd r (finProdFinEquiv (t.2,b₀))))
    (fun t => measurable_cavityProjectionSiteTest _ _)
    (Nat.cast_nonneg (n*K+r)) (fun t => cavityProjectionSiteTest_bound _ _)]
  calc
    _ ≤ ∑ _ : Fin m × Fin n, ((n : ℝ) + rMax) := Finset.sum_le_sum fun t _ =>
      repeated_block_remainder_projection_uniform hn hK hr C hC R hR μ T eig I u hu (I t.1) t.2 b₀
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]

theorem repeated_block_remainder_tightness {n m d depth rMax : ℕ} (hn : 0 < n)
    (K r : ℕ → ℕ) (hK : ∀ a, 3 ≤ K a) (hr : ∀ a, r a ≤ rMax)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (R : (a : ℕ) → Finset (Spin (r a))) (hR : ∀ a, (R a).Nonempty)
    (μ : (a : ℕ) → Measure (SpecialOrthogonal (n*K a+r a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (T : ℕ → LabeledTree depth) (eig : (a : ℕ) → Fin (n*K a+r a) → ℝ)
    (I : (a : ℕ) → Fin m → Finset (Fin (n*K a+r a)))
    (u : ℕ → ℕ → ℝ) (hu : ∀ a k, |u a k| ≤ 2) (b₀ : (a : ℕ) → Fin (K a))
    (good : (a : ℕ) → Set (SpecialOrthogonal (n*K a+r a)))
    (hgood : ∀ a, MeasurableSet (good a))
    (hp : Tendsto (fun a => (μ a).real (good a)) atTop (𝓝 1))
    (y : (a : ℕ) → SpecialOrthogonal (n*K a+r a) →
      (Fin 2 → Spin (n*K a+r a) × LabeledLeaf depth) → EuclideanSpace ℝ (Fin d))
    (hmy : ∀ a, Measurable (Function.uncurry (y a))) {c : ℝ} (hc : 0 < c)
    (hgeometry : ∀ a U, U ∈ good a → ∀ σ, c * ‖y a U σ‖ ^ 2 ≤
      cavityProjectionAxesTest (I a) (fun i => Fin.castAdd (r a) (finProdFinEquiv (i,b₀ a))) U σ) :
    ∀ ε > 0, ∃ B > 0, ∀ᶠ a in atTop,
      restrictedCavityFullDisorderTest (cavityProductSlice (spinBlockConstraint n (K a) C) (R a))
        (cavityProductSlice_nonempty _ (spinBlockConstraint_nonempty C hC) (R a) (hR a))
        (μ a) (T a) (eig a) (I a) (u a)
        (fun U σ => if B < ‖y a U σ‖ then 1 else 0) < ε := by
  have he : Tendsto (fun a => (μ a).real (good a)ᶜ) atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp
    simpa only [measureReal_compl (hgood _), probReal_univ, sub_self] using ht
  apply cavity_tightness_of_square_tail (C := (m : ℝ) * n * (n+rMax) / c) _ _ he
  intro a B hB
  have ht := restricted_full_tail_probability _ _ (μ a) (T a) (eig a) (I a) (u a) _
    (repeated_block_remainder_axes_mean hn (hK a) (hr a) C hC (R a) (hR a)
      (μ a) (T a) (eig a) (I a) (u a) (hu a) (b₀ a))
    (good a) (hgood a) (y a) (hmy a) hc hB (hgeometry a)
  convert ht using 1
  ring

end InvariantIsing

end

end OAI
