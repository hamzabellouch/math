import OAI.Geometry.EinsteinFour.OperatorGreen

namespace OAI

/-! The derivative-slot curvature integration. Divergence freedom removes
the differentiated coefficient, and skew-symmetry leaves exactly one half
of the covariant commutator. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

abbrev CurvatureIndex := (Fin 4 × Fin 4) × (Fin 4 × Fin 4)

private def outerSwap : CurvatureIndex ≃ CurvatureIndex :=
  Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl _)

variable {Ω E : Type*} [TopologicalSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem divergence_sum_zero
    (A : CurvatureIndex → C(Ω, ℝ)) (X : Fin 4 → Fin 4 → C(Ω, E))
    (Z : Fin 4 → C(Ω, E))
    (hdiv : ∀ i j l x, (∑ k, A ((i, k), (j, l)) x) = 0) (x : Ω) :
    (∑ p : CurvatureIndex, A p x * inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) = 0 := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  calc
    _ = ∑ j, ∑ k, ∑ l, A ((i, k), (j, l)) x * inner ℝ (X i j x) (Z l x) :=
      Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, A ((i, k), (j, l)) x * inner ℝ (X i j x) (Z l x) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = 0 := by
      simp_rw [← Finset.sum_mul, hdiv, zero_mul]
      simp

private theorem skew_commutator_sum
    (A : CurvatureIndex → C(Ω, ℝ))
    (D : Fin 4 → Fin 4 → Fin 4 → C(Ω, E)) (Z : Fin 4 → C(Ω, E))
    (hskew : ∀ i k j l x, A ((k, i), (j, l)) x = -A ((i, k), (j, l)) x)
    (x : Ω) :
    -(∑ p : CurvatureIndex, A p x *
      inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) =
      (1 / 2 : ℝ) * (∑ p : CurvatureIndex, A p x *
        inner ℝ (D p.1.1 p.1.2 p.2.1 x - D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) := by
  have hs : (∑ p : CurvatureIndex, A p x *
      inner ℝ (D p.1.1 p.1.2 p.2.1 x) (Z p.2.2 x)) =
      -(∑ p : CurvatureIndex, A p x *
        inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) := by
    calc
      _ = ∑ p : CurvatureIndex, A (outerSwap p) x *
          inner ℝ (D (outerSwap p).1.1 (outerSwap p).1.2 (outerSwap p).2.1 x)
            (Z (outerSwap p).2.2 x) := (outerSwap.sum_comp _).symm
      _ = _ := by
        change (∑ p : CurvatureIndex, A ((p.1.2, p.1.1), p.2) x *
          inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) = _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro p _
        rw [hskew]
        ring
  simp_rw [inner_sub_left, mul_sub, Finset.sum_sub_distrib]
  rw [hs]
  ring

variable [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Integrating a divergence-free curvature coefficient leaves the precise
half-commutator term. All first-derivative weight terms are retained. -/
theorem weighted_curvature_green
    (φ : Fin 4 → ℝ → Ω ≃ᵐ Ω)
    (hφ : ∀ k, Continuous (fun p : ℝ × Ω => φ k p.1 p.2))
    (hμ : ∀ k t, MeasurePreserving (φ k t) μ μ)
    (m : C(Ω, ℝ)) (dm : Fin 4 → C(Ω, ℝ))
    (A dA : CurvatureIndex → C(Ω, ℝ))
    (Z : Fin 4 → C(Ω, E)) (X : Fin 4 → Fin 4 → C(Ω, E))
    (D : Fin 4 → Fin 4 → Fin 4 → C(Ω, E))
    (hdiv : ∀ i j l x, (∑ k, dA ((i, k), (j, l)) x) = 0)
    (hskew : ∀ i k j l x, A ((k, i), (j, l)) x = -A ((i, k), (j, l)) x)
    (hm : ∀ k t x, HasDerivAt (fun s => m (φ k s x)) (dm k (φ k t x)) t)
    (hA : ∀ p t x, HasDerivAt (fun s => A p (φ p.1.2 s x)) (dA p (φ p.1.2 t x)) t)
    (hZ : ∀ k j t x, HasDerivAt (fun s => Z j (φ k s x)) (X k j (φ k t x)) t)
    (hX : ∀ k i j t x, HasDerivAt (fun s => X i j (φ k s x)) (D k i j (φ k t x)) t) :
    (∫ x, ∑ p : CurvatureIndex,
      (m x * A p x * inner ℝ (X p.1.1 p.2.1 x) (X p.1.2 p.2.2 x) +
        dm p.1.2 x * A p x * inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) ∂μ) =
      (1 / 2 : ℝ) * (∫ x, ∑ p : CurvatureIndex, m x * A p x *
        inner ℝ (D p.1.1 p.1.2 p.2.1 x - D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x) ∂μ) := by
  have hL (p : CurvatureIndex) : Integrable (fun x =>
      m x * A p x * inner ℝ (X p.1.1 p.2.1 x) (X p.1.2 p.2.2 x) +
        dm p.1.2 x * A p x * inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ (p : CurvatureIndex) : Integrable (fun x => m x * A p x *
      inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hK (p : CurvatureIndex) : Integrable (fun x => m x * dA p x *
      inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : (∫ x, ∑ p : CurvatureIndex,
      (m x * A p x * inner ℝ (X p.1.1 p.2.1 x) (X p.1.2 p.2.2 x) +
        dm p.1.2 x * A p x * inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) ∂μ) =
      -(∫ x, ∑ p : CurvatureIndex, m x * A p x *
        inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x) ∂μ) -
      (∫ x, ∑ p : CurvatureIndex, m x * dA p x *
        inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x) ∂μ) := by
    rw [integral_finsetSum _ (fun p _ => hL p),
      integral_finsetSum _ (fun p _ => hJ p),
      integral_finsetSum _ (fun p _ => hK p)]
    simp_rw [weighted_scalar_coefficient_green μ _ (hφ _) (hμ _) m (dm _) (A _) (dA _)
      (X _ _) (D _ _ _) (Z _) (X _ _) (hm _) (hA _) (hX _ _ _) (hZ _ _)]
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hz : (∫ x, ∑ p : CurvatureIndex, m x * dA p x *
      inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x) ∂μ) = 0 := by
    have he (x : Ω) : (∑ p : CurvatureIndex, m x * dA p x *
        inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) = 0 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, divergence_sum_zero dA X Z hdiv x, mul_zero]
    simp_rw [he]
    simp
  rw [hs, hz, sub_zero, ← integral_neg, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have h := skew_commutator_sum A D Z hskew x
  have hm' := congrArg (fun z : ℝ => m x * z) h
  rw [mul_left_comm (m x) (1 / 2 : ℝ)] at hm'
  simpa only [mul_neg, Finset.mul_sum, mul_assoc] using hm'

end

end PositiveEinsteinFour.Averages

end OAI
