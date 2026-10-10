import OAI.Probability.InvariantIsing.Spectral.SpectralCanonicalWard
import OAI.Probability.InvariantIsing.Spectral.SpectralReconstruction
import OAI.Probability.InvariantIsing.Arrays.PathSymbolCongruence

namespace OAI

/-! Positive semidefinite array geometry supplies the diagonal bound needed
for nonnegative canonical group symbols. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma gramDiagonal_pair_le {B : RealArray} {d : ℝ} (h : GramDiagonal d B) :
    B 0 1 ≤ d := by
  have hp := (h.1 2).dotProduct_mulVec_nonneg (![1, -1] : Fin 2 → ℝ)
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, star_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
    Fin.val_zero, Fin.val_one, one_mul, mul_one, neg_mul, mul_neg] at hp
  rw [h.2 0, h.2 1, ← h.symm 0 1] at hp
  linarith

lemma spectralGroupQuantilePath_le_diagonal {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (a : Fin m) :
    ∀ᵐ s ∂pathMeasure, spectralGroupQuantilePath Q hn a s ≤ q a.castSucc := by
  have hx : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      spectralLinearArray (Pi.single a.castSucc 1) x 0 1 ≤ q a.castSucc := by
    filter_upwards [hG, hd] with x hx hdx
    simpa only [spectralLinearArray_single] using
      gramDiagonal_pair_le (spectralGram_diagonal hx q hdx a.castSucc)
  have hm : Measurable (fun x : SpectralArray (m + 1) =>
      spectralLinearArray (Pi.single a.castSucc 1) x 0 1) := by
    unfold spectralLinearArray spectralLinearEntry
    fun_prop
  have hy : ∀ᵐ r ∂spectralLinearLaw Q (Pi.single a.castSucc 1), r ≤ q a.castSucc :=
    (ae_map_iff hm.aemeasurable measurableSet_Iic).mpr hx
  rw [← spectralQuantilePath_law Q (Pi.single a.castSucc 1)
    (spectralCoordinate_unit hn a.castSucc)] at hy
  exact (ae_map_iff (spectralGroupQuantilePath Q hn a).measurable.aemeasurable
    measurableSet_Iic).mp hy

lemma OverlapPath.symbol_nonneg_ae (p : OverlapPath) (d : ℝ)
    (hd : ∀ᵐ s ∂pathMeasure, p s ≤ d) :
    ∀ᵐ s ∂pathMeasure, 0 ≤ pathSymbol d p s := by
  have hdv : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → p u ≤ d :=
    (ae_restrict_iff' measurableSet_Ioo).mp hd
  filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with s hs hsmem
  have ht : ∀ᵐ u ∂volume.restrict (Icc s 1), p u ≤ d := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hdv, volume.ae_ne (1 : ℝ)] with u hu hu1 humem
    exact hu ⟨hsmem.1.trans_le humem.1, lt_of_le_of_ne humem.2 hu1⟩
  have hi := intervalIntegral.integral_mono_ae_restrict hsmem.2.le
    p.monotone.intervalIntegrable intervalIntegrable_const ht
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hm := mul_le_mul_of_nonneg_left hs hsmem.1.le
  unfold pathSymbol
  nlinarith

lemma sum_pathSymbols_ae {ι : Type*} [Fintype ι] (pa : ι → OverlapPath)
    (p : OverlapPath) (q : ι → ℝ) (hq : ∑ a, q a = 1)
    (hsum : ∀ᵐ s ∂pathMeasure, (∑ a, pa a s) = p s) :
    ∀ᵐ s ∂pathMeasure, (∑ a, pathSymbol (q a) (pa a) s) = deficit p (p s) := by
  filter_upwards [hsum, ae_restrict_mem measurableSet_Ioo] with s hs hsmem
  simp only [pathSymbol, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hq, hs, ← intervalIntegral.integral_finsetSum
    (fun a _ => (pa a).monotone.intervalIntegrable),
    intervalIntegral_congr_path_ae hsum hsmem.1.le le_rfl hsmem.2.le]
  exact (deficit_at_path_eq_symbol p ⟨hsmem.1.le, hsmem.2.le⟩).symm

 theorem spectralCanonical_symbols {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hoff : ∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
      spectralOffWardResidual Q ρ eig a b Φ = 0)
    (hdiag : ∀ a b, spectralDiagonalWardResidual Q ρ eig a b = 0) :
    ∀ᵐ s ∂pathMeasure, ∀ a,
      pathSymbol (q a.castSucc) (spectralGroupQuantilePath Q hn a) s =
        projectedResolvent ρ eig hρ hρsum a
          (deficit (spectralSpinQuantilePath Q hP hn) (spectralSpinQuantilePath Q hP hn s)) := by
  let pa := spectralGroupQuantilePath Q hn
  let p := spectralSpinQuantilePath Q hP hn
  have hnn : ∀ᵐ s ∂pathMeasure, ∀ a, 0 ≤ pathSymbol (q a.castSucc) (pa a) s :=
    ae_all_iff.mpr fun a => (pa a).symbol_nonneg_ae (q a.castSucc)
      (spectralGroupQuantilePath_le_diagonal hG q hd hn a)
  have hws : ∀ᵐ s ∂pathMeasure, ∀ a b,
      ρ b * pathSymbol (q a.castSucc) (pa a) s -
        ρ a * pathSymbol (q b.castSucc) (pa b) s =
        (eig a - eig b) * pathSymbol (q a.castSucc) (pa a) s * pathSymbol (q b.castSucc) (pa b) s :=
    ae_all_iff.mpr fun a => ae_all_iff.mpr fun b =>
      (spectralCanonicalWard_pair hgg hG q hq hd hE hP hn ρ eig a b (hoff a b) (hdiag a b)).1
  have hsum : ∀ᵐ s ∂pathMeasure, (∑ a, pathSymbol (q a.castSucc) (pa a) s) = deficit p (p s) :=
    sum_pathSymbols_ae pa p (fun a => q a.castSucc) (spectralPartition_diagonal_sum hP q hd)
      (spectralPartition_quantile_sum hgg hG q hq hd (fun e => hE e e.injective) hP hn)
  filter_upwards [hnn, hws, hsum] with s hs hw hsum
  intro a
  rw [spectral_symbol_reconstruction ρ eig hρ hρsum
    (fun a => pathSymbol (q a.castSucc) (pa a) s) hs hw a, hsum]

end InvariantIsing

end

end OAI
