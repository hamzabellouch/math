import OAI.Geometry.SurfaceImmersion.Atlas.FastPhaseBounds
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicFiniteAnsatz

namespace OAI

/-! Uniform fast-scale estimates for finite collections of the actual
periodic correctors, and for their finite oscillatory sum. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates

/-- Finitely many coefficients admit one common prefactor and one common
scale loss, also in the Euclidean norm on the target. -/
theorem compact_finite_fast_bound {ι : Type*} [Fintype ι]
    {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (R : ι → VectorExpression) (hRs : ∀ a, (R a).SmoothCoeffs O)
    (N d : ℕ) (hN : ∀ a i, (R a i).order ≤ N) (hd : ∀ a i, (R a i).loss ≤ d)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K → WeightedBound S s (m + N) B (lowJet G) →
      ∀ (U : ι → Family S R4), (∀ a, Represents G (R a) (U a)) → ∀ a,
        WeightedBound S z m (D / s ^ d) ((U a).fastValue ℓ z) := by
  classical
  have hex := fun a : ι × Fin 4 => compact_fast_bound (S := S) hO hK hKO (R a.1) (hRs a.1) a.2 ℓ m B hB
  choose C hC hc using hex
  let C₀ : ℝ := ∑ a : ι × Fin 4, C a
  let L : (Fin 4 → ℝ) →L[ℝ] R4 := (EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap
  refine ⟨‖L‖ * C₀, mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun a _ => hC a), ?_⟩
  intro G s z hz hzs hs1 hG hGK hb U hrep a
  have hs : 0 < s := hz.trans_le hzs
  have hcoord (i : Fin 4) :
      WeightedBound S z m (C₀ / s ^ d) (fun p => (U a).fastValue ℓ z p i) := by
    have hi := hc (a, i) G s z hz hzs hs1 hG hGK
      (hb.mono_order (Nat.add_le_add_left (hN a i) m)) (U a) (hrep a)
    apply hi.mono_const
    calc
      C (a, i) / s ^ (R a i).loss ≤ C (a, i) / s ^ d :=
        div_le_div_of_nonneg_left (hC _) (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 (hd a i))
      _ ≤ C₀ / s ^ d := div_le_div_of_nonneg_right
        (Finset.single_le_sum (fun b _ => hC b) (Finset.mem_univ (a, i))) (pow_nonneg hs.le _)
  have hsmooth (i : Fin 4) : ContDiffOn ℝ ∞ (fun p => (U a).fastValue ℓ z p i) S :=
    (show R4 →L[ℝ] ℝ from EuclideanSpace.proj i).contDiff.comp_contDiffOn ((U a).fastValue_smooth ℓ z)
  have hp := WeightedBound.pi S.isOpen.uniqueDiffOn hz
    (div_nonneg (Finset.sum_nonneg fun b _ => hC b) (pow_nonneg hs.le _)) hsmooth hcoord
  have hp' := hp.linear S.isOpen.uniqueDiffOn hz.le (contDiffOn_pi.mpr hsmooth) L
  have heq : (L ∘ fun p i => (U a).fastValue ℓ z p i) = (U a).fastValue ℓ z := by
    funext p
    exact (EuclideanSpace.equiv (Fin 4) ℝ).symm_apply_apply _
  rw [heq] at hp'
  convert hp' using 1
  ring

/-- The finite ansatz differs from the slow map by `O_z(z s⁻ᵈ)`.
The exponent `d` is supplied by the finite jet expressions and is independent
of `m`; there is no assumption on an unconstructed correction. -/
theorem compact_finite_ansatz_bound {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (R : ℕ → VectorExpression) (L N d : ℕ)
    (hRs : ∀ i < L, (R i).SmoothCoeffs O)
    (hN : ∀ i < L, ∀ a, (R i a).order ≤ N)
    (hd : ∀ i < L, ∀ a, (R i a).loss ≤ d)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K → WeightedBound S s (m + N) B (lowJet G) →
      ∀ (F : Base → R4) (U : ℕ → Family S R4),
        (∀ i < L, Represents G (R i) (U i)) →
        WeightedBound S z m (D * z / s ^ d)
          (fun p => finiteAnsatz F U ℓ L z p - F p) := by
  obtain ⟨C, hC, hc⟩ := compact_finite_fast_bound hO hK hKO
    (fun i : Fin L => R i) (fun i => hRs i i.isLt) N d
    (fun i => hN i i.isLt) (fun i => hd i i.isLt) ℓ m B hB
  refine ⟨L * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro G s z hz hzs hs1 hG hGK hb F U hrep
  have hs : 0 < s := hz.trans_le hzs
  have hz1 : z ≤ 1 := hzs.trans hs1
  have hbU : ∀ i < L, WeightedBound S z m (C / s ^ d) ((U i).fastValue ℓ z) := by
    intro i hi
    exact hc G s z hz hzs hs1 hG hGK hb (fun j : Fin L => U j)
      (fun j => hrep j j.isLt) ⟨i, hi⟩
  have hterm (i : ℕ) (hi : i ∈ Finset.range L) :
      WeightedBound S z m (z * (C / s ^ d))
        (fun p => z ^ (i + 1) • (U i).fastValue ℓ z p) := by
    have hh := (hbU i (Finset.mem_range.mp hi)).const_smul S.isOpen.uniqueDiffOn
      ((U i).fastValue_smooth ℓ z) (z ^ (i + 1))
    apply hh.mono_const
    rw [abs_of_nonneg (pow_nonneg hz.le _)]
    apply mul_le_mul_of_nonneg_right _ (div_nonneg hC (pow_nonneg hs.le _))
    simpa only [pow_one] using pow_le_pow_of_le_one hz.le hz1 (by omega : 1 ≤ i + 1)
  have hh := WeightedBound.finset_sum S.isOpen.uniqueDiffOn hz.le (Finset.range L)
    (fun _ => z * (C / s ^ d))
    (fun i p => z ^ (i + 1) • (U i).fastValue ℓ z p)
    (fun i _ => (contDiffOn_const (c := z ^ (i + 1))).smul ((U i).fastValue_smooth ℓ z)) hterm
  have heq : (fun p => finiteAnsatz F U ℓ L z p - F p) =
      (fun p => ∑ i ∈ Finset.range L, z ^ (i + 1) • (U i).fastValue ℓ z p) := by
    funext p
    simp only [finiteAnsatz, add_sub_cancel_left]
  rw [heq]
  convert hh using 1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
