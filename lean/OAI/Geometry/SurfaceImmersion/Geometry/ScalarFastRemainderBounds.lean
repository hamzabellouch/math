import OAI.Geometry.SurfaceImmersion.Atlas.FastPhaseBounds
import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialScalar

namespace OAI

/-! The finite high-order metric tail has the required `z^L` gain after
fast evaluation, with a slow-scale loss independent of derivative order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Expression
open LocalPeriodicExpansion WeightedEstimates

theorem compact_scalar_fast_bound {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K → WeightedBound S s (m + e.order) B (lowJet G) →
      ∀ (U : Family S ℝ), Represents G e U →
        WeightedBound S z m (D / s ^ e.loss) (U.fastValue ℓ z) := by
  obtain ⟨D, hD, hd⟩ := compact_periodic_fast_bound S.isOpen hO hK hKO e he ℓ m B hB
  exact ⟨D, hD, fun G s z hz hzs hs1 hG hGK hb U hR =>
    hd G s z hz hzs hs1 hG hGK hb (fun p t => U.val p t) hR⟩

/-- This is the finite-tail estimate used for the pullback-metric error.
Every coefficient is an actual represented family; its derivatives are not
postulated as hypotheses. -/
theorem compact_tail_bound {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (R : ℕ → Expression) (hRs : ∀ r, (R r).SmoothCoeffs O) (L T N d : ℕ)
    (hN : ∀ r ∈ Finset.Ico L T, (R r).order ≤ N)
    (hd : ∀ r ∈ Finset.Ico L T, (R r).loss ≤ d)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K → WeightedBound S s (m + N) B (lowJet G) →
      ∀ (U : ℕ → Family S ℝ), (∀ r ∈ Finset.Ico L T, Represents G (R r) (U r)) →
        WeightedBound S z m (D * z ^ L / s ^ d)
          (fun p => ∑ r ∈ Finset.Ico L T, z ^ r * (U r).fastValue ℓ z p) := by
  classical
  have hex := fun r => compact_scalar_fast_bound (S := S) hO hK hKO (R r) (hRs r) ℓ m B hB
  choose C hC hc using hex
  refine ⟨∑ r ∈ Finset.Ico L T, C r, Finset.sum_nonneg (fun r _ => hC r), ?_⟩
  intro G s z hz hzs hs1 hG hGK hb U hrep
  have hs : 0 < s := hz.trans_le hzs
  have hz1 : z ≤ 1 := hzs.trans hs1
  have hterm (r : ℕ) (hr : r ∈ Finset.Ico L T) :
      WeightedBound S z m (C r * z ^ L / s ^ d)
        (fun p => z ^ r • (U r).fastValue ℓ z p) := by
    have hh := hc r G s z hz hzs hs1 hG hGK
      (hb.mono_order (Nat.add_le_add_left (hN r hr) m)) (U r) (hrep r hr)
    have hh' : WeightedBound S z m (C r / s ^ d) ((U r).fastValue ℓ z) :=
      hh.mono_const (div_le_div_of_nonneg_left (hC r) (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (hd r hr)))
    have hmul := hh'.const_smul S.isOpen.uniqueDiffOn ((U r).fastValue_smooth ℓ z) (z ^ r)
    apply hmul.mono_const
    rw [abs_of_nonneg (pow_nonneg hz.le _)]
    calc
      z ^ r * (C r / s ^ d) ≤ z ^ L * (C r / s ^ d) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hz.le hz1 (Finset.mem_Ico.mp hr).1)
          (div_nonneg (hC r) (pow_nonneg hs.le _))
      _ = C r * z ^ L / s ^ d := by ring
  have hh := WeightedBound.finset_sum S.isOpen.uniqueDiffOn hz.le (Finset.Ico L T)
    (fun r => C r * z ^ L / s ^ d) (fun r p => z ^ r • (U r).fastValue ℓ z p)
    (fun r _ => (contDiffOn_const (c := z ^ r)).smul ((U r).fastValue_smooth ℓ z)) hterm
  have heq : (∑ r ∈ Finset.Ico L T, C r * z ^ L / s ^ d) =
      (∑ r ∈ Finset.Ico L T, C r) * z ^ L / s ^ d := by
    rw [← Finset.sum_div, ← Finset.sum_mul]
  rw [heq] at hh
  simpa only [smul_eq_mul] using hh

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
