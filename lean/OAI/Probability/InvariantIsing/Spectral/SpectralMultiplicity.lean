import OAI.Probability.InvariantIsing.Spectral.SpectralPermutation
import OAI.Probability.InvariantIsing.Spectral.SpectralCountAlignment

namespace OAI

/-! The spectral multiplicity comparison, with an arbitrary deterministic
magnetic field. The relative count error is supplied as a scalar bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

/-- Manuscript Lemma gen:counts. Taking `r` to be the maximum relative
multiplicity error gives its displayed bound. -/
theorem meanPressure_multiplicity_comparison {N m : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (a b : Fin N → Fin m) (ha : Function.Surjective a) (hb : Function.Surjective b)
    (lam : Fin m → ℝ) (c : Fin N → ℝ)
    (K : ℝ) (hK : ∀ v, |lam v| ≤ K)
    (L r : ℝ) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hdiam : ∀ v w, |lam v - lam w| ≤ L)
    (herr : ∀ v,
      |((Finset.univ.filter fun i => a i = v).card : ℝ) -
        ((Finset.univ.filter fun i => b i = v).card : ℝ)| ≤
      r * min ((Finset.univ.filter fun i => a i = v).card : ℝ)
        ((Finset.univ.filter fun i => b i = v).card : ℝ)) :
    |(∫ U, rotatedPressure (fun i => lam (b i)) (specialRotation U) c ∂μ) -
      ∫ U, rotatedPressure (fun i => lam (a i)) (specialRotation U) c ∂μ| ≤ L * r / 2 := by
  classical
  obtain ⟨p, hp⟩ := exists_spectral_label_alignment a b
  let b' := fun i => b (p i)
  let changed := Finset.univ.filter fun i => a i ≠ b' i
  have herr' v :
      |((Finset.univ.filter fun i => a i = v).card : ℝ) -
        ((Finset.univ.filter fun i => b' i = v).card : ℝ)| ≤
      r * min ((Finset.univ.filter fun i => a i = v).card : ℝ)
        ((Finset.univ.filter fun i => b' i = v).card : ℝ) := by
    simpa only [b', spectral_label_count_comp] using herr v
  have hc v : ((changed.filter fun i => a i = v).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => a i = v).card : ℝ) := by
    have hd := aligned_changed_count_le a b' v (hp v)
    have he : changed.filter (fun i => a i = v) =
        Finset.univ.filter (fun i => a i = v ∧ a i ≠ b' i) := by
      ext i
      simp only [changed, Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_comm
    rw [he]
    exact hd.trans ((herr' v).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hr))
  have hc' v : ((changed.filter fun i => b' i = v).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => b' i = v).card : ℝ) := by
    have hp' : (∀ i, b' i = v → a i = v) ∨ (∀ i, a i = v → b' i = v) := (hp v).symm
    have hd := aligned_changed_count_le b' a v hp'
    have he : changed.filter (fun i => b' i = v) =
        Finset.univ.filter (fun i => b' i = v ∧ b' i ≠ a i) := by
      ext i
      simp only [changed, Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]
      exact and_comm
    rw [he]
    rw [abs_sub_comm] at hd
    exact hd.trans ((herr' v).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hr))
  have hcomp := meanPressure_change_counts_le hN μ
    (fun i => lam (a i)) (fun i => lam (b' i)) c K
    (fun i => hK (a i)) (fun i => hK (b' i)) a b' ha (hb.comp p.surjective)
    lam (fun _ => rfl) (fun _ => rfl) changed
    (fun i hi => by
      have hlabel : a i = b' i := by simpa only [changed, Finset.mem_filter,
        Finset.mem_univ, true_and, not_not] using hi
      rw [hlabel])
    L r hL (fun i => hdiam (b' i) (a i)) hc hc'
  have he := meanPressure_spectralPermutation hN μ p (fun i => lam (b i)) c
  simpa only [b', he] using hcomp

end InvariantIsing

end

end OAI
