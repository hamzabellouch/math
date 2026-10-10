import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialPolynomialValues
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialSections
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SubexponentialCompactImage
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ParameterSplit

namespace OAI

/-! # Compact image-volume witnesses for arbitrary measurable parameters

The domain can have more coordinates than the range. The scalar polynomial
is an actual derivative minor. Remez, inner regularity, Fubini, and the
quantitative injective patch estimate provide the compact image witnesses.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem exists_subexponential_polynomial_image
    (rem : RemezPolynomialInput) (n k D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D)
    (f : ℝ → (Fin (n + k) → ℝ) → (Fin n → ℝ))
    (df : ℝ → (Fin n → ℝ) → (Fin k → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (p : ℝ → MvPolynomial (Fin (n + k)) ℝ)
    (hp : ∀ r, (p r).totalDegree ≤ D)
    (hminor : ∀ r v z, MvPolynomial.eval (Fin.append v z) (p r) = (df r v z).det)
    (R L c : ℝ → ℝ) (hR : ∀ r, 1 ≤ R r) (hL : ∀ r, 1 ≤ L r)
    (hc : ∀ r, 0 < c r)
    (hRupper : HasSubexponentialUpperBound R) (hLupper : HasSubexponentialUpperBound L)
    (hclower : HasSubexponentialLowerBound c)
    (hf : ∀ r z, ‖z‖ ≤ R r → ∀ v, ‖v‖ ≤ R r + 2 →
      HasFDerivAt (fun w => f r (Fin.append w z)) (df r v z) v)
    (hdf : ∀ r z, ‖z‖ ≤ R r → ∀ v, ‖v‖ ≤ R r + 2 → ‖df r v z‖ ≤ L r)
    (hosc : ∀ r z, ‖z‖ ≤ R r → ∀ v w, ‖v‖ ≤ R r + 2 → ‖w‖ ≤ R r + 2 →
      ‖df r v z - df r w z‖ ≤ L r * dist v w)
    (x₀ : ℝ → Fin (n + k) → ℝ) (hx₀ : ∀ r, x₀ r ∈ closedBall 0 (R r))
    (hvalue : ∀ r, c r ≤ |MvPolynomial.eval (x₀ r) (p r)|)
    (E : ℝ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBound (fun r => (volume (E r)).toReal)) :
    ∃ C : ℝ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧ (∀ r, C r ⊆ f r '' E r) ∧
      HasSubexponentialLowerBound (fun r => (volume (C r)).toReal) := by
  obtain ⟨η, K, hη, hηlower, hKE, hK, hKpos, hKlower, hgood⟩ :=
    exists_subexponential_large_polynomial_values rem (n + k) D (by omega) hD
      p hp R c hR hc hRupper hclower x₀ hx₀ hvalue E hE hER hm hmlower
  let e := Fin.appendIsometry (α := ℝ) n k
  let K' := fun r => e ⁻¹' K r
  have hK' (r : ℝ) : IsCompact (K' r) := e.toHomeomorph.isCompact_preimage.mpr (hK r)
  have hK'mass (r : ℝ) : volume (K' r) = volume (K r) :=
    (measurePreserving_finAppend n k).measure_preimage (hK r).measurableSet.nullMeasurableSet
  have hbound (r : ℝ) (v : (Fin n → ℝ) × (Fin k → ℝ)) (hv : v ∈ K' r) :
      ‖v‖ ≤ R r := by
    have hb := hER r (hKE r hv)
    have hd := e.dist_eq v 0
    have he0 : e 0 = 0 := by
      ext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [e]
    rw [he0, dist_zero_right, dist_zero_right] at hd
    simpa only [mem_closedBall, dist_zero_right, hd] using hb
  obtain ⟨z, hz, hs, hsmass⟩ := exists_subexponential_compact_sections n k R hR hRupper
    K' hK' (fun r v hv => (norm_snd_le v).trans (hbound r v hv))
    (fun r => by rw [hK'mass]; exact hKpos r)
    (by simpa only [hK'mass] using hKlower)
  have himage := subexponential_compact_image n
    (fun r v => f r (Fin.append v (z r))) (fun r v => df r v (z r))
    R L η (fun r => (hR r).trans' zero_le_one) hL hη hRupper hLupper hηlower
    (fun r => hf r (z r) (hz r)) (fun r => hdf r (z r) (hz r))
    (fun r => hosc r (z r) (hz r))
    (fun r => {v | (v, z r) ∈ K' r}) hs (fun r v hv => by
      refine ⟨(norm_fst_le (v, z r)).trans (hbound r (v, z r) hv), ?_⟩
      rw [← hminor]
      exact hgood r _ hv) hsmass
  refine ⟨fun r => (fun v => f r (Fin.append v (z r))) '' {v | (v, z r) ∈ K' r},
    himage.1, ?_, himage.2⟩
  intro r y hy
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨Fin.append v (z r), hKE r hv, rfl⟩

end PolycyclicRecognition

end

end OAI
