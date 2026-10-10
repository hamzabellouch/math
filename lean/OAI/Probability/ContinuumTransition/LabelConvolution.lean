import OAI.Probability.ContinuumTransition.GrandProduct

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

lemma binaryRegion_same {ι : Type} [Fintype ι] [DecidableEq ι] (A : Set Space) (s : Finset ι) :
    binaryRegion A A s = {x : ι → Space | ∀ i, x i ∈ A} := by
  ext x
  simp only [binaryRegion, mem_ofPred_eq, ite_self]

theorem grandIntegral_label_convolution (F G H : ConfigFamily)
    (hG : RelabelInvariant G) (hH : RelabelInvariant H) {A : Set Space}
    (hA : MeasurableSet A) (hF : GrandFinite F A) (hGF : GrandFinite G A) (hHF : GrandFinite H A)
    (hbound : ∀ (n : ℕ) (x : Fin n → Space), (∀ i, x i ∈ A) →
      F (Fin n) x ≤ ∑ s : Finset (Fin n),
        G {i : Fin n // i ∈ s} (fun i => x i)*H {i : Fin n // i ∉ s} (fun i => x i)) :
    grandIntegral F A ≤ grandIntegral G A*grandIntegral H A := by
  apply tsum_le_convolution hF.summable hGF.summable hHF.summable
  intro n
  have hi (s : Finset (Fin n)) : IntegrableOn
      (fun x : Fin n → Space => G {i : Fin n // i ∈ s} (fun i => x i)*
        H {i : Fin n // i ∉ s} (fun i => x i)) {x | ∀ i, x i ∈ A} := by
    have hh := integrableOn_binary_product volume A A s
      (by simpa only [← volume_pi] using hGF.integrable {i : Fin n // i ∈ s})
      (by simpa only [← volume_pi] using hHF.integrable {i : Fin n // i ∉ s})
    simpa only [← volume_pi, binaryRegion, ite_self] using hh
  have hle := setIntegral_mono_on (hF.integrable (Fin n))
    (integrable_finsetSum _ (fun s _ => hi s)) (measurableSet_generalConfigurations hA (Fin n)) (hbound n)
  rw [integral_finsetSum _ (fun s _ => hi s)] at hle
  have he (s : Finset (Fin n)) :
      (∫ x in {x : Fin n → Space | ∀ i, x i ∈ A},
        G {i : Fin n // i ∈ s} (fun i => x i)*H {i : Fin n // i ∉ s} (fun i => x i)) =
      familyIntegral G A (Fin s.card)*familyIntegral H A (Fin (n-s.card)) := by
    rw [← binaryRegion_same A s,
      show volume = Measure.pi (fun _ : Fin n => (volume : Measure Space)) by exact volume_pi,
      setIntegral_binary_product volume A A s (G {i : Fin n // i ∈ s}) (H {i : Fin n // i ∉ s})]
    simp only [← volume_pi]
    have hg := familyIntegral_eq_Fin G hG A {i : Fin n // i ∈ s}
    have hh := familyIntegral_eq_Fin H hH A {i : Fin n // i ∉ s}
    rw [Fintype.card_coe] at hg
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe] at hh
    exact congrArg₂ (·*·) hg hh
  simp_rw [he] at hle
  have hs := Finset.sum_powerset_apply_card
    (fun k => familyIntegral G A (Fin k)*familyIntegral H A (Fin (n-k)))
    (x := (Finset.univ : Finset (Fin n)))
  simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc] at hs
  rw [hs] at hle
  have hh := div_le_div_of_nonneg_right hle (Nat.cast_nonneg n.factorial : (0 : ℝ) ≤ n.factorial)
  rw [factorial_binomial_sum (fun k => familyIntegral G A (Fin k))
    (fun k => familyIntegral H A (Fin k)) n] at hh
  exact hh

end ContinuumTemperature
end

end OAI
