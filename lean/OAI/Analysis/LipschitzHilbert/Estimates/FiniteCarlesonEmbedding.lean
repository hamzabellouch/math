import OAI.Analysis.LipschitzHilbert.Geometry.FiniteCarlesonPacking
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace OAI

/-! Weighted Carleson embedding for a finite laminar family. The proof
uses maximal selected sets and the layer-cake formula. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]
attribute [local instance] Classical.propDecidable

theorem finite_carleson_embedding_ae (Q : ι → Set X) (mu : Measure X)
    (hQ : ∀ i, MeasurableSet (Q i))
    (hlam : ∀ i j, Q i⊆Q j ∨ Q j⊆Q i ∨ Disjoint (Q i) (Q j))
    (a : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (hcar : ∀ j, (∑ i, if Q i⊆Q j then a i else 0)≤C*mu (Q j))
    (v : ι → ℝ) (hv : ∀ i, 0≤v i) (g : X → ℝ)
    (hg : Measurable g) (hgnonneg : ∀ x, 0≤g x)
    (hvg : ∀ i, ∀ᵐ x ∂mu.restrict (Q i), v i≤g x) :
    (∑ i, a i*ENNReal.ofReal (v i))≤C*∫⁻ x, ENNReal.ofReal (g x) ∂mu := by
  classical
  let : MeasurableSpace ι := ⊤
  let nu : Measure ι := ∑ i, a i • Measure.dirac i
  have hnu (S : Set ι) : nu S=∑ i, if i∈S then a i else 0 := by
    simp [nu,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply',Set.indicator_apply,mul_ite]
  have hnu_integral : (∫⁻ i, ENNReal.ofReal (v i) ∂nu)=∑ i, a i*ENNReal.ofReal (v i) := by
    simp [nu,lintegral_finsetSum_measure,lintegral_smul_measure,lintegral_dirac]
  have hvmeas : Measurable v := measurable_of_countable v
  rw [←hnu_integral,lintegral_eq_lintegral_meas_lt nu
    (Filter.Eventually.of_forall hv) hvmeas.aemeasurable,
    lintegral_eq_lintegral_meas_lt mu (Filter.Eventually.of_forall hgnonneg) hg.aemeasurable]
  have htail : Measurable (fun t : ℝ => mu {x | t<g x}) := by
    apply Antitone.measurable
    intro a b hab
    exact measure_mono (fun x hx => lt_of_le_of_lt hab hx)
  rw [←lintegral_const_mul C htail]
  apply lintegral_mono
  intro t
  change nu {i | t<v i}≤C*mu {x | t<g x}
  rw [hnu]
  let I : Finset ι := Finset.univ.filter (fun i => t<v i)
  have he : (∑ i, if i∈{i | t<v i} then a i else 0)=∑ i∈I, a i := by
    simp only [I,Finset.sum_filter,mem_ofPred_eq]
  rw [he]
  apply (finite_laminar_carleson_packing Q mu hQ hlam a C hcar I).trans
  apply mul_le_mul' le_rfl
  apply measure_mono_ae
  have hgood : ∀ᵐ x ∂mu, ∀ i, x∈Q i → v i≤g x :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hQ i)).mp (hvg i))
  filter_upwards [hgood] with x hx hmem
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hmem
  exact lt_of_lt_of_le (Finset.mem_filter.mp hi).2 (hx i hxi)


theorem finite_carleson_embedding (Q : ι → Set X) (mu : Measure X)
    (hQ : ∀ i, MeasurableSet (Q i))
    (hlam : ∀ i j, Q i⊆Q j ∨ Q j⊆Q i ∨ Disjoint (Q i) (Q j))
    (a : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (hcar : ∀ j, (∑ i, if Q i⊆Q j then a i else 0)≤C*mu (Q j))
    (v : ι → ℝ) (hv : ∀ i, 0≤v i) (g : X → ℝ)
    (hg : Measurable g) (hgnonneg : ∀ x, 0≤g x)
    (hvg : ∀ i, ∀ x∈Q i, v i≤g x) :
    (∑ i, a i*ENNReal.ofReal (v i))≤C*∫⁻ x, ENNReal.ofReal (g x) ∂mu := by
  apply finite_carleson_embedding_ae Q mu hQ hlam a C hcar v hv g hg hgnonneg
  intro i
  exact (ae_restrict_iff' (hQ i)).mpr (Filter.Eventually.of_forall (fun x hx => hvg i x hx))

end LipschitzHilbert

end

end OAI
