import Mathlib
import OAI.Analysis.Commutator.CommutatorPerturbation
import OAI.Analysis.Commutator.DecomposableAlgebra
import OAI.Analysis.Commutator.DecomposableNorm
import OAI.Analysis.Commutator.StrongContractionLimit

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma commutator_measurable (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ) (ξ : H) :
    AEStronglyMeasurable (fun a => (T a*S a-S a*T a) ξ) μ :=
  (mul_measurable μ T S hT hS ξ).sub (mul_measurable μ S T hS hT ξ)

omit [CompleteSpace H] in
lemma commutator_field_bound (T S : Ω → H →L[ℂ] H) {b c : ℝ} (hb0 : 0≤b) (hc0 : 0≤c)
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖≤c) :
    ∀ᵐ a ∂μ,‖T a*S a-S a*T a‖≤2*b*c := by
  filter_upwards [mul_bound μ T S hb0 hb hc,mul_bound μ S T hc0 hc hb] with a h1 h2
  exact (norm_sub_le _ _).trans (by nlinarith)

omit [CompleteSpace H] in
lemma operator_commutator (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb0 : 0≤b) (hc0 : 0≤c)
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖≤c) :
    operator μ T hT hb*operator μ S hS hc-operator μ S hS hc*operator μ T hT hb=
    operator μ (fun a => T a*S a-S a*T a) (commutator_measurable μ T S hT hS)
      (commutator_field_bound μ T S hb0 hc0 hb hc) := by
  apply operator_eq_of_ae_apply
  intro f
  filter_upwards [operator_ae μ T hT hb (operator μ S hS hc f),
    operator_ae μ S hS hc (operator μ T hT hb f),operator_ae μ T hT hb f,
    operator_ae μ S hS hc f,
    Lp.coeFn_sub (operator μ T hT hb (operator μ S hS hc f))
      (operator μ S hS hc (operator μ T hT hb f))] with a h1 h2 h3 h4 h5
  change (operator μ T hT hb (operator μ S hS hc f)-operator μ S hS hc (operator μ T hT hb f)) a=_
  rw [h5]
  change operator μ T hT hb (operator μ S hS hc f) a-
    operator μ S hS hc (operator μ T hT hb f) a=_
  rw [h1,h2,h3,h4]
  rfl

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

omit [CompleteSpace H] in
lemma commutator_ae_bound (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c d : ℝ} (hb0 : 0≤b) (hc0 : 0≤c) (hd : 0≤d)
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖≤c)
    (hn : ‖operator μ T hT hb*operator μ S hS hc-operator μ S hS hc*operator μ T hT hb‖≤d) :
    ∀ᵐ a ∂μ,‖T a*S a-S a*T a‖≤d := by
  rw [operator_commutator μ T S hT hS hb0 hc0 hb hc] at hn
  exact (operator_norm_le_iff_ae μ _ _ _ hd).mp hn

theorem seminorm_ae_le (P : VonNeumannAlgebra (Lp H 2 μ)) (Q : Ω → VonNeumannAlgebra H)
    (T : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb0 : 0≤b) (hb : ∀ᵐ a ∂μ,‖T a‖≤b)
    (c : ℕ → Ω → H →L[ℂ] H)
    (hm : ∀ n ξ,AEStronglyMeasurable (fun a => c n a ξ) μ)
    (hc : ∀ n,∀ᵐ a ∂μ,‖c n a‖≤1)
    (hmem : ∀ n,operator μ (c n) (hm n) (hc n)∈P)
    (hdense : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => c (k n) a ξ) atTop (𝓝 (A ξ))) :
    ∀ᵐ a ∂μ,commutatorSeminorm (Q a) (T a)≤commutatorSeminorm P (operator μ T hT hb) := by
  let d := commutatorSeminorm P (operator μ T hT hb)
  have hd : 0≤d := commutatorSeminorm_nonneg P _
  have ht (n : ℕ) : ∀ᵐ a ∂μ,‖T a*c n a-c n a*T a‖≤d := by
    apply commutator_ae_bound μ T (c n) hT (hm n) hb0 (by norm_num) hd hb (hc n)
    exact commutator_bound_unitball P _ (hmem n)
      (operator_norm_le μ (c n) (hm n) (hc n) (by norm_num) (hc n))
  filter_upwards [ae_all_iff.mpr ht,hdense] with a ha hda
  apply commutatorSeminorm_le
  intro A hA hnA
  obtain ⟨k,hk⟩ := hda A hA hnA
  apply StrongContractionLimit.norm_le_of_strong (l:=atTop) (fun n => T a*c (k n) a-c (k n) a*T a) _ _ hd
    (Eventually.of_forall (fun n => ha (k n)))
  intro ξ
  exact ((T a).continuous.tendsto (A ξ) |>.comp (hk ξ)).sub (hk (T a ξ))

end Kadison.Decomposable

end

end
end

end OAI
