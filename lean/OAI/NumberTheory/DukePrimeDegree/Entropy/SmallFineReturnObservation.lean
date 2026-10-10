import OAI.NumberTheory.DukePrimeDegree.Dynamics.SmallFineReturnRefinement
import OAI.NumberTheory.DukePrimeDegree.Entropy.EncodedObservationEntropy
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ErgodicReturnLevels

namespace OAI

/-! # Small-entropy observations with fine recurrent future fibers -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

lemma fine_return_fibers_of_scaled_refinement
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Ergodic T μ)
    {S : Set Y} (hS : MeasurableSet S)
    (htail : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ μ (firstReturnLevel T S n) ≠ 0)
    {d : ℕ} (f : Y → Fin d → ℝ)
    {α : ℝ} (hα : 0 < α) {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n))
    (hclose : ∀ n x y, x ∈ firstReturnLevel T S n →
      returnRefinement T S B y=returnRefinement T S B x →
        ∀ i, |f y i-f x i| < 2*Real.exp (-α*(n+1:ℝ))) :
    ∀ᵐ x ∂μ, ∀ y, (∀ k : ℕ,
      returnRefinement T S B (T^[k+1] y)=returnRefinement T S B (T^[k+1] x)) →
      ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, T^[k] x ∈ S ∧ T^[k] y ∈ S ∧
        ∀ i, |f (T^[k] y) i-f (T^[k] x) i| < ε := by
  have hv := ae_visits_unbounded_return_levels μ hT hS htail
  filter_upwards [hT.toMeasurePreserving.quasiMeasurePreserving.ae hv] with x hx
  intro y hy ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (-Real.log (ε/2)/α)
  obtain ⟨k,n,hn,hret⟩ := hx N
  have hxret : T^[k+1] x ∈ firstReturnLevel T S n := by
    simpa only [Function.iterate_succ_apply] using hret
  have hxcode : returnRefinement T S B (T^[k+1] x)=some ⟨n,B n (T^[k+1] x)⟩ := by
    have hm : T^[k+1] x ∈ returnRefinementAtom T S B
        (some ⟨n,B n (T^[k+1] x)⟩) := ⟨hxret,rfl⟩
    rwa [←returnRefinement_fiber] at hm
  have hyret : T^[k+1] y ∈ firstReturnLevel T S n := by
    have hm : T^[k+1] y ∈ returnRefinementAtom T S B
        (some ⟨n,B n (T^[k+1] x)⟩) := by
      rw [←returnRefinement_fiber]
      exact (hy k).trans hxcode
    exact hm.1
  refine ⟨k+1,hxret.1,hyret.1,?_⟩
  intro i
  have hNn : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hNa : -Real.log (ε/2) < (N:ℝ)*α := (div_lt_iff₀ hα).mp hN
  have he : Real.exp (-α*(n+1:ℝ)) < ε/2 := by
    rw [←Real.exp_log (by positivity : 0 < ε/2)]
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact (hclose n _ _ hxret (hy k) i).trans (by linarith)

theorem exists_small_entropy_fine_return_observation
    {Y : Type*} [MeasurableSpace Y] {d : ℕ} {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure Y) [IsProbabilityMeasure μ]
      {T : Y → Y} (_hT : Ergodic T μ) (_hE : MeasurableEmbedding T)
      {S : Set Y} (_hS : MeasurableSet S),
      (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ μ (firstReturnLevel T S n) ≠ 0) →
      μ.real S ≤ δ → ∀ (f : Y → Fin d → ℝ), Measurable f →
      (∀ x ∈ S, ∀ i, |f x i| ≤ R) →
      ∃ Q : Y → ℕ, Measurable Q ∧
        Summable (fun n => Real.negMulLog (μ.real {x | Q x=n})) ∧
        (∑' n, Real.negMulLog (μ.real {x | Q x=n})) < ε ∧
        ∀ᵐ x ∂μ, ∀ y, (∀ k : ℕ, Q (T^[k+1] y)=Q (T^[k+1] x)) →
          ∀ η : ℝ, 0 < η → ∃ k : ℕ, T^[k] x ∈ S ∧ T^[k] y ∈ S ∧
            ∀ i, |f (T^[k] y) i-f (T^[k] x) i| < η := by
  obtain ⟨δ,hδ,H⟩ := exists_small_entropy_return_refinement (Y := Y) (d := d) hR hε
  refine ⟨δ,hδ,?_⟩
  intro μ _ T hT hE S hS htail hsmall f hf hbound
  obtain ⟨α,K,B,hα,hB,hs,he,hclose⟩ :=
    H μ hT.toMeasurePreserving hE hS hsmall f hf hbound
  let I := Option (Σ n : ℕ, Fin (K n))
  let : MeasurableSpace I := ⊤
  let Q : Y → ℕ := fun x => Encodable.encode (returnRefinement T S B x)
  have hQ : Measurable Q := (measurable_of_countable Encodable.encode).comp
    (measurable_returnRefinement hT.measurable hS B hB)
  have henc := encoded_observation_information μ (returnRefinement T S B)
  refine ⟨Q,hQ,henc.1.mpr hs,?_,?_⟩
  · exact henc.2.trans_lt he
  · filter_upwards [fine_return_fibers_of_scaled_refinement μ hT hS htail f hα B hclose] with x hx
    intro y hy
    exact hx y (fun k => Encodable.encode_injective (hy k))

end DukePrimeDegree

end

end OAI
