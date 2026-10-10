import OAI.Analysis.CircleDomains.Sobolev.CoordinateEnergy

namespace OAI

/-!
# Localizing the finite-transfer energy estimate

Exact agreement of a coordinate and metric on the retained core, together
with small nonnegative total energy outside it, gives the manuscript's
localized estimate after any measurable part of that core is removed.
-/

open Set MeasureTheory Filter

namespace CircleDomainRigidity.FiniteTransfer

theorem localized_energy_lt
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {S K E : Set X} (hS : MeasurableSet S) (hK : MeasurableSet K)
    (hE : MeasurableSet E) (hEK : E ⊆ K)
    {f g T : X → ℝ} (hf : IntegrableOn f S μ) (hg : IntegrableOn g S μ)
    (hT : IntegrableOn T (S \ K) μ)
    (hcore : ∀ x ∈ S ∩ K, f x = g x)
    (hg0 : ∀ x ∈ S, 0 ≤ g x) (htail : ∀ x ∈ S \ K, f x ≤ T x)
    {ε : ℝ} (hε : (∫ x in S \ K, T x ∂μ) < ε) :
    (∫ x in S \ E, f x ∂μ) < (∫ x in S \ E, g x ∂μ) + ε := by
  have hdiff : (S \ E) \ K = S \ K := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · exact fun hx => ⟨⟨hx.1, fun he => hx.2 (hEK he)⟩, hx.2⟩
  have heq : (∫ x in (S \ E) ∩ K, f x ∂μ) = ∫ x in (S \ E) ∩ K, g x ∂μ :=
    setIntegral_congr_fun ((hS.diff hE).inter hK)
      (fun x hx => hcore x ⟨hx.1.1, hx.2⟩)
  have hsplit := integral_inter_add_sdiff hK (hf.mono_set (s := S \ E) sdiff_subset)
  rw [hdiff, heq] at hsplit
  have htail' : (∫ x in S \ K, f x ∂μ) < ε :=
    (setIntegral_mono_on (hf.mono_set sdiff_subset) hT (hS.diff hK) htail).trans_lt hε
  have hcore' : (∫ x in (S \ E) ∩ K, g x ∂μ) ≤ ∫ x in S \ E, g x ∂μ :=
    setIntegral_mono_set (hg.mono_set sdiff_subset)
      ((ae_restrict_mem (hS.diff hE)).mono (fun x hx => hg0 x hx.1))
      (Eventually.of_forall (fun _ hx => hx.1))
  linarith

end CircleDomainRigidity.FiniteTransfer

end OAI
