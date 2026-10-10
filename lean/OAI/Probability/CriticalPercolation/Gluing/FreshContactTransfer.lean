import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Gluing.SelectedTrials
import OAI.Probability.CriticalPercolation.Gluing.ConditionalGluing

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {E V : Type*} [Countable E] [Countable V] (G : BondGraph V E)

theorem fresh_contact_transfer (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → Finset V) (F : V → Set E)
    (B : V → Set V) (L T Input : Set V) (o : V)
    (hd : ∀ U, MeasurableSet[blockSigma X] {ω | d ω=U})
    (hF : ∀ v, F v ⊆ Y)
    (hconnect : ∀ v∈L, ∀ b∈B v, (G.openGraph (F v)).Reachable v b)
    (C Small : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (hinput : G.hitEvent o Input ⊆ Small∪C)
    (hcontact : ∀ ω∈C, ∀ v∈d ω, v∈L ∧ (G.openGraph ω).Reachable o v)
    (K η lam : ℝ) (hK : 0 ≤ K+1) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hmean : ∀ v∈L, 1-η ≤ (BernoulliProduct.law q).real (G.seedHitEvent (B v) T))
    (hdis : ∀ σ∈C, (d σ : Set V).Pairwise (fun v w => Disjoint (F v) (F w)))
    (hs : ∀ σ∈C, K ≤ ∑ v∈d σ, (BernoulliProduct.law q).real (allOpen (F v)))
    (hs' : ∀ σ∈C, (∑ v∈d σ, (BernoulliProduct.law q).real (allOpen (F v))) ≤ K+1) :
    (BernoulliProduct.law q).real (G.hitEvent o Input\G.hitEvent o T) ≤
      (BernoulliProduct.law q).real Small+Real.exp (-K)+(K+1)*η/lam+lam := by
  let No := C∩{ω | ∀ v∈d ω, ω∉allOpen (F v)}
  let Bad := C∩{ω | ∃ v∈d ω, ω∈allOpen (F v) ∧
    (blockProbability q Y (G.seedHitEvent (B v) T) ω).toReal<1-lam}
  let Glue := {ω : Set E | ω∈G.hitEvent o (G.goodRelay q Y L F B T lam ω) ∧
    ω∉G.hitEvent o T}
  have hcover : G.hitEvent o Input\G.hitEvent o T ⊆ ((Small∪No)∪Bad)∪Glue := by
    intro ω hω
    obtain hSmall|hCω := hinput hω.1
    · exact Or.inl (Or.inl (Or.inl hSmall))
    · by_cases hno : ∀ v∈d ω, ω∉allOpen (F v)
      · exact Or.inl (Or.inl (Or.inr ⟨hCω,hno⟩))
      · push Not at hno
        obtain ⟨v,hv,hopen⟩ := hno
        by_cases hbad : (blockProbability q Y (G.seedHitEvent (B v) T) ω).toReal<1-lam
        · exact Or.inl (Or.inr ⟨hCω,v,hv,hopen,hbad⟩)
        · exact Or.inr ⟨⟨v,(hcontact ω hCω v hv).2,
            (hcontact ω hCω v hv).1,hopen,le_of_not_gt hbad⟩,hω.2⟩
  have hno := selected_no_success_bound q X Y hXY d F hd hF C hC K hdis hs
  have hbad := selected_bad_trial_bound q X Y hXY d F (fun v => G.seedHitEvent (B v) T)
    (fun v => G.measurableSet_seedHitEvent (B v) T) (fun v => G.seedHitEvent_upper (B v) T)
    hd hF C hC K η lam hK hη hlam
    (fun σ hσ v hv => hmean v (hcontact σ hσ v hv).1) hs'
  have hglue := G.goodRelay_gluing q Y L F B T hF hconnect o lam hlam.le
  have hno' : (BernoulliProduct.law q).real No ≤ Real.exp (-K) :=
    hno.trans (mul_le_of_le_one_right (Real.exp_nonneg _) measureReal_le_one)
  have hbad' : (BernoulliProduct.law q).real Bad ≤ (K+1)*η/lam :=
    hbad.trans (mul_le_of_le_one_right (div_nonneg (mul_nonneg hK hη) hlam.le)
      measureReal_le_one)
  have hu := measureReal_union_le ((Small∪No)∪Bad) Glue (μ := BernoulliProduct.law q)
  have hu' := measureReal_union_le (Small∪No) Bad (μ := BernoulliProduct.law q)
  have hu'' := measureReal_union_le Small No (μ := BernoulliProduct.law q)
  have hmono := measureReal_mono (μ := BernoulliProduct.law q) hcover
  change (BernoulliProduct.law q).real Glue ≤ lam at hglue
  linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
