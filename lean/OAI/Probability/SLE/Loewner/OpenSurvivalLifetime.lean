import Mathlib

namespace OAI

/-! The finite lifetime of a downward-closed survival condition with
strict continuation at each surviving time. -/
noncomputable section
open Set

namespace SLEExactGauge

lemma exists_open_survival_lifetime (p : ℝ → Prop) (hzero : p 0)
    (hdown : ∀ s t, 0 ≤ s → s ≤ t → p t → p s)
    (hext : ∀ t, 0 ≤ t → p t → ∃ s, t < s ∧ p s)
    {T : ℝ} (hT : 0 ≤ T) (hdead : ¬p T) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ T ∧ ∀ t, 0 ≤ t → (p t ↔ t < τ) := by
  let S : Set ℝ := {t | 0 ≤ t ∧ p t}
  have hSne : S.Nonempty := ⟨0,le_rfl,hzero⟩
  have hbound (s : ℝ) (hs : s ∈ S) : s ≤ T := by
    by_contra hn
    exact hdead (hdown T s hT (lt_of_not_ge hn).le hs.2)
  have hSb : BddAbove S := ⟨T,hbound⟩
  obtain ⟨s,hs,hsp⟩ := hext 0 le_rfl hzero
  have hsS : s ∈ S := ⟨hs.le,hsp⟩
  have hτp : 0 < sSup S := hs.trans_le (le_csSup hSb hsS)
  refine ⟨sSup S,hτp,csSup_le hSne hbound,?_⟩
  intro t ht
  constructor
  · intro hpt
    obtain ⟨s,hts,hps⟩ := hext t ht hpt
    exact hts.trans_le (le_csSup hSb ⟨ht.trans hts.le,hps⟩)
  · intro hlt
    obtain ⟨s,hsS,hts⟩ := exists_lt_of_lt_csSup hSne hlt
    exact hdown t s ht hts.le hsS.2

end SLEExactGauge

end

end OAI
