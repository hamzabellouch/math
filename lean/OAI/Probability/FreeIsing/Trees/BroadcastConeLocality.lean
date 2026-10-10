import OAI.Probability.FreeIsing.Trees.BroadcastLocality

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

theorem ofNoise_congr_cone {d : ℕ} (noise₁ noise₂ : TreeVertex d → IsingSpin)
    (c : TreeVertex d) (hbase : ofNoise noise₁ c = ofNoise noise₂ c)
    (hedge : ∀ w : TreeVertex d, c.1 <+: w.1 → w ≠ c → noise₁ w = noise₂ w)
    (v : TreeVertex d) (hcv : c.1 <+: v.1) :
    ofNoise noise₁ v = ofNoise noise₂ v := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.1.length = n → c.1 <+: v.1 →
      ofNoise noise₁ v = ofNoise noise₂ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hcv
      by_cases hvc : v = c
      · simpa only [hvc] using hbase
      · have hlt : c.1.length < v.1.length := by
          have hle := hcv.length_le
          have hne : c.1.length ≠ v.1.length := by
            intro heq
            exact hvc (Subtype.ext (hcv.eq_of_length heq).symm)
          omega
        have hnil : v.1 ≠ [] := by
          intro hh
          simp only [hh, List.length_nil] at hlt
          omega
        have hcp : c.1 <+: (parent v).1 := by
          apply List.prefix_of_prefix_length_le hcv (List.dropLast_prefix v.1)
          change c.1.length ≤ (parentVertex v).1.length
          rw [parentVertex_length]
          omega
        have hp : (parent v).1.length < n := by
          change (parentVertex v).1.length < n
          rw [parentVertex_length]
          omega
        rw [ofNoise_nonroot noise₁ v hnil, ofNoise_nonroot noise₂ v hnil]
        exact congrArg₂ spinMul (hedge v hcv hvc) (ih _ hp _ rfl hcp)
  exact h _ v rfl hcv

abbrev DescendantVertex {d : ℕ} (c : TreeVertex d) :=
  {v : TreeVertex d // c.1 <+: v.1}

abbrev StrictDescendantVertex {d : ℕ} (c : TreeVertex d) :=
  {v : TreeVertex d // c.1 <+: v.1 ∧ v ≠ c}

def coneNoise {d : ℕ} (theta : ℝ) (c : TreeVertex d)
    (s : IsingSpin) (Y : StrictDescendantVertex c → ℝ) (v : TreeVertex d) : IsingSpin :=
  if v.1 = [] then s
  else if hv : c.1 <+: v.1 ∧ v ≠ c then edgeNoise theta (Y ⟨v, hv⟩)
  else IsingSpin.pos

theorem measurable_coneNoise {d : ℕ} (theta : ℝ) (c : TreeVertex d) :
    Measurable (fun p : IsingSpin × (StrictDescendantVertex c → ℝ) =>
      coneNoise theta c p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  by_cases hnil : v.1 = []
  · simpa only [coneNoise, ite_eq_left hnil] using
      (measurable_fst : Measurable (Prod.fst :
        IsingSpin × (StrictDescendantVertex c → ℝ) → IsingSpin))
  · by_cases hv : c.1 <+: v.1 ∧ v ≠ c
    · simpa only [coneNoise, ite_eq_right hnil, dite_eq_left hv, Function.comp_def] using
        (measurable_edgeNoise theta).comp
          ((measurable_pi_apply (X := fun _ : StrictDescendantVertex c => ℝ)
            ⟨v, hv⟩).comp measurable_snd)
    · simpa only [coneNoise, ite_eq_right hnil, dite_eq_right hv] using
        (measurable_const : Measurable (fun _ :
          IsingSpin × (StrictDescendantVertex c → ℝ) => IsingSpin.pos))

theorem ofNoise_coneNoise_at_root {d : ℕ} (theta : ℝ) (c : TreeVertex d)
    (s : IsingSpin) (Y : StrictDescendantVertex c → ℝ) :
    ofNoise (coneNoise theta c s Y) c = s := by
  calc
    ofNoise (coneNoise theta c s Y) c =
        ofNoise (noiseFromSpins (fun _ : TreeVertex d => s)) c := by
      apply ofNoise_congr_prefix
      intro w hw
      have hnot : ¬ (c.1 <+: w.1 ∧ w ≠ c) := by
        rintro ⟨hcw, hne⟩
        exact hne (Subtype.ext (hw.eq_of_length_le hcw.length_le))
      by_cases hnil : w.1 = [] <;>
        simp [coneNoise, noiseFromSpins, hnil, hnot]
    _ = s := congrFun (ofNoise_noiseFromSpins (fun _ : TreeVertex d => s)) c

def coneFactor {d : ℕ} (theta : ℝ) (c : TreeVertex d)
    (p : IsingSpin × (StrictDescendantVertex c → ℝ)) : DescendantVertex c → IsingSpin :=
  fun v => ofNoise (coneNoise theta c p.1 p.2) v.1

theorem measurable_coneFactor {d : ℕ} (theta : ℝ) (c : TreeVertex d) :
    Measurable (coneFactor theta c) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_ofNoise_apply v.1).comp (measurable_coneNoise theta c)

theorem factor_cone_representation {d : ℕ} (theta : ℝ) (c : TreeVertex d)
    (U : TreeVertex d → ℝ) :
    (fun v : DescendantVertex c => factor theta U v.1) =
      coneFactor theta c (factor theta U c,
        fun w : StrictDescendantVertex c => U w.1) := by
  funext v
  apply ofNoise_congr_cone (inputNoise theta U) _ c
  · exact (ofNoise_coneNoise_at_root theta c (factor theta U c) _).symm
  · intro w hcw hne
    have hnil : w.1 ≠ [] := by
      intro hw
      have hc : c.1 = [] := by simpa only [hw, List.prefix_nil] using hcw
      exact hne (Subtype.ext (hw.trans hc.symm))
    simp [inputNoise, coneNoise, hnil, hcw, hne]
  · exact v.2

end Problem367.RootedBroadcast

end

end OAI
