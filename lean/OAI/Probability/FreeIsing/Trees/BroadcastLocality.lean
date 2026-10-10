import OAI.Probability.FreeIsing.Trees.RootedBroadcastLaw

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

lemma ofNoise_congr_prefix {d : ℕ} (noise₁ noise₂ : TreeVertex d → IsingSpin)
    (v : TreeVertex d)
    (heq : ∀ w : TreeVertex d, w.val <+: v.val → noise₁ w = noise₂ w) :
    ofNoise noise₁ v = ofNoise noise₂ v := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      (∀ w : TreeVertex d, w.val <+: v.val → noise₁ w = noise₂ w) →
      ofNoise noise₁ v = ofNoise noise₂ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv heq
      by_cases hnil : v.val = []
      · calc
          ofNoise noise₁ v = noise₁ v := by rw [ofNoise]; simp [hnil]
          _ = noise₂ v := heq v (List.prefix_refl _)
          _ = ofNoise noise₂ v := by rw [ofNoise]; simp [hnil]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise₁ v hnil, ofNoise_nonroot noise₂ v hnil]
        apply congrArg₂ spinMul (heq v (List.prefix_refl _))
        apply ih _ hlt (parent v) rfl
        intro w hw
        exact heq w (hw.trans (List.dropLast_prefix v.val))
  exact h _ v rfl heq

lemma factor_congr_prefix {d : ℕ} (theta : ℝ) (U V : TreeVertex d → ℝ)
    (v : TreeVertex d) (heq : ∀ w : TreeVertex d, w.val <+: v.val → U w = V w) :
    factor theta U v = factor theta V v := by
  apply ofNoise_congr_prefix
  intro w hw
  simp only [inputNoise, heq w hw]

abbrev BranchVertex {d : ℕ} (c : Fin d) := {v : TreeVertex d // [c] <+: v.val}

lemma prefix_in_branch_or_root {d : ℕ} (c : Fin d)
    {u v : TreeVertex d} (hv : [c] <+: v.val) (huv : u.val <+: v.val) :
    u.val = [] ∨ [c] <+: u.val := by
  by_cases hu : u.val = []
  · exact Or.inl hu
  · right
    apply List.prefix_of_prefix_length_le hv huv
    have : 0 < u.val.length := List.length_pos_iff.mpr hu
    simpa only [List.length_singleton] using Nat.succ_le_of_lt this

def branchNoise {d : ℕ} (theta : ℝ) (c : Fin d)
    (s : IsingSpin) (Y : BranchVertex c → ℝ) (v : TreeVertex d) : IsingSpin :=
  if v.val = [] then s
  else if hv : [c] <+: v.val then edgeNoise theta (Y ⟨v, hv⟩)
  else IsingSpin.pos

lemma measurable_branchNoise {d : ℕ} (theta : ℝ) (c : Fin d) :
    Measurable (fun p : IsingSpin × (BranchVertex c → ℝ) => branchNoise theta c p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  by_cases hnil : v.val = []
  · simpa only [branchNoise, ite_eq_left hnil] using
      (measurable_fst : Measurable (Prod.fst : IsingSpin × (BranchVertex c → ℝ) → IsingSpin))
  · by_cases hv : [c] <+: v.val
    · simpa only [branchNoise, ite_eq_right hnil, dite_eq_left hv, Function.comp_def] using
        (measurable_edgeNoise theta).comp
          ((measurable_pi_apply (X := fun _ : BranchVertex c => ℝ) ⟨v,hv⟩).comp measurable_snd)
    · simpa only [branchNoise, ite_eq_right hnil, dite_eq_right hv] using
        (measurable_const : Measurable (fun _ : IsingSpin × (BranchVertex c → ℝ) => IsingSpin.pos))

def branchFactor {d : ℕ} (theta : ℝ) (c : Fin d)
    (p : IsingSpin × (BranchVertex c → ℝ)) : BranchVertex c → IsingSpin :=
  fun v => ofNoise (branchNoise theta c p.1 p.2) v.val

lemma measurable_branchFactor {d : ℕ} (theta : ℝ) (c : Fin d) :
    Measurable (branchFactor theta c) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_ofNoise_apply v.val).comp (measurable_branchNoise theta c)

lemma factor_branch_representation {d : ℕ} (theta : ℝ) (c : Fin d)
    (U : TreeVertex d → ℝ) :
    (fun v : BranchVertex c => factor theta U v.val) =
      branchFactor theta c (fairSpin (U (root d)), fun v : BranchVertex c => U v.val) := by
  funext v
  apply ofNoise_congr_prefix
  intro w hw
  rcases prefix_in_branch_or_root c v.property hw with hnil | hbranch
  · have heq : w = root d := (eq_root_iff w).mpr hnil
    subst w
    simp [inputNoise, branchNoise]
  · have hnil : w.val ≠ [] := by
      intro heq
      rw [heq] at hbranch
      have hl := hbranch.length_le
      simp at hl
    simp [inputNoise, branchNoise, hnil, hbranch]

end RootedBroadcast
end Problem367

end

end OAI
