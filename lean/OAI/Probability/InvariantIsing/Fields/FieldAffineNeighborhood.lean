import OAI.Probability.InvariantIsing.Fields.FieldSecondRecursion

namespace OAI

/-! Every strict affine covariance vector has a common neighborhood
where the finite recursion has uniformly positive and bounded variances. -/

noncomputable section
open Set
open scoped Topology

namespace InvariantIsing

lemma fieldAffine_variance_neighborhood (L : List FieldAffineStep) (t : ℝ)
    (hpos : ∀ av ∈ L, 0 < av.base + av.slope * t) :
    ∃ (I : Set ℝ) (_ : IsOpen I), t ∈ I ∧ ∃ m V : ℝ, 0 < m ∧
      ∀ av ∈ L, ∀ s ∈ I, m ≤ av.base + av.slope * s ∧ av.base + av.slope * s ≤ V := by
  induction L with
  | nil =>
    exact ⟨univ, isOpen_univ, mem_univ _, 1, 1, by norm_num, by simp⟩
  | cons av L ih =>
    obtain ⟨J, hJ, htJ, m, V, hm, hL⟩ := ih (fun bv hb => hpos bv (List.mem_cons_of_mem av hb))
    let b := av.base + av.slope * t
    have hb : 0 < b := hpos av List.mem_cons_self
    let K := (fun s : ℝ => av.base + av.slope * s) ⁻¹' Ioo (b / 2) (b + 1)
    have hK : IsOpen K := isOpen_Ioo.preimage (by fun_prop)
    have htK : t ∈ K := by change b / 2 < b ∧ b < b + 1; constructor <;> linarith
    refine ⟨J ∩ K, hJ.inter hK, ⟨htJ, htK⟩, min m (b / 2), max V (b + 1),
      lt_min hm (by positivity), ?_⟩
    intro bv hmem s hs
    rcases List.mem_cons.mp hmem with heq | htail
    · subst bv
      exact ⟨(min_le_right _ _).trans hs.2.1.le, hs.2.2.le.trans (le_max_right _ _)⟩
    · exact ⟨(min_le_left _ _).trans (hL bv htail s hs.1).1,
        (hL bv htail s hs.1).2.trans (le_max_left _ _)⟩

end InvariantIsing

end

end OAI
