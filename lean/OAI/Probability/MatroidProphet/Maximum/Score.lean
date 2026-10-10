import OAI.Probability.MatroidProphet.BranchMix

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

noncomputable def maximumRounded {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (fun o : Option (Fin n) =>
    match o with
    | none => 0
    | some e => if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0)

lemma maximumRounded_nonneg {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) :
    0 ≤ maximumRounded M w := by
  classical
  exact Finset.le_sup' (s := Finset.univ)
    (f := fun o : Option (Fin n) => match o with
      | none => 0
      | some e => if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0)
    (Finset.mem_univ none)

lemma roundedWeight_le_maximumRounded {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (e : Fin n) (he : M.Indep ({e} : Set (Fin n))) :
    roundedWeight weightBase (w e) ≤ maximumRounded M w := by
  classical
  have h := Finset.le_sup' (s := Finset.univ)
    (f := fun o : Option (Fin n) => match o with
      | none => 0
      | some e => if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0)
    (Finset.mem_univ (some e))
  change (if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0) ≤
    maximumRounded M w at h
  rwa [ite_eq_left he] at h

noncomputable def maximumPayoff {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) : ℝ :=
  ∫ r, hiddenWorstReward (roundedMaximumHidden M (seedSet (bits := n))) w r
    ∂bernoulliSeedLaw (fun _ => (1 / 2 : ℝ)) (fun _ => by norm_num) (fun _ => by norm_num)

lemma maximumPayoff_nonneg {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    0 ≤ maximumPayoff M w :=
  integral_nonneg (fun r => hiddenWorstReward_nonneg _ w hw r)

lemma roundedWeight_le_four_maximumPayoff {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (hw : ∀ e, 0 ≤ w e) (e : Fin n) (he : M.Indep ({e} : Set (Fin n))) :
    roundedWeight weightBase (w e) ≤ 4 * maximumPayoff M w := by
  classical
  let a : Fin n → WithBot ℤ := fun f => Priority.asLevel (roundedLevel weightBase (w f))
  by_cases hea : a e = ⊥
  · have hu : roundedWeight weightBase (w e) = 0 := by
      change levelWeight weightBase (a e) = 0
      rw [hea]
      rfl
    rw [hu]
    exact mul_nonneg (by norm_num) (maximumPayoff_nonneg M w hw)
  · let P : Finset (Fin n) := Finset.univ.filter fun f => M.Indep ({f} : Set (Fin n)) ∧ a f ≠ ⊥
    have heP : e ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ e, he, hea⟩
    obtain ⟨g, hgP, htop⟩ := Maximum.exists_top a P ⟨e, heP⟩
    have hg := (Finset.mem_filter.mp hgP).2
    have hwin : w g / 4 ≤ maximumPayoff M w :=
      Maximum.maximum_integral_top M (fun x => Priority.asLevel (roundedLevel weightBase x))
        ((measurable_of_countable Priority.asLevel).comp (measurable_roundedLevel weightBase))
        (fun x => x ≠ ⊥) w hw g hg.1 hg.2
        (fun f hf haf hfg => htop f (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf, haf⟩) hfg)
    have hkey : a e ≤ a g := by
      by_cases heg : e = g
      · exact heg ▸ le_rfl
      · rcases htop e heP heg with hlt | ⟨heq, _⟩
        · exact hlt.le
        · exact heq.symm.le
    have hu : roundedWeight weightBase (w e) ≤ roundedWeight weightBase (w g) :=
      levelWeight_mono (by norm_num [weightBase]) hkey
    have hraw := roundedWeight_le (by norm_num [weightBase] : 1 < weightBase) (hw g)
    nlinarith

theorem maximum_branch_guarantee {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (hw : ∀ e, 0 ≤ w e) : maximumRounded M w / 4 ≤ maximumPayoff M w := by
  classical
  have hnonneg := maximumPayoff_nonneg M w hw
  have hfour : maximumRounded M w ≤ 4 * maximumPayoff M w := by
    apply Finset.sup'_le
    intro o _
    cases o with
    | none => exact mul_nonneg (by norm_num) hnonneg
    | some e =>
      change (if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0) ≤ _
      split_ifs with he
      · exact roundedWeight_le_four_maximumPayoff M w hw e he
      · exact mul_nonneg (by norm_num) hnonneg
  nlinarith

end MatroidProphet

end OAI
