import OAI.Probability.FreeIsing.Posterior.ChildObservationRegression
import OAI.Probability.FreeIsing.Trees.BranchFlipGeometry

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

abbrev NoisyRootOtherData {d : ℕ} (A : Type*) (c : Fin d) :=
  (IsingSpin × A) × (∀ b : {b : Fin d // b ≠ c},
    (RootedBroadcast.BranchVertex b.val → IsingSpin) ×
      (RootedBroadcast.BranchVertex b.val → A))

private theorem exists_otherBranch_of_nonroot {d : ℕ} (c : Fin d)
    (w : {w : TreeVertex d // ¬ [c] <+: w.val}) (hw : w.val.val ≠ []) :
    ∃ b : {b : Fin d // b ≠ c}, [b.val] <+: w.val.val := by
  rcases w with ⟨⟨w, hwred⟩, hwc⟩
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons b t =>
    have hbc : b ≠ c := by
      intro h
      subst b
      exact hwc (by simp)
    exact ⟨⟨b, hbc⟩, by simp⟩

def noisyRootOtherDecode {d : ℕ} {A : Type*} (c : Fin d)
    (p : NoisyRootOtherData A c)
    (w : {w : TreeVertex d // ¬ [c] <+: w.val}) : IsingSpin × A :=
  if hw : w.val.val = [] then p.1 else
    let b := Classical.choose (exists_otherBranch_of_nonroot c w hw)
    let v : RootedBroadcast.BranchVertex b.val :=
      ⟨w.val, Classical.choose_spec (exists_otherBranch_of_nonroot c w hw)⟩
    ((p.2 b).1 v, (p.2 b).2 v)

theorem measurable_noisyRootOtherDecode {d : ℕ} {A : Type*} [MeasurableSpace A]
    (c : Fin d) (w : {w : TreeVertex d // ¬ [c] <+: w.val}) :
    Measurable (fun p : NoisyRootOtherData A c => noisyRootOtherDecode c p w) := by
  unfold noisyRootOtherDecode
  split_ifs <;> dsimp <;> fun_prop

theorem noisyRootOtherDecode_array {d : ℕ} {A : Type*} (c : Fin d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A))
    (w : {w : TreeVertex d // ¬ [c] <+: w.val}) :
    noisyRootOtherDecode c (noisyRootOtherArray c z) w = (z.1 w.val, z.2 w.val) := by
  unfold noisyRootOtherDecode
  split_ifs with hw
  · have hroot : w.val = RootedBroadcast.root d := Subtype.ext hw
    simp only [noisyRootOtherArray, hroot]
  · rfl

def decodeFlippedBranch {d : ℕ} {A : Type*} (c : Fin d)
    (p : NoisyRootOtherData A c) :
    (RootedBroadcast.BranchVertex c → IsingSpin) × (RootedBroadcast.BranchVertex c → A) :=
  ((fun v => (noisyRootOtherDecode c p (RootedBroadcast.flipBranchToComplement c v)).1),
    fun v => (noisyRootOtherDecode c p (RootedBroadcast.flipBranchToComplement c v)).2)

theorem measurable_decodeFlippedBranch {d : ℕ} {A : Type*} [MeasurableSpace A]
    (c : Fin d) : Measurable (decodeFlippedBranch (A := A) c) :=
  (Measurable.of_eval (fun v =>
    (measurable_noisyRootOtherDecode c (RootedBroadcast.flipBranchToComplement c v)).fst)).prodMk
      (Measurable.of_eval (fun v =>
        (measurable_noisyRootOtherDecode c (RootedBroadcast.flipBranchToComplement c v)).snd))

theorem decodeFlippedBranch_relabel {d : ℕ} {A : Type*} (c : Fin d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    decodeFlippedBranch c (noisyRootOtherArray c
      (Prod.map (relabel (prefixTreeAut c)) (relabel (prefixTreeAut c)) z)) =
        noisyBranchArray c z := by
  apply Prod.ext
  · funext v
    change (noisyRootOtherDecode c _ (RootedBroadcast.flipBranchToComplement c v)).1 = _
    rw [noisyRootOtherDecode_array]
    change z.1 (prefixFlip c (prefixFlip c v.val)) = z.1 v.val
    rw [prefixFlip_twice]
  · funext v
    change (noisyRootOtherDecode c _ (RootedBroadcast.flipBranchToComplement c v)).2 = _
    rw [noisyRootOtherDecode_array]
    change z.2 (prefixFlip c (prefixFlip c v.val)) = z.2 v.val
    rw [prefixFlip_twice]

theorem HasFreeIsingLaw.condExp_root_of_noisy_branch_observable
    {d : ℕ} {theta : ℝ} {A C : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [mC : MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν] (c : Fin d)
    (G : (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A) → C) (hG : Measurable G) :
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))[
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        spinSign (z.1 (RootedBroadcast.root d))) |
      mC.comap (G ∘ noisyBranchArray c)] =ᵐ[
        μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      fun z => theta * (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))[
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          spinSign (z.1 (RootedBroadcast.branchRoot c))) |
        mC.comap (G ∘ noisyBranchArray c)] z := by
  have h := hμ.condExp_relabel_spin_of_noisy_root_others_observable h0 h1 ν
    (prefixTreeAut c) c (G ∘ decodeFlippedBranch c)
    (hG.comp (measurable_decodeFlippedBranch c))
  have hcomp : (G ∘ decodeFlippedBranch c) ∘ noisyRootOtherArray c ∘
      Prod.map (relabel (prefixTreeAut c)) (relabel (prefixTreeAut c)) =
        G ∘ noisyBranchArray c := by
    funext z
    exact congrArg G (decodeFlippedBranch_relabel c z)
  have hparent : (prefixTreeAut c).toEquiv.symm ⟨[c], List.IsChain.singleton c⟩ =
      RootedBroadcast.root d := RootedBroadcast.prefixTreeAut_symm_branchRoot c
  simpa only [hcomp, hparent, RootedBroadcast.prefixTreeAut_symm_root] using h

end Problem367

end

end OAI
