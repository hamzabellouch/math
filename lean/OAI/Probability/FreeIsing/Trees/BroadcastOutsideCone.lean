import OAI.Probability.FreeIsing.Trees.BroadcastLocality

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

abbrev OutsideConeVertex {d : ℕ} (b : TreeVertex d) :=
  {v : TreeVertex d // ¬ b.1 <+: v.1}

abbrev OutsideConeNonroot {d : ℕ} (b : TreeVertex d) :=
  {v : TreeVertex d // v.1 ≠ [] ∧ ¬ b.1 <+: v.1}

def outsideConeNoise {d : ℕ} (theta : ℝ) (b : TreeVertex d)
    (Y : OutsideConeNonroot b → ℝ) (v : TreeVertex d) : IsingSpin :=
  if hv : v.1 ≠ [] ∧ ¬ b.1 <+: v.1 then edgeNoise theta (Y ⟨v, hv⟩)
  else IsingSpin.pos

theorem measurable_outsideConeNoise {d : ℕ} (theta : ℝ) (b : TreeVertex d) :
    Measurable (outsideConeNoise theta b) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v.1 ≠ [] ∧ ¬ b.1 <+: v.1
  · simpa only [outsideConeNoise, dite_eq_left hv, Function.comp_def] using
      (measurable_edgeNoise theta).comp
        (measurable_pi_apply (X := fun _ : OutsideConeNonroot b => ℝ) ⟨v, hv⟩)
  · simpa only [outsideConeNoise, dite_eq_right hv] using
      (measurable_const : Measurable (fun _ : OutsideConeNonroot b → ℝ => IsingSpin.pos))

theorem outsideConeNoise_ofNoise_eq_rootless {d : ℕ} (theta : ℝ)
    (b : TreeVertex d) (U : TreeVertex d → ℝ) (v : OutsideConeVertex b) :
    ofNoise (outsideConeNoise theta b (fun w : OutsideConeNonroot b => U w.1)) v.1 =
      rootlessFactor theta (fun w : NonrootVertex d => U w.1) v.1 := by
  apply ofNoise_congr_prefix
  intro w hw
  have hb : ¬ b.1 <+: w.1 := fun hbw => v.2 (hbw.trans hw)
  by_cases hr : w = root d
  · subst w
    simp [outsideConeNoise, nonrootNoise]
  · have hnil : w.1 ≠ [] := fun h => hr ((eq_root_iff w).mpr h)
    simp [outsideConeNoise, nonrootNoise, hnil, hb, hr]

def outsideConeFactor {d : ℕ} (theta : ℝ) (b : TreeVertex d)
    (a : OutsideConeVertex b) (p : IsingSpin × (OutsideConeNonroot b → ℝ)) :
    OutsideConeVertex b → IsingSpin :=
  fun v => spinMul p.1
    (spinMul (ofNoise (outsideConeNoise theta b p.2) a.1)
      (ofNoise (outsideConeNoise theta b p.2) v.1))

theorem measurable_outsideConeFactor {d : ℕ} (theta : ℝ)
    (b : TreeVertex d) (a : OutsideConeVertex b) :
    Measurable (outsideConeFactor theta b a) := by
  apply Measurable.of_eval
  intro v
  have ha : Measurable (fun p : IsingSpin × (OutsideConeNonroot b → ℝ) =>
      ofNoise (outsideConeNoise theta b p.2) a.1) :=
    (measurable_ofNoise_apply a.1).comp
      ((measurable_outsideConeNoise theta b).comp measurable_snd)
  have hv : Measurable (fun p : IsingSpin × (OutsideConeNonroot b → ℝ) =>
      ofNoise (outsideConeNoise theta b p.2) v.1) :=
    (measurable_ofNoise_apply v.1).comp
      ((measurable_outsideConeNoise theta b).comp measurable_snd)
  exact measurable_spinMul.comp
    (measurable_fst.prodMk (measurable_spinMul.comp (ha.prodMk hv)))

theorem factor_outsideCone_representation {d : ℕ} (theta : ℝ)
    (b : TreeVertex d) (a : OutsideConeVertex b) (U : TreeVertex d → ℝ) :
    (fun v : OutsideConeVertex b => factor theta U v.1) =
      outsideConeFactor theta b a (factor theta U a.1,
        fun w : OutsideConeNonroot b => U w.1) := by
  funext v
  change factor theta U v.1 = spinMul (factor theta U a.1)
    (spinMul (ofNoise (outsideConeNoise theta b _) a.1)
      (ofNoise (outsideConeNoise theta b _) v.1))
  rw [outsideConeNoise_ofNoise_eq_rootless theta b U a,
    outsideConeNoise_ofNoise_eq_rootless theta b U v,
    factor_root_decomposition theta U a.1, factor_root_decomposition theta U v.1]
  simp only [spinMul_assoc, spinMul_cancel]

end Problem367.RootedBroadcast

end

end OAI
