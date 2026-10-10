import OAI.Probability.FirstPassage.CrossingTilt

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

lemma crossingEvent_eq_rareFastEvent (b m K s : ℝ) (n : ℤ) (t : Vertex) :
    crossingEvent b m K s n t = rareFastEvent b m 0 1 8 (-K) s n t := by
  ext w
  constructor <;> rintro ⟨p,ds,hcols,hin,hcost⟩
  all_goals
    have hd : (displacement ds).1=n := by
      have hh := hcols.2
      simp only [Prod.fst_add,hcols.1] at hh
      omega
    refine ⟨p,ds,hcols,hin,?_⟩
    simpa only [support,zero_mul,add_zero,hd,neg_mul,sub_neg_eq_add] using hcost

lemma crossingEvent_translate (b m K s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    (fun e => w (shiftEdge t e)) ∈ crossingEvent b m K s n 0 ↔
      w ∈ crossingEvent b m K s n t := by
  rw [crossingEvent_eq_rareFastEvent,crossingEvent_eq_rareFastEvent]
  exact rareFastEvent_translate b m 0 1 8 (-K) s n t w

noncomputable def gridTrialTranslate (b : ℝ) (X h w : ℤ) (t : ℕ) : Vertex :=
  (X,⌊b*X⌋+(h+30*(t+1 : ℕ))*w)

lemma gridTrialTranslate_center (b : ℝ) (X h w : ℤ) (t : ℕ) :
    transverse b (gridTrialTranslate b X h w t) =
      (⌊b*X⌋ : ℝ)-b*X+((h : ℝ)+30*(t+1))*w := by
  simp [gridTrialTranslate,transverse]
  ring

lemma gridTrialTranslate_separation (b : ℝ) (X h w : ℤ) (hw : 1 ≤ w)
    {t u : ℕ} (htu : t ≠ u) :
    2*(8*(w : ℝ)) < |transverse b (gridTrialTranslate b X h w t)-
      transverse b (gridTrialTranslate b X h w u)| := by
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hsep : 1 ≤ |(t : ℝ)-u| := by
    have hn : (1 : ℤ) ≤ |(t : ℤ)-u| := by
      rw [abs_eq_max_neg]
      omega
    exact_mod_cast hn
  rw [gridTrialTranslate_center,gridTrialTranslate_center,
    show ((⌊b*X⌋ : ℝ)-b*X+((h : ℝ)+30*(t+1))*w)-
      ((⌊b*X⌋ : ℝ)-b*X+((h : ℝ)+30*(u+1))*w) =
      30*(w : ℝ)*((t : ℝ)-u) by ring,abs_mul,abs_of_nonneg (by positivity)]
  nlinarith

lemma gridTrials_disjoint (b : ℝ) (X h w l : ℤ) (hw : 1 ≤ w) (j : ℕ) :
    Pairwise (fun t u : Fin (j^2) => Disjoint
      (rareFastVertices b 1 8 w l (gridTrialTranslate b X h w t))
      (rareFastVertices b 1 8 w l (gridTrialTranslate b X h w u))) := by
  intro t u htu
  apply strip_vertices_disjoint _ _ b
    (transverse b (gridTrialTranslate b X h w t))
    (transverse b (gridTrialTranslate b X h w u)) (8*w)
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · exact gridTrialTranslate_separation b X h w hw (fun he => htu (Fin.ext he))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma crossingEvent_probability_translate (h : ExponentialEnvironment P τ)
    (b m K s : ℝ) (n : ℤ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ crossingEvent b m K s n t} =
      P {ω | (fun e => τ e ω) ∈ crossingEvent b m K s n 0} := by
  simp only [crossingEvent_eq_rareFastEvent]
  exact rareFastEvent_probability_translate h b m 0 1 8 (-K) s n t

theorem gridTrials_failure_bound (henv : ExponentialEnvironment P τ)
    (b m K q₀ : ℝ) (X h w l : ℤ) (hw : 1 ≤ w) (j : ℕ)
    (hq : q₀ ≤ P.real {ω | (fun e => τ e ω) ∈ crossingEvent b m K w l 0}) :
    P.real {ω | ∀ t : Fin (j^2), (fun e => τ e ω) ∉
      crossingEvent b m K w l (gridTrialTranslate b X h w t)} ≤ (1-q₀)^(j^2) := by
  have hh := disjoint_trials_failure_bound henv (Finset.univ : Finset (Fin (j^2)))
    (fun t => crossingEvent b m K w l (gridTrialTranslate b X h w t))
    (fun t => internalEdges (rareFastVertices b 1 8 w l (gridTrialTranslate b X h w t)))
    (fun _ _ => measurableSet_crossingEvent ..)
    (fun t _ => crossingEvent_depends b m K w l (gridTrialTranslate b X h w t))
    (fun _ _ _ _ htu => internalEdges_disjoint (gridTrials_disjoint b X h w l hw j htu))
    q₀ (fun t _ => ?_)
  · simpa using hh
  · unfold Measure.real
    rw [crossingEvent_probability_translate henv]
    exact hq

end PlanarFPP

end OAI
