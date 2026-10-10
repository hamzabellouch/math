import OAI.Probability.GammaPassage.GoodSiteEvents

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem goodSiteEvent_failure_bound (h : GammaEnvironment shape rate P τ)
    (μ : Plane → ℝ) (b A R ε s p0 : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ) (v : Vertex)
    (hR : 0 ≤ R) (hs : 1 ≤ s)
    (hp0 : p0 ≤ P.real {ω | (fun e => τ e ω) ∈
      rareFastEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε s n 0}) :
    P.real {ω | (fun e => τ e ω) ∉ goodSiteEvent μ b A R ε s plus n d M v} ≤
      (1-p0)^M + P.real {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n d M v 1} +
        P.real {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n d M v 2} := by
  let _ := h.probability
  let F := {ω | ∀ j : Fin M, (fun e => τ e ω) ∉ siteTrial μ b A R ε s plus n d M v j}
  let C₁ := {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n d M v 1}
  let C₂ := {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n d M v 2}
  have hsub : {ω | (fun e => τ e ω) ∉ goodSiteEvent μ b A R ε s plus n d M v} ⊆
      (F ∪ C₁) ∪ C₂ := by
    intro ω hh
    simp only [goodSiteEvent,mem_ofPred_eq,not_and_or,not_exists] at hh
    rcases hh with hf | hc | hc
    · exact Or.inl (Or.inl hf)
    · exact Or.inl (Or.inr hc)
    · exact Or.inr hc
  have hf : P.real F ≤ (1-p0)^M := rareFastTrials_failure_bound h b (μ (direction b))
    (extremeSlope μ b plus) A R ε s p0 n (blockX n d v)
    (blockY (contactSign plus) (trialWindow M R s) v) M hR hs hp0
  calc
    _ ≤ P.real ((F ∪ C₁) ∪ C₂) := measureReal_mono hsub
    _ ≤ P.real (F ∪ C₁)+P.real C₂ := measureReal_union_le _ _
    _ ≤ (P.real F+P.real C₁)+P.real C₂ := by linarith [measureReal_union_le (μ := P) F C₁]
    _ ≤ _ := by dsimp [C₁,C₂]; linarith

/-- Choosing the separation after the trial count gives an error uniform
in both the site and the longitudinal scale. -/
theorem gamma_goodSiteEvent_failure (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (plus : Bool) (M : ℕ) (hM : 0 < M)
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ κ > 0, ∀ᶠ s : ℝ in atTop,
      ∀ (n : ℤ) (v : Vertex) (p0 : ℝ),
      p0 ≤ P.real {ω | (fun e => τ e ω) ∈
        rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε s n 0} →
      P.real {ω | (fun e => τ e ω) ∉ goodSiteEvent (gammaMeanNorm h hshape hrate) b A R ε s plus n ⌈D0*s⌉ M v} <
        (1-p0)^M+κ := by
  obtain ⟨D0,hD0,hc⟩ := gamma_source_connector_test h hshape hrate b hb plus M hM R ε hR hε
  refine ⟨D0,hD0,?_⟩
  intro κ hκ
  filter_upwards [hc (κ/2) (by positivity),eventually_ge_atTop (1 : ℝ)] with s hcs hs
  intro n v p0 hp0
  have h1 := hcs (blockX n ⌈D0*s⌉ v+n)
    (blockY (contactSign plus) (trialWindow M R s) v) 1 (by norm_num) (by norm_num)
  have h2 := hcs (blockX n ⌈D0*s⌉ v+n)
    (blockY (contactSign plus) (trialWindow M R s) v) 2 (by norm_num) (by norm_num)
  have hh := goodSiteEvent_failure_bound h (gammaMeanNorm h hshape hrate) b A R ε s p0 plus n ⌈D0*s⌉ M v hR hs hp0
  change P.real {ω | (fun e => τ e ω) ∉ siteConnector (gammaMeanNorm h hshape hrate) b R ε s plus n ⌈D0*s⌉ M v 1} < κ/2 at h1
  change P.real {ω | (fun e => τ e ω) ∉ siteConnector (gammaMeanNorm h hshape hrate) b R ε s plus n ⌈D0*s⌉ M v 2} < κ/2 at h2
  linarith

end GammaFPP.CrossingBridge

end OAI
