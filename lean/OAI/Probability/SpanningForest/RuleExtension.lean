import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

def gatedRule (p : GraphCode → (ℕ → ℝ) → Prop) (Phi : FactorRule) : FactorRule := by
  classical
  exact fun G U e => if p G U then Phi G U e else false

theorem RuleBorel.gated {Phi : FactorRule} (hPhi : RuleBorel Phi)
    {p : GraphCode → (ℕ → ℝ) → Prop}
    (hp : Measurable (fun q : GraphCode × (ℕ → ℝ) => p q.1 q.2)) :
    RuleBorel (gatedRule p Phi) := by
  classical
  have hgate : Measurable
      (fun q : GraphCode × ((ℕ → ℝ) × EdgeCode) => p q.1 q.2.1) :=
    hp.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact Measurable.ite hgate.setOf hPhi measurable_const

theorem RuleEquivariant.gated {Phi : FactorRule} (hPhi : RuleEquivariant Phi)
    {p : GraphCode → (ℕ → ℝ) → Prop}
    (hp : ∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ),
      p (relabelGraph σ G) (relabelLabels σ U) ↔ p G U) :
    RuleEquivariant (gatedRule p Phi) := by
  classical
  intro σ G U e
  simp only [gatedRule, hp σ G U]
  split_ifs
  · exact hPhi σ G U e
  · rfl

theorem gatedRule_eq_of_gate {p : GraphCode → (ℕ → ℝ) → Prop}
    {Phi : FactorRule} {G : GraphCode} {U : ℕ → ℝ} (h : p G U) :
    gatedRule p Phi G U = Phi G U := by
  classical
  funext e
  simp [gatedRule, h]

theorem HasFUSFLaw.congr {Ω : Type} [MeasurableSpace Ω]
    {G : GraphCode} {P : Measure Ω} {X Y : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X)
    (hY : ∀ e, Measurable (fun ω => Y ω e))
    (hXY : X =ᵐ[P] Y) : HasFUSFLaw G P Y := by
  refine ⟨hY, ?_⟩
  intro H hH A B
  have hcyl :
      P {ω | (∀ e ∈ A, X ω e = true) ∧ (∀ e ∈ B, X ω e = false)} =
      P {ω | (∀ e ∈ A, Y ω e = true) ∧ (∀ e ∈ B, Y ω e = false)} := by
    apply measure_congr
    filter_upwards [hXY] with ω hω
    exact congrArg (fun f : EdgeConfiguration =>
      (∀ e ∈ A, f e = true) ∧ (∀ e ∈ B, f e = false)) hω
  rw [← hcyl]
  exact hX.2 H hH A B

theorem gatedRule_ae_eq {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {p : GraphCode → (ℕ → ℝ) → Prop}
    {Phi : FactorRule} {G : GraphCode} {U : Ω → ℕ → ℝ}
    (hp : ∀ᵐ ω ∂P, p G (U ω)) :
    (fun ω => gatedRule p Phi G (U ω)) =ᵐ[P] (fun ω => Phi G (U ω)) := by
  filter_upwards [hp] with ω hω
  exact gatedRule_eq_of_gate hω

end Problem336

end

end OAI
