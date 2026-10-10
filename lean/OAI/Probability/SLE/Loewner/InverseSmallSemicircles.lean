import OAI.Probability.SLE.Loewner.InverseStripEnergy
import OAI.Probability.SLE.Geometry.ShrinkingStripEnergy
import OAI.Probability.SLE.Loewner.InverseBoundaryArc

namespace OAI

/-! Arbitrarily small closed image semicircles at each real boundary point.
The endpoint values are obtained from finite energy, not from an assumed
continuous extension of the inverse map. -/
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.inverse_log_holomorphic
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (x : ℝ) :
    DifferentiableOn ℂ (fun z => F t ((x:ℂ)+Complex.exp z))
      {z | 0<z.im ∧ z.im<Real.pi} := by
  apply (hw.2.2.2.2.1 t).comp
    ((differentiable_const (x:ℂ)).add Complex.differentiable_exp).differentiableOn
  intro z hz
  change 0<((x:ℂ)+Complex.exp z).im
  simpa only [Set.mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,zero_add] using exp_strip_halfplane hz

lemma IsCapacityTwoWitness.exists_small_inverse_semicircle
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (x Q ε : ℝ) (hε : 0<ε) :
    ∃ (v : ℝ) (c : ℝ → ℂ), v<Q ∧ Continuous c ∧
      (∀ θ∈Ioo 0 Real.pi, c θ=F t ((x:ℂ)+Complex.exp ((v:ℂ)+(θ:ℂ)*Complex.I))) ∧
      (∀ θ∈Icc 0 Real.pi, ∀ φ∈Icc 0 Real.pi, ‖c θ-c φ‖≤ε) ∧
      c 0∈frontier (survivingDomain γ t) ∧ c Real.pi∈frontier (survivingDomain γ t) ∧
      MapsTo c (Ioo 0 Real.pi) (survivingDomain γ t) ∧ InjOn c (Ioo 0 Real.pi) := by
  let f : ℂ → ℂ := fun z => F t ((x:ℂ)+Complex.exp z)
  have hf := hw.inverse_log_holomorphic t x
  obtain ⟨v,hv,hd,hsmall⟩ := exists_small_holomorphic_section hf
    (hw.inverse_strip_dirichlet_finite t x 0) Q ε hε
  let w : ℝ → ℂ := fun θ => (x:ℂ)+Complex.exp ((v:ℂ)+(θ:ℂ)*Complex.I)
  have hS : IsOpen {z : ℂ | 0<z.im ∧ z.im<Real.pi} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hsection (θ : ℝ) (hθ : θ∈Ioo 0 Real.pi) :
      DifferentiableAt ℝ (fun θ : ℝ => F t (w θ)) θ := by
    change DifferentiableAt ℝ (f ∘ fun θ : ℝ => (v:ℂ)+(θ:ℂ)*Complex.I) θ
    have hz : (v:ℂ)+(θ:ℂ)*Complex.I∈{z : ℂ | 0<z.im ∧ z.im<Real.pi} := by
      simpa using hθ
    exact ((hf.differentiableAt (hS.mem_nhds hz)).restrictScalars ℝ).comp θ
      ((Complex.ofRealCLM.differentiableAt.mul_const Complex.I).const_add (v:ℂ))
  obtain ⟨c,hc,he⟩ := finite_energy_angular_extension hsection hd
  have hwc : Continuous w := by dsimp [w]; fun_prop
  have hwin : MapsTo w (Ioo 0 Real.pi) upperHalfPlane := by
    intro θ hθ
    change 0<((x:ℂ)+Complex.exp ((v:ℂ)+(θ:ℂ)*Complex.I)).im
    simpa only [Set.mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,zero_add] using
      exp_strip_halfplane (x := (v:ℂ)+(θ:ℂ)*Complex.I) (by simpa using hθ)
  have hwend (s : ℝ) (hs : s=0 ∨ s=Real.pi) : w s∉upperHalfPlane := by
    rcases hs with rfl | rfl <;>
      simp [w,upperHalfPlane,Complex.exp_add,Complex.exp_ofReal_mul_I,← Complex.ofReal_exp]
  have hend (s : ℝ) (hs : s∈Icc 0 Real.pi) (hs' : s=0 ∨ s=Real.pi) :
      c s∈frontier (survivingDomain γ t) :=
    inverse_arc_endpoint_mem_frontier (isOpen_survivingDomain hw.1 t)
      (hw.2.2.2.1 t).continuousOn (hw.2.2.2.2.2.1 t) (hw.2.2.2.2.2.2.1 t)
      (hw.2.2.2.2.2.2.2.2.1 t) hwc hc Real.pi_pos hs hwin (hwend s hs') he
  refine ⟨v,c,hv,hc,he,?_,hend 0 ⟨le_rfl,Real.pi_pos.le⟩ (Or.inl rfl),
    hend Real.pi ⟨Real.pi_pos.le,le_rfl⟩ (Or.inr rfl),?_,?_⟩
  · apply continuous_angular_oscillation_on_endpoints hc ε
    intro θ hθ φ hφ
    rw [he hθ,he hφ]
    exact (hsmall θ hθ φ hφ).le
  · intro θ hθ
    rw [he hθ]
    exact hw.2.2.2.2.2.2.1 t (hwin hθ)
  · intro θ hθ φ hφ heq
    rw [he hθ,he hφ] at heq
    change F t (w θ)=F t (w φ) at heq
    have hwθ := hw.2.2.2.2.2.2.2.2.1 t (w θ) (hwin hθ)
    have hwφ := hw.2.2.2.2.2.2.2.2.1 t (w φ) (hwin hφ)
    have hww : w θ=w φ := by rw [heq,hwφ] at hwθ; exact hwθ.symm
    have harg := exp_injective_strip
      (x₁ := (v:ℂ)+(θ:ℂ)*Complex.I) (x₂ := (v:ℂ)+(φ:ℂ)*Complex.I)
      (by simpa using hθ) (by simpa using hφ) (add_left_cancel hww)
    have him := congrArg Complex.im harg
    simpa using him

end SLEExactGauge

end

end OAI
