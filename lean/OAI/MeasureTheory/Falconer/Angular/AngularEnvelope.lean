import OAI.MeasureTheory.Falconer.Angular.AngularTerminal
import OAI.MeasureTheory.Falconer.Fourier.ChartSymbolControl
import OAI.MeasureTheory.Falconer.Fourier.SpatialSymbols
import OAI.MeasureTheory.Falconer.Geometry.NormalizedInverseFactors
import OAI.MeasureTheory.Falconer.Estimates.SpatialEndpointFamily

namespace OAI

/-! # A bounded supremum of the actual admissible endpoint energies

The admissible class records only the existing chart-symbol control and
the required support. Its envelope is the real supremum of the original
endpoint-transform energies, with zero inserted to ensure nonemptiness.
-/

namespace Falconer
open Set MeasureTheory

def AngularAdmissible {n : ℕ} (k : ℕ) (D : ℝ)
    (Good : Set (Space (n+2) × Sphere (n+2)))
    (b : Space (n+2) → Sphere (n+2) → ℂ) : Prop :=
  ChartSymbolControl k b 1 D ∧ ∀ x w, b x w ≠ 0 → (x,w) ∈ Good

theorem AngularAdmissible.spatialMultiplier {n k : ℕ} {D : ℝ}
    {Good : Set (Space (n+2) × Sphere (n+2))}
    {b : Space (n+2) → Sphere (n+2) → ℂ} (h : AngularAdmissible k D Good b)
    (c : Space (n+2) → ℂ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1) :
    AngularAdmissible k D Good (fun x w => c x*b x w) :=
  ⟨h.1.spatialMultiplier c hc hcb,fun x w hw => h.2 x w (mul_ne_zero_iff.mp hw).2⟩

theorem AngularAdmissible.spatialFourier {n k : ℕ} {D : ℝ}
    {Good : Set (Space (n+2) × Sphere (n+2))}
    {b : Space (n+2) → Sphere (n+2) → ℂ} (h : AngularAdmissible k D Good b)
    (s : ℝ) (ξ : Space (n+2)) :
    AngularAdmissible k D Good (fun x w => spatialFourierPhase s ξ x*b x w) :=
  h.spatialMultiplier _ (by unfold spatialFourierPhase; fun_prop)
    (fun x => (spatialFourierPhase_norm s ξ x).le)

theorem AngularAdmissible.conj {n k : ℕ} {D : ℝ}
    {Good : Set (Space (n+2) × Sphere (n+2))}
    {b : Space (n+2) → Sphere (n+2) → ℂ} (h : AngularAdmissible k D Good b) :
    AngularAdmissible k D Good (fun x w => star (b x w)) := by
  refine ⟨h.1.conj,?_⟩
  intro x w hw
  apply h.2 x w
  intro hzero
  apply hw
  change star (b x w) = 0
  rw [hzero,star_zero]

noncomputable def angularEnergyValues {n : ℕ}
    (μ ν : Measure (Space (n+2))) (M P : ℝ) (k : ℕ) (D a v : ℝ) (Ψ : ℝ → ℝ)
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2))) : Set ℝ :=
  insert 0 {H | ∃ b c, AngularAdmissible k D GoodLeft b ∧
    AngularAdmissible k D GoodRight c ∧ H = independentAngularEnergy a v Ψ
      (fun z => endpointTransform μ M b z.1 z.2)
      (fun z => endpointTransform ν P c z.1 z.2)}

noncomputable def angularEnvelope {n : ℕ}
    (μ ν : Measure (Space (n+2))) (M P : ℝ) (k : ℕ) (D a v : ℝ) (Ψ : ℝ → ℝ)
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2))) : ℝ :=
  sSup (angularEnergyValues μ ν M P k D a v Ψ GoodLeft GoodRight)

noncomputable def angularEnvelopeBound {n : ℕ}
    (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  (2:ℝ)^(((n+2:ℕ):ℝ)*(v-a))*
    ((μ.real univ/M)^2*(ν.real univ/P)^2*(sphereMeasure (n+2)).real univ^2)*
    (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ

theorem angularEnergyValues_nonempty {n : ℕ}
    (μ ν : Measure (Space (n+2))) (M P : ℝ) (k : ℕ) (D a v : ℝ) (Ψ : ℝ → ℝ)
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2))) :
    (angularEnergyValues μ ν M P k D a v Ψ GoodLeft GoodRight).Nonempty :=
  ⟨0,Or.inl rfl⟩

theorem angularEnergyValues_bound {n : ℕ}
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (k : ℕ) (D a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2))) :
    ∀ H ∈ angularEnergyValues μ ν M P k D a v Ψ GoodLeft GoodRight,
      H ≤ angularEnvelopeBound μ ν M P a v Ψ := by
  intro H hH
  rcases hH with rfl | ⟨b,c,hb,hc,rfl⟩
  · unfold angularEnvelopeBound
    positivity
  · apply independentAngularEnergy_bound a v Ψ _ _
      (div_nonneg measureReal_nonneg hM.le) (div_nonneg measureReal_nonneg hP.le)
    · intro z
      simpa only [one_mul] using endpointTransform_norm_le μ hM b hb.1.bound z.1 z.2
    · intro z
      simpa only [one_mul] using endpointTransform_norm_le ν hP c hc.1.bound z.1 z.2

theorem angularEnergyValues_bddAbove {n : ℕ}
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (k : ℕ) (D a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2))) :
    BddAbove (angularEnergyValues μ ν M P k D a v Ψ GoodLeft GoodRight) :=
  ⟨angularEnvelopeBound μ ν M P a v Ψ,
    angularEnergyValues_bound μ ν hM hP k D a v Ψ GoodLeft GoodRight⟩

theorem angularEnvelope_nonneg {n : ℕ}
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (k : ℕ) (D a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2))) :
    0 ≤ angularEnvelope μ ν M P k D a v Ψ GoodLeft GoodRight :=
  le_csSup (angularEnergyValues_bddAbove μ ν hM hP k D a v Ψ GoodLeft GoodRight) (Or.inl rfl)

theorem angularEnvelope_le_bound {n : ℕ}
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (k : ℕ) (D a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2))) :
    angularEnvelope μ ν M P k D a v Ψ GoodLeft GoodRight ≤
      angularEnvelopeBound μ ν M P a v Ψ :=
  csSup_le (angularEnergyValues_nonempty μ ν M P k D a v Ψ GoodLeft GoodRight)
    (angularEnergyValues_bound μ ν hM hP k D a v Ψ GoodLeft GoodRight)

theorem admissible_energy_le_angularEnvelope {n : ℕ}
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (k : ℕ) (D a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2)))
    (b c : Space (n+2) → Sphere (n+2) → ℂ)
    (hb : AngularAdmissible k D GoodLeft b) (hc : AngularAdmissible k D GoodRight c) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform μ M b z.1 z.2)
      (fun z => endpointTransform ν P c z.1 z.2) ≤
      angularEnvelope μ ν M P k D a v Ψ GoodLeft GoodRight :=
  le_csSup (angularEnergyValues_bddAbove μ ν hM hP k D a v Ψ GoodLeft GoodRight)
    (Or.inr ⟨b,c,hb,hc,rfl⟩)

theorem spatial_endpoint_energy_le_envelope {n : ℕ}
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (k : ℕ) (D a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2)))
    (b c : Space (n+2) → Sphere (n+2) → ℂ)
    (hb : AngularAdmissible k D GoodLeft b) (hc : AngularAdmissible k D GoodRight c)
    (s : ℝ) (ξ : Space (n+2)) :
    independentAngularEnergy a v Ψ
      (fun z => spatialEndpointFamily μ M s b (ξ,z))
      (fun z => spatialEndpointFamily ν P s (fun x w => star (c x w)) (ξ,z)) ≤
      angularEnvelope μ ν M P k D a v Ψ GoodLeft GoodRight := by
  let b' : Space (n+2) → Sphere (n+2) → ℂ :=
    fun x w => spatialFourierPhase s ξ x*b x w
  let c' : Space (n+2) → Sphere (n+2) → ℂ :=
    fun x w => spatialFourierPhase s ξ x*star (c x w)
  have hb' : AngularAdmissible k D GoodLeft b' := hb.spatialFourier s ξ
  have hc' : AngularAdmissible k D GoodRight c' := hc.conj.spatialFourier s ξ
  change independentAngularEnergy a v Ψ
    (fun z => endpointTransform μ M b' z.1 z.2)
    (fun z => endpointTransform ν P c' z.1 z.2) ≤ _
  exact admissible_energy_le_angularEnvelope (n := n) μ ν hM hP k D a v Ψ
    GoodLeft GoodRight b' c' hb' hc'

theorem AngularAdmissible.mono {n k : ℕ} {D E : ℝ}
    {Good Good' : Set (Space (n+2) × Sphere (n+2))}
    {b : Space (n+2) → Sphere (n+2) → ℂ}
    (h : AngularAdmissible k D Good b) (hD : 0 ≤ D) (hDE : D ≤ E)
    (hGood : Good ⊆ Good') : AngularAdmissible k E Good' b := by
  refine ⟨⟨h.1.measurable,h.1.bound,h.1.smooth,?_⟩,fun x w hw => hGood (h.2 x w hw)⟩
  intro e l hl x y hy u hu
  exact (h.1.derivative e l hl x y hy u hu).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hDE l) (by norm_num : (0:ℝ) ≤ 1))

theorem angularEnvelope_mono {n : ℕ}
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (k : ℕ) {D E : ℝ}
    (hD : 0 ≤ D) (hDE : D ≤ E) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    {GoodLeft GoodRight GoodLeft' GoodRight' : Set (Space (n+2) × Sphere (n+2))}
    (hLeft : GoodLeft ⊆ GoodLeft') (hRight : GoodRight ⊆ GoodRight') :
    angularEnvelope μ ν M P k D a v Ψ GoodLeft GoodRight ≤
      angularEnvelope μ ν M P k E a v Ψ GoodLeft' GoodRight' := by
  apply csSup_le_csSup
    (angularEnergyValues_bddAbove μ ν hM hP k E a v Ψ GoodLeft' GoodRight')
    (angularEnergyValues_nonempty μ ν M P k D a v Ψ GoodLeft GoodRight)
  intro H hH
  rcases hH with rfl | ⟨b,c,hb,hc,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨b,c,hb.mono hD hDE hLeft,hc.mono hD hDE hRight,rfl⟩

end Falconer

end OAI
