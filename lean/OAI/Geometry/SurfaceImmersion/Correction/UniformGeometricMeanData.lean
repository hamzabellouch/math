import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanProfile
import OAI.Geometry.SurfaceImmersion.Correction.CompactMeanBudgets
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartBounds

namespace OAI

/-! A single geometric mean datum at unit slow scale supplies one fixed
profile and actual mean data at all admissible smaller scales. -/
noncomputable section
open TopologicalSpace Set
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseMean
open RealModes

theorem LocalBounds.atScale {U V : Set SmallModes.Base} {s r ρ R : ℝ}
    {reference : SmallModes.Base → Tensor} {F : RField 4} {ψ : SmallModes.Base → ℝ}
    {Q : SmallModes.Base → Tensor →L[ℝ] ℝ} {χ e : SmallModes.Base → SmallModes.Base}
    (h : LocalBounds U V s r ρ R reference F ψ Q χ e) (t : ℝ) :
    LocalBounds U V t r ρ R reference F ψ Q χ e where
  openU := h.openU
  smoothF := h.smoothF
  domain := h.domain
  smoothPsi := h.smoothPsi
  smoothQ := h.smoothQ
  smoothChi := h.smoothChi
  smoothInv := h.smoothInv
  chiInto := h.chiInto
  invInto := h.invInto
  smoothPullback := h.smoothPullback
  margin := h.margin

theorem LocalBounds.atRadius {U V : Set SmallModes.Base} {s r r' ρ R : ℝ}
    {reference : SmallModes.Base → Tensor} {F : RField 4} {ψ : SmallModes.Base → ℝ}
    {Q : SmallModes.Base → Tensor →L[ℝ] ℝ} {χ e : SmallModes.Base → SmallModes.Base}
    (h : LocalBounds U V s r ρ R reference F ψ Q χ e) (hr : r' ≤ r) :
    LocalBounds U V s r' ρ R reference F ψ Q χ e := by
  refine { h with margin := ?_ }
  intro x hx
  have hm := h.margin x hx
  have hn : ‖Q x‖*r' ≤ ‖Q x‖*r := mul_le_mul_of_nonneg_left hr (norm_nonneg _)
  constructor <;> linarith

end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

theorem unit_mean_data_uniform_family {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ} {K : Compacts Base}
    (c₀ : PolynomialSolveData P 0 G hG φ K 1 1)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d₀ : ChartedMeanData c₀ r ρ R reference) :
    ∃ p : ChartedMeanProfile P, ∀ (ε τ : ℝ) (s : ℝ≥0) (r' : ℝ), r' ≤ r →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      ∃ c : PolynomialSolveData P ε G hG φ K τ s,
      ∃ d : ChartedMeanData c r' ρ R reference,
        p.Fits d ∧ c.e = c₀.e ∧ (∀ x, d.cutoff x = d₀.cutoff x) ∧ d.form = d₀.form := by
  let I : ℕ → ℝ := fun m => d₀.budgets.inv (m+1)
  have hI (m : ℕ) : 1 ≤ I m := d₀.budgets.inv_pos (m+1)
  have hIb (m j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m+1) (x : SmallModes.Base) (hx : x ∈ c₀.e.target) :
      ‖iteratedFDerivWithin ℝ j c₀.e.symm c₀.e.target x‖ ≤ I m :=
    d₀.budgets.inv_bound (m+1) j hj hjm x hx
  obtain ⟨D,hD,hd⟩ := phaseChartPolynomialOperator_bounds c₀.openU c₀.openO d₀.compact d₀.subsetDomain
    P c₀.smoothP K c₀.supportU c₀.e c₀.smoothForward c₀.smoothInverse c₀.supportChart
    d₀.B d₀.F c₀.J I d₀.oneLEB d₀.nonnegF c₀.oneLEJ hI c₀.coordinates hIb
  let p : ChartedMeanProfile P := {
    U := c₀.U
    O := c₀.O
    Q := d₀.compactJets
    V := c₀.e.target
    openU := c₀.openU
    openO := c₀.openO
    openV := c₀.e.open_target
    compact := d₀.compact
    subsetDomain := d₀.subsetDomain
    smoothP := c₀.smoothP
    C := c₀.C
    D := D
    J := c₀.J
    inv := d₀.budgets.inv
    forms := d₀.budgets.forms
    psi := d₀.budgets.psi
    normal := d₀.budgets.normal
    B := d₀.B
    F := d₀.F
    nonnegC := c₀.nonnegC
    oneLEJ := c₀.oneLEJ
    oneLEInv := d₀.budgets.inv_pos
    oneLEForms := d₀.budgets.forms_pos
    oneLEPsi := d₀.budgets.psi_pos
    oneLENormal := d₀.budgets.normal_pos
    oneLEB := d₀.oneLEB
    nonnegF := d₀.nonnegF
  }
  refine ⟨p,?_⟩
  intro ε τ s r' hr hτ hs hτs hs1 hε hε1
  have hBj (m : ℕ) := (d₀.jetsBound m).shrink_scale s.coe_nonneg hs1
  have hFj (m : ℕ) (v : Fin 2) := (d₀.phaseBound m v).shrink_scale s.coe_nonneg hs1
  let c : PolynomialSolveData P ε G hG φ K τ s := {
    U := c₀.U
    O := c₀.O
    openU := c₀.openU
    openO := c₀.openO
    smoothP := c₀.smoothP
    mapsG := c₀.mapsG
    supportU := c₀.supportU
    smoothPhase := c₀.smoothPhase
    e := c₀.e
    smoothForward := c₀.smoothForward
    smoothInverse := c₀.smoothInverse
    supportChart := c₀.supportChart
    phase := c₀.phase
    smoothMap := c₀.smoothMap
    domain := c₀.domain
    C := c₀.C
    D := D
    J := c₀.J
    nonnegC := c₀.nonnegC
    nonnegD := hD
    oneLEJ := c₀.oneLEJ
    coordinates := c₀.coordinates
    coefficients := fun m => reconstruction_shrink_scale (c₀.coefficients m) s.coe_nonneg hs1
    polynomial := hd G φ hG c₀.smoothPhase d₀.mapsJets s τ ε hτ hs hτs hs1 hε hε1 hBj hFj
  }
  let d : ChartedMeanData c r' ρ R reference := {
    cutoff := d₀.cutoff
    form := d₀.form
    localBounds := (d₀.localBounds.atScale s).atRadius hr
    budgets := d₀.budgets.atScale s s.coe_nonneg hs1
    compactJets := d₀.compactJets
    compact := d₀.compact
    subsetDomain := d₀.subsetDomain
    mapsJets := d₀.mapsJets
    B := d₀.B
    F := d₀.F
    oneLEB := d₀.oneLEB
    nonnegF := d₀.nonnegF
    jetsBound := hBj
    phaseBound := hFj
  }
  refine ⟨c,d,?_,rfl,(fun _ => rfl),rfl⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
