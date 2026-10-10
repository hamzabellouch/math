import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseBudgets
import OAI.Geometry.SurfaceImmersion.Atlas.UniformPhaseChartBounds

namespace OAI

/-! Fixed numerical mean budgets for nearby immersions in a linear phase chart.
The chart, cut-off, coefficient form, and weighted two-jet profile are fixed
before the nearby immersion and slow scale are supplied. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes

/-- The numerical part of the local mean budgets, without the map or scale. -/
structure BudgetProfiles where
  inv : ℕ → ℝ
  chi : ℕ → ℝ
  psi : ℕ → ℝ
  forms : ℕ → ℝ
  pull : ℕ → ℝ
  normal : ℕ → ℝ
  mode : ℕ → ℝ
  inv_pos : ∀ m, 1 ≤ inv m
  chi_pos : ∀ m, 1 ≤ chi m
  psi_pos : ∀ m, 1 ≤ psi m
  forms_pos : ∀ m, 1 ≤ forms m
  pull_pos : ∀ m, 1 ≤ pull m
  normal_pos : ∀ m, 1 ≤ normal m
  mode_pos : ∀ m, 1 ≤ mode m

def Budgets.profiles {U V : Set Base} {s : ℝ} {F : RField 4}
    {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}
    (d : Budgets U V s F ψ Q χ e) : BudgetProfiles where
  inv := d.inv
  chi := d.chi
  psi := d.psi
  forms := d.forms
  pull := d.pull
  normal := d.normal
  mode := d.mode
  inv_pos := d.inv_pos
  chi_pos := d.chi_pos
  psi_pos := d.psi_pos
  forms_pos := d.forms_pos
  pull_pos := d.pull_pos
  normal_pos := d.normal_pos
  mode_pos := d.mode_pos

end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean WeightedEstimates

/-- All seven mean-budget profiles can be chosen before a nearby immersion
and its actual slow scale. The dependence on its two-jet is the displayed
fixed profile `H`, rather than an implicit map-dependent constant. -/
theorem uniform_linear_phase_budgets_all_profiles {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {Ω U K : Set Base} (hΩ : IsOpen Ω) (hU : IsOpen U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hKΩ : K ⊆ Ω) {ξ : Base} (hξ : ξ ≠ 0)
    (hImm : ∀ x ∈ Ω, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ Ω, Good (realSecondTensor F x) ξ)
    {ψ : Base → ℝ} (hψ : ContDiff ℝ ∞ ψ) (Q : PhaseMean.Tensor →L[ℝ] ℝ)
    : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (H : ℕ → ℝ), (∀ m, 1 ≤ H m) →
    ∃ b : BudgetProfiles,
      ∀ (G : RField 4), ContDiff ℝ ∞ G → ∀ C₀ : ℝ, 0 ≤ C₀ → C₀ < ρ →
      WeightedBound univ 1 2 C₀ (G-F) →
      ∀ s : ℝ, 0 < s → s ≤ 1 →
      (∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (H m)
        (realTwoJet (G ∘ (linearPhaseChart ξ hξ U hU).symm))) →
      RealModeDomain (G ∘ (linearPhaseChart ξ hξ U hU).symm)
        (linearPhaseChart ξ hξ U hU).target ∧
      ∃ d : Budgets U (linearPhaseChart ξ hξ U hU).target s
        (G ∘ (linearPhaseChart ξ hξ U hU).symm) ψ (fun _ => Q)
        (linearPhaseChart ξ hξ U hU) (linearPhaseChart ξ hξ U hU).symm,
        d.profiles = b := by
  let L := phaseEquiv ξ hξ
  let V := (linearPhaseChart ξ hξ U hU).target
  let KV := L '' K
  let ΩV := L '' Ω
  have hV : IsOpen V := (linearPhaseChart ξ hξ U hU).open_target
  have hKV : IsCompact KV := hK.image L.continuous
  have hVK : V ⊆ KV := image_mono hUK
  have hsm := linearPhaseChart_smooth ξ hξ U hU
  let c : GoodPhaseChart F (phaseLinear ξ) := {
    chart := linearPhaseChart ξ hξ U hU
    phase := linearPhaseChart_phase ξ hξ U hU
    smooth := hsm.1
    smoothInverse := hsm.2
    sourceCompact := ⟨K,hK⟩
    targetCompact := ⟨KV,hKV⟩
    domain := ΩV
    sourceBound := hUK
    targetBound := hVK
    targetInside := image_mono hKΩ
    good := realModeDomain_phase hF hΩ hξ hImm hgood
  }
  obtain ⟨ρ,D,E,hρ,hD,hE,hnear⟩ := c.uniform_mode_bounds hF
  have hpull : ContDiffOn ℝ ∞ (pullbackField (linearPhaseChart ξ hξ U hU)) univ := by
    have hh : pullbackField (linearPhaseChart ξ hξ U hU) =
        fun _ => pullback (phaseEquiv ξ hξ).toContinuousLinearMap :=
      funext (pullbackField_linearPhaseChart hξ hU)
    rw [hh]
    exact contDiffOn_const
  choose I hI hbI using fun m => compact_local_weighted_bound hV isOpen_univ hKV
    hVK (subset_univ KV) hsm.2.contDiffOn m
  choose J hJ hbJ using fun m => compact_local_weighted_bound hU isOpen_univ hK
    hUK (subset_univ K) hsm.1.contDiffOn m
  choose P hP hbP using fun m => compact_local_weighted_bound hV isOpen_univ hKV
    hVK (subset_univ KV) hψ.contDiffOn m
  choose Qb hQb hbQ using fun m => compact_local_weighted_bound hV isOpen_univ hKV
    hVK (subset_univ KV) (show ContDiffOn ℝ ∞ (fun _ : Base => Q) univ from
      contDiffOn_const) m
  choose T hT hbT using fun m => compact_local_weighted_bound hU isOpen_univ hK
    hUK (subset_univ K) hpull m
  refine ⟨ρ,hρ,?_⟩
  intro H hH
  have hfactor (A : ℕ → ℝ) (hA : ∀ m, 1 ≤ A m) (m : ℕ) :
      1 ≤ (m.factorial : ℝ) * A m * H m ^ m := by
    have hf : (1 : ℝ) ≤ (m.factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos m)
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hf (hA m)) (one_le_pow₀ (hH m))
  let b : BudgetProfiles := {
    inv := I
    chi := J
    psi := P
    forms := Qb
    pull := T
    normal := fun m => (m.factorial : ℝ) * E m * H m ^ m
    mode := fun m => (m.factorial : ℝ) * D m * H m ^ m
    inv_pos := hI
    chi_pos := hJ
    psi_pos := hP
    forms_pos := hQb
    pull_pos := hT
    normal_pos := hfactor E hE
    mode_pos := hfactor D hD
  }
  refine ⟨b,?_⟩
  intro G hG C₀ hC₀ hCρ hb s hs hs1 hjet
  obtain ⟨hdom,hmodes⟩ := hnear G hG C₀ hC₀ hCρ hb
  refine ⟨hdom, {
    inv := b.inv
    chi := b.chi
    psi := b.psi
    forms := b.forms
    pull := b.pull
    normal := b.normal
    mode := b.mode
    inv_pos := b.inv_pos
    chi_pos := b.chi_pos
    psi_pos := b.psi_pos
    forms_pos := b.forms_pos
    pull_pos := b.pull_pos
    normal_pos := b.normal_pos
    mode_pos := b.mode_pos
    inv_bound := ?_
    chi_bound := ?_
    psi_bound := fun m => hbP m s hs.le hs1
    forms_bound := fun m => hbQ m s hs.le hs1
    pull_bound := fun m => hbT m s hs.le hs1
    normal_bound := fun m => (hmodes m s (H m) hs (hH m) (hjet m)).2
    mode_bound := fun m => (hmodes m s (H m) hs (hH m) (hjet m)).1
  }, rfl⟩
  · intro m j _ hj x hx
    simpa only [one_pow,one_mul] using hbI m 1 zero_le_one le_rfl j hj x hx
  · intro m j _ hj x hx
    simpa only [one_pow,one_mul] using hbJ m 1 zero_le_one le_rfl j hj x hx

/-- All seven mean-budget profiles can be chosen before a nearby immersion
and its actual slow scale. The dependence on its two-jet is the displayed
fixed profile `H`, rather than an implicit map-dependent constant. -/
theorem uniform_linear_phase_budgets {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {Ω U K : Set Base} (hΩ : IsOpen Ω) (hU : IsOpen U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hKΩ : K ⊆ Ω) {ξ : Base} (hξ : ξ ≠ 0)
    (hImm : ∀ x ∈ Ω, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ Ω, Good (realSecondTensor F x) ξ)
    {ψ : Base → ℝ} (hψ : ContDiff ℝ ∞ ψ) (Q : PhaseMean.Tensor →L[ℝ] ℝ)
    (H : ℕ → ℝ) (hH : ∀ m, 1 ≤ H m) :
    ∃ (ρ : ℝ) (b : BudgetProfiles), 0 < ρ ∧
      ∀ (G : RField 4), ContDiff ℝ ∞ G → ∀ C₀ : ℝ, 0 ≤ C₀ → C₀ < ρ →
      WeightedBound univ 1 2 C₀ (G-F) →
      ∀ s : ℝ, 0 < s → s ≤ 1 →
      (∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (H m)
        (realTwoJet (G ∘ (linearPhaseChart ξ hξ U hU).symm))) →
      RealModeDomain (G ∘ (linearPhaseChart ξ hξ U hU).symm)
        (linearPhaseChart ξ hξ U hU).target ∧
      ∃ d : Budgets U (linearPhaseChart ξ hξ U hU).target s
        (G ∘ (linearPhaseChart ξ hξ U hU).symm) ψ (fun _ => Q)
        (linearPhaseChart ξ hξ U hU) (linearPhaseChart ξ hξ U hU).symm,
        d.profiles = b := by
  obtain ⟨ρ,hρ,hall⟩ := uniform_linear_phase_budgets_all_profiles hF hΩ hU hK hUK hKΩ
    hξ hImm hgood hψ Q
  obtain ⟨b,hb⟩ := hall H hH
  exact ⟨ρ,b,hρ,hb⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
