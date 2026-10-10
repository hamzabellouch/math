import OAI.Analysis.LipschitzHilbert.Packets.PacketDataUniversalEstimate
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAdjointEnergy

namespace OAI

/-! Explicit adjoint energy with the same analytic constants selected
before all lattices in the ordinary estimate. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_universal_ordinary_adjoint_energy (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0<cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar<cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ S : Finset P.PacketIndex, S⊆initial →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ E : Set (ℝ×ℝ), MeasurableSet E → (volume.prod volume) E≠∞ →
      (∀ z, z∉E → g z=0) → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∫ z, ‖P.ordinaryAdjointSum S d.selector u g z‖^2 ∂volume.prod volume)≤
        (d.modelCost CD CS CT*ordinaryDensityUpper^(1/4:ℝ))^2*(volume.prod volume).real E := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hAll⟩ := exists_universal_ordinary_model_estimate hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d h₁ h₂ h₃ h₄ h₅
  let C := d.modelCost CD CS CT
  have hC : 0<C := d.modelCost_pos CD CS CT
  let U := ordinaryDensityUpper
  have hU : 0<U := zero_lt_one.trans_le (le_max_left _ _)
  have hModel := hAll N κ Label Item P initial d h₁ h₂ h₃ h₄ h₅
  intro S hS g hgm hgb E hE hEfin hsupport u hu
  have hg := (bounded_supported_input g hgm hgb E hE hEfin hsupport).1
  let f := P.ordinaryAdjointSum S d.selector u g
  have hf : MemLp f 2 (volume.prod volume) := P.ordinaryAdjointSum_memLp S d.selector u g
  have hd (q : P.PacketIndex) (_hq : q∈S) : P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤U :=
    ((P.densityTile 0 d.cell q).density_le P.topLength d.w P.width d.tau d.grid E u).trans
      (le_max_right _ _)
  have h := hModel S hS f hf E hE hEfin u hu U hU hd
  let F := P.ordinaryForwardSum S d.selector u f
  change IntegrableOn F E (volume.prod volume) ∧
    (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
      C*Real.sqrt (∫ z, ‖f z‖^2 ∂volume.prod volume)*
        Real.sqrt ((volume.prod volume).real E)*U^(1/4:ℝ) at h
  let energy := ∫ z, ‖f z‖^2 ∂volume.prod volume
  have henergy : 0≤energy := integral_nonneg (fun z => sq_nonneg ‖f z‖)
  have hpair := P.ordinary_forward_adjoint_pairing S d.selector d.measurable d.bounded u hu f g hf hg
  have hself : (∫ z, inner ℂ (f z) (f z) ∂volume.prod volume)=(energy:ℂ) := by
    simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow]
    exact integral_ofReal (μ:=volume.prod volume) (f:=fun z : ℝ×ℝ => ‖f z‖^2)
  change (∫ z, inner ℂ (F z) (g z) ∂volume.prod volume)=
    conj (∫ z, inner ℂ (f z) (f z) ∂volume.prod volume) at hpair
  rw [hself,Complex.conj_ofReal] at hpair
  have hpairNorm : ‖∫ z, inner ℂ (F z) (g z) ∂volume.prod volume‖=energy := by
    rw [hpair,Complex.norm_real,Real.norm_of_nonneg henergy]
  have hset : (∫ z, inner ℂ (F z) (g z) ∂volume.prod volume)=
      ∫ z in E, inner ℂ (F z) (g z) ∂volume.prod volume := by
    calc
      _ = ∫ z, E.indicator (fun z => inner ℂ (F z) (g z)) z ∂volume.prod volume := by
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z∈E
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz,hsupport z hz,inner_zero_right]
      _ = _ := integral_indicator hE
  have hpoint (z : ℝ×ℝ) : ‖inner ℂ (F z) (g z)‖≤‖F z‖ :=
    (norm_inner_le_norm (𝕜:=ℂ) _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hgb z))
  have hInt : IntegrableOn (fun z => inner ℂ (F z) (g z)) E (volume.prod volume) :=
    h.1.norm.mono' (h.1.aestronglyMeasurable.inner hgm.aestronglyMeasurable)
      (Filter.Eventually.of_forall hpoint)
  have he : energy≤C*Real.sqrt energy*Real.sqrt ((volume.prod volume).real E)*U^(1/4:ℝ) := by
    calc
      _ = ‖∫ z, inner ℂ (F z) (g z) ∂volume.prod volume‖ := hpairNorm.symm
      _ = ‖∫ z in E, inner ℂ (F z) (g z) ∂volume.prod volume‖ := congrArg norm hset
      _ ≤ ∫ z in E, ‖inner ℂ (F z) (g z)‖ ∂volume.prod volume := norm_integral_le_integral_norm _
      _ ≤ ∫ z in E, ‖F z‖ ∂volume.prod volume := integral_mono hInt.norm h.1.norm hpoint
      _ ≤ _ := h.2
  have hroot : Real.sqrt energy≤C*Real.sqrt ((volume.prod volume).real E)*U^(1/4:ℝ) := by
    by_cases hz : Real.sqrt energy=0
    · rw [hz]
      positivity
    · have hp : 0<Real.sqrt energy := lt_of_le_of_ne (Real.sqrt_nonneg energy) (Ne.symm hz)
      nlinarith [Real.sq_sqrt henergy]
  calc
    _ = (Real.sqrt energy)^2 := (Real.sq_sqrt henergy).symm
    _ ≤ (C*Real.sqrt ((volume.prod volume).real E)*U^(1/4:ℝ))^2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg energy) hroot 2
    _ = (C*U^(1/4:ℝ))^2*(Real.sqrt ((volume.prod volume).real E))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt measureReal_nonneg]

end LipschitzHilbert.PacketLatticeData

end

end OAI
