import OAI.Analysis.LipschitzHilbert.Packets.PacketDataUniformReverseModel
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundedInputEnergy
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelDegenerateCases
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataUniversalEstimate

namespace OAI

/-! The supported reverse estimate with constants independent of the
finite lattice. All geometric dependence is exposed in reverseModelCost. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
theorem exists_uniform_reverse_disparity (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0<cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar<cEta*cb) :
    ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ (F : Set (ℝ×ℝ)), MeasurableSet F → (volume.prod volume) F≠∞ →
      (∀ z, z∉F → g z=0) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun j =>
        P.ordinaryCoefficient g q.1 q.2.1 q.2.2 j*d.selector q.1 q.2.1 j (u z)*
          P.physicalPacket 0 q.1 q.2.1 q.2.2 j z)
      IntegrableOn (fun z => ∑ q∈initial, V q z) E (volume.prod volume) ∧
        (∫ z in E, ‖∑ q∈initial, V q z‖ ∂volume.prod volume)≤
          d.reverseModelCost CD CS CT CZ ordinaryDensityUpper*Real.sqrt (((volume.prod volume).real F)*((volume.prod volume).real E))*
            (((volume.prod volume).real E)/((volume.prod volume).real F))^(9/20:ℝ) := by
  obtain ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,hAll⟩ := exists_uniform_reverse_model_bound hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅
  let U := ordinaryDensityUpper
  have hU : 1≤U := le_max_left _ _
  have hModel := hAll N κ Label Item P initial d heq₁ heq₂ heq₃ heq₄ heq₅ U hU
  let C := d.reverseModelCost CD CS CT CZ U
  have hC : 0<C := d.reverseModelCost_pos CD CS CT CZ U
  intro g hgm hgb F hF hFfin hsupport E hE hEfin u hu V
  obtain ⟨hg,henergyBound⟩ := bounded_supported_input g hgm hgb F hF hFfin hsupport
  by_cases henergy : (∫ z, ‖g z‖^2 ∂volume.prod volume)=0
  · have heval (z : ℝ×ℝ) : (∑ q∈initial, V q z)=0 := by
      apply Finset.sum_eq_zero
      intro q _
      have hc := P.ordinaryCoefficient_zero_of_energy_zero g hg henergy q.1 q.2.1 q.2.2
      apply WithLp.ofLp_injective
      funext k
      change P.ordinaryCoefficient g q.1 q.2.1 q.2.2 k*d.selector q.1 q.2.1 k (u z)*
        P.physicalPacket 0 q.1 q.2.1 q.2.2 k z=0
      rw [hc]
      simp only [WithLp.ofLp_zero,Pi.zero_apply,zero_mul]
    refine ⟨?_,?_⟩
    · simpa only [heval] using (integrableOn_zero : IntegrableOn (fun _ : ℝ×ℝ => (0:EuclideanSpace ℂ κ)) E (volume.prod volume))
    · simp only [heval,norm_zero,integral_zero]
      positivity
  · by_cases harea : (volume.prod volume).real E=0
    · have hm : (volume.prod volume) E=0 := (measureReal_eq_zero_iff hEfin).mp harea
      have hr : (volume.prod volume).restrict E=0 := Measure.restrict_eq_zero.mpr hm
      simp [IntegrableOn,hr,harea]
    · have henergyPos : 0<(∫ z, ‖g z‖^2 ∂volume.prod volume) :=
        lt_of_le_of_ne (integral_nonneg (fun z => sq_nonneg ‖g z‖)) (Ne.symm henergy)
      have hareaPos : 0<(volume.prod volume).real E := lt_of_le_of_ne measureReal_nonneg (Ne.symm harea)
      have hdenU (q : P.PacketIndex) : P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤U :=
        ((P.densityTile 0 d.cell q).density_le P.topLength d.w P.width d.tau d.grid E u).trans
          (le_max_right _ _)
      have h := hModel g hg hgm hgb (Real.sqrt (∫ z, ‖g z‖^2 ∂volume.prod volume))
        (Real.sqrt_pos.mpr henergyPos) (Real.sq_sqrt henergyPos.le) E hE hEfin hareaPos
        u hu U (zero_lt_one.trans_le hU) le_rfl (fun q _ => hdenU q)
      rw [Real.sq_sqrt henergyPos.le] at h
      have hFpos : 0<(volume.prod volume).real F := henergyPos.trans_le henergyBound
      have hratio : ((volume.prod volume).real E)/((volume.prod volume).real F)≤
          ((volume.prod volume).real E)/(∫ z, ‖g z‖^2 ∂volume.prod volume) :=
        div_le_div_of_nonneg_left hareaPos.le henergyPos henergyBound
      have hp := Real.rpow_le_rpow_of_nonpos (div_pos hareaPos hFpos) hratio
        (by norm_num : -(1/20:ℝ)≤0)
      refine ⟨h.1,h.2.trans ?_⟩
      calc
        _ ≤ C*((volume.prod volume).real E)*
            (((volume.prod volume).real E)/((volume.prod volume).real F))^(-(1/20:ℝ)) :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg hC.le hareaPos.le)
        _ = _ := by
          rw [mul_assoc,reverse_disparity_identity hareaPos hFpos]
          ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
