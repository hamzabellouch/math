import OAI.Analysis.LipschitzHilbert.Trees.SourceOrdinaryModelBound
import OAI.Analysis.LipschitzHilbert.Trees.SourceModelDegenerateCases

namespace OAI

/-! The ordinary finite-packet estimate, including zero input energy,
zero tested measure, and every positive density bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem exists_ordinary_submodel_estimate (hL : LepingleInput)
    (P : SourceLabeledLattice N κ Label Item) (initial : Finset P.PacketIndex)
    (d : OrdinaryModelConfig P initial) :
    ∃ C : ℝ, 0<C ∧
    ∀ (packets : Finset P.PacketIndex), packets⊆initial →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), MemLp g 2 (volume.prod volume) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (gamma : ℝ), 0<gamma →
      (∀ q∈packets, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤gamma) →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun j =>
        P.ordinaryCoefficient g q.1 q.2.1 q.2.2 j*d.selector q.1 q.2.1 j (u z)*
          P.physicalPacket 0 q.1 q.2.1 q.2.2 j z)
      IntegrableOn (fun z => ∑ q∈packets, V q z) E (volume.prod volume) ∧
        (∫ z in E, ‖∑ q∈packets, V q z‖ ∂volume.prod volume)≤
          C*Real.sqrt (∫ z, ‖g z‖^2 ∂volume.prod volume)*
            Real.sqrt ((volume.prod volume).real E)*gamma^(1/4:ℝ) := by
  let U := max 1 (∫ z, topProfile 203 z ∂volume.prod volume)
  have hU : 1≤U := le_max_left _ _
  obtain ⟨C,hC,hModel⟩ := exists_ordinary_submodel_bound_bounded hL P initial d U hU
  refine ⟨C,hC,?_⟩
  intro packets hpackets g hg E hE hEfin u hu gamma hgamma hden V
  by_cases henergy : (∫ z, ‖g z‖^2 ∂volume.prod volume)=0
  · have heval (z : ℝ×ℝ) : (∑ q∈packets, V q z)=0 := by
      apply Finset.sum_eq_zero
      intro q _
      have hc := P.ordinaryCoefficient_zero_of_energy_zero g hg henergy q.1 q.2.1 q.2.2
      apply WithLp.ofLp_injective
      funext k
      change P.ordinaryCoefficient g q.1 q.2.1 q.2.2 k*d.selector q.1 q.2.1 k (u z)*
        P.physicalPacket 0 q.1 q.2.1 q.2.2 k z=0
      rw [hc]
      simp only [WithLp.ofLp_zero,Pi.zero_apply,zero_mul]
    simp only [heval,norm_zero,integral_zero,henergy,Real.sqrt_zero,mul_zero,zero_mul,le_refl,and_true]
    exact integrableOn_zero
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
      have h := hModel packets hpackets g hg (Real.sqrt (∫ z, ‖g z‖^2 ∂volume.prod volume))
        (Real.sqrt_pos.mpr henergyPos) (Real.sq_sqrt henergyPos.le) E hE hEfin hareaPos
        u hu (min gamma U) (lt_min hgamma (zero_lt_one.trans_le hU)) (min_le_right _ _)
        (fun q hq => le_min (hden q hq) (hdenU q))
      refine ⟨h.1,h.2.trans ?_⟩
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (le_min hgamma.le (zero_le_one.trans hU)) (min_le_left _ _) (by norm_num))
        (by positivity)

theorem exists_ordinary_model_estimate (hL : LepingleInput)
    (P : SourceLabeledLattice N κ Label Item) (initial : Finset P.PacketIndex)
    (d : OrdinaryModelConfig P initial) :
    ∃ C : ℝ, 0<C ∧
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), MemLp g 2 (volume.prod volume) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (gamma : ℝ), 0<gamma →
      (∀ q∈initial, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤gamma) →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun j =>
        P.ordinaryCoefficient g q.1 q.2.1 q.2.2 j*d.selector q.1 q.2.1 j (u z)*
          P.physicalPacket 0 q.1 q.2.1 q.2.2 j z)
      IntegrableOn (fun z => ∑ q∈initial, V q z) E (volume.prod volume) ∧
        (∫ z in E, ‖∑ q∈initial, V q z‖ ∂volume.prod volume)≤
          C*Real.sqrt (∫ z, ‖g z‖^2 ∂volume.prod volume)*
            Real.sqrt ((volume.prod volume).real E)*gamma^(1/4:ℝ) := by
  obtain ⟨C,hC,h⟩ := exists_ordinary_submodel_estimate hL P initial d
  exact ⟨C,hC,h initial (Finset.Subset.refl _)⟩

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
