import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensity

namespace OAI

/-! A zero-density packet contributes zero on the tested set. This is
the exact finite-remainder assertion used by the threshold iteration. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem selector_zero_of_density_zero
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ) (q : P.PacketIndex)
    (hlen : P.length q.1≤tau)
    (hslope : P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (hdensity : P.ordinaryDensity 0 cell grid w tau E u q≤0)
    (selector : κ → ℝ → ℂ)
    (hsupport : ∀ k s, selector k s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) (k : κ) :
    ∀ᵐ z ∂(volume.prod volume).restrict E, selector k (u z)=0 := by
  let test := P.ownDensityTest 0 cell grid w tau q hlen (by simpa only [zero_add] using hslope)
  let A := E ∩ u ⁻¹' scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)
  have hA : MeasurableSet A := hE.inter (hu (scaledAngularCell_measurable _ _ _ _))
  have havg : densityAverage test.top E u
      (scaledAngularCell (w/P.topLength) grid test.level test.cell)≤0 := by
    apply le_trans (le_csSup ((P.densityTile 0 cell q).densityValues_bddAbove
      P.topLength w P.width tau grid E u) (Or.inr ⟨test,rfl⟩)) hdensity
  have hzero : (∫ z in A, test.top.densityKernel 203 z ∂volume.prod volume)=0 := by
    have hn : 0≤(∫ z in A, test.top.densityKernel 203 z ∂volume.prod volume) :=
      integral_nonneg (fun z => test.top.densityKernel_nonneg 203 z)
    have hl : (∫ z in A, test.top.densityKernel 203 z ∂volume.prod volume)≤0 := by
      have h := (div_le_iff₀ test.top.area_pos).mp havg
      simpa only [zero_mul,A,test,ownDensityTest] using h
    exact le_antisymm hl hn
  have hzeroAE : (test.top.densityKernel 203)=ᵐ[(volume.prod volume).restrict A] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => test.top.densityKernel_nonneg 203 z)
      (test.top.densityKernel_integrable (by norm_num)).integrableOn).mp hzero
  have hout : ∀ᵐ z ∂volume.prod volume, z∈A → test.top.densityKernel 203 z=0 :=
    (ae_restrict_iff' hA).mp hzeroAE
  filter_upwards [ae_restrict_of_ae hout,self_mem_ae_restrict hE] with z hz hzE
  by_contra hn
  have hmem : z∈A := ⟨hzE,hsupport k (u z) hn⟩
  have hp : 0<test.top.densityKernel 203 z := Real.rpow_pos_of_pos
    (by linarith [test.top.radius_nonnegative z]) _
  exact hp.ne' (hz hmem)

theorem packet_sum_zero_of_density_zero
    (packets : Finset P.PacketIndex) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ)
    (hlength : ∀ q∈packets, P.length q.1≤tau)
    (hrow : ∀ q∈packets, P.rowSlope q.1 q.2.1∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (hdensity : ∀ q∈packets, P.ordinaryDensity 0 cell grid w tau E u q≤0)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) :
    (fun z => ∑ q∈packets, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
      selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z))
      =ᵐ[(volume.prod volume).restrict E] 0 := by
  have hq (q : packets) : ∀ᵐ z ∂(volume.prod volume).restrict E,
      ∀ k, selector q.val.1 q.val.2.1 k (u z)=0 :=
    ae_all_iff.mpr (fun k => P.selector_zero_of_density_zero cell grid w tau q.val
      (hlength q.val q.property) (hrow q.val q.property) E hE u hu
      (hdensity q.val q.property) (selector q.val.1 q.val.2.1) (hsupport _ _) k)
  filter_upwards [ae_all_iff.mpr hq] with z hz
  apply Finset.sum_eq_zero
  intro q hq
  apply WithLp.ofLp_injective
  funext k
  simp only [WithLp.ofLp_zero,Pi.zero_apply,hz ⟨q,hq⟩ k,mul_zero,zero_mul]

end LipschitzHilbert.PacketLatticeData

end

end OAI
