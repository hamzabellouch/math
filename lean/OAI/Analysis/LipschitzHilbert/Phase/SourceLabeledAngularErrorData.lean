import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledRawEnvelope
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledErrorFamily
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalCoefficient

namespace OAI

/-! The labeled dyadic error family formed from the original physical
packets and selectors, with an exact measure-preserving coefficient identity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item) (horder : 6 ≤ P.order)
  (t a c Cwide M Lip radius : ℝ) (E J K H : ℕ)
  (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1)
  (hC : Cwide ≤ c*(2:ℝ)^J) (hwide : 1 ≤ Cwide*((2:ℝ)^E)^4)
  (hM : 0 ≤ M) (hLip : 0 ≤ Lip) (hradius : radius ≤ K)
  (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
    (fun l => t+P.rowSlope j l) (a*(2:ℝ)^j.val) H)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (hb : ∀ j l k, Measurable (b j l k))
  (hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
  (hsupport : ∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius*(a*(2:ℝ)^j.val))
  (hnear : ∀ j l k s, |s-t| ≤ c*(a*(2:ℝ)^j.val) →
    ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(a*(2:ℝ)^j.val)))
  (hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(a*(2:ℝ)^j.val) < |s-t| → b j l k s = 0)
  (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

def angularErrorFamily :
    LabeledAngularErrorFamily N (fun j => P.labels j) κ (fun j l => Item j l) where
  topLength := P.topLength
  width := P.width
  angleBase := a
  referenceSlope := t
  smallRatio := c
  wideConstant := Cwide
  exponent := E
  wideExponent := J
  packetBound := P.absoluteConstant
  multiplierBound := M
  multiplierLip := Lip
  radius := radius
  radiusBound := K
  multiplicity := H
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  angleBase_pos := ha
  smallRatio_pos := hc
  smallRatio_le := hc1
  wideConstant_le := hC
  wideRatio_ge := hwide
  packetBound_nonneg := P.absoluteConstant_pos.le
  multiplierBound_nonneg := hM
  multiplierLip_nonneg := hLip
  radius_le := hradius
  direction := fun z => v (slopeShear t z)
  direction_measurable := hv.comp (slopeShear t).measurable
  test := fun z => g (slopeShear t z)
  test_measurable := hg.comp (slopeShear t).measurable
  test_bound := fun _ => hg1 _
  originX := fun _ _ => 0
  originY := fun _ _ => 0
  slope := fun j l => t+P.rowSlope j l
  localMultiplicity := hlocal
  site := P.snappedSite
  site_injective := P.snappedSite_injective
  multiplier := b
  multiplier_measurable := hb
  multiplier_bounded := hbM
  multiplier_support := hsupport
  multiplier_near := hnear
  multiplier_far := hfar
  wave := fun j l u k z => P.raw 0 j l u k z.2 z.1
  wave_measurable := fun j l u k => P.raw_swapped_joint_measurable 0 j l u k
  wave_bound := by
    intro j l u k z
    simpa only [zero_add,length] using P.raw_absolute_tileEnvelope horder 0 j l u k z

def physicalAngularErrorCoefficient (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    (angularErrorWave (fun _ k => b j l k) (fun u k => P.physicalPacket t j l u k)
      v t (a*(2:ℝ)^j.val)) g u

theorem angularErrorFamily_coefficient (j : Fin N) (l : P.labels j) (u : Item j l) :
    (P.angularErrorFamily horder t a c Cwide M Lip radius E J K H ha hc hc1 hC hwide
      hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1).coefficient j l u =
      P.physicalAngularErrorCoefficient t a b v g j l u := by
  ext k
  simp only [LabeledAngularErrorFamily.coefficient,physicalAngularErrorCoefficient,analyzingCoefficient,
    WithLp.ofLp_toLp]
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g (slopeShear t z) k * conj
      (multiplierError (b j l k) t (a*(2:ℝ)^j.val) (v (slopeShear t z))*P.raw 0 j l u k z.2 z.1)
        ∂volume.prod volume) = _
  have hw (z : ℝ×ℝ) : P.raw 0 j l u k z.2 z.1 = P.physicalPacket t j l u k (slopeShear t z) := by
    have h := congrArg (fun f : SchwartzMap ℝ ℂ => f z.1)
      (P.raw_eq_physical_slice 0 j l u k z.2 t)
    exact h
  simp_rw [hw]
  congr 1
  exact (slopeShear_measurePreserving t).integral_comp (slopeShear t).measurableEmbedding
    (fun z => g z k * conj
      (multiplierError (b j l k) t (a*(2:ℝ)^j.val) (v z)*P.physicalPacket t j l u k z))

/-- The original positive error sum evaluated at a physical point. -/
def physicalAngularError (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  ∑ j, ∑ l : P.labels j, ∑ u : Item j l,
    ‖P.physicalAngularErrorCoefficient t a b v g j l u‖*
      tileEnvelope (P.length j*(P.snappedSite j l u).1)
        (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (z.1,z.2-t*z.1)

theorem angularErrorFamily_error (z : ℝ×ℝ) :
    (P.angularErrorFamily horder t a c Cwide M Lip radius E J K H ha hc hc1 hC hwide
      hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1).error z.2 z.1 =
      P.physicalAngularError t a b v g (slopeShear t z) := by
  unfold LabeledAngularErrorFamily.error LabeledAngularErrorFamily.scaleError physicalAngularError
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro u _
  rw [P.angularErrorFamily_coefficient horder t a c Cwide M Lip radius E J K H ha hc hc1
    hC hwide hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1]
  have hy : (slopeShear t z).2-t*(slopeShear t z).1 = z.2 := by
    change z.2+t*z.1-t*z.1 = z.2
    ring
  simp only [hy,angularErrorFamily,LabeledAngularErrorFamily.length,zero_add]
  rfl

theorem physicalAngularError_measurable (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    Measurable (P.physicalAngularError t a b v g) := by
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro l _
  apply Finset.measurable_sum
  intro u _
  apply measurable_const.mul
  exact (tileEnvelope_measurable _ _ _ _ _).comp
    (measurable_fst.prodMk (measurable_snd.sub (measurable_fst.const_mul t)))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
