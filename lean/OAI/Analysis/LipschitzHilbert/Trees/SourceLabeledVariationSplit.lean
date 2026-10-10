import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledMaskedSlots
import OAI.Analysis.LipschitzHilbert.Packets.VariationPacketL1

namespace OAI

/-! The fixed masked variation uses the full original analyzing
coefficients. Its centered main part has the narrow-slot variation
bound; its angular error is bounded by the positive physical error
sum, using the carrier-free synthesis envelope. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

def physicalMaskedBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ l : P.labels j, ∑ u : Item j l,
    P.physicalMultiplierCoefficient t b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))

def physicalErrorMaskedBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ l : P.labels j, ∑ u : Item j l,
    P.physicalAngularErrorCoefficient t a b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))

def physicalMaskedVariation (x : ℝ) : ℝ :=
  cubicVariation (packetPartialSum (fun j => P.physicalMaskedBand
    alt hAlt t b v g T L A y j x)) N

theorem physicalMaskedBand_physical_continuous (j : Fin N) :
    Continuous (fun z : ℝ×ℝ => P.physicalMaskedBand
      alt hAlt t b v g T L A (z.2-t*z.1) j z.1) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro l _
  apply continuous_finsetSum
  intro u _
  have hpoint : Continuous (fun z : ℝ×ℝ => (z.1,(z.2-t*z.1)+t*z.1)) := by fun_prop
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (((T j l u).mask_continuous L A).comp hpoint))).mul
    (((P.withProfile alt hAlt).physicalPacket t j l u k).continuous.comp hpoint)

theorem physicalMaskedVariation_physical_continuous :
    Continuous (fun z : ℝ×ℝ => P.physicalMaskedVariation
      alt hAlt t b v g T L A (z.2-t*z.1) z.1) := by
  apply continuous_cubicVariation _ _ N
  intro n
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using
      P.physicalMaskedBand_physical_continuous alt hAlt t b v g T L A j
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem physicalMaskedBand_split
    (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (x : ℝ) :
    P.physicalMaskedBand alt hAlt t b v g T L A y j x =
      P.physicalCenteredMaskedBand alt hAlt t a b v g T L A y j x+
        P.physicalErrorMaskedBand alt hAlt t a b v g T L A y j x := by
  ext k
  simp only [physicalMaskedBand,physicalCenteredMaskedBand,physicalErrorMaskedBand,
    WithLp.ofLp_toLp,PiLp.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [P.physicalMultiplierCoefficient_split t a b hb hb1 v hv g hg hg1]
  simp only [PiLp.add_apply]
  ring

private theorem masked_packet_norm (horder : 6 ≤ P.order)
    (j : Fin N) (l : P.labels j) (u : Item j l)
    (c : EuclideanSpace ℂ κ) (x : ℝ) :
    ‖WithLp.toLp 2 (fun k => c k*((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))‖ ≤
      P.absoluteConstant*(‖c‖*tileEnvelope
        (P.length j*(P.snappedSite j l u).1) (P.width*(P.snappedSite j l u).2)
        (P.length j) P.width 6 (x,y)) := by
  have heq : WithLp.toLp 2 (fun k => c k*((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x)) =
      (T j l u).mask L A (x,y+t*x) •
        (P.withProfile alt hAlt).rawPacketValue 0 j l u c y x := by
    ext k
    have hw := congrArg (fun f : SchwartzMap ℝ ℂ => f x)
      ((P.withProfile alt hAlt).raw_eq_physical_slice 0 j l u k y t)
    change (P.withProfile alt hAlt).raw 0 j l u k y x =
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x) at hw
    simp only [PiLp.smul_apply,rawPacketValue,Complex.real_smul]
    rw [hw]
    ring
  have hm0 : 0 ≤ (T j l u).mask L A (x,y+t*x) := topSincMask_nonneg _ _ _ _
  have hm1 : (T j l u).mask L A (x,y+t*x) ≤ 1 := topSincMask_le_one _ _ _ _
  rw [heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg hm0]
  exact (mul_le_of_le_one_left (norm_nonneg _) hm1).trans
    ((P.withProfile alt hAlt).raw_packet_value_norm horder 0 j l u c y x)

theorem physicalErrorMaskedBand_norm_le (horder : 6 ≤ P.order) (j : Fin N) (x : ℝ) :
    ‖P.physicalErrorMaskedBand alt hAlt t a b v g T L A y j x‖ ≤
      P.absoluteConstant*P.physicalErrorScale t a b v g j y x := by
  have heq : P.physicalErrorMaskedBand alt hAlt t a b v g T L A y j x =
      ∑ l : P.labels j, ∑ u : Item j l,
        WithLp.toLp 2 (fun k => P.physicalAngularErrorCoefficient t a b v g j l u k*
          ((T j l u).mask L A (x,y+t*x):ℂ)*
          (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x)) := by
    ext k
    simp only [physicalErrorMaskedBand,WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]
  rw [heq]
  calc
    _ ≤ ∑ l : P.labels j, ‖∑ u : Item j l,
        WithLp.toLp 2 (fun k => P.physicalAngularErrorCoefficient t a b v g j l u k*
          ((T j l u).mask L A (x,y+t*x):ℂ)*
          (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))‖ := norm_sum_le _ _
    _ ≤ ∑ l : P.labels j, ∑ u : Item j l,
        ‖WithLp.toLp 2 (fun k => P.physicalAngularErrorCoefficient t a b v g j l u k*
          ((T j l u).mask L A (x,y+t*x):ℂ)*
          (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))‖ :=
      Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ l : P.labels j, ∑ u : Item j l,
        P.absoluteConstant*(‖P.physicalAngularErrorCoefficient t a b v g j l u‖*
          tileEnvelope (P.length j*(P.snappedSite j l u).1)
            (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y)) :=
      Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun u _ =>
        P.masked_packet_norm alt hAlt t T L A y horder j l u _ x))
    _ = _ := by simp only [physicalErrorScale,Finset.mul_sum]

/-- The full original masked sequence has the narrow main variation
plus the single carrier-free positive angular-error sum. -/
theorem physicalMaskedVariation_le_main_add_error (horder : 6 ≤ P.order)
    (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1) (x : ℝ) :
    P.physicalMaskedVariation alt hAlt t b v g T L A y x ≤
      P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x+
        P.absoluteConstant*P.physicalAngularError t a b v g (x,y+t*x) := by
  have hp : packetPartialSum (fun j => P.physicalMaskedBand alt hAlt t b v g T L A y j x) =
      fun n => packetPartialSum (fun j => P.physicalCenteredMaskedBand
          alt hAlt t a b v g T L A y j x) n+
        packetPartialSum (fun j => P.physicalErrorMaskedBand alt hAlt t a b v g T L A y j x) n := by
    funext n
    unfold packetPartialSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · exact P.physicalMaskedBand_split alt hAlt t a b v g T L A y hb hb1 hv hg hg1 j x
    · simp
  unfold physicalMaskedVariation
  rw [hp]
  apply (cubicVariation_add_le _ _ _).trans
  apply add_le_add le_rfl
  apply (cubicVariation_packetPartialSum_le _).trans
  calc
    _ ≤ ∑ j, P.absoluteConstant*P.physicalErrorScale t a b v g j y x :=
      Finset.sum_le_sum (fun j _ => P.physicalErrorMaskedBand_norm_le
        alt hAlt t a b v g T L A y horder j x)
    _ = _ := by rw [← Finset.mul_sum,P.sum_physicalErrorScale]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
