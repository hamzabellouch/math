import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorEnvelope
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledCrossIdentity

namespace OAI

/-! A single length of original physical packets has a uniform positive
summation bound. Selector overlap is counted before convolution. The
analyzing coefficients remain those of the original profiles, while the
synthesis profiles may be any profiles with the same seminorm bound. -/

noncomputable section
open MeasureTheory
open Filter
open scoped BigOperators ComplexConjugate Topology
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- The shear changes coordinates, not the original analyzing coefficient. -/
theorem physicalMultiplierCoefficient_shear (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) :
    analyzingCoefficient volume (fun _ : Item j l => P.length j*P.width)
      (fun u k z => b j l k (v (slopeShear t z))*P.raw 0 j l u k z.2 z.1)
      (fun z => g (slopeShear t z)) u =
        P.physicalMultiplierCoefficient t b v g j l u := by
  ext k
  simp only [analyzingCoefficient,physicalMultiplierCoefficient,WithLp.ofLp_toLp]
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g (slopeShear t z) k*conj
      (b j l k (v (slopeShear t z))*P.raw 0 j l u k z.2 z.1)
        ∂volume.prod volume) = _
  have hw (z : ℝ×ℝ) : P.raw 0 j l u k z.2 z.1 =
      P.physicalPacket t j l u k (slopeShear t z) := by
    exact congrArg (fun f : SchwartzMap ℝ ℂ => f z.1)
      (P.raw_eq_physical_slice 0 j l u k z.2 t)
  simp_rw [hw]
  congr 1
  exact (slopeShear_measurePreserving t).integral_comp (slopeShear t).measurableEmbedding
    (fun z => g z k*conj (b j l k (v z)*P.physicalPacket t j l u k z))

/-- The positive coefficient sum has no factor for the total number of
labels. Only the selector's local multiplicity enters. -/
theorem physical_single_scale_coefficients (horder : 6 ≤ P.order)
    (j : Fin N) (t d radius M : ℝ) (K H : ℕ)
    (hd : 0 < d) (hM : 0 ≤ M) (hK : radius ≤ K)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d H)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ l k, Measurable (b j l k))
    (hbM : ∀ l k s, ‖b j l k s‖ ≤ M)
    (hsupport : ∀ l k s, b j l k s ≠ 0 →
      |s-(t+P.rowSlope j l)| ≤ radius*d)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y x : ℝ) :
    (∑ l : P.labels j, ∑ u : Item j l,
      ‖P.physicalMultiplierCoefficient t b v g j l u‖*
        tileEnvelope (P.length j*(P.snappedSite j l u).1)
          (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y)) ≤
      (64*(4*Real.pi)^2)*((P.absoluteConstant*M*((2*K+1)*H:ℕ))*Real.pi^2) := by
  have h := source_selector_single_scale (fun l : P.labels j => Item j l)
    (P.snappedSite j) (P.snappedSite_injective j) (fun _ => 0) (fun _ => 0)
    (fun l => t+P.rowSlope j l) (P.length_pos j) P.width_pos hd
    P.absoluteConstant_pos.le hM hlocal hK (b j) hb hbM hsupport
    (fun z => v (slopeShear t z)) (hv.comp (slopeShear t).measurable)
    (fun l u k z => P.raw 0 j l u k z.2 z.1)
    (fun l u k => P.raw_swapped_joint_measurable 0 j l u k)
    (by
      intro l u k z
      simpa only [zero_add] using P.raw_absolute_tileEnvelope horder 0 j l u k z)
    (fun z => g (slopeShear t z)) (hg.comp (slopeShear t).measurable)
    (fun z => hg1 (slopeShear t z)) (x,y)
  simpa only [zero_add,physicalMultiplierCoefficient_shear] using h

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

/-- Any selected packets at the given length, with alternate synthesis
and any of the three covariant jets, obey the same positive bound. -/
theorem physical_single_scale_raw_synthesis (horder : 6 ≤ P.order)
    (i : Fin 3) (j : Fin N) (t d radius M : ℝ) (K H : ℕ)
    (hd : 0 < d) (hM : 0 ≤ M) (hK : radius ≤ K)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d H)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ l k, Measurable (b j l k))
    (hbM : ∀ l k s, ‖b j l k s‖ ≤ M)
    (hsupport : ∀ l k s, b j l k s ≠ 0 →
      |s-(t+P.rowSlope j l)| ≤ radius*d)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (Q : Finset (Σ l : P.labels j, Item j l)) (y x : ℝ) :
    (∑ q ∈ Q, ‖(P.withProfile alt hAlt).rawPacketValue i j q.1 q.2
      (P.physicalMultiplierCoefficient t b v g j q.1 q.2) y x‖) ≤
      P.absoluteConstant*((64*(4*Real.pi)^2)*
        ((P.absoluteConstant*M*((2*K+1)*H:ℕ))*Real.pi^2)) := by
  classical
  calc
    _ ≤ ∑ q : (Σ l : P.labels j, Item j l),
        ‖(P.withProfile alt hAlt).rawPacketValue i j q.1 q.2
          (P.physicalMultiplierCoefficient t b v g j q.1 q.2) y x‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Q)
        (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ q : (Σ l : P.labels j, Item j l),
        P.absoluteConstant*(‖P.physicalMultiplierCoefficient t b v g j q.1 q.2‖*
          tileEnvelope (P.length j*(P.snappedSite j q.1 q.2).1)
            (P.width*(P.snappedSite j q.1 q.2).2) (P.length j) P.width 6 (x,y)) := by
      apply Finset.sum_le_sum
      intro q _
      exact (P.withProfile alt hAlt).raw_packet_value_norm horder i j q.1 q.2
        (P.physicalMultiplierCoefficient t b v g j q.1 q.2) y x
    _ = P.absoluteConstant*(∑ l : P.labels j, ∑ u : Item j l,
        ‖P.physicalMultiplierCoefficient t b v g j l u‖*
          tileEnvelope (P.length j*(P.snappedSite j l u).1)
            (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y)) := by
      rw [← Finset.mul_sum,Fintype.sum_sigma]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (P.physical_single_scale_coefficients horder j t d radius M K H hd hM hK hlocal
        b hb hbM hsupport v hv g hg hg1 y x) P.absoluteConstant_pos.le

/-- The same bound in the original physical coordinates, restricted to
any finite packet set at one length. -/
theorem physical_single_scale_cross_packets (horder : 6 ≤ P.order)
    (i : Fin 3) (j : Fin N) (t d radius M : ℝ) (K H : ℕ)
    (hd : 0 < d) (hM : 0 ≤ M) (hK : radius ≤ K)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d H)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ l k, Measurable (b j l k))
    (hbM : ∀ l k s, ‖b j l k s‖ ≤ M)
    (hsupport : ∀ l k s, b j l k s ≠ 0 →
      |s-(t+P.rowSlope j l)| ≤ radius*d)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (Q : Finset P.PacketIndex) (z : ℝ×ℝ) :
    (∑ q ∈ Q.filter (fun q => q.1 = j),
      ‖P.physicalCrossPacketValue alt hAlt t b v g i z q‖) ≤
      P.absoluteConstant*((64*(4*Real.pi)^2)*
        ((P.absoluteConstant*M*((2*K+1)*H:ℕ))*Real.pi^2)) := by
  classical
  calc
    _ ≤ ∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => q.1 = j),
        ‖P.physicalCrossPacketValue alt hAlt t b v g i z q‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset_filter _ (Finset.subset_univ Q)) (fun _ _ _ => norm_nonneg _)
    _ = ∑ u : (Σ l : P.labels j, Item j l),
        ‖P.physicalCrossPacketValue alt hAlt t b v g i z ⟨j,u⟩‖ := by
      rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
      · simp only [ite_true]
      · intro k _ hkj
        simp only [hkj,ite_false,Finset.sum_const_zero]
      · simp
    _ ≤ _ := P.physical_single_scale_raw_synthesis alt hAlt horder i j t d radius M K H
      hd hM hK hlocal b hb hbM hsupport v hv g hg hg1 Finset.univ (z.2-t*z.1) z.1

/-- Multiplying each synthesis packet by its actual top mask does not
enlarge the single-scale bound. -/
theorem physical_single_scale_masked_packets (horder : 6 ≤ P.order)
    (j : Fin N) (t d radius M : ℝ) (K H : ℕ)
    (hd : 0 < d) (hM : 0 ≤ M) (hK : radius ≤ K)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d H)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ l k, Measurable (b j l k))
    (hbM : ∀ l k s, ‖b j l k s‖ ≤ M)
    (hsupport : ∀ l k s, b j l k s ≠ 0 →
      |s-(t+P.rowSlope j l)| ≤ radius*d)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)
    (Q : Finset P.PacketIndex) (z : ℝ×ℝ) :
    (∑ q ∈ Q.filter (fun q => q.1 = j),
      ‖P.physicalMaskedValue alt hAlt t b v g T L A z q‖) ≤
      P.absoluteConstant*((64*(4*Real.pi)^2)*
        ((P.absoluteConstant*M*((2*K+1)*H:ℕ))*Real.pi^2)) := by
  apply le_trans (Finset.sum_le_sum ?_)
    (P.physical_single_scale_cross_packets alt hAlt horder 0 j t d radius M K H
      hd hM hK hlocal b hb hbM hsupport v hv g hg hg1 Q z)
  intro q _
  have heq := P.physicalMaskedValue_eq_cross alt hAlt t b v g T L A
    (z.2-t*z.1) z.1 q
  simp only [sub_add_cancel] at heq
  have hm0 : 0 ≤ (T q.1 q.2.1 q.2.2).mask L A (z.1,z.2) :=
    topSincMask_nonneg _ _ _ _
  have hm1 : (T q.1 q.2.1 q.2.2).mask L A (z.1,z.2) ≤ 1 :=
    topSincMask_le_one _ _ _ _
  rw [heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg hm0]
  exact mul_le_of_le_one_left (norm_nonneg _) hm1

/-- The fixed selector constants cost only one additional polynomial
power, uniformly before choosing the packet family. -/
theorem eventually_single_scale_budget (q M : ℝ) (hM : 0 ≤ M) (K H : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ C : ℝ, 0 ≤ C → C ≤ L^q →
      C*((64*(4*Real.pi)^2)*((C*M*((2*K+1)*H:ℕ))*Real.pi^2)) ≤ L^(2*q+1) := by
  let A : ℝ := (64*(4*Real.pi)^2)*M*((2*K+1)*H:ℕ)*Real.pi^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  filter_upwards [eventually_ge_atTop (max 1 A)] with L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hAL : A ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  intro C hC hCb
  calc
    _ = A*C^2 := by dsimp [A]; ring
    _ ≤ A*(L^q)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC hCb 2) hA
    _ ≤ L*(L^q)^2 := mul_le_mul_of_nonneg_right hAL (sq_nonneg _)
    _ = L^(2*q+1) := by
      rw [← Real.rpow_mul_natCast hL0.le]
      push_cast
      rw [Real.rpow_add hL0,Real.rpow_one]
      rw [mul_comm q 2]
      ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
