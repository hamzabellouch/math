import OAI.Analysis.LipschitzHilbert.Trees.SourceMixedReference
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceMask
import OAI.Analysis.LipschitzHilbert.Fourier.SincMaskedLine

namespace OAI

/-! The masked reference family synthesizes the original physical top
mask and alternate packet. Its analyzing coefficient is unchanged, so
the normalization is the original `constant * pi^2`, not its doubled
synthesis-envelope constant. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

theorem mixedReferenceLine_length (y : ℝ) (j : Fin N) :
    (P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).length j =
      P.length j/P.topLength := by
  change (P.topLength/P.topLength)/(2:ℝ)^j.val =
    (P.topLength/(2:ℝ)^j.val)/P.topLength
  ring

variable (T : ∀ j, ι j → SlopeBox) (L A t y : ℝ)

private theorem normalized_mask_rate
    (hrate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
      (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j) :
    ∀ j u (_k : κ), 2*(⌈L⌉₊:ℝ)*
      (|P.topLength*(T j u).maskLineA L A|+
       |P.topLength*(T j u).maskLineC L A t|) ≤
      1/(P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).length j := by
  intro j u k
  rw [abs_mul,abs_mul,abs_of_pos P.topLength_pos,
    P.mixedReferenceLine_length c hc alt hAlt d v hv g hg hg1]
  calc
    _ = P.topLength*(2*(⌈L⌉₊:ℝ)*
        (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|)) := by ring
    _ ≤ P.topLength*(1/P.length j) :=
      mul_le_mul_of_nonneg_left (hrate j u) P.topLength_pos.le
    _ = 1/(P.length j/P.topLength) := by simp [div_eq_mul_inv,mul_comm]

/-- The actual top mask is applied only to the synthesis wave. -/
def maskedMixedReferenceLine
    (hrate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
      (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j) :
    LinePacketFamily N κ ι :=
  (P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).sincMasked ⌈L⌉₊
    (fun j u _ => P.topLength*(T j u).maskLineA L A)
    (fun j u _ => (T j u).maskLineB L A)
    (fun j u _ => P.topLength*(T j u).maskLineC L A t)
    (fun j u _ => (T j u).maskLineD L A y)
    (P.normalized_mask_rate c hc alt hAlt d v hv g hg hg1 T L A t y hrate)

variable (hrate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
  (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j)

@[simp] theorem maskedMixedReferenceLine_coeff (j : Fin N) (u : ι j) :
    (P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y hrate).coeff j u =
      (P.constant*Real.pi^2)⁻¹ • (P.frozenProfile c hc).family.mainCoefficient d v g j u :=
  P.mixedReferenceLine_coeff c hc alt hAlt d v hv g hg hg1 y j u

@[simp] theorem maskedMixedReferenceLine_wave (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    (P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y hrate).wave j u k x =
      ((T j u).mask L A (P.topLength*x,y+t*(P.topLength*x)):ℂ)*
        (P.withProfile alt hAlt).raw 0 j u k y (P.topLength*x) := by
  rw [maskedMixedReferenceLine,LinePacketFamily.sincMasked_wave,
    P.mixedReferenceLine_wave,← (T j u).mask_on_scaled_reference_line]

theorem maskedMixedReferenceLine_budget_iff (B : ℝ) :
    (P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y hrate).HasLocalBudget B ↔
      ((P.frozenProfile c hc).referenceAnalyzedLine d v hv g hg hg1 y).HasLocalBudget B :=
  Iff.rfl

/-- The exact physical band, with the original analyzing coefficient,
the physical top mask, and the original alternate synthesis packet. -/
def maskedMixedReferenceBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ u : ι j,
    (P.frozenProfile c hc).family.mainCoefficient d v g j u k *
      ((T j u).mask L A (x,y+t*x):ℂ)*(P.withProfile alt hAlt).raw 0 j u k y x)

theorem maskedMixedReferenceLine_partial (x : ℝ) (n : ℕ) :
    hilbertPartialBandSum
      (P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y hrate).packets n x =
      (P.constant*Real.pi^2)⁻¹ • packetPartialSum
        (fun j => P.maskedMixedReferenceBand c hc alt hAlt d v g T L A t y j (P.topLength*x)) n := by
  ext k
  simp only [hilbertPartialBandSum,partialBandSum,packetPartialSum,
    LinePacketFamily.packets,packetSynthesis_apply,maskedMixedReferenceBand,
    WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < n
  · simp only [ite_eq_left hj]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [P.maskedMixedReferenceLine_coeff,P.maskedMixedReferenceLine_wave,PiLp.smul_apply]
    simp only [Complex.real_smul]
    ring
  · simp only [ite_eq_right hj,WithLp.ofLp_zero,Pi.zero_apply,smul_zero]

theorem maskedMixedReferenceBand_variation (x : ℝ) :
    cubicVariation (packetPartialSum
      (fun j => P.maskedMixedReferenceBand c hc alt hAlt d v g T L A t y j (P.topLength*x))) N =
      (P.constant*Real.pi^2)*
        (P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y hrate).variation x := by
  have hD : 0 < P.constant*Real.pi^2 := mul_pos P.constant_pos (pow_pos Real.pi_pos _)
  have heq : packetPartialSum (fun j =>
      P.maskedMixedReferenceBand c hc alt hAlt d v g T L A t y j (P.topLength*x)) =
      fun n => (P.constant*Real.pi^2) • hilbertPartialBandSum
        (P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y hrate).packets n x := by
    funext n
    rw [P.maskedMixedReferenceLine_partial c hc alt hAlt d v hv g hg hg1 T L A t y hrate x n,
      smul_smul,mul_inv_cancel₀ hD.ne',one_smul]
  rw [heq,LinePacketFamily.cubicVariation_smul_nonneg _ N _ hD.le]
  rfl

/-- In physical coordinates the frozen selector appears exactly once,
conjugated in the original analyzing coefficient. The synthesis packet
and its mask are the original physical ones. -/
theorem maskedMixedReferenceBand_physical (j : Fin N) (x : ℝ) :
    P.maskedMixedReferenceBand c hc alt hAlt d
      (fun z => v (sourceReferenceToPhysical t z))
      (fun z => g (sourceReferenceToPhysical t z)) T L A t y j x =
      WithLp.toLp 2 (fun k => ∑ u : ι j,
        (conj (c j u k)*P.physicalCoefficient t d v g j u k)*
          ((T j u).mask L A (x,y+t*x):ℂ)*
          (P.withProfile alt hAlt).physicalPacket t j u k (x,y+t*x)) := by
  ext k
  simp only [maskedMixedReferenceBand,WithLp.ofLp_toLp]
  apply Finset.sum_congr rfl
  intro u _
  rw [P.frozenProfile_mainCoefficient c hc,P.family_mainCoefficient_physical]
  have hraw := congrArg (fun f : SchwartzMap ℝ ℂ => f x)
    ((P.withProfile alt hAlt).raw_eq_physical_slice 0 j u k y t)
  change (P.withProfile alt hAlt).raw 0 j u k y x =
    (P.withProfile alt hAlt).physicalPacket t j u k (x,y+t*x) at hraw
  rw [hraw]

end LipschitzHilbert.SourceLatticePacket

end

end OAI
