import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceLattice
import OAI.Analysis.LipschitzHilbert.Packets.UniformAnalyzedLine
import OAI.Analysis.LipschitzHilbert.Fourier.SquareLineConcentration
import OAI.Analysis.LipschitzHilbert.Estimates.PlanarHorizontalRescale

namespace OAI

/-! Reference-line packets are normalized at their actual horizontal
length before applying the published scalar variation input. The local
coefficient budget is independent of that length, the number of scales,
and the Hilbert dimension. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

def referencePlanarFamily : PlanarPacketFamily N κ ι :=
  P.family.horizontalRescale P.topLength P.topLength_pos

theorem family_derivative (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖deriv (P.family.wave j u k y) x‖ ≤ (P.family.constant/P.family.length j)*
      (lineEnvelope (P.family.centerX j u) (P.family.length j) 3 x*
        lineEnvelope (P.family.centerZ j u) P.width 2 y) := by
  apply (P.raw_derivative_bound 0 j u k y x).trans
  change _ ≤ (P.constant/P.length j)*_
  rw [P.family_centerX,P.family_centerZ]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg P.constant_pos.le (P.length_pos j).le)
  exact mul_le_mul (lineEnvelope_antitone _ _ _ P.order_ge_three)
    (lineEnvelope_antitone _ _ _ (Nat.le_trans (by decide : 2 ≤ 3) P.order_ge_three))
    (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem referencePlanarFamily_derivative (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖deriv (P.referencePlanarFamily.wave j u k y) x‖ ≤
      (P.referencePlanarFamily.constant/P.referencePlanarFamily.length j)*
        (lineEnvelope (P.referencePlanarFamily.centerX j u) (P.referencePlanarFamily.length j) 3 x*
          lineEnvelope (P.referencePlanarFamily.centerZ j u) P.width 2 y) := by
  change ‖deriv (schwartzDilation (P.family.wave j u k y) P.topLength P.topLength_pos.ne') x‖ ≤ _
  rw [schwartzDilation_deriv,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos P.topLength_pos]
  dsimp only [referencePlanarFamily]
  rw [PlanarPacketFamily.horizontalRescale_centerX,PlanarPacketFamily.horizontalRescale_length,
    PlanarPacketFamily.horizontalRescale_centerZ,
    lineEnvelope_horizontalDilation _ _ P.topLength _ _ P.topLength_pos.ne']
  have h := mul_le_mul_of_nonneg_left (P.family_derivative j u k y (P.topLength*x)) P.topLength_pos.le
  convert h using 1
  change (P.constant/(P.length j/P.topLength))*_ = _
  field_simp [(P.length_pos j).ne',P.topLength_pos.ne']
  change P.constant * _ * _ * P.length j = P.length j * _ * _ * P.constant
  ring

variable (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

def referenceAnalyzedLine (y : ℝ) : LinePacketFamily N κ ι :=
  P.referencePlanarFamily.analyzedLine d
    (fun z => v (z.1,P.topLength*z.2))
    (hv.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd)))
    (fun z => g (z.1,P.topLength*z.2))
    (hg.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd)))
    (fun _z => hg1 _) y (fun j u k x => P.referencePlanarFamily_derivative j u k y x)

@[simp] theorem referenceAnalyzedLine_coeff (y : ℝ) (j : Fin N) (u : ι j) :
    (P.referenceAnalyzedLine d v hv g hg hg1 y).coeff j u =
      (P.constant*Real.pi^2)⁻¹ • P.family.mainCoefficient d v g j u := by
  dsimp only [referenceAnalyzedLine,PlanarPacketFamily.analyzedLine]
  dsimp only [referencePlanarFamily]
  rw [PlanarPacketFamily.horizontalRescale_mainCoefficient]
  rfl

@[simp] theorem referenceAnalyzedLine_wave (y : ℝ) (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    (P.referenceAnalyzedLine d v hv g hg hg1 y).wave j u k x =
      P.raw 0 j u k y (P.topLength*x) := rfl

@[simp] theorem referenceAnalyzedLine_topLength (y : ℝ) :
    (P.referenceAnalyzedLine d v hv g hg hg1 y).topLength = 1 := by
  change P.topLength/P.topLength = 1
  exact div_self P.topLength_pos.ne'

variable {d v g}

theorem referencePlanarFamily_cutoffs {lo hi : ℝ}
    (hlow : ∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j u k y) xi = 0)
    (hhigh : ∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j u k y) xi = 0) :
    (∀ j u k y xi, |xi| < lo*(2:ℝ)^j.val → 𝓕 (P.referencePlanarFamily.wave j u k y) xi = 0) ∧
    (∀ j u k y xi, hi*(2:ℝ)^j.val < |xi| → 𝓕 (P.referencePlanarFamily.wave j u k y) xi = 0) := by
  constructor
  · intro j u k y xi hxi
    apply schwartzDilation_low (P.raw 0 j u k y) P.topLength (lo*(2:ℝ)^j.val) P.topLength_pos _ xi hxi
    intro eta heta
    apply hlow j u k y eta
    convert heta using 1
    ring
  · intro j u k y xi hxi
    apply schwartzDilation_high (P.raw 0 j u k y) P.topLength (hi*(2:ℝ)^j.val) P.topLength_pos _ xi hxi
    intro eta heta
    apply hhigh j u k y eta
    convert heta using 1
    ring

/-- The normalized analyzing coefficients have a single budget chosen
before the packet family, length and dimension. -/
theorem referenceAnalyzedLine_uniform_budget (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j u k y) xi = 0) →
      ∀ y, (P.referenceAnalyzedLine d v hv g hg hg1 y).HasLocalBudget (A/Real.pi^4) := by
  obtain ⟨A,hA,hbudget⟩ := PlanarPacketFamily.uniform_analyzedLine_localBudget hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P d v hv g hg hg1 hd hlow hhigh y
  obtain ⟨hl,hh⟩ := P.referencePlanarFamily_cutoffs hlow hhigh
  have h := hbudget N κ ι P.referencePlanarFamily d
    (fun z => v (z.1,P.topLength*z.2))
    (hv.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd)))
    (fun z => g (z.1,P.topLength*z.2))
    (hg.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd)))
    (fun _z => hg1 _) y (fun j u k x => P.referencePlanarFamily_derivative j u k y x) hd hl hh
  have heq : A*P.referencePlanarFamily.constant^2*P.referencePlanarFamily.coefficientScale⁻¹^2 =
      A/Real.pi^4 := by
    change A*P.constant^2*(P.constant*Real.pi^2)⁻¹^2 = _
    field_simp [P.constant_pos.ne',Real.pi_ne_zero]
  rw [heq] at h
  exact h

end LipschitzHilbert.SourceLatticePacket

end

end OAI
