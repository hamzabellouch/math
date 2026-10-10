import OAI.Analysis.LipschitzHilbert.Trees.SourceCenteredSquareBound
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalSquareTail
import OAI.Analysis.LipschitzHilbert.Trees.SourceBadEventUnion

namespace OAI

/-! The actual symmetric frozen main coefficient has a single
polynomial exceptional threshold on every physical interval. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

 theorem physical_centered_square_tail (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (q J : ℝ) (hq : 0 ≤ q) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι),
      P.constant ≤ L^q →
    ∀ (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j, 0 ≤ d j) → Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j u k y) xi = 0) →
    ∀ (s t y u H : ℝ), 0 < H → (∀ j (_i : ι j), P.length j ≤ H) →
      Measurable (P.physicalCenteredSquare s t d v g y) ∧
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+6) ≤ |P.physicalCenteredSquare s t d v g y x|} ≤
          ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [physical_reference_square_tail hVariation hlo hhi q (J+1) hq (by linarith),
    eventually_source_polynomial_exp 3 0 J (by norm_num),
    eventually_ge_atTop (max 1 (4*Real.pi^2))] with L htail hdecay hlarge
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL : 0 < L := zero_lt_one.trans_le hL1
  simp only [Real.rpow_zero,mul_one] at hdecay
  intro N κ ι _ _ P hP d v hv g hg hg1 hd hmono hlow hhigh s t y u H hH hwidth
  obtain ⟨_hU,hU⟩ := htail N κ ι P hP (fun j => t+d j) v hv g hg hg1
    (centered_upper_monotone t hmono) hlow hhigh s y u H hH hwidth
  obtain ⟨_hD,hD⟩ := htail N κ ι P hP (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1
    (centered_lower_monotone t hmono) hlow hhigh s y u H hH hwidth
  obtain ⟨_hT,hT⟩ := htail N κ ι P hP (fun _ => 0) (fun _ => 0) measurable_const g hg hg1
    (fun _ _ _ => le_rfl) hlow hhigh s y u H hH hwidth
  have hthreshold : 4*(P.constant*Real.pi^2)*L^(q+4) ≤ L^(2*q+6) := by
    have hpi : 4*Real.pi^2 ≤ L := (le_max_right _ _).trans hlarge
    have hC : 0 ≤ P.constant := P.constant_pos.le
    calc
      _ = (4*Real.pi^2)*P.constant*L^(q+4) := by ring
      _ ≤ L*L^q*L^(q+4) := by gcongr
      _ = L^(2*q+5) := by
        calc
          _ = (L^(1:ℝ)*L^q)*L^(q+4) := by rw [Real.rpow_one]
          _ = L^(1+q+(q+4)) := by rw [← Real.rpow_add hL,← Real.rpow_add hL]
          _ = _ := by congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  let U := {x | L^(q+4) ≤ |P.physicalReferenceSquare s (fun j => t+d j) v hv g hg hg1 y x|}
  let D := {x | L^(q+4) ≤ |P.physicalReferenceSquare s (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1 y x|}
  let T := {x | L^(q+4) ≤ |P.physicalReferenceSquare s (fun _ => 0) (fun _ => 0) measurable_const g hg hg1 y x|}
  have hsub : {x | L^(2*q+6) ≤ |P.physicalCenteredSquare s t d v g y x|} ⊆ U∪D∪T := by
    intro x hx
    apply P.physicalCenteredSquare_bad_subset s t d hd v hv g hg hg1 y
      (L^(q+4)) (L^(2*q+6)) (Real.rpow_pos_of_pos hL _) hthreshold
    change L^(2*q+6) ≤ |P.physicalCenteredSquare s t d v g y x| at hx
    change L^(2*q+6) ≤ P.physicalCenteredSquare s t d v g y x
    simpa only [abs_of_nonneg (P.physicalCenteredSquare_nonneg s t d v g y x)] using hx
  let mu := volume.restrict (Ico u (u+H))
  have hunion : mu (U∪D∪T) ≤
      (ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal H+
        ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal H)+
        ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal H := by
    calc
      _ ≤ (mu U+mu D)+mu T :=
        (measure_union_le (U∪D) T).trans (add_le_add (measure_union_le U D) le_rfl)
      _ ≤ _ := add_le_add (add_le_add hU hD) hT
  refine ⟨(P.physicalCenteredSquare_continuous s t d v g y).measurable,?_⟩
  apply (measure_mono hsub).trans (hunion.trans ?_)
  calc
    _ = ENNReal.ofReal (3*Real.exp (-(J+1)*L))*ENNReal.ofReal H := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hdecay) le_rfl

end LipschitzHilbert.SourceLatticePacket

end

end OAI
