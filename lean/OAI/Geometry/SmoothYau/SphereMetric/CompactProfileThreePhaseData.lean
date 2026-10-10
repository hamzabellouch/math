import Mathlib
import OAI.Geometry.SmoothYau.Estimates.CriticalTransversePositive
import OAI.Geometry.SmoothYau.Estimates.RealPhaseLinear

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise
variable {T : Type*} [TopologicalSpace T]

theorem local_three_phase_data
    (H : T → RealForm PhaseSpace) (a ν : T → PhaseSpace)
    (hH : Continuous (fun s => phaseFormMatrix (H s)))
    (ha : Continuous a) (hν : Continuous ν)
    (hunit : ∀ s, ‖ν s‖ = 1) (halign : ∀ s, a s = ‖a s‖ • ν s)
    (t : T) (hsymm : (H t).IsSymm)
    (hnc : a t ≠ 0 → ∃ b, inner ℝ (a t) b = 0 ∧ ‖b‖^2 = 1 + ‖a t‖^2 ∧
      0 < H t (a t) (a t) + H t b b)
    (hcrit : a t = 0 → ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H t v v) :
    ∃ κ > 0, ∃ η > 0, ∃ C > 0, ∀ᶠ q : T × ℝ in 𝓝 (t, 0),
      ThreePhaseData (H q.1) (a q.1) (ν q.1) q.2 κ η C := by
  obtain ⟨b, c, hνb, hνc, hbn, hcn, hbg, hcg, hbc⟩ :=
    actual_two_transverse_phases (by simp) (H t) (a t) (ν t)
      (hunit t) (halign t) hnc hcrit
  have hbnpos : 0 < ‖b‖ := by nlinarith [norm_nonneg b, sq_nonneg ‖a t‖]
  have hcnpos : 0 < ‖c‖ := by nlinarith [norm_nonneg c, sq_nonneg ‖a t‖]
  let A : T × ℝ → PhaseSpace := fun q => a q.1
  let N : T × ℝ → PhaseSpace := fun q => ν q.1
  let A' : T × ℝ → PhaseSpace := fun q => a q.1 + q.2 • ν q.1
  let B : T × ℝ → PhaseSpace := fun q => normalizedTransverse (A q) (N q) b
  let D : T × ℝ → PhaseSpace := fun q => normalizedTransverse (A q) (N q) c
  let B' : T × ℝ → PhaseSpace := fun q => normalizedTransverse (A' q) (N q) b
  have hA : Continuous A := ha.comp continuous_fst
  have hN : Continuous N := hν.comp continuous_fst
  have hA' : Continuous A' := hA.add (continuous_snd.smul hN)
  have hbproj : transverseProjection (ν t) b ≠ 0 := by
    rw [transverseProjection_eq hνb]; exact norm_ne_zero_iff.mp hbnpos.ne'
  have hcproj : transverseProjection (ν t) c ≠ 0 := by
    rw [transverseProjection_eq hνc]; exact norm_ne_zero_iff.mp hcnpos.ne'
  have hB : ContinuousAt B (t, 0) := continuousAt_normalizedTransverse A N b (t, 0)
    hA.continuousAt hN.continuousAt hbproj
  have hD : ContinuousAt D (t, 0) := continuousAt_normalizedTransverse A N c (t, 0)
    hA.continuousAt hN.continuousAt hcproj
  have hB' : ContinuousAt B' (t, 0) := continuousAt_normalizedTransverse A' N b (t, 0)
    hA'.continuousAt hN.continuousAt hbproj
  have hB0 : B (t, 0) = b := normalizedTransverse_eq hνb hbn
  have hD0 : D (t, 0) = c := normalizedTransverse_eq hνc hcn
  have hA0 : A' (t, 0) = a t := by simp [A']
  have hB'0 : B' (t, 0) = b := by
    change normalizedTransverse (A' (t, 0)) (ν t) b = b
    rw [hA0]; exact hB0
  have hab : inner ℝ (a t) b = 0 := by
    rw [halign t, inner_smul_left, conj_trivial, hνb, mul_zero]
  have hac : inner ℝ (a t) c = 0 := by
    rw [halign t, inner_smul_left, conj_trivial, hνc, mul_zero]
  obtain ⟨Q₀, hs₀, hz₀, μ₀, hμ₀, hg₀⟩ := actual_complex_phase_matrix
    (H t) hsymm (a t) b hab (by simpa only [real_inner_self_eq_norm_sq] using hbn) hbg
  obtain ⟨Q₁, hs₁, hz₁, μ₁, hμ₁, hg₁⟩ := actual_complex_phase_matrix
    (H t) hsymm (a t) c hac (by simpa only [real_inner_self_eq_norm_sq] using hcn) hcg
  have hgap₀ : ∀ v : Fin 3 → ℝ, v ≠ 0 →
      0 < realQuadratic (phaseFormMatrix (H t) - Q₀.map Complex.re) v :=
    fun v hv => (mul_pos hμ₀ (squareSum_pos v hv)).trans_le (hg₀ v)
  have hgap₁ : ∀ v : Fin 3 → ℝ, v ≠ 0 →
      0 < realQuadratic (phaseFormMatrix (H t) - Q₁.map Complex.re) v :=
    fun v hv => (mul_pos hμ₁ (squareSum_pos v hv)).trans_le (hg₁ v)
  let HM : T × ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun q => phaseFormMatrix (H q.1)
  let Z₀ := fun q => complexPhaseVector (A q) (B q)
  let Z₁ := fun q => complexPhaseVector (A q) (D q)
  let Z₂ := fun q => complexPhaseVector (A' q) (B' q)
  have hHM : ContinuousAt HM (t, 0) := (hH.comp continuous_fst).continuousAt
  obtain ⟨κ₀, hk₀, C₀, hC₀, he₀⟩ := phase_matrix_continuation_at HM Z₀ (t, 0) hHM
    (complexPhaseVector_continuousAt A B _ hA.continuousAt hB) Q₀ hs₀
      (by simpa only [Z₀, hB0, A] using hz₀) hgap₀
  obtain ⟨κ₁, hk₁, C₁, hC₁, he₁⟩ := phase_matrix_continuation_at HM Z₁ (t, 0) hHM
    (complexPhaseVector_continuousAt A D _ hA.continuousAt hD) Q₁ hs₁
      (by simpa only [Z₁, hD0, A] using hz₁) hgap₁
  obtain ⟨κ₂, hk₂, C₂, hC₂, he₂⟩ := phase_matrix_continuation_at HM Z₂ (t, 0) hHM
    (complexPhaseVector_continuousAt A' B' _ hA'.continuousAt hB') Q₀ hs₀
      (by simpa only [Z₂, hA0, hB'0] using hz₀) hgap₀
  have hden : 0 < ‖b‖^2 * ‖c‖^2 := mul_pos (pow_pos hbnpos _) (pow_pos hcnpos _)
  have hang : 0 < transverseAngleSq b c := div_pos hbc hden
  have hangle : ContinuousAt (fun q => transverseAngleSq (B q) (D q)) (t, 0) := by
    apply ((hB.norm.pow 2).mul (hD.norm.pow 2)).sub ((hB.inner hD).pow 2) |>.div
      ((hB.norm.pow 2).mul (hD.norm.pow 2))
    change ‖B (t, 0)‖^2 * ‖D (t, 0)‖^2 ≠ 0
    rw [hB0, hD0]
    exact hden.ne'
  have hea : ∀ᶠ q in 𝓝 (t, 0), transverseAngleSq b c / 2 <
      transverseAngleSq (B q) (D q) := hangle.tendsto.eventually_const_lt (by
        rw [hB0, hD0]; linarith)
  have hep (v : PhaseSpace) (hv : transverseProjection (ν t) v ≠ 0) :
      ∀ᶠ q : T × ℝ in 𝓝 (t, 0), transverseProjection (N q) v ≠ 0 := by
    have hh : Continuous (fun q : T × ℝ => transverseProjection (N q) v) :=
      continuous_transverseProjection.comp (hN.prodMk continuous_const)
    have h := (hh.norm.tendsto (t, 0)).eventually_const_lt (norm_pos_iff.mpr hv)
    filter_upwards [h] with q hq using norm_pos_iff.mp hq
  refine ⟨min κ₀ (min κ₁ κ₂), lt_min hk₀ (lt_min hk₁ hk₂),
    transverseAngleSq b c / 2, by positivity, C₀ + C₁ + C₂, by positivity, ?_⟩
  filter_upwards [he₀, he₁, he₂, hea, hep b hbproj, hep c hcproj] with q h₀ h₁ h₂ hangle hbq hcq
  have hBq := normalizedTransverse_orthogonal (hunit q.1) (a q.1) b
  have hDq := normalizedTransverse_orthogonal (hunit q.1) (a q.1) c
  have hBqn := normalizedTransverse_norm_sq (a q.1) (ν q.1) b hbq
  have hDqn := normalizedTransverse_norm_sq (a q.1) (ν q.1) c hcq
  have hZ₀ := aligned_phase_square hBq (halign q.1) hBqn
  have hZ₁ := aligned_phase_square hDq (halign q.1) hDqn
  have hshift : shiftedPhaseImag (a q.1) (ν q.1) (B q) q.2 = B' q :=
    shiftedPhaseImag_eq_normalized (a q.1) (ν q.1) b q.2
  have hZ₂ := shifted_phase_square hBq (halign q.1) hBqn q.2
  rw [hshift] at hZ₂
  refine ⟨B q, D q, hBq, hDq, hBqn, hDqn, hangle.le, ?_, ?_, ?_⟩
  · refine ⟨continuedPhaseMatrix Q₀ (Z₀ q), ?_⟩
    exact (show PhaseMatrixValid (H q.1) (Z₀ q) κ₀ C₀ _ from
      ⟨h₀.1, h₀.2.1 hZ₀, h₀.2.2.1, h₀.2.2.2⟩).mono
      (min_le_left _ _) (by linarith)
  · refine ⟨continuedPhaseMatrix Q₁ (Z₁ q), ?_⟩
    exact (show PhaseMatrixValid (H q.1) (Z₁ q) κ₁ C₁ _ from
      ⟨h₁.1, h₁.2.1 hZ₁, h₁.2.2.1, h₁.2.2.2⟩).mono
      ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  · rw [hshift]
    refine ⟨continuedPhaseMatrix Q₀ (Z₂ q), ?_⟩
    exact (show PhaseMatrixValid (H q.1) (Z₂ q) κ₂ C₂ _ from
      ⟨h₂.1, h₂.2.1 hZ₂, h₂.2.2.1, h₂.2.2.2⟩).mono
      ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise

lemma finite_positive_common_lower {I : Type*} (s : Finset I) (c : I → ℝ)
    (hc : ∀ i ∈ s, 0 < c i) : ∃ d > 0, ∀ i ∈ s, d ≤ c i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨d, hd, hds⟩ := ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    refine ⟨min (c i) d, lt_min (hc i (Finset.mem_insert_self _ _)) hd, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hds j hj)

theorem uniform_three_phase_data {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (H : T → RealForm PhaseSpace) (a ν : T → PhaseSpace)
    (hH : Continuous (fun s => phaseFormMatrix (H s)))
    (ha : Continuous a) (hν : Continuous ν)
    (hunit : ∀ s, ‖ν s‖ = 1) (halign : ∀ s, a s = ‖a s‖ • ν s)
    (hsymm : ∀ t, (H t).IsSymm)
    (hnc : ∀ t, a t ≠ 0 → ∃ b, inner ℝ (a t) b = 0 ∧ ‖b‖^2 = 1 + ‖a t‖^2 ∧
      0 < H t (a t) (a t) + H t b b)
    (hcrit : ∀ t, a t = 0 → ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H t v v) :
    ∃ δ₀ > 0, ∃ κ > 0, ∃ η > 0, ∃ C > 0, ∀ t, ∀ δ ∈ Icc 0 δ₀,
      ThreePhaseData (H t) (a t) (ν t) δ κ η C := by
  classical
  have hlocal : ∀ t : T, ∃ κ > 0, ∃ η > 0, ∃ C > 0, ∃ U : Set T,
      IsOpen U ∧ t ∈ U ∧ ∃ ε > 0, ∀ s ∈ U, ∀ δ ∈ Icc 0 ε,
        ThreePhaseData (H s) (a s) (ν s) δ κ η C := by
    intro t
    obtain ⟨κ, hk, η, hη, C, hC, he⟩ := local_three_phase_data H a ν hH ha hν
      hunit halign t (hsymm t) (hnc t) (hcrit t)
    rw [nhds_prod_eq] at he
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp he
    obtain ⟨W, hWU, hW, htW⟩ := mem_nhds_iff.mp hU
    obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
    refine ⟨κ, hk, η, hη, C, hC, W, hW, htW, r / 2, by positivity, ?_⟩
    intro s hs δ hδ
    refine hUV (show (s, δ) ∈ U ×ˢ V from ?_)
    refine ⟨hWU hs, hrV ?_⟩
    change dist δ 0 < r
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hδ.1]
    linarith [hδ.2]
  choose κ hk η hη C hC U hU htU ε hε hlocal using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (by intro t _; exact mem_iUnion_of_mem t (htU t))
  obtain ⟨δ₀, hδ₀, hδε⟩ := finite_positive_common_lower s ε (fun t _ => hε t)
  obtain ⟨κ₀, hk₀, hκ⟩ := finite_positive_common_lower s κ (fun t _ => hk t)
  obtain ⟨η₀, hη₀, hηη⟩ := finite_positive_common_lower s η (fun t _ => hη t)
  let C₀ : ℝ := 1 + ∑ t ∈ s, C t
  have hC₀ : 0 < C₀ := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun t _ => (hC t).le)
  refine ⟨δ₀, hδ₀, κ₀, hk₀, η₀, hη₀, C₀, hC₀, ?_⟩
  intro t δ hδ
  obtain ⟨i, hi, hti⟩ := mem_iUnion₂.mp (hs (mem_univ t))
  have hci : C i ≤ C₀ := by
    have hh := Finset.single_le_sum (fun j _ => (hC j).le) hi
    dsimp [C₀]
    linarith
  exact (hlocal i t hti δ ⟨hδ.1, hδ.2.trans (hδε i hi)⟩).mono
    (hκ i hi) (hηη i hi) hci

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise

theorem compact_profile_three_phase_data {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : X → RealForm PhaseSpace) (a : X → PhaseSpace)
    (hH : Continuous (fun x => phaseFormMatrix (H x))) (ha : Continuous a)
    (hsymm : ∀ x, (H x).IsSymm)
    (hnc : ∀ x, a x ≠ 0 → ∃ b, inner ℝ (a x) b = 0 ∧ ‖b‖^2 = 1 + ‖a x‖^2 ∧
      0 < H x (a x) (a x) + H x b b)
    (hcrit : ∀ x, a x = 0 → ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H x v v) :
    ∃ δ₀ > 0, ∃ κ > 0, ∃ η > 0, ∃ C > 0, ∀ x ν,
      ‖ν‖ = 1 → a x = ‖a x‖ • ν → ∀ δ ∈ Icc 0 δ₀,
        ThreePhaseData (H x) (a x) ν δ κ η C := by
  let K : Set (X × PhaseSpace) := {p | ‖p.2‖ = 1 ∧ a p.1 = ‖a p.1‖ • p.2}
  have hcompact : IsCompact K := by
    have heq : K = (univ ×ˢ Metric.sphere (0 : PhaseSpace) 1) ∩
        {p | a p.1 = ‖a p.1‖ • p.2} := by
      ext p
      simp [K]
    rw [heq]
    exact (isCompact_univ.prod (isCompact_sphere 0 1)).inter_right
      (isClosed_eq (ha.comp continuous_fst)
        ((ha.comp continuous_fst).norm.smul continuous_snd))
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let partition : K → X := fun p => p.val.1
  let ν : K → PhaseSpace := fun p => p.val.2
  have hπ : Continuous partition := continuous_fst.comp continuous_subtype_val
  obtain ⟨δ₀, hδ₀, κ, hk, η, hη, C, hC, h⟩ := uniform_three_phase_data
    (fun p => H (partition p)) (fun p => a (partition p)) ν
    (hH.comp hπ) (ha.comp hπ) (continuous_snd.comp continuous_subtype_val)
    (fun p => p.property.1) (fun p => p.property.2)
    (fun p => hsymm (partition p)) (fun p => hnc (partition p)) (fun p => hcrit (partition p))
  refine ⟨δ₀, hδ₀, κ, hk, η, hη, C, hC, ?_⟩
  intro x v hv hav δ hδ
  exact h ⟨(x, v), hv, hav⟩ δ hδ



end YauCounterexamples
end

end OAI
