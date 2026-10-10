import Mathlib

namespace OAI

/-! Branched sphere quotients and obstructions to holomorphic lifts. -/

noncomputable section
open Bundle Set Filter
open scoped Manifold Bundle Topology BoundedContinuousFunction

open scoped Topology
open Set Filter

namespace QuotientLift

structure SphereTangentSection where
  affine : ℂ → ℂ
  infinity : ℂ → ℂ
  affine_holomorphic : Differentiable ℂ affine
  infinity_holomorphic : Differentiable ℂ infinity
  overlap : ∀ z : ℂ, z ≠ 0 → infinity z⁻¹ = -(z⁻¹) ^ 2 * affine z

lemma twice_dslope_differentiable (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    Differentiable ℂ (dslope (dslope f 0) 0) := by
  rw [← differentiableOn_univ]
  apply (Complex.differentiableOn_dslope (Filter.univ_mem : (Set.univ : Set ℂ) ∈ 𝓝 0)).2
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hf.differentiableOn

theorem section_polynomial (s : SphereTangentSection) (z : ℂ) :
    s.affine z = s.affine 0 +
      (s.affine 1 - s.affine 0 + s.infinity 0) * z - s.infinity 0 * z ^ 2 := by
  let u := dslope (dslope s.affine 0) 0
  let b := dslope s.affine 0 0
  have hrec (w : ℂ) :
      w ^ 2 * u w = s.affine w - s.affine 0 - b * w := by
    have h₁ := sub_smul_dslope s.affine 0 w
    have h₂ := sub_smul_dslope (dslope s.affine 0) 0 w
    simp only [sub_zero, smul_eq_mul] at h₁ h₂
    dsimp only [u, b]
    linear_combination w * h₂ + h₁
  have hu (w : ℂ) (hw : w ≠ 0) :
      u w = -s.infinity w⁻¹ - s.affine 0 * (w⁻¹) ^ 2 - b * w⁻¹ := by
    have ho := s.overlap w hw
    have hr := hrec w
    field_simp at ho ⊢
    linear_combination hr + ho
  have hinv : Tendsto (fun w : ℂ => w⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [← Metric.cobounded_eq_cocompact] using
      (Filter.tendsto_inv₀_cobounded : Tendsto (fun w : ℂ => w⁻¹)
        (Bornology.cobounded ℂ) (𝓝 0))
  have hlim : Tendsto u (cocompact ℂ) (𝓝 (-s.infinity 0)) := by
    have h := ((s.infinity_holomorphic.continuous.continuousAt.tendsto.comp hinv).neg.sub
      ((tendsto_const_nhds (x := s.affine 0)).mul (hinv.pow 2))).sub
        ((tendsto_const_nhds (x := b)).mul hinv)
    have hevent : u =ᶠ[cocompact ℂ]
        (fun w => -s.infinity w⁻¹ - s.affine 0 * (w⁻¹) ^ 2 - b * w⁻¹) := by
      filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with w hw
      exact hu w hw
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, sub_zero] using
      h.congr' hevent.symm
  have huconst (w : ℂ) : u w = -s.infinity 0 :=
    (twice_dslope_differentiable s.affine s.affine_holomorphic).apply_eq_of_tendsto_cocompact
      w hlim
  have hz := hrec z
  have h₁ := hrec 1
  rw [huconst] at hz h₁
  norm_num at h₁
  linear_combination -hz + z * h₁

theorem invariant_section_zero (s : SphereTangentSection)
    (hsign : ∀ z : ℂ, s.affine (-z) = -s.affine z)
    (hinversion : s.infinity = s.affine) :
    (∀ z, s.affine z = 0) ∧ (∀ z, s.infinity z = 0) := by
  have h0 : s.affine 0 = 0 := by
    have h := hsign 0
    simp only [neg_zero] at h
    linear_combination (1 / 2 : ℂ) * h
  have hi0 : s.infinity 0 = 0 := by rw [hinversion, h0]
  have h1 : s.affine 1 = 0 := by
    have h := s.overlap 1 one_ne_zero
    rw [hinversion] at h
    norm_num at h
    linear_combination (1 / 2 : ℂ) * h
  have hall (z : ℂ) : s.affine z = 0 := by
    rw [section_polynomial, h0, hi0, h1]
    ring
  exact ⟨hall, fun z => by rw [hinversion, hall]⟩

def quotientCoordinate (z : ℂ) : ℂ := z ^ 2 + z⁻¹ ^ 2

theorem quotient_fibers {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    quotientCoordinate z = quotientCoordinate w ↔
      w = z ∨ w = -z ∨ w = z⁻¹ ∨ w = -z⁻¹ := by
  constructor
  · intro h
    dsimp only [quotientCoordinate] at h
    have hmul : (w ^ 2 - z ^ 2) * (w ^ 2 - z⁻¹ ^ 2) = 0 := by
      field_simp [hz, hw] at h ⊢
      linear_combination -h
    have hfact : (w - z) * (w + z) * (w - z⁻¹) * (w + z⁻¹) = 0 := by
      linear_combination hmul
    simpa only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg, or_assoc] using hfact
  · rintro (rfl | rfl | rfl | rfl) <;> simp [quotientCoordinate, add_comm]

theorem quotient_surjective_finite (t : ℂ) :
    ∃ z : ℂ, z ≠ 0 ∧ quotientCoordinate z = t := by
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (t ^ 2 - 4) (by norm_num : 0 < (2 : ℕ))
  let u := (t + v) / 2
  have hu : u ^ 2 - t * u + 1 = 0 := by
    dsimp only [u]
    linear_combination (1 / 4 : ℂ) * hv
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    norm_num at hu
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq u (by norm_num : 0 < (2 : ℕ))
  have hz0 : z ≠ 0 := by
    intro h
    apply hu0
    rw [h] at hz
    simpa using hz.symm
  refine ⟨z, hz0, ?_⟩
  rw [← hz] at hu
  dsimp only [quotientCoordinate]
  field_simp [hz0]
  linear_combination hu

theorem no_anticanonical_lift :
    ¬ ∃ v : ℂ → ℂ, ∀ z : ℂ, z ≠ 0 → deriv quotientCoordinate z * v z = 1 := by
  have hd : HasDerivAt quotientCoordinate 0 1 := by
    have h₁ : HasDerivAt (fun z : ℂ => z ^ 2) (2 : ℂ) 1 := by
      simpa using! (hasDerivAt_id (1 : ℂ)).pow 2
    have h₂ : HasDerivAt (fun z : ℂ => (z⁻¹) ^ 2) (-2 : ℂ) 1 := by
      simpa using! ((hasDerivAt_id (1 : ℂ)).inv one_ne_zero).pow 2
    simpa only [quotientCoordinate, add_neg_cancel] using! h₁.add h₂
  rintro ⟨v, hv⟩
  have h := hv 1 one_ne_zero
  rw [hd.deriv, zero_mul] at h
  exact zero_ne_one h

 
def constantAffineSection : SphereTangentSection where
  affine := fun _ => 1
  infinity := fun w => -w ^ 2
  affine_holomorphic := by fun_prop
  infinity_holomorphic := by fun_prop
  overlap := by intro z hz; simp

theorem downstairs_nonzero : constantAffineSection.affine 0 ≠ 0 := by
  exact one_ne_zero

 
def signSection (s : SphereTangentSection) : SphereTangentSection := by
  refine ⟨fun z => -s.affine (-z), fun w => -s.infinity (-w), ?_, ?_, ?_⟩
  · exact (s.affine_holomorphic.comp differentiable_neg).neg
  · exact (s.infinity_holomorphic.comp differentiable_neg).neg
  · intro z hz
    have h := s.overlap (-z) (neg_ne_zero.mpr hz)
    simpa using congrArg Neg.neg h

def inversionSection (s : SphereTangentSection) : SphereTangentSection := by
  refine ⟨s.infinity, s.affine, s.infinity_holomorphic, s.affine_holomorphic, ?_⟩
  intro z hz
  have h := s.overlap z⁻¹ (inv_ne_zero hz)
  simp only [inv_inv] at h
  field_simp [hz] at h ⊢
  linear_combination h

 
def coefficients (s : SphereTangentSection) : Fin 3 → ℂ :=
  ![s.affine 0, s.affine 1 - s.affine 0 + s.infinity 0, -s.infinity 0]

 
def sectionHermitian (s t : SphereTangentSection) : ℂ :=
  ∑ i, star (coefficients s i) * coefficients t i

theorem coefficients_injective : Function.Injective coefficients := by
  intro s t h
  have h0 : s.affine 0 = t.affine 0 := by
    simpa [coefficients] using congrFun h 0
  have hi0 : s.infinity 0 = t.infinity 0 := by
    simpa [coefficients] using congrFun h 2
  have h1 : s.affine 1 = t.affine 1 := by
    have hb := congrFun h 1
    simp only [coefficients, Matrix.cons_val_one, Matrix.cons_val_zero] at hb
    linear_combination hb + h0 - hi0
  have ha : s.affine = t.affine := by
    funext z
    rw [section_polynomial s, section_polynomial t, h0, h1, hi0]
  have hi : s.infinity = t.infinity := by
    funext z
    by_cases hz : z = 0
    · simpa only [hz] using hi0
    · have hs := s.overlap z⁻¹ (inv_ne_zero hz)
      have ht := t.overlap z⁻¹ (inv_ne_zero hz)
      simp only [inv_inv] at hs ht
      rw [ha] at hs
      exact hs.trans ht.symm
  cases s
  cases t
  cases ha
  cases hi
  rfl

lemma sign_coefficients (s : SphereTangentSection) :
    coefficients (signSection s) =
      ![-coefficients s 0, coefficients s 1, -coefficients s 2] := by
  ext i
  fin_cases i
  · simp [coefficients, signSection]
  · dsimp [coefficients, signSection]
    rw [section_polynomial s (-1)]
    ring_nf
  · simp [coefficients, signSection]

lemma inversion_coefficients (s : SphereTangentSection) :
    coefficients (inversionSection s) =
      ![-coefficients s 2, -coefficients s 1, -coefficients s 0] := by
  have h := s.overlap 1 one_ne_zero
  norm_num at h
  ext i
  fin_cases i
  · simp [coefficients, inversionSection]
  · dsimp [coefficients, inversionSection]
    rw [h]
    ring
  · simp [coefficients, inversionSection]

theorem sign_preserves_Hermitian (s t : SphereTangentSection) :
    sectionHermitian (signSection s) (signSection t) = sectionHermitian s t := by
  unfold sectionHermitian
  rw [sign_coefficients, sign_coefficients]
  simp [Fin.sum_univ_succ]

theorem inversion_preserves_Hermitian (s t : SphereTangentSection) :
    sectionHermitian (inversionSection s) (inversionSection t) = sectionHermitian s t := by
  unfold sectionHermitian
  rw [inversion_coefficients, inversion_coefficients]
  simp [Fin.sum_univ_succ]
  ring

open scoped OnePoint Manifold

abbrev Sphere := OnePoint ℂ

local instance branchedSphereDecidableEq : DecidableEq Sphere := Classical.decEq Sphere

def inversionPoint : Sphere → Sphere
  | ∞ => (0 : ℂ)
  | (z : ℂ) => if z = 0 then ∞ else (z⁻¹ : ℂ)

theorem inversionPoint_involutive : Function.Involutive inversionPoint := by
  intro x
  cases x using OnePoint.rec with
  | infty => simp [inversionPoint]
  | coe z =>
    by_cases hz : z = 0
    · simp [hz, inversionPoint]
    · simp [inversionPoint, hz, inv_ne_zero hz]

theorem inversionPoint_continuous : Continuous inversionPoint := by
  apply (OnePoint.continuous_iff inversionPoint).mpr
  constructor
  · rw [Filter.coclosedCompact_eq_cocompact]
    have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
      simpa only [← Metric.cobounded_eq_cocompact] using
        (Filter.tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹)
          (Bornology.cobounded ℂ) (𝓝 0))
    have h := (OnePoint.continuous_coe.continuousAt (x := (0 : ℂ))).tendsto.comp hinv
    apply h.congr'
    filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
    have hz0 : z ≠ 0 := hz
    simp [inversionPoint, hz0]
  · apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z
      rw [continuousAt_iff_punctured_nhds]
      have hinv : Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] 0) (coclosedCompact ℂ) := by
        simpa only [Filter.coclosedCompact_eq_cocompact,
          ← Metric.cobounded_eq_cocompact] using
          (Filter.tendsto_inv₀_nhdsNE_zero : Tendsto (fun z : ℂ => z⁻¹)
            (𝓝[≠] 0) (Bornology.cobounded ℂ))
      have h := (OnePoint.tendsto_coe_infty (X := ℂ)).comp hinv
      simpa [inversionPoint] using h.congr'
        (show (fun z : ℂ => ((z⁻¹ : ℂ) : Sphere)) =ᶠ[𝓝[≠] 0]
          (fun z : ℂ => inversionPoint (z : Sphere)) from by
          filter_upwards [self_mem_nhdsWithin] with z hz
          have hz0 : z ≠ 0 := hz
          simp [inversionPoint, hz0])
    · have h := OnePoint.continuous_coe.continuousAt.comp (continuousAt_id.inv₀ hz)
      change Tendsto (fun w : ℂ => inversionPoint (w : Sphere)) (𝓝 z)
        (𝓝 (inversionPoint (z : Sphere)))
      simp only [inversionPoint, ite_eq_right hz]
      apply h.tendsto.congr'
      filter_upwards [eventually_ne_nhds hz] with w hw
      simp [hw]

def inversionHomeomorph : Sphere ≃ₜ Sphere where
  toFun := inversionPoint
  invFun := inversionPoint
  left_inv := inversionPoint_involutive
  right_inv := inversionPoint_involutive
  continuous_toFun := inversionPoint_continuous
  continuous_invFun := inversionPoint_continuous

@[simp] lemma inversionHomeomorph_apply (x : Sphere) :
    inversionHomeomorph x = inversionPoint x := rfl

def affineChart : OpenPartialHomeomorph Sphere ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : ℂ → Sphere)).symm

def infinityChart : OpenPartialHomeomorph Sphere ℂ :=
  inversionHomeomorph.toOpenPartialHomeomorph.trans affineChart

@[simp] lemma affineChart_source : affineChart.source = {∞}ᶜ := by
  simp [affineChart, OnePoint.compl_infty]

@[simp] lemma affineChart_target : affineChart.target = Set.univ := by
  simp [affineChart]

@[simp] lemma affineChart_coe (z : ℂ) : affineChart (z : Sphere) = z :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv _

@[simp] lemma affineChart_symm (z : ℂ) : affineChart.symm z = (z : Sphere) := by
  simp [affineChart]

instance sphereChartedSpace : ChartedSpace ℂ Sphere where
  atlas := {affineChart, infinityChart}
  chartAt := fun x => if x = ∞ then infinityChart else affineChart
  mem_chart_source := by
    intro x
    by_cases hx : x = ∞
    · subst x
      simp [infinityChart, inversionPoint]
    · simp [hx]
  chart_mem_atlas := by
    intro x
    split_ifs <;> simp

@[simp] lemma infinityChart_source (x : Sphere) :
    x ∈ infinityChart.source ↔ x ≠ (0 : ℂ) := by
  cases x using OnePoint.rec with
  | infty => simp [infinityChart, inversionPoint]
  | coe z =>
    by_cases hz : z = 0
    · simp [hz, infinityChart, inversionPoint]
    · simp [hz, infinityChart, inversionPoint]

@[simp] lemma infinityChart_target : infinityChart.target = Set.univ := by
  simp [infinityChart]

@[simp] lemma infinityChart_symm (z : ℂ) :
    infinityChart.symm z = inversionPoint (z : Sphere) := by
  change inversionPoint (affineChart.symm z) = _
  rw [affineChart_symm]

@[simp] lemma infinityChart_coe {z : ℂ} (hz : z ≠ 0) :
    infinityChart (z : Sphere) = z⁻¹ := by
  change affineChart (inversionPoint (z : Sphere)) = _
  simp [inversionPoint, hz]

@[simp] lemma infinityChart_infty : infinityChart ∞ = 0 := by
  change affineChart (inversionPoint ∞) = _
  simp [inversionPoint]

lemma chart_self_contDiff (e : OpenPartialHomeomorph Sphere ℂ) :
    ContDiffOn ℂ (⊤ : WithTop ℕ∞) (e.symm.trans e) (e.symm.trans e).source := by
  apply contDiffOn_id.congr
  intro z hz
  exact e.right_inv hz.1

lemma affine_infinity_contDiff :
    ContDiffOn ℂ (⊤ : WithTop ℕ∞) (affineChart.symm.trans infinityChart)
      (affineChart.symm.trans infinityChart).source := by
  have hs : (affineChart.symm.trans infinityChart).source = {0}ᶜ := by
    ext z
    simp
  rw [hs]
  apply (contDiffOn_inv ℂ).congr
  intro z hz
  simpa only [OpenPartialHomeomorph.trans_apply, affineChart_symm] using
    infinityChart_coe hz

lemma infinity_affine_contDiff :
    ContDiffOn ℂ (⊤ : WithTop ℕ∞) (infinityChart.symm.trans affineChart)
      (infinityChart.symm.trans affineChart).source := by
  have hs : (infinityChart.symm.trans affineChart).source = {0}ᶜ := by
    ext z
    by_cases hz : z = 0
    · simp [hz, inversionPoint]
    · simp [hz, inversionPoint]
  rw [hs]
  apply (contDiffOn_inv ℂ).congr
  intro z hz
  have hz0 : z ≠ 0 := hz
  simp [OpenPartialHomeomorph.trans_apply, inversionPoint, hz0]

theorem sphere_is_complex_manifold : IsManifold 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) Sphere := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have h : ContDiffOn ℂ (⊤ : WithTop ℕ∞) (e.symm.trans e') (e.symm.trans e').source := by
    change e ∈ ({affineChart, infinityChart} : Set _) at he
    change e' ∈ ({affineChart, infinityChart} : Set _) at he'
    simp only [mem_insert_iff, mem_singleton_iff] at he he'
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl
    · exact chart_self_contDiff _
    · exact affine_infinity_contDiff
    · exact infinity_affine_contDiff
    · exact chart_self_contDiff _
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id, range_id, inter_univ] using h

def signPoint : Sphere → Sphere := OnePoint.map (fun z : ℂ => -z)

def quotientPoint : Sphere → Sphere
  | ∞ => ∞
  | (z : ℂ) => if z = 0 then ∞ else (quotientCoordinate z : ℂ)

theorem quotientPoint_fibers (z w : Sphere) :
    quotientPoint z = quotientPoint w ↔
      w = z ∨ w = signPoint z ∨ w = inversionPoint z ∨ w = signPoint (inversionPoint z) := by
  cases z using OnePoint.rec with
  | infty =>
    cases w using OnePoint.rec with
    | infty => simp [quotientPoint]
    | coe w =>
      by_cases hw : w = 0
      · simp [hw, quotientPoint, signPoint, inversionPoint]
      · simp [hw, quotientPoint, signPoint, inversionPoint]
  | coe z =>
    cases w using OnePoint.rec with
    | infty =>
      by_cases hz : z = 0
      · simp [hz, quotientPoint, signPoint, inversionPoint]
      · simp [hz, quotientPoint, signPoint, inversionPoint]
    | coe w =>
      by_cases hz : z = 0
      · simp [hz, quotientPoint, signPoint, inversionPoint]
      · by_cases hw : w = 0
        · simp [hw, hz, quotientPoint, signPoint, inversionPoint, inv_ne_zero hz, Ne.symm hz]
        · simpa [hz, hw, quotientPoint, signPoint, inversionPoint] using quotient_fibers hz hw

theorem quotientPoint_surjective : Function.Surjective quotientPoint := by
  intro t
  cases t using OnePoint.rec with
  | infty => exact ⟨∞, rfl⟩
  | coe t =>
    obtain ⟨z, hz, hq⟩ := quotient_surjective_finite t
    exact ⟨(z : Sphere), by simp [quotientPoint, hz, hq]⟩

theorem sphere_compact_connected : CompactSpace Sphere ∧ ConnectedSpace Sphere ∧ T2Space Sphere :=
  ⟨inferInstance, inferInstance, inferInstance⟩

lemma quotientPoint_inversion (x : Sphere) : quotientPoint (inversionPoint x) = quotientPoint x := by
  cases x using OnePoint.rec with
  | infty => simp [inversionPoint, quotientPoint]
  | coe z =>
    by_cases hz : z = 0
    · simp [hz, inversionPoint, quotientPoint]
    · simp [inversionPoint, quotientPoint, hz, inv_ne_zero hz, quotientCoordinate, add_comm]

def reciprocalQuotientCoordinate (z : ℂ) : ℂ := z ^ 2 / (1 + z ^ 4)

lemma quotientPoint_reciprocal {z : ℂ} (hd : 1 + z ^ 4 ≠ 0) :
    quotientPoint (z : Sphere) = inversionPoint (reciprocalQuotientCoordinate z : ℂ) := by
  by_cases hz : z = 0
  · simp [hz, quotientPoint, reciprocalQuotientCoordinate, inversionPoint]
  · have hr : reciprocalQuotientCoordinate z ≠ 0 := div_ne_zero (pow_ne_zero _ hz) hd
    simp only [quotientPoint, ite_eq_right hz, inversionPoint, ite_eq_right hr,
      OnePoint.coe_injective.eq_iff]
    unfold reciprocalQuotientCoordinate quotientCoordinate
    field_simp [hz, hd]
    ring

lemma reciprocalQuotientCoordinate_contDiffAt :
    ContDiffAt ℂ (⊤ : WithTop ℕ∞) reciprocalQuotientCoordinate 0 := by
  unfold reciprocalQuotientCoordinate
  exact (contDiffAt_id.pow 2).div (contDiffAt_const.add (contDiffAt_id.pow 4)) (by norm_num)

lemma denominator_near_zero : ∀ᶠ z : ℂ in 𝓝 0, 1 + z ^ 4 ≠ 0 :=
  (continuousAt_const.add (continuousAt_id.pow 4)).eventually_ne (by norm_num)

lemma quotientPoint_coe_continuous : Continuous (fun z : ℂ => quotientPoint (z : Sphere)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    have h := inversionPoint_continuous.continuousAt.comp
      (OnePoint.continuous_coe.continuousAt.comp
        reciprocalQuotientCoordinate_contDiffAt.continuousAt)
    apply h.congr_of_eventuallyEq
    filter_upwards [denominator_near_zero] with w hw
    exact quotientPoint_reciprocal hw
  · have hq : ContinuousAt quotientCoordinate z :=
      (continuousAt_id.pow 2).add ((continuousAt_id.inv₀ hz).pow 2)
    have h := OnePoint.continuous_coe.continuousAt.comp hq
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with w hw
    simp [quotientPoint, hw]

theorem quotientPoint_continuous : Continuous quotientPoint := by
  apply continuous_iff_continuousAt.mpr
  intro x
  cases x using OnePoint.rec with
  | coe z => exact (OnePoint.continuousAt_coe.mpr (quotientPoint_coe_continuous.continuousAt))
  | infty =>
    have h0 : ContinuousAt quotientPoint ((0 : ℂ) : Sphere) :=
      OnePoint.continuousAt_coe.mpr (quotientPoint_coe_continuous.continuousAt)
    have h := ContinuousAt.comp (f := inversionPoint) (g := quotientPoint)
      (x := (∞ : Sphere)) h0 inversionPoint_continuous.continuousAt
    simpa only [Function.comp_def, quotientPoint_inversion] using h

theorem quotientPoint_isQuotientMap : Topology.IsQuotientMap quotientPoint :=
  .of_surjective_continuous quotientPoint_surjective quotientPoint_continuous

@[simp] lemma sphere_chartAt_infty : chartAt ℂ (∞ : Sphere) = infinityChart := by
  change (if (∞ : Sphere) = ∞ then infinityChart else affineChart) = _
  simp

@[simp] lemma sphere_chartAt_coe (z : ℂ) : chartAt ℂ (z : Sphere) = affineChart := by
  change (if (z : Sphere) = ∞ then infinityChart else affineChart) = _
  simp

@[simp] lemma infinityChart_inversion_coe (z : ℂ) :
    infinityChart (inversionPoint (z : Sphere)) = z := by
  change affineChart (inversionPoint (inversionPoint (z : Sphere))) = z
  rw [inversionPoint_involutive]
  simp

lemma sphere_analyticAt_of_chart (f : Sphere → Sphere) (x : Sphere)
    (hf : ContinuousAt f x)
    (hc : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (chartAt ℂ (f x) ∘ f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f x := by
  rw [contMDiffAt_iff]
  refine ⟨hf, ?_⟩
  simpa only [extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Set.range_id, contDiffWithinAt_univ] using hc

theorem quotientPoint_analytic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) quotientPoint := by
  intro x
  apply sphere_analyticAt_of_chart _ _ quotientPoint_continuous.continuousAt
  cases x using OnePoint.rec with
  | infty =>
    simp only [quotientPoint, sphere_chartAt_infty, infinityChart_infty]
    apply reciprocalQuotientCoordinate_contDiffAt.congr_of_eventuallyEq
    filter_upwards [denominator_near_zero] with z hz
    simp only [Function.comp_apply, infinityChart_symm, quotientPoint_inversion,
      quotientPoint_reciprocal hz, infinityChart_inversion_coe]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp only [quotientPoint, ite_true, sphere_chartAt_infty, sphere_chartAt_coe,
        affineChart_coe]
      apply reciprocalQuotientCoordinate_contDiffAt.congr_of_eventuallyEq
      filter_upwards [denominator_near_zero] with w hw
      simp only [Function.comp_apply, affineChart_symm,
        quotientPoint_reciprocal hw, infinityChart_inversion_coe]
    · simp only [quotientPoint, ite_eq_right hz, sphere_chartAt_coe, affineChart_coe]
      have hq : ContDiffAt ℂ (⊤ : WithTop ℕ∞) quotientCoordinate z :=
        (contDiffAt_id.pow 2).add (((contDiffAt_inv ℂ hz)).pow 2)
      apply hq.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with w hw
      simp [Function.comp_apply, quotientPoint, hw]

def polynomialSection (c : Fin 3 → ℂ) : SphereTangentSection where
  affine := fun z => c 0 + c 1 * z + c 2 * z ^ 2
  infinity := fun w => -c 2 - c 1 * w - c 0 * w ^ 2
  affine_holomorphic := by fun_prop
  infinity_holomorphic := by fun_prop
  overlap := by
    intro z hz
    field_simp
    ring

@[simp] lemma polynomialSection_coefficients (c : Fin 3 → ℂ) :
    coefficients (polynomialSection c) = c := by
  ext i
  fin_cases i <;> simp [coefficients, polynomialSection]
  ring

theorem coefficients_surjective : Function.Surjective coefficients :=
  fun c => ⟨polynomialSection c, polynomialSection_coefficients c⟩

def coefficientEquiv : SphereTangentSection ≃ EuclideanSpace ℂ (Fin 3) :=
  (Equiv.ofBijective coefficients ⟨coefficients_injective, coefficients_surjective⟩).trans
    (WithLp.equiv 2 (Fin 3 → ℂ)).symm

instance sectionAddCommGroup : AddCommGroup SphereTangentSection := coefficientEquiv.addCommGroup
instance sectionModule : Module ℂ SphereTangentSection := coefficientEquiv.addEquiv.module ℂ

def coefficientLinearEquiv : SphereTangentSection ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 3) :=
  coefficientEquiv.addEquiv.linearEquiv ℂ

instance sectionNormedAddCommGroup : NormedAddCommGroup SphereTangentSection :=
  NormedAddCommGroup.induced _ _ coefficientLinearEquiv.toAddMonoidHom
    coefficientLinearEquiv.injective

instance sectionInnerProductSpace : InnerProductSpace ℂ SphereTangentSection :=
  InnerProductSpace.induced coefficientLinearEquiv

theorem section_inner (s t : SphereTangentSection) :
    inner ℂ s t = sectionHermitian s t := by
  change inner ℂ (coefficientEquiv s) (coefficientEquiv t) = _
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i, coefficients t i * star (coefficients s i)) = _
  simp only [sectionHermitian, mul_comm]

theorem sign_preserves_norm (s : SphereTangentSection) : ‖signSection s‖ = ‖s‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
    section_inner, section_inner, sign_preserves_Hermitian]

theorem inversion_preserves_norm (s : SphereTangentSection) : ‖inversionSection s‖ = ‖s‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
    section_inner, section_inner, inversion_preserves_Hermitian]

@[simp] lemma coefficients_zero : coefficients (0 : SphereTangentSection) = 0 := by
  have h := coefficientLinearEquiv.map_zero
  exact congrArg WithLp.ofLp h

@[simp] lemma zero_affine (z : ℂ) : (0 : SphereTangentSection).affine z = 0 := by
  have h : (0 : SphereTangentSection) = polynomialSection 0 := by
    apply coefficients_injective
    simp
  rw [h]
  simp [polynomialSection]

@[simp] lemma zero_infinity (z : ℂ) : (0 : SphereTangentSection).infinity z = 0 := by
  have h : (0 : SphereTangentSection) = polynomialSection 0 := by
    apply coefficients_injective
    simp
  rw [h]
  simp [polynomialSection]

theorem constantAffineSection_ne_zero : constantAffineSection ≠ 0 := by
  intro h
  have := congrArg (fun s : SphereTangentSection => s.affine 0) h
  simp [constantAffineSection] at this

theorem invariant_section_eq_zero (s : SphereTangentSection)
    (hs : signSection s = s) (hi : inversionSection s = s) : s = 0 := by
  have hsign : ∀ z : ℂ, s.affine (-z) = -s.affine z := by
    intro z
    have h := congrArg (fun t : SphereTangentSection => t.affine z) hs
    simpa [signSection] using congrArg Neg.neg h
  have hinv : s.infinity = s.affine := congrArg SphereTangentSection.affine hi
  obtain ⟨ha, hi⟩ := invariant_section_zero s hsign hinv
  apply coefficients_injective
  ext i
  fin_cases i <;> simp [coefficients, ha, hi]

lemma signPoint_involutive : Function.Involutive signPoint := by
  intro x
  cases x using OnePoint.rec <;> simp [signPoint]

lemma inversion_signPoint (x : Sphere) :
    inversionPoint (signPoint x) = signPoint (inversionPoint x) := by
  cases x using OnePoint.rec with
  | infty => simp [signPoint, inversionPoint]
  | coe z =>
    by_cases hz : z = 0 <;> simp [signPoint, inversionPoint, hz]

lemma signSection_involutive : Function.Involutive signSection := by
  intro s
  apply coefficients_injective
  ext i
  fin_cases i <;> simp [sign_coefficients]

lemma inversionSection_involutive : Function.Involutive inversionSection := by
  intro s
  cases s
  rfl

lemma inversion_signSection (s : SphereTangentSection) :
    inversionSection (signSection s) = signSection (inversionSection s) := by
  cases s
  rfl

lemma inversionPoint_analytic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) inversionPoint := by
  intro x
  apply sphere_analyticAt_of_chart _ _ inversionPoint_continuous.continuousAt
  cases x using OnePoint.rec with
  | infty =>
    simp only [inversionPoint, sphere_chartAt_coe, sphere_chartAt_infty, infinityChart_infty]
    have heq : affineChart ∘ inversionPoint ∘ infinityChart.symm = id := by
      funext z
      simp only [Function.comp_apply, infinityChart_symm,
        inversionPoint_involutive (z : Sphere), affineChart_coe, id_eq]
    rw [heq]
    exact contDiffAt_id
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp only [inversionPoint, ite_true, sphere_chartAt_infty, sphere_chartAt_coe,
        affineChart_coe]
      have heq : infinityChart ∘ inversionPoint ∘ affineChart.symm = id := by
        funext z
        simp only [Function.comp_apply, affineChart_symm, infinityChart_inversion_coe, id_eq]
      rw [heq]
      exact contDiffAt_id
    · simp only [inversionPoint, ite_eq_right hz, sphere_chartAt_coe, affineChart_coe]
      apply (contDiffAt_inv ℂ hz).congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with w hw
      simp [Function.comp_apply, inversionPoint, hw]

lemma signPoint_continuous : Continuous signPoint := by
  exact (Homeomorph.neg ℂ).onePointCongr.continuous

lemma infinityChart_sign_inversion (z : ℂ) :
    infinityChart (signPoint (inversionPoint (z : Sphere))) = -z := by
  by_cases hz : z = 0
  · simp [hz, inversionPoint, signPoint]
  · simp [inversionPoint, hz, signPoint, infinityChart_coe (neg_ne_zero.mpr (inv_ne_zero hz))]

lemma signPoint_analytic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) signPoint := by
  intro x
  apply sphere_analyticAt_of_chart _ _ signPoint_continuous.continuousAt
  cases x using OnePoint.rec with
  | infty =>
    simp only [signPoint, OnePoint.map_infty, sphere_chartAt_infty, infinityChart_infty]
    have heq : infinityChart ∘ signPoint ∘ infinityChart.symm = fun z : ℂ => -z := by
      funext z
      exact infinityChart_sign_inversion z
    change ContDiffAt ℂ (⊤ : WithTop ℕ∞) (infinityChart ∘ signPoint ∘ infinityChart.symm) 0
    rw [heq]
    exact contDiffAt_id.neg
  | coe z =>
    simp only [signPoint, OnePoint.map_some, sphere_chartAt_coe, affineChart_coe]
    change ContDiffAt ℂ (⊤ : WithTop ℕ∞) (affineChart ∘ signPoint ∘ affineChart.symm) z
    have heq : affineChart ∘ signPoint ∘ affineChart.symm = fun z : ℂ => -z := by
      funext w
      simp [Function.comp_apply, signPoint]
    rw [heq]
    exact contDiffAt_id.neg

abbrev Klein := Multiplicative (ZMod 2 × ZMod 2)

def sphereAct (g : Klein) (x : Sphere) : Sphere :=
  (if g.toAdd.1 = 0 then id else signPoint)
    ((if g.toAdd.2 = 0 then id else inversionPoint) x)

def sectionAct (g : Klein) (s : SphereTangentSection) : SphereTangentSection :=
  (if g.toAdd.1 = 0 then id else signSection)
    ((if g.toAdd.2 = 0 then id else inversionSection) s)

lemma zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  classical
  fin_cases a <;> (first | exact Or.inl rfl | exact Or.inr rfl)

instance kleinSphereAction : MulAction Klein Sphere where
  smul := sphereAct
  one_smul := by
    intro x
    change sphereAct 1 x = x
    simp [sphereAct]
  mul_smul := by
    intro g h x
    change sphereAct (g * h) x = sphereAct g (sphereAct h x)
    simp only [sphereAct, toAdd_mul]
    obtain ⟨⟨a,b⟩, rfl⟩ := Multiplicative.ofAdd.surjective g
    obtain ⟨⟨c,d⟩, rfl⟩ := Multiplicative.ofAdd.surjective h
    rcases zmod_two_cases a with rfl | rfl <;>
      rcases zmod_two_cases b with rfl | rfl <;>
      rcases zmod_two_cases c with rfl | rfl <;>
      rcases zmod_two_cases d with rfl | rfl <;>
      simp [signPoint_involutive _,
        inversionPoint_involutive _, inversion_signPoint, show (1 : ZMod 2) + 1 = 0 by decide]

instance kleinSectionAction : MulAction Klein SphereTangentSection where
  smul := sectionAct
  one_smul := by
    intro s
    change sectionAct 1 s = s
    simp [sectionAct]
  mul_smul := by
    intro g h s
    change sectionAct (g * h) s = sectionAct g (sectionAct h s)
    simp only [sectionAct, toAdd_mul]
    obtain ⟨⟨a,b⟩, rfl⟩ := Multiplicative.ofAdd.surjective g
    obtain ⟨⟨c,d⟩, rfl⟩ := Multiplicative.ofAdd.surjective h
    rcases zmod_two_cases a with rfl | rfl <;>
      rcases zmod_two_cases b with rfl | rfl <;>
      rcases zmod_two_cases c with rfl | rfl <;>
      rcases zmod_two_cases d with rfl | rfl <;>
      simp [signSection_involutive _,
        inversionSection_involutive _, inversion_signSection, show (1 : ZMod 2) + 1 = 0 by decide]

theorem sphereAct_analytic (g : Klein) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) (sphereAct g) := by
  unfold sphereAct
  by_cases h1 : g.toAdd.1 = 0 <;> by_cases h2 : g.toAdd.2 = 0
  · simpa [sphereAct, h1, h2] using! (contMDiff_id (I := 𝓘(ℂ, ℂ))
      (n := (⊤ : WithTop ℕ∞)) (M := Sphere))
  · simpa [sphereAct, h1, h2] using inversionPoint_analytic
  · simpa [sphereAct, h1, h2] using signPoint_analytic
  · simpa [sphereAct, h1, h2, Function.comp_def] using
      signPoint_analytic.comp inversionPoint_analytic

theorem sectionAct_preserves_norm (g : Klein) (s : SphereTangentSection) :
    ‖sectionAct g s‖ = ‖s‖ := by
  unfold sectionAct
  split_ifs <;> simp [sign_preserves_norm, inversion_preserves_norm]

@[simp] lemma coefficients_add (s t : SphereTangentSection) :
    coefficients (s + t) = coefficients s + coefficients t := by
  exact congrArg WithLp.ofLp (coefficientLinearEquiv.map_add s t)

@[simp] lemma coefficients_smul (a : ℂ) (s : SphereTangentSection) :
    coefficients (a • s) = a • coefficients s := by
  exact congrArg WithLp.ofLp (coefficientLinearEquiv.map_smul a s)

lemma signSection_add (s t : SphereTangentSection) :
    signSection (s + t) = signSection s + signSection t := by
  apply coefficients_injective
  ext i
  fin_cases i <;> simp [sign_coefficients, coefficients_add, add_comm]

lemma inversionSection_add (s t : SphereTangentSection) :
    inversionSection (s + t) = inversionSection s + inversionSection t := by
  apply coefficients_injective
  ext i
  fin_cases i <;> simp [inversion_coefficients, coefficients_add, add_comm]

lemma signSection_smul (a : ℂ) (s : SphereTangentSection) :
    signSection (a • s) = a • signSection s := by
  apply coefficients_injective
  ext i
  fin_cases i <;> simp [sign_coefficients, coefficients_smul]

lemma inversionSection_smul (a : ℂ) (s : SphereTangentSection) :
    inversionSection (a • s) = a • inversionSection s := by
  apply coefficients_injective
  ext i
  fin_cases i <;> simp [inversion_coefficients, coefficients_smul]

theorem sectionAct_add (g : Klein) (s t : SphereTangentSection) :
    sectionAct g (s + t) = sectionAct g s + sectionAct g t := by
  unfold sectionAct
  split_ifs <;> simp [signSection_add, inversionSection_add]

theorem sectionAct_smul (g : Klein) (a : ℂ) (s : SphereTangentSection) :
    sectionAct g (a • s) = a • sectionAct g s := by
  unfold sectionAct
  split_ifs <;> simp [signSection_smul, inversionSection_smul]

theorem quotientPoint_orbits (z w : Sphere) :
    quotientPoint z = quotientPoint w ↔ ∃ g : Klein, sphereAct g z = w := by
  rw [quotientPoint_fibers]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨Multiplicative.ofAdd (0, 0), by simp [sphereAct]⟩
    · exact ⟨Multiplicative.ofAdd (1, 0), by simp [sphereAct]⟩
    · exact ⟨Multiplicative.ofAdd (0, 1), by simp [sphereAct]⟩
    · exact ⟨Multiplicative.ofAdd (1, 1), by simp [sphereAct]⟩
  · rintro ⟨g, rfl⟩
    unfold sphereAct
    split_ifs <;> simp

theorem no_nonzero_invariant_section :
    ¬ ∃ s : SphereTangentSection, s ≠ 0 ∧ ∀ g : Klein, sectionAct g s = s := by
  rintro ⟨s, hs, hinv⟩
  apply hs
  apply invariant_section_eq_zero
  · simpa [sectionAct] using hinv (Multiplicative.ofAdd (1, 0))
  · simpa [sectionAct] using hinv (Multiplicative.ofAdd (0, 1))

theorem klein_action_not_free : ∃ g : Klein, g ≠ 1 ∧ sphereAct g (1 : ℂ) = (1 : ℂ) := by
  refine ⟨Multiplicative.ofAdd (0, 1), ?_, ?_⟩
  · intro h
    have h' := congrArg (fun g : Klein => g.toAdd.2) h
    norm_num at h'
  · simp [sphereAct, inversionPoint]

attribute [local instance] sphere_is_complex_manifold

def sectionValue (s : SphereTangentSection) (x : Sphere) : TangentSpace 𝓘(ℂ, ℂ) x :=
  (match x with
  | ∞ => s.infinity 0
  | (z : ℂ) => s.affine z : ℂ)

lemma affineChart_comp_symm : affineChart ∘ affineChart.symm = id := by
  funext z
  simp

lemma infinityChart_comp_symm : infinityChart ∘ infinityChart.symm = id := by
  funext z
  simp

lemma tangent_triv_affine (z w v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (z : Sphere)
      ⟨(w : Sphere), v⟩).2 = v := by
  rw [TangentBundle.trivializationAt_apply]
  simp [affineChart_comp_symm, fderiv_id]

lemma tangent_triv_infty (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : Sphere)
      ⟨∞, v⟩).2 = v := by
  rw [TangentBundle.trivializationAt_apply]
  simp [infinityChart_comp_symm, fderiv_id]

lemma tangent_triv_infty_coe (z v : ℂ) (hz : z ≠ 0) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : Sphere)
      ⟨(z : Sphere), v⟩).2 = -(z⁻¹)^2 * v := by
  rw [TangentBundle.trivializationAt_apply]
  simp only [sphere_chartAt_infty, sphere_chartAt_coe, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
    range_id, fderivWithin_univ, affineChart_coe]
  have heq : infinityChart ∘ affineChart.symm =ᶠ[𝓝 z] (fun w : ℂ => w⁻¹) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    simp [Function.comp_apply, infinityChart_coe hw]
  rw [heq.fderiv_eq]
  rw [(hasDerivAt_inv hz).hasFDerivAt.fderiv]
  simp [pow_two, mul_comm]

 
def tangentCoordinates (p x : Sphere) (v : ℂ) : ℂ :=
  (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) p ⟨x, v⟩).2

@[simp] lemma tangentCoordinates_affine (z w v : ℂ) :
    tangentCoordinates (z : Sphere) (w : Sphere) v = v := tangent_triv_affine z w v

@[simp] lemma tangentCoordinates_infty (v : ℂ) :
    tangentCoordinates ∞ ∞ v = v := tangent_triv_infty v

lemma tangentCoordinates_infty_coe (z v : ℂ) (hz : z ≠ 0) :
    tangentCoordinates ∞ (z : Sphere) v = -(z⁻¹)^2 * v := tangent_triv_infty_coe z v hz

lemma tangent_section_infty_chart (s : SphereTangentSection) (w : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : Sphere)
      ⟨infinityChart.symm w, sectionValue s (infinityChart.symm w)⟩).2 = s.infinity w := by
  change tangentCoordinates ∞ (infinityChart.symm w) (sectionValue s (infinityChart.symm w)) = _
  by_cases hw : w = 0
  · subst w
    simp [sectionValue, inversionPoint]
  · simp only [infinityChart_symm, inversionPoint, ite_eq_right hw, sectionValue]
    rw [tangentCoordinates_infty_coe _ _ (inv_ne_zero hw)]
    simpa only [inv_inv] using (s.overlap w⁻¹ (inv_ne_zero hw)).symm

lemma sphere_to_complex_analyticAt_iff (f : Sphere → ℂ) (x : Sphere) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f x ↔
      ContDiffAt ℂ (⊤ : WithTop ℕ∞) (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
  rw [contMDiffAt_iff_source]
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    range_id, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]

theorem sectionValue_analytic (s : SphereTangentSection) :
    ContMDiff 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)) (⊤ : WithTop ℕ∞)
      (fun x => Bundle.TotalSpace.mk' ℂ x (sectionValue s x)) := by
  intro x
  rw [Bundle.contMDiffAt_section, sphere_to_complex_analyticAt_iff]
  cases x using OnePoint.rec with
  | infty =>
    simp only [sphere_chartAt_infty, infinityChart_infty]
    have heq : (fun x => (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : Sphere)
      ⟨x, sectionValue s x⟩).2) ∘ infinityChart.symm = s.infinity := by
      funext w
      exact tangent_section_infty_chart s w
    rw [heq]
    exact s.infinity_holomorphic.contDiff.contDiffAt
  | coe z =>
    simp only [sphere_chartAt_coe, affineChart_coe]
    have heq : (fun x => (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (z : Sphere)
      ⟨x, sectionValue s x⟩).2) ∘ affineChart.symm = s.affine := by
      funext w
      change tangentCoordinates (z : Sphere) (affineChart.symm w)
        (sectionValue s (affineChart.symm w)) = _
      simp [sectionValue]
    rw [heq]
    exact s.affine_holomorphic.contDiff.contDiffAt

abbrev HolomorphicVectorField := ContMDiffSection 𝓘(ℂ, ℂ) ℂ (⊤ : WithTop ℕ∞)
  (TangentSpace 𝓘(ℂ, ℂ) : Sphere → Type)

def toTangentSection (s : SphereTangentSection) : HolomorphicVectorField :=
  ⟨sectionValue s, sectionValue_analytic s⟩

lemma infinityChart_symm_analytic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) infinityChart.symm := by
  have h := contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, ℂ))
    (n := (⊤ : WithTop ℕ∞)) (∞ : Sphere)
  simpa [extChartAt, OpenPartialHomeomorph.extend_coe_symm,
    OpenPartialHomeomorph.extend_target, contMDiffOn_univ] using h

def nativeValue (v : HolomorphicVectorField) (x : Sphere) : ℂ := v x

def affineCoefficient (v : HolomorphicVectorField) (z : ℂ) : ℂ := nativeValue v (z : Sphere)

def infinityCoefficient (v : HolomorphicVectorField) (z : ℂ) : ℂ :=
  tangentCoordinates ∞ (infinityChart.symm z) (nativeValue v (infinityChart.symm z))

lemma affineCoefficient_holomorphic (v : HolomorphicVectorField) :
    Differentiable ℂ (affineCoefficient v) := by
  intro z
  have h := (Bundle.contMDiffAt_section (z : Sphere)).mp (v.contMDiff (z : Sphere))
  rw [sphere_to_complex_analyticAt_iff] at h
  simp only [sphere_chartAt_coe, affineChart_coe] at h
  have heq : (fun x => (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (z : Sphere)
      ⟨x, v x⟩).2) ∘ affineChart.symm = affineCoefficient v := by
    funext w
    change tangentCoordinates (z : Sphere) (affineChart.symm w)
      (nativeValue v (affineChart.symm w)) = affineCoefficient v w
    simp [affineCoefficient]
  rw [heq] at h
  exact h.differentiableAt (by simp)

lemma infinityCoefficient_holomorphic (v : HolomorphicVectorField) :
    Differentiable ℂ (infinityCoefficient v) := by
  intro z
  have hz : infinityChart.symm z ∈
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : Sphere)).baseSet := by
    simp only [TangentBundle.trivializationAt_baseSet, sphere_chartAt_infty]
    exact infinityChart.map_target (by simp)
  have h := ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : Sphere)).contMDiffAt_section_iff hz).mp
    (v.contMDiff (infinityChart.symm z))
  have hc := h.comp z (infinityChart_symm_analytic z)
  exact hc.contDiffAt.differentiableAt (by simp)

def fromTangentSection (v : HolomorphicVectorField) : SphereTangentSection where
  affine := affineCoefficient v
  infinity := infinityCoefficient v
  affine_holomorphic := affineCoefficient_holomorphic v
  infinity_holomorphic := infinityCoefficient_holomorphic v
  overlap := by
    intro z hz
    simp [affineCoefficient, infinityCoefficient, inversionPoint, inv_ne_zero hz,
      tangentCoordinates_infty_coe z (nativeValue v (z : Sphere)) hz]

lemma SphereTangentSection.ext {s t : SphereTangentSection}
    (ha : s.affine = t.affine) (hi : s.infinity = t.infinity) : s = t := by
  cases s
  cases t
  cases ha
  cases hi
  rfl

lemma section_eq_polynomial (s : SphereTangentSection) :
    s = polynomialSection (coefficients s) := by
  apply coefficients_injective
  simp

lemma affine_as_coefficients (s : SphereTangentSection) (z : ℂ) :
    s.affine z = coefficients s 0 + coefficients s 1 * z + coefficients s 2 * z^2 := by
  conv_lhs => rw [section_eq_polynomial s]
  rfl

lemma infinity_as_coefficients (s : SphereTangentSection) (z : ℂ) :
    s.infinity z = -(coefficients s 2 + coefficients s 1 * z + coefficients s 0 * z^2) := by
  conv_lhs => rw [section_eq_polynomial s]
  simp [polynomialSection]
  ring

lemma affine_add (s t : SphereTangentSection) (z : ℂ) :
    (s + t).affine z = s.affine z + t.affine z := by
  simp only [affine_as_coefficients, coefficients_add, Pi.add_apply]
  ring

lemma infinity_add (s t : SphereTangentSection) (z : ℂ) :
    (s + t).infinity z = s.infinity z + t.infinity z := by
  simp only [infinity_as_coefficients, coefficients_add, Pi.add_apply]
  ring

lemma affine_smul (a : ℂ) (s : SphereTangentSection) (z : ℂ) :
    (a • s).affine z = a * s.affine z := by
  simp only [affine_as_coefficients, coefficients_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma infinity_smul (a : ℂ) (s : SphereTangentSection) (z : ℂ) :
    (a • s).infinity z = a * s.infinity z := by
  simp only [infinity_as_coefficients, coefficients_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma from_toTangentSection (s : SphereTangentSection) :
    fromTangentSection (toTangentSection s) = s := by
  apply SphereTangentSection.ext
  · funext z
    rfl
  · funext z
    exact tangent_section_infty_chart s z

lemma to_fromTangentSection (v : HolomorphicVectorField) :
    toTangentSection (fromTangentSection v) = v := by
  apply ContMDiffSection.ext
  intro x
  cases x using OnePoint.rec with
  | coe z => rfl
  | infty =>
    change infinityCoefficient v 0 = v ∞
    change infinityCoefficient v 0 = nativeValue v ∞
    simp [infinityCoefficient, inversionPoint]

theorem toTangentSection_bijective : Function.Bijective toTangentSection :=
  ⟨Function.LeftInverse.injective from_toTangentSection,
    Function.RightInverse.surjective to_fromTangentSection⟩

theorem toTangentSection_add (s t : SphereTangentSection) :
    toTangentSection (s + t) = toTangentSection s + toTangentSection t := by
  apply ContMDiffSection.ext
  intro x
  cases x using OnePoint.rec with
  | infty => exact infinity_add s t 0
  | coe z => exact affine_add s t z

theorem toTangentSection_smul (a : ℂ) (s : SphereTangentSection) :
    toTangentSection (a • s) = a • toTangentSection s := by
  apply ContMDiffSection.ext
  intro x
  cases x using OnePoint.rec with
  | infty => exact infinity_smul a s 0
  | coe z => exact affine_smul a s z

def tangentSectionLinearEquiv : SphereTangentSection ≃ₗ[ℂ] HolomorphicVectorField :=
  LinearEquiv.ofBijective
    { toFun := toTangentSection
      map_add' := toTangentSection_add
      map_smul' := toTangentSection_smul }
    toTangentSection_bijective

def sphereDerivative (f : Sphere → Sphere) (x : Sphere) (v : ℂ) : ℂ :=
  (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x) v

lemma sphereDerivative_chart (f : Sphere → Sphere) (x : Sphere)
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x) (v : ℂ) :
    sphereDerivative f x v =
      fderiv ℂ (chartAt ℂ (f x) ∘ f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) v := by
  simpa only [sphereDerivative, writtenInExtChartAt, extChartAt,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, range_id, fderivWithin_univ] using!
    congrArg (fun L : ℂ →L[ℂ] ℂ => L v) hf.mfderiv

lemma sphereDerivative_sign (x : Sphere) (v : ℂ) :
    sphereDerivative signPoint x v = -v := by
  rw [sphereDerivative_chart _ _ ((signPoint_analytic x).mdifferentiableAt (by simp))]
  cases x using OnePoint.rec with
  | infty =>
    simp only [signPoint, OnePoint.map_infty, sphere_chartAt_infty, infinityChart_infty]
    have heq : infinityChart ∘ OnePoint.map (fun z : ℂ => -z) ∘ infinityChart.symm =
        fun z : ℂ => -z := by
      funext z
      exact infinityChart_sign_inversion z
    rw [heq]
    have hd : HasFDerivAt (fun z : ℂ => -z) (-ContinuousLinearMap.id ℂ ℂ) 0 := by
      simpa using! (hasFDerivAt_id (𝕜 := ℂ) (0 : ℂ)).neg
    rw [hd.fderiv]
    simp
  | coe z =>
    simp only [signPoint, OnePoint.map_some, sphere_chartAt_coe, affineChart_coe]
    have heq : affineChart ∘ OnePoint.map (fun z : ℂ => -z) ∘ affineChart.symm =
        fun z : ℂ => -z := by
      funext w
      simp [Function.comp_apply]
    rw [heq]
    have hd : HasFDerivAt (fun w : ℂ => -w) (-ContinuousLinearMap.id ℂ ℂ) z := by
      simpa using! (hasFDerivAt_id (𝕜 := ℂ) z).neg
    rw [hd.fderiv]
    simp

lemma sphereDerivative_inversion_infty (v : ℂ) :
    sphereDerivative inversionPoint ∞ v = v := by
  rw [sphereDerivative_chart _ _ ((inversionPoint_analytic ∞).mdifferentiableAt (by simp))]
  simp only [inversionPoint, sphere_chartAt_coe, sphere_chartAt_infty, infinityChart_infty]
  have heq : affineChart ∘ inversionPoint ∘ infinityChart.symm = id := by
    funext z
    simp only [Function.comp_apply, infinityChart_symm, inversionPoint_involutive _, affineChart_coe]
    rfl
  change fderiv ℂ (affineChart ∘ inversionPoint ∘ infinityChart.symm) 0 v = v
  rw [heq, fderiv_id]
  rfl

lemma sphereDerivative_inversion_zero (v : ℂ) :
    sphereDerivative inversionPoint (0 : ℂ) v = v := by
  rw [sphereDerivative_chart _ _ ((inversionPoint_analytic (0 : ℂ)).mdifferentiableAt (by simp))]
  have h0 : inversionPoint (0 : ℂ) = ∞ := by simp [inversionPoint]
  rw [h0]
  simp only [sphere_chartAt_infty, sphere_chartAt_coe, affineChart_coe]
  have heq : infinityChart ∘ inversionPoint ∘ affineChart.symm = id := by
    funext z
    simp [Function.comp_apply]
  rw [heq, fderiv_id]
  rfl

lemma sphereDerivative_inversion_coe (z v : ℂ) (hz : z ≠ 0) :
    sphereDerivative inversionPoint (z : Sphere) v = -(z⁻¹)^2 * v := by
  rw [sphereDerivative_chart _ _ ((inversionPoint_analytic (z : Sphere)).mdifferentiableAt (by simp))]
  have hz' : inversionPoint (z : Sphere) = (z⁻¹ : ℂ) := by simp [inversionPoint, hz]
  rw [hz']
  simp only [sphere_chartAt_coe, affineChart_coe]
  have heq : affineChart ∘ inversionPoint ∘ affineChart.symm =ᶠ[𝓝 z] (fun w : ℂ => w⁻¹) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    simp [Function.comp_apply, inversionPoint, hw]
  rw [heq.fderiv_eq, (hasDerivAt_inv hz).hasFDerivAt.fderiv]
  simp [pow_two, mul_comm]

def chartValue (s : SphereTangentSection) (x : Sphere) : ℂ := sectionValue s x

lemma sign_action_natural (s : SphereTangentSection) (x : Sphere) :
    sphereDerivative signPoint x (chartValue s x) = chartValue (signSection s) (signPoint x) := by
  rw [sphereDerivative_sign]
  cases x using OnePoint.rec <;> simp [chartValue, sectionValue, signPoint, signSection]

lemma inversion_action_natural (s : SphereTangentSection) (x : Sphere) :
    sphereDerivative inversionPoint x (chartValue s x) =
      chartValue (inversionSection s) (inversionPoint x) := by
  cases x using OnePoint.rec with
  | infty => simp [sphereDerivative_inversion_infty, chartValue, sectionValue,
      inversionPoint, inversionSection]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp [sphereDerivative_inversion_zero, chartValue, sectionValue,
        inversionPoint, inversionSection]
    · rw [sphereDerivative_inversion_coe _ _ hz]
      simpa [chartValue, sectionValue, inversionPoint, inversionSection, hz] using (s.overlap z hz).symm

lemma sphereDerivative_comp (f g : Sphere → Sphere) (x : Sphere) (v : ℂ)
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f (g x))
    (hg : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g x) :
    sphereDerivative (f ∘ g) x v = sphereDerivative f (g x) (sphereDerivative g x v) := by
  simp only [sphereDerivative, mfderiv_comp x hf hg]
  rfl

theorem tangent_action_natural (g : Klein) (s : SphereTangentSection) (x : Sphere) :
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (sphereAct g) x) (toTangentSection s x) =
      toTangentSection (sectionAct g s) (sphereAct g x) := by
  change sphereDerivative (sphereAct g) x (chartValue s x) = chartValue (sectionAct g s) (sphereAct g x)
  by_cases h1 : g.toAdd.1 = 0 <;> by_cases h2 : g.toAdd.2 = 0
  · have heq : sphereAct g = id := by funext y; simp [sphereAct, h1, h2]
    rw [heq]
    simp [sectionAct, h1, h2, sphereDerivative, mfderiv_id]
    rfl
  · have heq : sphereAct g = inversionPoint := by funext y; simp [sphereAct, h1, h2]
    rw [heq]
    simpa [sectionAct, h1, h2] using inversion_action_natural s x
  · have heq : sphereAct g = signPoint := by funext y; simp [sphereAct, h1, h2]
    rw [heq]
    simpa [sectionAct, h1, h2] using sign_action_natural s x
  · have heq : sphereAct g = signPoint ∘ inversionPoint := by funext y; simp [sphereAct, h1, h2]
    rw [heq]
    simp only [sectionAct, ite_eq_right h1, ite_eq_right h2]
    rw [sphereDerivative_comp _ _ _ _
      ((signPoint_analytic _).mdifferentiableAt (by simp))
      ((inversionPoint_analytic _).mdifferentiableAt (by simp)),
      inversion_action_natural, sign_action_natural]
    rfl

theorem no_nonzero_invariant_holomorphic_vectorfield :
    ¬ ∃ v : HolomorphicVectorField, v ≠ 0 ∧ ∀ (g : Klein) (x : Sphere),
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (sphereAct g) x) (v x) = v (sphereAct g x) := by
  rintro ⟨v, hv, hinv⟩
  obtain ⟨s, rfl⟩ := toTangentSection_bijective.2 v
  apply no_nonzero_invariant_section
  refine ⟨s, ?_, ?_⟩
  · intro hs
    apply hv
    rw [hs]
    exact tangentSectionLinearEquiv.map_zero
  · intro g
    apply toTangentSection_bijective.1
    apply ContMDiffSection.ext
    intro y
    obtain ⟨x, rfl⟩ := MulAction.surjective g y
    exact (tangent_action_natural g s x).symm.trans (hinv g x)

instance nativeNormedAddCommGroup : NormedAddCommGroup HolomorphicVectorField :=
  NormedAddCommGroup.induced _ _ tangentSectionLinearEquiv.symm.toAddMonoidHom
    tangentSectionLinearEquiv.symm.injective

instance nativeInnerProductSpace : InnerProductSpace ℂ HolomorphicVectorField :=
  InnerProductSpace.induced tangentSectionLinearEquiv.symm

def nativeSectionAct (g : Klein) (v : HolomorphicVectorField) : HolomorphicVectorField :=
  toTangentSection (sectionAct g (tangentSectionLinearEquiv.symm v))

theorem nativeSectionAct_preserves_norm (g : Klein) (v : HolomorphicVectorField) :
    ‖nativeSectionAct g v‖ = ‖v‖ := by
  change ‖tangentSectionLinearEquiv.symm
    (tangentSectionLinearEquiv (sectionAct g (tangentSectionLinearEquiv.symm v)))‖ =
    ‖tangentSectionLinearEquiv.symm v‖
  rw [tangentSectionLinearEquiv.symm_apply_apply, sectionAct_preserves_norm]

theorem native_downstairs_nonzero : toTangentSection constantAffineSection ≠ 0 := by
  intro h
  apply constantAffineSection_ne_zero
  exact tangentSectionLinearEquiv.injective (h.trans tangentSectionLinearEquiv.map_zero.symm)

lemma quotientCoordinate_derivative_one : HasDerivAt quotientCoordinate 0 1 := by
  have h₁ : HasDerivAt (fun z : ℂ => z ^ 2) (2 : ℂ) 1 := by
    simpa using! (hasDerivAt_id (1 : ℂ)).pow 2
  have h₂ : HasDerivAt (fun z : ℂ => (z⁻¹) ^ 2) (-2 : ℂ) 1 := by
    simpa using! ((hasDerivAt_id (1 : ℂ)).inv one_ne_zero).pow 2
  simpa only [quotientCoordinate, add_neg_cancel] using! h₁.add h₂

lemma sphereDerivative_quotient_one (v : ℂ) :
    sphereDerivative quotientPoint (1 : ℂ) v = 0 := by
  rw [sphereDerivative_chart _ _ ((quotientPoint_analytic _).mdifferentiableAt (by simp))]
  simp only [quotientPoint, ite_eq_right one_ne_zero, sphere_chartAt_coe, affineChart_coe]
  have heq : (affineChart ∘ quotientPoint ∘ affineChart.symm) =ᶠ[𝓝 (1 : ℂ)]
      quotientCoordinate := by
    filter_upwards [eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0)] with z hz
    simp [Function.comp_apply, quotientPoint, hz]
  rw [heq.fderiv_eq, quotientCoordinate_derivative_one.hasFDerivAt.fderiv]
  simp

theorem native_no_anticanonical_lift :
    ¬ ∃ v : ∀ x : Sphere, TangentSpace 𝓘(ℂ, ℂ) x,
      ∀ x : Sphere, (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) quotientPoint x) (v x) =
        toTangentSection constantAffineSection (quotientPoint x) := by
  rintro ⟨v, hv⟩
  have h := hv ((1 : ℂ) : Sphere)
  change sphereDerivative quotientPoint (1 : ℂ) (v (1 : ℂ)) =
    chartValue constantAffineSection (quotientPoint (1 : ℂ)) at h
  have h' : (0 : ℂ) = chartValue constantAffineSection (quotientPoint (1 : ℂ)) :=
    (sphereDerivative_quotient_one _).symm.trans h
  simp [chartValue, sectionValue, constantAffineSection, quotientPoint] at h'

abbrev AnticanonicalFiber (x : Sphere) := ⋀[ℂ]^1 (TangentSpace 𝓘(ℂ, ℂ) x)

def determinantValue (s : ∀ x : Sphere, AnticanonicalFiber x) (x : Sphere) :
    TangentSpace 𝓘(ℂ, ℂ) x := exteriorPower.oneEquiv ℂ _ (s x)

def IsHolomorphicDeterminantSection (s : ∀ x : Sphere, AnticanonicalFiber x) : Prop :=
  ContMDiff 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)) (⊤ : WithTop ℕ∞)
    (fun x => Bundle.TotalSpace.mk' ℂ x (determinantValue s x))

theorem downstairs_anticanonical_section :
    ∃ s : ∀ x : Sphere, AnticanonicalFiber x,
      (∃ x, s x ≠ 0) ∧ IsHolomorphicDeterminantSection s := by
  let s : ∀ x : Sphere, AnticanonicalFiber x := fun x =>
    (exteriorPower.oneEquiv ℂ _).symm (toTangentSection constantAffineSection x)
  refine ⟨s, ⟨(0 : ℂ), ?_⟩, ?_⟩
  · intro h
    have heq := congrArg
      (exteriorPower.oneEquiv ℂ (TangentSpace 𝓘(ℂ, ℂ) ((0 : ℂ) : Sphere))) h
    dsimp only [s] at heq
    simp only [LinearEquiv.apply_symm_apply, map_zero] at heq
    change (1 : ℂ) = 0 at heq
    exact one_ne_zero heq
  · change ContMDiff _ _ _ (fun x => Bundle.TotalSpace.mk' ℂ x
      ((exteriorPower.oneEquiv ℂ _) ((exteriorPower.oneEquiv ℂ _).symm
        (toTangentSection constantAffineSection x))))
    simpa only [LinearEquiv.apply_symm_apply] using
      (toTangentSection constantAffineSection).contMDiff

theorem no_nonzero_invariant_anticanonical_section :
    ¬ ∃ s : ∀ x : Sphere, AnticanonicalFiber x,
      (∃ x, s x ≠ 0) ∧ IsHolomorphicDeterminantSection s ∧
        ∀ (g : Klein) (x : Sphere),
          exteriorPower.map 1
            (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (sphereAct g) x).toLinearMap (s x) =
              s (sphereAct g x) := by
  rintro ⟨s, ⟨x, hx⟩, hs, hi⟩
  apply no_nonzero_invariant_holomorphic_vectorfield
  let v : HolomorphicVectorField := ⟨determinantValue s, hs⟩
  refine ⟨v, ?_, ?_⟩
  · intro hv
    apply hx
    have h : determinantValue s x = 0 :=
      congrArg (fun t : HolomorphicVectorField => t x) hv
    apply (exteriorPower.oneEquiv ℂ _).injective
    exact h.trans (map_zero _).symm
  · intro g y
    have heq := congrArg (fun L : AnticanonicalFiber y →ₗ[ℂ]
        TangentSpace 𝓘(ℂ, ℂ) (sphereAct g y) => L (s y))
      (exteriorPower.oneEquiv_naturality
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (sphereAct g) y).toLinearMap)
    have h := congrArg (exteriorPower.oneEquiv ℂ _) (hi g y)
    exact heq.symm.trans h

lemma nativeSectionAct_equiv (g : Klein) (t : SphereTangentSection) :
    nativeSectionAct g (tangentSectionLinearEquiv t) =
      tangentSectionLinearEquiv (sectionAct g t) := by
  change tangentSectionLinearEquiv
    (sectionAct g (tangentSectionLinearEquiv.symm (tangentSectionLinearEquiv t))) = _
  rw [LinearEquiv.symm_apply_apply]

 

def determinantSectionMap : HolomorphicVectorField →ₗ[ℂ]
    (∀ x : Sphere, AnticanonicalFiber x) where
  toFun v x := (exteriorPower.oneEquiv ℂ _).symm (v x)
  map_add' v w := by
    funext x
    exact map_add (exteriorPower.oneEquiv ℂ _).symm (v x) (w x)
  map_smul' c v := by
    funext x
    exact map_smul (exteriorPower.oneEquiv ℂ _).symm c (v x)

theorem determinantSectionMap_injective : Function.Injective determinantSectionMap := by
  intro v w h
  apply ContMDiffSection.ext
  intro x
  exact (exteriorPower.oneEquiv ℂ _).symm.injective (congrFun h x)

abbrev AnticanonicalSections := LinearMap.range determinantSectionMap

def anticanonicalSectionEquiv : HolomorphicVectorField ≃ₗ[ℂ] AnticanonicalSections :=
  LinearEquiv.ofInjective determinantSectionMap determinantSectionMap_injective

theorem mem_anticanonicalSections_iff (s : ∀ x : Sphere, AnticanonicalFiber x) :
    s ∈ LinearMap.range determinantSectionMap ↔ IsHolomorphicDeterminantSection s := by
  constructor
  · rintro ⟨v, rfl⟩
    simpa only [IsHolomorphicDeterminantSection, determinantValue,
      determinantSectionMap, LinearMap.coe_mk, AddHom.coe_mk,
      LinearEquiv.apply_symm_apply] using v.contMDiff
  · intro hs
    refine ⟨⟨determinantValue s, hs⟩, ?_⟩
    funext x
    exact (exteriorPower.oneEquiv ℂ _).symm_apply_apply (s x)

instance anticanonicalNormedAddCommGroup : NormedAddCommGroup AnticanonicalSections :=
  NormedAddCommGroup.induced _ _ anticanonicalSectionEquiv.symm.toAddMonoidHom
    anticanonicalSectionEquiv.symm.injective

instance anticanonicalInnerProductSpace : InnerProductSpace ℂ AnticanonicalSections :=
  InnerProductSpace.induced anticanonicalSectionEquiv.symm

def anticanonicalSectionAct (g : Klein) (s : AnticanonicalSections) : AnticanonicalSections :=
  anticanonicalSectionEquiv (nativeSectionAct g (anticanonicalSectionEquiv.symm s))

theorem anticanonicalSectionAct_preserves_norm (g : Klein) (s : AnticanonicalSections) :
    ‖anticanonicalSectionAct g s‖ = ‖s‖ := by
  change ‖anticanonicalSectionEquiv.symm
    (anticanonicalSectionEquiv (nativeSectionAct g (anticanonicalSectionEquiv.symm s)))‖ =
      ‖anticanonicalSectionEquiv.symm s‖
  rw [anticanonicalSectionEquiv.symm_apply_apply, nativeSectionAct_preserves_norm]

theorem anticanonicalSectionAct_natural (g : Klein) (s : AnticanonicalSections) (x : Sphere) :
    exteriorPower.map 1 (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (sphereAct g) x).toLinearMap (s.1 x) =
      (anticanonicalSectionAct g s).1 (sphereAct g x) := by
  obtain ⟨v, rfl⟩ := anticanonicalSectionEquiv.surjective s
  obtain ⟨t, rfl⟩ := tangentSectionLinearEquiv.surjective v
  simp only [anticanonicalSectionAct, LinearEquiv.symm_apply_apply, nativeSectionAct_equiv]
  apply (exteriorPower.oneEquiv ℂ _).injective
  have heq := congrArg (fun L : AnticanonicalFiber x →ₗ[ℂ]
      TangentSpace 𝓘(ℂ, ℂ) (sphereAct g x) =>
        L ((exteriorPower.oneEquiv ℂ _).symm (toTangentSection t x)))
    (exteriorPower.oneEquiv_naturality
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (sphereAct g) x).toLinearMap)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at heq
  change (exteriorPower.oneEquiv ℂ _) (exteriorPower.map 1 _
    ((exteriorPower.oneEquiv ℂ _).symm (toTangentSection t x))) =
      (exteriorPower.oneEquiv ℂ _) ((exteriorPower.oneEquiv ℂ _).symm
        (toTangentSection (sectionAct g t) (sphereAct g x)))
  rw [LinearEquiv.apply_symm_apply]
  exact heq.trans (tangent_action_natural g t x)

theorem anticanonicalSectionAct_one (s : AnticanonicalSections) :
    anticanonicalSectionAct 1 s = s := by
  obtain ⟨v, rfl⟩ := anticanonicalSectionEquiv.surjective s
  obtain ⟨t, rfl⟩ := tangentSectionLinearEquiv.surjective v
  simp only [anticanonicalSectionAct, LinearEquiv.symm_apply_apply, nativeSectionAct_equiv]
  simp [sectionAct]

theorem anticanonicalSectionAct_mul (g h : Klein) (s : AnticanonicalSections) :
    anticanonicalSectionAct (g * h) s =
      anticanonicalSectionAct g (anticanonicalSectionAct h s) := by
  obtain ⟨v, rfl⟩ := anticanonicalSectionEquiv.surjective s
  obtain ⟨t, rfl⟩ := tangentSectionLinearEquiv.surjective v
  have hmul : sectionAct (g * h) t = sectionAct g (sectionAct h t) :=
    mul_smul g h t
  simp only [anticanonicalSectionAct, LinearEquiv.symm_apply_apply, nativeSectionAct_equiv]
  rw [hmul]

 

theorem branched_quotient_anticanonical_obstruction :
    (∃ s : AnticanonicalSections, s ≠ 0) ∧
      (∀ g s, ‖anticanonicalSectionAct g s‖ = ‖s‖) ∧
      ¬ ∃ s : AnticanonicalSections, s ≠ 0 ∧ ∀ g, anticanonicalSectionAct g s = s := by
  refine ⟨?_, anticanonicalSectionAct_preserves_norm, ?_⟩
  · refine ⟨anticanonicalSectionEquiv (toTangentSection constantAffineSection), ?_⟩
    intro h
    apply native_downstairs_nonzero
    exact anticanonicalSectionEquiv.injective
      (h.trans anticanonicalSectionEquiv.map_zero.symm)
  · rintro ⟨s, hs, hi⟩
    apply no_nonzero_invariant_anticanonical_section
    refine ⟨s.1, ?_, (mem_anticanonicalSections_iff s.1).mp s.2, ?_⟩
    · by_contra! h
      apply hs
      exact Subtype.ext (funext h)
    · intro g x
      rw [anticanonicalSectionAct_natural, hi g]

 

abbrev ZeroComplex := Fin 0 → ℂ
abbrev SplitModel := 𝓘(ℂ, ZeroComplex).prod (𝓘(ℂ, ZeroComplex).prod 𝓘(ℂ, ℂ))
abbrev SplitSpace := ZeroComplex × ZeroComplex × Sphere

def translation (_g : Klein) : ZeroComplex := 0

def productAct (g : Klein) (p : SplitSpace) : SplitSpace :=
  (p.1 + translation g, p.2.1, sphereAct g p.2.2)

def productQuotient (p : SplitSpace) : Sphere := quotientPoint p.2.2

instance zeroTranslationLattice : IsZLattice ℝ (⊥ : Submodule ℤ ZeroComplex) := by
  constructor
  exact Subsingleton.elim _ _

theorem translation_range : Set.range translation =
    (↑(⊥ : Submodule ℤ ZeroComplex) : Set ZeroComplex) := by
  ext x
  constructor
  · intro h
    change x = 0
    exact Subsingleton.elim _ _
  · intro h
    exact ⟨1, Subsingleton.elim _ _⟩

theorem productAct_one (p : SplitSpace) : productAct 1 p = p := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · apply Prod.ext
    · rfl
    · exact one_smul Klein p.2.2

theorem productAct_mul (g h : Klein) (p : SplitSpace) :
    productAct (g * h) p = productAct g (productAct h p) := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · apply Prod.ext
    · rfl
    · exact mul_smul g h p.2.2

theorem productAct_analytic (g : Klein) :
    ContMDiff SplitModel SplitModel (⊤ : WithTop ℕ∞) (productAct g) := by
  have h := (contMDiff_id (I := 𝓘(ℂ, ZeroComplex)) (M := ZeroComplex) (n := (⊤ : WithTop ℕ∞))).prodMap
    ((contMDiff_id (I := 𝓘(ℂ, ZeroComplex)) (M := ZeroComplex) (n := (⊤ : WithTop ℕ∞))).prodMap
      (sphereAct_analytic g))
  have heq : productAct g = Prod.map id (Prod.map id (sphereAct g)) := by
    funext p
    dsimp [productAct, translation, Prod.map]
    rw [add_zero]
  rw [heq]
  exact h

theorem productQuotient_analytic :
    ContMDiff SplitModel 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) productQuotient := by
  exact quotientPoint_analytic.comp
    ((contMDiff_id (I := SplitModel) (M := SplitSpace)).snd.snd)

theorem productQuotient_isQuotientMap : Topology.IsQuotientMap productQuotient := by
  apply Topology.IsQuotientMap.of_surjective_continuous
  · intro x
    obtain ⟨y, hy⟩ := quotientPoint_surjective x
    exact ⟨(0, 0, y), hy⟩
  · exact quotientPoint_continuous.comp (continuous_snd.comp continuous_snd)

theorem productQuotient_orbits (p p' : SplitSpace) :
    productQuotient p = productQuotient p' ↔ ∃ g : Klein, productAct g p = p' := by
  change quotientPoint p.2.2 = quotientPoint p'.2.2 ↔ _
  rw [quotientPoint_orbits]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, Prod.ext (Subsingleton.elim _ _)
      (Prod.ext (Subsingleton.elim _ _) hg)⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg (fun q : SplitSpace => q.2.2) hg⟩

abbrev ZeroCanonicalFiber (x : ZeroComplex) :=
  ⋀[ℂ]^0 (Module.Dual ℂ (TangentSpace 𝓘(ℂ, ZeroComplex) x))

def zeroCanonicalFrame (x : ZeroComplex) : ZeroCanonicalFiber x :=
  (exteriorPower.zeroEquiv ℂ _).symm 1

theorem zeroCanonicalFrame_nowhere_zero (x : ZeroComplex) : zeroCanonicalFrame x ≠ 0 := by
  intro h
  have heq := congrArg (exteriorPower.zeroEquiv ℂ _) h
  simp [zeroCanonicalFrame] at heq

theorem zeroCanonicalFrame_holomorphic :
    ContMDiff 𝓘(ℂ, ZeroComplex) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞)
      (fun x => exteriorPower.zeroEquiv ℂ _ (zeroCanonicalFrame x)) := by
  simpa only [zeroCanonicalFrame, LinearEquiv.apply_symm_apply] using
    (contMDiff_const (I := 𝓘(ℂ, ZeroComplex)) (c := (1 : ℂ))
      (n := (⊤ : WithTop ℕ∞)))

theorem zeroCanonicalFrame_invariant (x : ZeroComplex) :
    exteriorPower.map 0
      (mfderiv 𝓘(ℂ, ZeroComplex) 𝓘(ℂ, ZeroComplex) id x).toLinearMap.dualMap
        (zeroCanonicalFrame x) = zeroCanonicalFrame x := by
  rw [mfderiv_id]
  change exteriorPower.map 0 LinearMap.id (zeroCanonicalFrame x) = _
  rw [exteriorPower.map_id]
  rfl

 

theorem literal_product_quotient_data :
    CompactSpace Sphere ∧ ConnectedSpace Sphere ∧
    CompactSpace ZeroComplex ∧ ConnectedSpace ZeroComplex ∧
    Topology.IsQuotientMap productQuotient ∧
    (∀ p p', productQuotient p = productQuotient p' ↔
      ∃ g : Klein, productAct g p = p') ∧
    (Set.range translation = (↑(⊥ : Submodule ℤ ZeroComplex) : Set ZeroComplex)) ∧
    (∀ x, zeroCanonicalFrame x ≠ 0) := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    productQuotient_isQuotientMap, productQuotient_orbits,
    translation_range, zeroCanonicalFrame_nowhere_zero⟩

 
theorem anticanonicalSectionAct_add (g : Klein) (s t : AnticanonicalSections) :
    anticanonicalSectionAct g (s + t) =
      anticanonicalSectionAct g s + anticanonicalSectionAct g t := by
  change anticanonicalSectionEquiv
    (tangentSectionLinearEquiv (sectionAct g
      (tangentSectionLinearEquiv.symm (anticanonicalSectionEquiv.symm (s + t))))) = _
  simp only [map_add, sectionAct_add]
  rfl

theorem anticanonicalSectionAct_smul (g : Klein) (a : ℂ) (s : AnticanonicalSections) :
    anticanonicalSectionAct g (a • s) = a • anticanonicalSectionAct g s := by
  change anticanonicalSectionEquiv
    (tangentSectionLinearEquiv (sectionAct g
      (tangentSectionLinearEquiv.symm (anticanonicalSectionEquiv.symm (a • s))))) = _
  simp only [map_smul, sectionAct_smul]
  rfl

def anticanonicalMonodromy (g : Klein) : AnticanonicalSections ≃ₗᵢ[ℂ] AnticanonicalSections where
  toLinearEquiv :=
    { toFun := anticanonicalSectionAct g
      invFun := anticanonicalSectionAct g⁻¹
      left_inv := by
        intro s
        rw [← anticanonicalSectionAct_mul, inv_mul_cancel, anticanonicalSectionAct_one]
      right_inv := by
        intro s
        rw [← anticanonicalSectionAct_mul, mul_inv_cancel, anticanonicalSectionAct_one]
      map_add' := anticanonicalSectionAct_add g
      map_smul' := anticanonicalSectionAct_smul g }
  norm_map' := anticanonicalSectionAct_preserves_norm g

theorem no_monodromy_invariant_anticanonical_section :
    ¬ ∃ s : AnticanonicalSections, s ≠ 0 ∧ ∀ g, anticanonicalMonodromy g s = s := by
  exact branched_quotient_anticanonical_obstruction.2.2

 

theorem literal_source_instance_obstruction :
    (0 < (1 : ℕ)) ∧
    IsManifold 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) Sphere ∧
    CompactSpace Sphere ∧ ConnectedSpace Sphere ∧
    IsManifold 𝓘(ℂ, ZeroComplex) (⊤ : WithTop ℕ∞) ZeroComplex ∧
    CompactSpace ZeroComplex ∧ ConnectedSpace ZeroComplex ∧
    (∀ p, productAct 1 p = p) ∧
    (∀ g h p, productAct (g * h) p = productAct g (productAct h p)) ∧
    (∀ g, ContMDiff SplitModel SplitModel (⊤ : WithTop ℕ∞) (productAct g)) ∧
    Topology.IsQuotientMap productQuotient ∧
    ContMDiff SplitModel 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) productQuotient ∧
    (∀ p p', productQuotient p = productQuotient p' ↔
      ∃ g : Klein, productAct g p = p') ∧
    IsZLattice ℝ (⊥ : Submodule ℤ ZeroComplex) ∧
    (Set.range translation = (↑(⊥ : Submodule ℤ ZeroComplex) : Set ZeroComplex)) ∧
    (∀ x, zeroCanonicalFrame x ≠ 0) ∧
    ContMDiff 𝓘(ℂ, ZeroComplex) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞)
      (fun x => exteriorPower.zeroEquiv ℂ _ (zeroCanonicalFrame x)) ∧
    (∀ x, exteriorPower.map 0
      (mfderiv 𝓘(ℂ, ZeroComplex) 𝓘(ℂ, ZeroComplex) id x).toLinearMap.dualMap
        (zeroCanonicalFrame x) = zeroCanonicalFrame x) ∧
    (∃ s : AnticanonicalSections, s ≠ 0) ∧
    (∀ g s, ‖anticanonicalMonodromy g s‖ = ‖s‖) ∧
    (∀ g s x, exteriorPower.map 1
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (sphereAct g) x).toLinearMap (s.1 x) =
        (anticanonicalMonodromy g s).1 (sphereAct g x)) ∧
    ¬ ∃ s : AnticanonicalSections, s ≠ 0 ∧ ∀ g, anticanonicalMonodromy g s = s := by
  exact ⟨by decide, sphere_is_complex_manifold, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, productAct_one, productAct_mul,
    productAct_analytic, productQuotient_isQuotientMap, productQuotient_analytic,
    productQuotient_orbits, inferInstance, translation_range,
    zeroCanonicalFrame_nowhere_zero, zeroCanonicalFrame_holomorphic,
    zeroCanonicalFrame_invariant, branched_quotient_anticanonical_obstruction.1,
    anticanonicalSectionAct_preserves_norm, anticanonicalSectionAct_natural,
    no_monodromy_invariant_anticanonical_section⟩

end QuotientLift

end

end OAI
