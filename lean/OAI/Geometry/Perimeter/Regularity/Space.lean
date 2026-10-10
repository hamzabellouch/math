import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
namespace RPI
namespace Boundary

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def divergence {n : ℕ} (X : Space n → Space n) (x : Space n) : ℝ :=
  ∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i

def PerimeterTest {n : ℕ} (U : Set (Space n)) (X : Space n → Space n) : Prop :=
  ContDiff ℝ 1 X ∧ HasCompactSupport X ∧ tsupport X ⊆ U ∧ ∀ x, ‖X x‖ ≤ 1

noncomputable def perimeter {n : ℕ} (K U : Set (Space n)) : ℝ≥0∞ :=
  ⨆ X : Space n → Space n, ⨆ (_ : PerimeterTest U X),
    ENNReal.ofReal (∫ x in K, divergence X x)

theorem perimeter_mono {n : ℕ} (K : Set (Space n)) {U V : Set (Space n)}
    (hUV : U ⊆ V) : perimeter K U ≤ perimeter K V := by
  unfold perimeter
  refine iSup_le fun X ↦ iSup_le fun hX ↦ ?_
  apply le_iSup_of_le X
  apply le_iSup_of_le (show PerimeterTest V X from
    ⟨hX.1, hX.2.1, hX.2.2.1.trans hUV, hX.2.2.2⟩)
  exact le_rfl

theorem perimeter_congr_ae {n : ℕ} {K L : Set (Space n)}
    (hKL : K =ᵐ[(volume : Measure (Space n))] L) (U : Set (Space n)) :
    perimeter K U = perimeter L U := by
  simp only [perimeter, Measure.restrict_congr_set hKL]

def LocallyFinitePerimeter {n : ℕ} (K : Set (Space n)) : Prop :=
  MeasurableSet K ∧ ∀ R : ℝ, 0 < R → perimeter K (Metric.ball 0 R) < ⊤

def CompactVariationIn {n : ℕ} (K L U : Set (Space n)) : Prop :=
  ∃ F : Set (Space n), IsCompact F ∧ F ⊆ U ∧
    ∀ᵐ x ∂(volume : Measure (Space n)), x ∉ F → (x ∈ K ↔ x ∈ L)

def LocallyPerimeterMinimizing {n : ℕ} (K : Set (Space n)) : Prop :=
  LocallyFinitePerimeter K ∧
    ∀ (L U : Set (Space n)), LocallyFinitePerimeter L → IsOpen U → Bornology.IsBounded U →
      CompactVariationIn K L U → perimeter K U ≤ perimeter L U

def perimeterSupport {n : ℕ} (K : Set (Space n)) : Set (Space n) :=
  {x | ∀ r : ℝ, 0 < r → 0 < perimeter K (Metric.ball x r)}

theorem isClosed_perimeterSupport {n : ℕ} (K : Set (Space n)) :
    IsClosed (perimeterSupport K) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro x hx
  change ¬ ∀ r : ℝ, 0 < r → 0 < perimeter K (Metric.ball x r) at hx
  push Not at hx
  obtain ⟨r, hr, hPr⟩ := hx
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro y hy
  change ¬ ∀ s : ℝ, 0 < s → 0 < perimeter K (Metric.ball y s)
  intro h
  have hsub : Metric.ball y (r / 2) ⊆ Metric.ball x r := by
    intro z hz
    have hzy := Metric.mem_ball.mp hz
    have hyx := Metric.mem_ball.mp hy
    have ht := dist_triangle z y x
    change dist z x < r
    linarith
  exact not_lt_of_ge ((perimeter_mono K hsub).trans hPr) (h (r / 2) (half_pos hr))

def IsCone {n : ℕ} (K : Set (Space n)) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ᵐ x ∂(volume : Measure (Space n)), (r • x ∈ K ↔ x ∈ K)

noncomputable def surfaceMeasure {n : ℕ} (S : Set (Space n)) : Measure (Space n) :=
  (Measure.euclideanHausdorffMeasure (n - 1)).restrict S

theorem surfaceMeasure_zero_of_dimH_lt {n : ℕ} (S T : Set (Space n))
    (hT : dimH T < (n - 1 : ℕ)) : surfaceMeasure S T = 0 := by
  have hraw : Measure.hausdorffMeasure ((n - 1 : ℕ) : ℝ) T = 0 := by
    simpa only [NNReal.coe_natCast] using
      hausdorffMeasure_of_dimH_lt (d := (n - 1 : ℕ)) hT
  have hnorm : (Measure.euclideanHausdorffMeasure (n - 1) : Measure (Space n)) T = 0 := by
    simp only [Measure.euclideanHausdorffMeasure, Measure.smul_apply, hraw, smul_zero]
  exact le_antisymm ((Measure.restrict_apply_le S T).trans_eq hnorm) zero_le

theorem surfaceMeasure_zero_of_singular_dim {n : ℕ} (hn : 8 ≤ n)
    (S T : Set (Space n)) (hT : dimH T ≤ (n - 8 : ℕ)) : surfaceMeasure S T = 0 := by
  apply surfaceMeasure_zero_of_dimH_lt S T
  apply hT.trans_lt
  exact_mod_cast (show n - 8 < n - 1 by omega)

theorem contact_measure_zero {n : ℕ} (S S' Z : Set (Space n))
    (hS : MeasurableSet S') (hcontact : S ∩ S' ⊆ Z)
    (hZ : dimH Z < (n - 1 : ℕ)) (U : Set (Space n)) :
    (surfaceMeasure S).restrict U S' = 0 := by
  have hbase : surfaceMeasure S S' = 0 := by
    rw [surfaceMeasure, Measure.restrict_apply hS]
    have hraw : Measure.hausdorffMeasure ((n - 1 : ℕ) : ℝ) Z = 0 := by
      simpa only [NNReal.coe_natCast] using
        hausdorffMeasure_of_dimH_lt (d := (n - 1 : ℕ)) hZ
    have hnorm : (Measure.euclideanHausdorffMeasure (n - 1) : Measure (Space n)) Z = 0 := by
      simp only [Measure.euclideanHausdorffMeasure, Measure.smul_apply, hraw, smul_zero]
    apply le_antisymm _ zero_le
    apply (measure_mono ?_).trans_eq hnorm
    exact fun x hx ↦ hcontact ⟨hx.2, hx.1⟩
  exact le_antisymm ((Measure.restrict_apply_le U S').trans_eq hbase) zero_le

noncomputable def tangentPlane {n : ℕ} (S : Set (Space n)) (x : Space n) :
    Submodule ℝ (Space n) :=
  Submodule.span ℝ {v | ∃ γ : ℝ → Space n,
    γ 0 = x ∧ HasDerivAt γ v 0 ∧ ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ S}

noncomputable def surfaceGradient {n : ℕ} (S : Set (Space n))
    (f : Space n → ℝ) (x : Space n) : Space n :=
  ((tangentPlane S x).orthogonalProjectionOnto (gradient f x) : Space n)

def smoothGradientGraph {n : ℕ} (S U : Set (Space n)) :
    Set (Lp ℝ 2 ((surfaceMeasure S).restrict U) ×
         Lp (Space n) 2 ((surfaceMeasure S).restrict U)) :=
  {z | ∃ f : Space n → ℝ, ContDiff ℝ ∞ f ∧
    ∃ hf : MemLp f 2 ((surfaceMeasure S).restrict U),
    ∃ hDf : MemLp (surfaceGradient S f) 2 ((surfaceMeasure S).restrict U),
      z = (hf.toLp f, hDf.toLp (surfaceGradient S f))}

def IsLocalSobolevPair {n : ℕ} (S U : Set (Space n))
    (h : Space n → ℝ) (G : Space n → Space n) : Prop :=
  ∀ V : Set (Space n), IsOpen V → IsCompact (closure V) → closure V ⊆ U →
    ∃ hh : MemLp h 2 ((surfaceMeasure S).restrict V),
    ∃ hG : MemLp G 2 ((surfaceMeasure S).restrict V),
      (hh.toLp h, hG.toLp G) ∈ closure (smoothGradientGraph S V)

def IsWeakLaplaceSupersolution {n : ℕ} (S U : Set (Space n))
    (h : Space n → ℝ) (G : Space n → Space n) : Prop :=
  IsLocalSobolevPair S U h G ∧
    ∀ φ : Space n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x) →
      Integrable (fun x ↦ inner ℝ (G x) (surfaceGradient S φ x)) (surfaceMeasure S) ∧
      0 ≤ ∫ x, inner ℝ (G x) (surfaceGradient S φ x) ∂surfaceMeasure S

end Boundary
end RPI

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
namespace RPI.Boundary

theorem surfaceGradient_congr_trace {n : ℕ} {S : Set (Space n)}
    {f g : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (heq : ∀ᶠ y in 𝓝 x, y ∈ S → f y = g y) :
    surfaceGradient S f x = surfaceGradient S g x := by
  have hker : tangentPlane S x ≤ (fderiv ℝ f x - fderiv ℝ g x).ker := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨γ, hγx, hγd, hγS⟩ := hv
    have hfe : HasDerivAt (f ∘ γ) (fderiv ℝ f x v) 0 := by
      exact (show HasFDerivAt f (fderiv ℝ f x) (γ 0) by
        simpa only [hγx] using hf.hasFDerivAt).comp_hasDerivAt 0 hγd
    have hge : HasDerivAt (g ∘ γ) (fderiv ℝ g x v) 0 := by
      exact (show HasFDerivAt g (fderiv ℝ g x) (γ 0) by
        simpa only [hγx] using hg.hasFDerivAt).comp_hasDerivAt 0 hγd
    have hcomp : (f ∘ γ) =ᶠ[𝓝 (0 : ℝ)] (g ∘ γ) := by
      have ht : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := hγx ▸ hγd.continuousAt
      filter_upwards [ht.eventually heq, hγS] with t ht hS
      exact ht hS
    have hd : fderiv ℝ f x v = fderiv ℝ g x v :=
      hfe.unique (hge.congr_of_eventuallyEq hcomp)
    change fderiv ℝ f x v - fderiv ℝ g x v = 0
    exact sub_eq_zero.mpr hd
  have ho : gradient f x - gradient g x ∈ (tangentPlane S x)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hk := hker hv
    change fderiv ℝ f x v - fderiv ℝ g x v = 0 at hk
    simpa only [inner_sub_right, inner_gradient_right, starRingEnd_apply, star_trivial] using hk
  have hp := (Submodule.orthogonalProjectionOnto_eq_zero_iff).mpr ho
  have hp' : (tangentPlane S x).orthogonalProjectionOnto (gradient f x) =
      (tangentPlane S x).orthogonalProjectionOnto (gradient g x) := by
    simpa only [map_sub, sub_eq_zero] using hp
  exact congrArg Subtype.val hp'

def HasSmoothTraceAt {n : ℕ} (S : Set (Space n)) (h : Space n → ℝ)
    (x : Space n) : Prop :=
  ∃ U : Set (Space n), IsOpen U ∧ x ∈ U ∧ ∃ f : Space n → ℝ,
    ContDiffOn ℝ ∞ f U ∧ EqOn f h (S ∩ U)

theorem exists_contDiff_eqOn_of_local_trace {n : ℕ} {S : Set (Space n)}
    (hS : IsClosed S) (h : Space n → ℝ)
    (hloc : ∀ x ∈ S, HasSmoothTraceAt S h x) :
    ∃ f : Space n → ℝ, ContDiff ℝ ∞ f ∧ EqOn f h S := by
  classical
  let t : Space n → Set ℝ := fun x ↦ if x ∈ S then {h x} else univ
  have hc : ∀ x, Convex ℝ (t x) := by
    intro x
    dsimp [t]
    split_ifs
    · exact convex_singleton _
    · exact convex_univ
  have hlocal : ∀ x : Space n, ∃ U ∈ 𝓝 x, ∃ g : Space n → ℝ,
      ContMDiffOn (modelWithCornersSelf ℝ (Space n)) (modelWithCornersSelf ℝ ℝ) ∞ g U ∧
      ∀ y ∈ U, g y ∈ t y := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨U, hU, hxU, f, hf, he⟩ := hloc x hx
      refine ⟨U, hU.mem_nhds hxU, f, hf.contMDiffOn, ?_⟩
      intro y hy
      by_cases hys : y ∈ S
      · simpa only [t, ite_eq_left hys, mem_singleton_iff] using he ⟨hys, hy⟩
      · simp only [t, ite_eq_right hys, mem_univ]
    · refine ⟨Sᶜ, hS.isOpen_compl.mem_nhds hx, fun _ ↦ 0, contMDiffOn_const, ?_⟩
      intro y hy
      simp only [t, ite_eq_right hy, mem_univ]
  obtain ⟨f, hf⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (modelWithCornersSelf ℝ (Space n)) (n := (⊤ : ℕ∞)) hc hlocal
  refine ⟨f, f.contMDiff.contDiff, ?_⟩
  intro x hx
  simpa only [t, ite_eq_left hx, mem_singleton_iff] using hf x

def HasSmoothTraceJetAt {n : ℕ} (S : Set (Space n)) (h : Space n → ℝ)
    (G : Space n → Space n) (x : Space n) : Prop :=
  ∃ U : Set (Space n), IsOpen U ∧ x ∈ U ∧ ∃ f : Space n → ℝ,
    ContDiffOn ℝ ∞ f U ∧ EqOn f h (S ∩ U) ∧ surfaceGradient S f x = G x

lemma HasSmoothTraceJetAt.trace {n : ℕ} {S : Set (Space n)} {h : Space n → ℝ}
    {G : Space n → Space n} {x : Space n} (hx : HasSmoothTraceJetAt S h G x) :
    HasSmoothTraceAt S h x := by
  obtain ⟨U, hU, hxU, f, hf, he, _⟩ := hx
  exact ⟨U, hU, hxU, f, hf, he⟩

theorem surfaceGradient_mul {n : ℕ} {S : Set (Space n)}
    {f g : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    surfaceGradient S (fun y ↦ f y * g y) x =
      f x • surfaceGradient S g x + g x • surfaceGradient S f x := by
  have hgrad : gradient (fun y ↦ f y * g y) x =
      f x • gradient g x + g x • gradient f x := by
    apply (InnerProductSpace.toDual ℝ (Space n)).injective
    simp only [map_add, map_smul, toDual_gradient]
    exact fderiv_mul hf hg
  simp only [surfaceGradient, hgrad, map_add, map_smul, Submodule.coe_add,
    Submodule.coe_smul]

@[simp] theorem surfaceGradient_const {n : ℕ} (S : Set (Space n))
    (c : ℝ) (x : Space n) : surfaceGradient S (fun _ ↦ c) x = 0 := by
  simp only [surfaceGradient, gradient_fun_const, map_zero, Submodule.coe_zero]

theorem exists_smooth_cutoff_trace {n : ℕ} {S Z : Set (Space n)}
    (hS : IsClosed S) {h : Space n → ℝ} {G : Space n → Space n}
    (hreg : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S h G x)
    (χ : Space n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hzero : ∃ U : Set (Space n), IsOpen U ∧ Z ⊆ U ∧ ∀ x ∈ U, χ x = 0) :
    ∃ F : Space n → ℝ, ContDiff ℝ ∞ F ∧ EqOn F (fun x ↦ χ x * h x) S ∧
      EqOn (surfaceGradient S F)
        (fun x ↦ χ x • G x + h x • surfaceGradient S χ x) S := by
  have hj : ∀ x ∈ S, HasSmoothTraceJetAt S (fun x ↦ χ x * h x)
      (fun x ↦ χ x • G x + h x • surfaceGradient S χ x) x := by
    intro x hx
    by_cases hxZ : x ∈ Z
    · obtain ⟨U, hU, hZU, he⟩ := hzero
      have hxU := hZU hxZ
      refine ⟨U, hU, hxU, fun _ ↦ 0, contDiffOn_const, ?_, ?_⟩
      · intro y hy
        simp only [he y hy.2, zero_mul]
      · have hχgrad : gradient χ x = 0 := by
          have heq : χ =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
            filter_upwards [hU.mem_nhds hxU] with y hy using he y hy
          simpa only [gradient_fun_const] using heq.gradient_eq
        simp only [he x hxU, zero_smul, surfaceGradient, gradient_fun_const,
          hχgrad, map_zero, Submodule.coe_zero, smul_zero, add_zero]
    · obtain ⟨U, hU, hxU, f, hf, he, hG⟩ := hreg x ⟨hx, hxZ⟩
      refine ⟨U, hU, hxU, fun y ↦ χ y * f y, hχ.contDiffOn.mul hf, ?_, ?_⟩
      · intro y hy
        exact congrArg (fun a ↦ χ y * a) (he hy)
      · rw [surfaceGradient_mul (hχ.differentiable (by simp) x)
            ((hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)),
          hG, he ⟨hx, hxU⟩]
  obtain ⟨F, hF, hFe⟩ := exists_contDiff_eqOn_of_local_trace hS
    (fun x ↦ χ x * h x) (fun x hx ↦ (hj x hx).trace)
  refine ⟨F, hF, hFe, ?_⟩
  intro x hx
  obtain ⟨U, hU, hxU, f, hf, he, hG⟩ := hj x hx
  calc
    surfaceGradient S F x = surfaceGradient S f x := by
      apply surfaceGradient_congr_trace (hF.differentiable (by simp) x)
        ((hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp))
      filter_upwards [hU.mem_nhds hxU] with y hy
      intro hys
      exact (hFe hys).trans (he ⟨hys, hy⟩).symm
    _ = _ := hG

end RPI.Boundary

end

end OAI
