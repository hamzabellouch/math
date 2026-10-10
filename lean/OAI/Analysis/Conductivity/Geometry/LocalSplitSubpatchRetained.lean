import Mathlib
import OAI.Analysis.Conductivity.Variational.PairedPotential
import OAI.Analysis.Conductivity.Sobolev.LocalPullbackTsupportInside

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped ENNReal Matrix.Norms.Elementwise
theorem exists_local_split_on_subpatch_retained
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {p : Coord3} (hA : ContinuousAt A p)
    (hD : Function.Surjective (fderiv ℝ u p))
    (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (hLd : L d = 1)
    (B : Mat3) (hB : B.IsSymm) (hBn : ∀ v, L (B *ᵥ v) = 0)
    {θ c m : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hm : 0 < m) (hpath : ∀ z ∈ Icc (-θ) (1-θ), m ≤ 1 + c * z)
    (C : ℝ → Symmetric3) (hC : ∀ z ∈ Icc (-θ) (1-θ), ContinuousAt C z)
    (hdet : ∀ z ∈ Icc (-θ) (1-θ), 0 < (splitJacobian d L c z).det)
    (hconstit : ∀ z ∈ Icc (-θ) (1-θ),
      (C z).val = (splitJacobian d L c z).det⁻¹ •
        (splitJacobian d L c z * ((A p).val + z • B) * (splitJacobian d L c z)ᵀ))
    {G : Set (ℝ × Symmetric3)} (hG : IsOpen G)
    (hCG : ∀ z ∈ Icc (-θ) (1-θ), (z, C z) ∈ G)
    {U : Set Coord3} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ (X : OpenPartialHomeomorph Coord3 Coord3) (W : Set Coord3),
      IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧ W ⊆ X.source ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W →
      ∀ ε : ℝ, 0 < ε →
      ∃ (χ : SmoothScalar Coord3) (H : SmoothScalar ℝ) (F : ℝ → Fin 2 → Coord3 → Coord3),
        HasCompactSupport χ.val ∧ tsupport χ.val ⊆ X '' O ∧
        (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) ∧
        (∀ t, -θ ≤ (smoothDirection 1 H).val t ∧ (smoothDirection 1 H).val t ≤ 1-θ) ∧
        (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
        (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ O ∧ tsupport (F k j) ⊆ X.symm '' tsupport χ.val) ∧
        (∀ k j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
          (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
        ∀ᶠ n : ℕ in atTop, ∃ Y : Coord3 ≃ Coord3,
          ContDiff ℝ (↑(⊤ : ℕ∞)) Y ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm ∧
          (∀ x ∉ O, Y x = x) ∧ Y '' O = O ∧
          (∀ x, Y x = x + (c * (n+1 : ℝ)⁻¹ * localPullback X χ.val x *
            H.val ((n+1 : ℝ) * L (X x))) • d) ∧
          μ {x | x ∈ O ∧
            localPullback X χ.val (Y.symm x) *
              (smoothDirection 1 H).val ((n+1 : ℝ) * L (X (Y.symm x))) ≠ -θ ∧
            localPullback X χ.val (Y.symm x) *
              (smoothDirection 1 H).val ((n+1 : ℝ) * L (X (Y.symm x))) ≠ 1-θ} ≤
            ENNReal.ofReal ε ∧
          ∀ x ∈ O,
            let z := localPullback X χ.val x * (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x))
            let E := gradientColumns (fderiv ℝ u x)
            let Ft := (A x).val * E + Matrix.of (fun i j => F (n+1 : ℝ) j x i)
            let J := operatorMatrix (fderiv ℝ Y x)
            let At := repairPushed (C z) J E Ft
            0 < J.det ∧ LinearIndependent ℝ E.col ∧ (z, At) ∈ G ∧
              At.val * gradientColumns (fderiv ℝ (u ∘ Y.symm) (Y x)) = pushFlux J Ft := by
  have hb : 0 ≤ 1-θ := by linarith
  have hb1 : 1-θ ≤ 1 := by linarith
  obtain ⟨X, V, hV, hpV, hVU, hVX, hX, hXi, M, hM, hop⟩ :=
    exists_local_two_field_split μ u hu A hA hD d L hLd B hB hBn
      hθ.le hb hθ1.le hb1 hm hpath C hC hdet hconstit hG hCG hU hpU
  obtain ⟨W, hW, hpW, hWV, hWc, hXW, D, hDpos, hDb⟩ :=
    exists_bounded_chart_neighborhood X hX.continuous hXi hV hVX hpV
  have hWV' : W ⊆ V := subset_closure.trans hWV
  have hWX : W ⊆ X.source := hWV'.trans hVX
  have hL : L ≠ 0 := by intro hz; simp only [hz, _root_.zero_apply] at hLd; norm_num at hLd
  refine ⟨X, W, hW, hpW, hWV.trans hVU, hWc, hWX, hX, hXi, ?_⟩
  intro O hO hOW ε hε
  have hOX : O ⊆ X.source := hOW.trans hWX
  have hOV : O ⊆ V := hOW.trans hWV'
  have hXO := hXW.subset (image_mono hOW)
  obtain ⟨χ, H, hχc, hχW, hχb, hHp, hHm, hHb, hHr, hpure⟩ :=
    exists_chart_pure_profile μ X hO hOX (hXi.differentiableOn (by simp))
      hXO hXO.measure_lt_top.ne hDpos (fun x hx => hDb x (image_mono hOW hx)) L hL hθ hθ1 (div_pos hε hM)
  obtain ⟨F, hF, hFs, hdiv, hlim⟩ := hop H hHp hHm hHb hHr χ hχc
    (hχW.trans (image_mono hOV)) hχb
  have hχt : tsupport χ.val ⊆ X.target := hχW.trans (by
    rintro y ⟨x, hx, rfl⟩; exact X.map_source (hOX hx))
  have hχp : tsupport (localPullback X χ.val) ⊆ O :=
    localPullback_tsupport_inside X χ.val hχc hOX hχW
  refine ⟨χ, H, F, hχc, hχW, hχb, hHr, hF, ?_, hdiv, ?_⟩
  · intro k j
    refine ⟨(hFs k j).1, ?_, (hFs k j).2.2⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hFs k j).2.2 hx
    obtain ⟨z, hz, rfl⟩ := hχW hy
    simpa only [X.left_inv (hOX hz)] using hz
  have hnat : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually hlim, hpure] with n hn hnp
  obtain ⟨Y, hY, hYi, _, _, hform, hYM, hstate⟩ := hn
  have hoff : ∀ x ∉ O, Y x = x := by
    intro x hx
    have hz := image_eq_zero_of_notMem_tsupport (fun h => hx (hχp h))
    rw [hform x, hz, mul_zero, zero_mul, zero_smul, add_zero]
  have himage := equiv_image_set_of_eq_off Y O hoff
  refine ⟨Y, hY, hYi, hoff, himage, hform, ?_, fun x hx => hstate x (hOV hx)⟩
  let z : Coord3 → ℝ := fun x => localPullback X χ.val x *
    (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x))
  have hz : Continuous z :=
    (localPullback_contDiff X hX.contDiffOn χ.val (smoothScalar_contDiff χ) hχc hχt).continuous.mul
      ((smoothScalar_contDiff (smoothDirection 1 H)).continuous.comp
        (continuous_const.mul (L.continuous.comp hX.continuous)))
  have he := pushed_exception_measure_le μ Y (hY.differentiable (by simp))
    hO.measurableSet himage z hz (-θ) (1-θ) hYM
  calc
    _ ≤ ENNReal.ofReal M * μ {x | x ∈ O ∧ z x ≠ -θ ∧ z x ≠ 1-θ} := he
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal (ε/M) := mul_le_mul_right hnp _
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul hM.le, mul_div_cancel₀ ε hM.ne']

end ScalarConductivity

end

end OAI
