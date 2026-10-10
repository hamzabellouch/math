import Mathlib
import OAI.Analysis.Conductivity.Variational.DerivativeEquiv
import OAI.Analysis.Conductivity.Variational.CrossingHxx
import OAI.Analysis.Conductivity.Variational.GradientColumns
import OAI.Analysis.Conductivity.Flux.ChartTwoFluxLocalized
import OAI.Analysis.Conductivity.Variational.UniformNormBound

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

section
open Set Filter Topology MeasureTheory

theorem exists_synchronized_chart_waves
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : ContDiff ℝ (↑(⊤ : ℕ∞)) X)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (D : E →L[ℝ] (Fin 2 → ℝ)) (hD : Function.Surjective D)
    (u : E → Fin 2 → ℝ) (hu : ∀ y ∈ X.source, D (X y) = u y)
    {p : E} (hp : p ∈ X.source) (hDp : fderiv ℝ X p = ContinuousLinearMap.id ℝ E)
    (d : E) (L : E →L[ℝ] ℝ) (hLd : L d = 1)
    {a b c m ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hm : 0 < m) (hε : 0 < ε) (hpath : ∀ z ∈ Icc (-a) b, m ≤ 1 + c * z)
    (R : Fin 2 → E) (hRs : D (R 0) 1 = D (R 1) 0) (hRn : ∀ j, L (R j) = 0) :
    ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ V ⊆ X.source ∧
      ∀ H : SmoothScalar ℝ, Function.Periodic (smoothDirection 1 H).val 1 →
        (∫ t in (0 : ℝ)..1, (smoothDirection 1 H).val t = 0) →
        (∃ B : ℝ, ∀ t, |H.val t| ≤ B) →
        (∀ t, -a ≤ (smoothDirection 1 H).val t ∧ (smoothDirection 1 H).val t ≤ b) →
      ∀ χ : SmoothScalar E, HasCompactSupport χ.val → tsupport χ.val ⊆ X '' V →
        (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) →
        ∃ F : ℝ → Fin 2 → E → E,
          (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
          (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ V ∧
            tsupport (F k j) ⊆ X.symm '' tsupport χ.val) ∧
          (∀ k y, fderiv ℝ u y (F k 0 y) 1 = fderiv ℝ u y (F k 1 y) 0) ∧
          (∀ k j (ψ : E → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
            (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
          ∀ᶠ k : ℝ in atTop, ∃ Y : E ≃ E,
            ContDiff ℝ (↑(⊤ : ℕ∞)) Y ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm ∧
            (∀ x ∉ V, Y x = x) ∧ Y '' V = V ∧
            (∀ x, Y x = x + (c * k⁻¹ * localPullback X χ.val x *
              H.val (k * L (X x))) • d) ∧
            (∀ j x, ‖F k j x - (localPullback X χ.val x *
              (smoothDirection 1 H).val (k * L (X x))) • R j‖ < ε) ∧
            ∀ x, ‖fderiv ℝ Y x -
              (ContinuousLinearMap.id ℝ E + lineShiftGradientOperator d c
                ((localPullback X χ.val x * (smoothDirection 1 H).val (k * L (X x))) • L))‖ < ε := by
  have hL : L ≠ 0 := by intro hz; simp only [hz, _root_.zero_apply] at hLd; norm_num at hLd
  obtain ⟨W, hW, hpW, hWs, hflux⟩ := exists_frozen_chart_two_flux hdim μ X hX.contDiffOn hXi
    D hD u hu hp hDp L hL R hRs hRn hε
  let φ : SmoothScalar E := ⟨fun x => L (X x), L.contDiff.comp hX⟩
  have hφ : fderiv ℝ φ.val p = L := by
    change fderiv ℝ ((L : E → ℝ) ∘ (X : E → E)) p = L
    rw [fderiv_comp p L.differentiableAt (hX.differentiable (by simp) p), hDp]
    simp
  obtain ⟨V, hV, hpV, hVW, hmaps⟩ := exists_local_phase_diffeomorphisms d φ hφ hLd
    ha hb ha1 hb1 hm hε hpath hW hpW
  refine ⟨V, hV, hpV, hVW.trans hWs, ?_⟩
  intro H hHp hHm hH hHr χ hχ hχV hχb
  have hHabs : ∀ t, |(smoothDirection 1 H).val t| ≤ 1 := by
    intro t
    exact abs_le.mpr ⟨by linarith only [(hHr t).1, ha1], by linarith only [(hHr t).2, hb1]⟩
  have hχW : tsupport χ.val ⊆ X '' W := hχV.trans (image_mono hVW)
  have hχs : tsupport χ.val ⊆ X.target := hχW.trans (by
    rintro z ⟨x, hx, rfl⟩; exact X.map_source (hWs hx))
  let χp : SmoothScalar E := ⟨localPullback X χ.val,
    localPullback_contDiff X hX.contDiffOn χ.val (smoothScalar_contDiff χ) hχ hχs⟩
  have hχp : HasCompactSupport χp.val := (localPullback_tsupport X χ.val hχ hχs).1
  have hχpV : tsupport χp.val ⊆ V := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (localPullback_tsupport X χ.val hχ hχs).2.1 hy
    obtain ⟨w, hw, rfl⟩ := hχV hz
    simpa only [X.left_inv (hWs (hVW hw))] using hw
  have hbχ : ∀ x, 0 ≤ χp.val x ∧ χp.val x ≤ 1 := localPullback_bounds X χ.val hχb
  obtain ⟨F, hF, hFs, hsym, hdiv, he⟩ := hflux (smoothDirection 1 H) hHp hHm hHabs χ hχ hχW hχb
  have hFfine : ∀ k j, tsupport (F k j) ⊆ V := by
    intro k j y hy
    obtain ⟨z, hz, rfl⟩ := (hFs k j).2.2 hy
    obtain ⟨w, hw, rfl⟩ := hχV hz
    simpa only [X.left_inv (hWs (hVW hw))] using hw
  refine ⟨F, hF, fun k j => ⟨(hFs k j).1, hFfine k j, (hFs k j).2.2⟩, hsym, hdiv, ?_⟩
  filter_upwards [he, hmaps H hH hHr χp hχp hχpV hbχ] with k hk hmap
  obtain ⟨Y, hY, hYs, hYi, hoff, himage, hderiv⟩ := hmap
  refine ⟨Y, hYs, hYi, hoff, himage, ?_, hk, hderiv⟩
  intro x
  rw [hY]
  change x + (c * (k⁻¹ * (localPullback X χ.val x * H.val (k * L (X x))))) • d = _
  congr 2
  ring

end

open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

abbrev Coord3 := Fin 3 → ℝ

def operatorMatrix {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : (n → ℝ) →L[ℝ] (m → ℝ)) : Matrix m n ℝ :=
  LinearMap.toMatrix' D.toLinearMap

lemma operatorMatrix_norm_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : (n → ℝ) →L[ℝ] (m → ℝ)) : ‖operatorMatrix D‖ ≤ ‖D‖ := by
  apply Matrix.norm_le_iff (norm_nonneg D) |>.mpr
  intro i j
  exact (norm_le_pi_norm (D (Pi.single j 1)) i).trans (by
    simpa only [Pi.norm_single, norm_one, mul_one] using D.le_opNorm (Pi.single j 1))

lemma operatorMatrix_sub {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D E : (n → ℝ) →L[ℝ] (m → ℝ)) :
    operatorMatrix (D - E) = operatorMatrix D - operatorMatrix E := by
  ext i j; rfl

lemma operatorMatrix_comp {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq n] [DecidableEq r]
    (D : (n → ℝ) →L[ℝ] (m → ℝ)) (E : (r → ℝ) →L[ℝ] (n → ℝ)) :
    operatorMatrix (D.comp E) = operatorMatrix D * operatorMatrix E :=
  LinearMap.toMatrix'_comp D.toLinearMap E.toLinearMap

lemma operatorMatrix_id : operatorMatrix (ContinuousLinearMap.id ℝ Coord3) = 1 :=
  LinearMap.toMatrix'_id

lemma operatorMatrix_det (D : Coord3 →L[ℝ] Coord3) : (operatorMatrix D).det = D.det :=
  LinearMap.det_toMatrix' D.toLinearMap

lemma operatorMatrix_mulVec {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : (n → ℝ) →L[ℝ] (m → ℝ)) (v : n → ℝ) : operatorMatrix D *ᵥ v = D v :=
  LinearMap.toMatrix'_mulVec D.toLinearMap v

lemma operatorMatrix_continuous {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] :
    Continuous (operatorMatrix : ((n → ℝ) →L[ℝ] (m → ℝ)) → Matrix m n ℝ) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  exact (continuous_apply i).comp (continuous_id.clm_apply continuous_const)

lemma columns_norm_lt {m : Type*} [Fintype m] (F : Matrix (Fin 3) m ℝ)
    {ε : ℝ} (hε : 0 < ε) (h : ∀ j, ‖F.col j‖ < ε) : ‖F‖ < ε := by
  apply (Matrix.norm_lt_iff hε).mpr
  intro i j
  exact (norm_le_pi_norm (F.col j) i).trans_lt (h j)

lemma operatorMatrix_inverse_fderiv (X : Coord3 ≃ Coord3)
    (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm) (x : Coord3) :
    operatorMatrix (fderiv ℝ X.symm (X x)) = (operatorMatrix (fderiv ℝ X x))⁻¹ := by
  have h := fderiv_equiv_symm_comp X hX hXi x
  have hm := congrArg operatorMatrix h
  rw [operatorMatrix_comp, operatorMatrix_id] at hm
  exact Matrix.inv_eq_left_inv hm |>.symm

lemma gradientColumns_recomposition (X : Coord3 ≃ Coord3)
    (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm)
    (u : Coord3 → Fin 2 → ℝ) (hu : Differentiable ℝ u) (x : Coord3) :
    gradientColumns (fderiv ℝ (u ∘ X.symm) (X x)) =
      pushGradient (operatorMatrix (fderiv ℝ X x)) (gradientColumns (fderiv ℝ u x)) := by
  rw [fderiv_comp (X x) (hu _) (hXi _), X.symm_apply_apply]
  change (operatorMatrix ((fderiv ℝ u x).comp (fderiv ℝ X.symm (X x))))ᵀ = _
  rw [operatorMatrix_comp, Matrix.transpose_mul, operatorMatrix_inverse_fderiv X hX hXi]
  rfl

lemma piolaFlux_columns (X : Coord3 ≃ Coord3) (F : Coord3 → Matrix (Fin 3) (Fin 2) ℝ)
    {x : Coord3} (hdet : 0 < (fderiv ℝ X x).det) (j : Fin 2) :
    piolaFlux X (fun y => (F y).col j) (X x) =
      (pushFlux (operatorMatrix (fderiv ℝ X x)) (F x)).col j := by
  simp only [piolaFlux, X.symm_apply_apply, pushFlux, operatorMatrix_det,
    abs_of_pos hdet]
  congr 1
  exact (operatorMatrix_mulVec (fderiv ℝ X x) ((F x).col j)).symm

end ScalarConductivity

end

end OAI
