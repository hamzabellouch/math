import Mathlib
import OAI.Analysis.Conductivity.Variational.CompletedPotential
import OAI.Analysis.Conductivity.Variational.SynchronizedChartWaves
import OAI.Analysis.Conductivity.Variational.RepairPushedGraphStability

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
open Matrix Set Filter Topology MeasureTheory
open scoped Matrix.Norms.Elementwise

def splitJacobian (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (c z : ℝ) : Mat3 :=
  operatorMatrix (ContinuousLinearMap.id ℝ Coord3 + lineShiftGradientOperator d c (z • L))

lemma splitJacobian_continuous (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (c : ℝ) :
    Continuous (splitJacobian d L c) :=
  operatorMatrix_continuous.comp (continuous_const.add
    ((lineShiftGradientOperator d c).continuous.comp (continuous_id.smul continuous_const)))

lemma matrix_two_pairing_symm (E F : Matrix (Fin 3) (Fin 2) ℝ)
    (h : (Eᵀ * F) 1 0 = (Eᵀ * F) 0 1) : (Eᵀ * F).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all [Matrix.transpose_apply]

theorem exists_local_two_field_split
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {p : Coord3} (hA : ContinuousAt A p)
    (hD : Function.Surjective (fderiv ℝ u p))
    (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (hLd : L d = 1)
    (B : Mat3) (hB : B.IsSymm) (hBn : ∀ v, L (B *ᵥ v) = 0)
    {a b c m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hm : 0 < m) (hpath : ∀ z ∈ Icc (-a) b, m ≤ 1 + c * z)
    (C : ℝ → Symmetric3) (hC : ∀ z ∈ Icc (-a) b, ContinuousAt C z)
    (hdet : ∀ z ∈ Icc (-a) b, 0 < (splitJacobian d L c z).det)
    (hconstit : ∀ z ∈ Icc (-a) b,
      (C z).val = (splitJacobian d L c z).det⁻¹ •
        (splitJacobian d L c z * ((A p).val + z • B) * (splitJacobian d L c z)ᵀ))
    {G : Set (ℝ × Symmetric3)} (hG : IsOpen G)
    (hCG : ∀ z ∈ Icc (-a) b, (z, C z) ∈ G)
    {U : Set Coord3} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ (X : OpenPartialHomeomorph Coord3 Coord3) (V : Set Coord3),
      IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ V ⊆ X.source ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target ∧
      ∃ M : ℝ, 0 < M ∧
      ∀ H : SmoothScalar ℝ, Function.Periodic (smoothDirection 1 H).val 1 →
        (∫ t in (0 : ℝ)..1, (smoothDirection 1 H).val t = 0) →
        (∃ B : ℝ, ∀ t, |H.val t| ≤ B) →
        (∀ t, -a ≤ (smoothDirection 1 H).val t ∧ (smoothDirection 1 H).val t ≤ b) →
      ∀ χ : SmoothScalar Coord3, HasCompactSupport χ.val → tsupport χ.val ⊆ X '' V →
        (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) →
        ∃ F : ℝ → Fin 2 → Coord3 → Coord3,
          (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
          (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ V ∧
            tsupport (F k j) ⊆ X.symm '' tsupport χ.val) ∧
          (∀ k j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
            (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
          ∀ᶠ k : ℝ in atTop, ∃ Y : Coord3 ≃ Coord3,
            ContDiff ℝ (↑(⊤ : ℕ∞)) Y ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm ∧
            (∀ x ∉ V, Y x = x) ∧ Y '' V = V ∧
            (∀ x, Y x = x + (c * k⁻¹ * localPullback X χ.val x *
              H.val (k * L (X x))) • d) ∧
            (∀ x, |(fderiv ℝ Y x).det| ≤ M) ∧
            ∀ x ∈ V,
              let z := localPullback X χ.val x * (smoothDirection 1 H).val (k * L (X x))
              let E := gradientColumns (fderiv ℝ u x)
              let Ft : Matrix (Fin 3) (Fin 2) ℝ := (A x).val * E + Matrix.of (fun i j => F k j x i)
              let J := operatorMatrix (fderiv ℝ Y x)
              let At := repairPushed (C z) J E Ft
              0 < J.det ∧ LinearIndependent ℝ E.col ∧ (z, At) ∈ G ∧
                At.val * gradientColumns (fderiv ℝ (u ∘ Y.symm) (Y x)) = pushFlux J Ft := by
  classical
  let D := fderiv ℝ u p
  let E₀ := gradientColumns D
  let E : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun y => gradientColumns (fderiv ℝ u y)
  let F₀ := (A p).val * E₀
  let Fe : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun y => (A y).val * E y
  let J := splitJacobian d L c
  let Fb : ℝ → Matrix (Fin 3) (Fin 2) ℝ := fun z => ((A p).val + z • B) * E₀
  have hEc : Continuous E := by
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    exact (continuous_apply j).comp ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hFc : ContinuousAt Fe p := matrix_mul_contAt (continuousAt_subtype_val.comp hA) hEc.continuousAt
  have hFbc : Continuous Fb := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact matrix_mul_contAt (continuousAt_const.add (continuousAt_id.smul continuousAt_const)) continuousAt_const
  have hrank : LinearIndependent ℝ E₀.col := gradientColumns_rank D hD
  have hexact : ∀ z ∈ Icc (-a) b, repairPushed (C z) (J z) E₀ (Fb z) = C z := by
    intro z hz
    exact repairPushed_exact (C z) (J z) ((A p).val + z • B) E₀ (hdet z hz).ne' (hconstit z hz)
  obtain ⟨O, _, hKO, ε, hε, heps⟩ := repairPushed_graph_stability isCompact_Icc
    C J (fun _ => E₀) Fb hC (fun _ _ => (splitJacobian_continuous d L c).continuousAt)
    (fun _ _ => continuousAt_const) (fun _ _ => hFbc.continuousAt) hdet (fun _ _ => hrank) hG
    (fun z hz => by rw [hexact z hz]; exact hCG z hz)
  have hnb : ∀ᶠ x in 𝓝 p, ‖E x - E₀‖ < ε/2 ∧ ‖Fe x - F₀‖ < ε/2 := by
    have he := hEc.continuousAt.eventually (Metric.ball_mem_nhds (E p) (half_pos hε))
    have hf := hFc.eventually (Metric.ball_mem_nhds (Fe p) (half_pos hε))
    simpa only [Metric.mem_ball, dist_eq_norm] using he.and hf
  obtain ⟨W, hWb, hWo, hpW⟩ := mem_nhds_iff.mp hnb
  obtain ⟨X, hpX, hXs, hX, hXi, hXu, hDX⟩ := exists_potential_chart hu p hD
    (hU.inter hWo) ⟨hpU, hpW⟩
  have hpol := symmetric_wave_polarization D B hB L hBn
  obtain ⟨V, hV, hpV, hVs, hpert⟩ := exists_synchronized_chart_waves
    (by simp [Coord3]) μ X hX hXi D hD u (fun y _ => hXu y)
    hpX hDX d L hLd ha hb ha1 hb1 hm (by positivity : 0 < ε/2)
    hpath (B * E₀).col hpol.1 hpol.2
  obtain ⟨M, hM, hMbd⟩ := synchronized_det_bound d c L (ε/2)
  refine ⟨X, V, hV, hpV, hVs.trans (fun _ hx => (hXs hx).1), hVs, hX, hXi, M, hM, ?_⟩
  intro H hHp hHm hH hHr χ hχ hχV hχb
  obtain ⟨F, hF, hFs, hsym, hdiv, hlim⟩ := hpert H hHp hHm hH hHr χ hχ hχV hχb
  refine ⟨F, hF, hFs, hdiv, ?_⟩
  filter_upwards [hlim] with k hk
  obtain ⟨Y, hY, hYi, hoff, himage, hform, hFerr, hJerr⟩ := hk
  refine ⟨Y, hY, hYi, hoff, himage, hform, ?_, ?_⟩
  · intro x
    apply hMbd _ _ _ (hJerr x).le
    have hz := scalar_cutoff_segment ha hb (localPullback_bounds X χ.val hχb x) (hHr (k * L (X x)))
    exact abs_le.mpr ⟨by linarith only [hz.1, ha1], by linarith only [hz.2, hb1]⟩
  intro x hx
  let z := localPullback X χ.val x * (smoothDirection 1 H).val (k * L (X x))
  let Q : Matrix (Fin 3) (Fin 2) ℝ := fun i j => F k j x i
  let Jy := operatorMatrix (fderiv ℝ Y x)
  have hz : z ∈ Icc (-a) b := scalar_cutoff_segment ha hb
    (localPullback_bounds X χ.val hχb x) (hHr _)
  have hsmall := hWb (hXs (hVs hx)).2
  have hdJ : ‖Jy - J z‖ < ε/2 := by
    change ‖operatorMatrix (fderiv ℝ Y x) - operatorMatrix _‖ < ε/2
    rw [← operatorMatrix_sub]
    exact (operatorMatrix_norm_le _).trans_lt (hJerr x)
  have hdF : ‖Fe x + Q - Fb z‖ < ε := by
    have hq : ‖Q - z • (B * E₀)‖ < ε/2 := by
      apply columns_norm_lt _ (half_pos hε)
      intro j
      exact hFerr j x
    have heq : Fe x + Q - Fb z = (Fe x - F₀) + (Q - z • (B * E₀)) := by
      dsimp only [Fb, F₀]
      rw [Matrix.add_mul, Matrix.smul_mul]
      abel
    rw [heq]
    exact (norm_add_le _ _).trans_lt (by linarith only [hq, hsmall.2])
  have hbound : ‖(Jy - J z, E x - E₀, Fe x + Q - Fb z)‖ < ε := by
    rw [Prod.norm_def, Prod.norm_def, max_lt_iff, max_lt_iff]
    exact ⟨hdJ.trans (by linarith), hsmall.1.trans (by linarith), hdF⟩
  have hs := heps z (hKO hz) (Jy - J z) (E x - E₀) (Fe x + Q - Fb z) hbound
  simp only [add_sub_cancel] at hs
  refine ⟨hs.1, hs.2.1, hs.2.2, ?_⟩
  rw [gradientColumns_recomposition Y (hY.differentiable (by simp))
    (hYi.differentiable (by simp)) u (hu.differentiable (by simp))]
  apply repairPushed_mul _ _ _ _ hs.1.ne' hs.2.1
  rw [Matrix.mul_add]
  apply (symmetric_gram_pairing (A x) (E x)).add
  apply matrix_two_pairing_symm
  rw [← gradientColumns_pairing, ← gradientColumns_pairing]
  exact hsym k x

end ScalarConductivity

end

end OAI
