import OAI.Geometry.Kahler.BaseChartNormalization

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma base_matrix_value_bound {H : Matrix (Fin 2) (Fin 2) ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hH : ∀ i j, ‖H i j‖ ≤ C) (v : Base) :
    (∑ i, ∑ j, H i j*v i*star (v j)).re ≤ 4*C*‖v‖^2 := by
  calc
    (∑ i, ∑ j, H i j*v i*star (v j)).re ≤ ‖∑ i, ∑ j, H i j*v i*star (v j)‖ := Complex.re_le_norm _
    _ ≤ ∑ i, ∑ j, ‖H i j*v i*star (v j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, C*‖v‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul,norm_mul,norm_star,pow_two, ← mul_assoc]
      apply mul_le_mul (mul_le_mul (hH i j) (PiLp.norm_apply_le v i) (norm_nonneg _) hC)
        (PiLp.norm_apply_le v j) (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
    _ = 4*C*‖v‖^2 := by simp; ring

lemma norm_jet_add_mul {f g : Base → ℝ} {z : Base}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => f x+L*g x) z‖ ≤
      ‖iteratedFDeriv ℝ n f z‖ + L*‖iteratedFDeriv ℝ n g z‖ := by
  rw [iteratedFDeriv_add_mul hf hg]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hL])

lemma basePotential_chart_control (a : ℝ) {ε D L : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D) (hL : 0 ≤ L)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))) :
    ∃ C : ℝ, ChartControl (basePotential P a ε L Q) 1 C ∧ ChartJets (basePotential P a ε L Q) C := by
  let f : Base → ℝ := fun z => ∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) z
  have hf : ContDiffOn ℝ ∞ f ball := testSeries_contDiffOn a he hD hQ P hP
  obtain ⟨C₂,hC₂,hb₂⟩ := testSeries_chart_uniform_jets a he hD hQ P hP (by norm_num : 1 ≤ (2:ℕ))
  obtain ⟨C₃,hC₃,hb₃⟩ := testSeries_chart_uniform_jets a he hD hQ P hP (by norm_num : 1 ≤ (3:ℕ))
  obtain ⟨C₄,hC₄,hb₄⟩ := testSeries_chart_uniform_jets a he hD hQ P hP (by norm_num : 1 ≤ (4:ℕ))
  let B₂ := ‖iteratedFDeriv ℝ 2 psi (0:Base)‖+L*C₂
  let B₃ := ‖iteratedFDeriv ℝ 3 psi (0:Base)‖+L*C₃
  let B₄ := ‖iteratedFDeriv ℝ 4 psi (0:Base)‖+L*C₄
  have hB₂ : 0 ≤ B₂ := add_nonneg (norm_nonneg _) (mul_nonneg hL hC₂)
  have hB₃ : 0 ≤ B₃ := add_nonneg (norm_nonneg _) (mul_nonneg hL hC₃)
  have hB₄ : 0 ≤ B₄ := add_nonneg (norm_nonneg _) (mul_nonneg hL hC₄)
  let C := 1+4*B₂+2*B₃+B₄
  refine ⟨C,?_,?_⟩
  · intro r hr hr1 U v
    have hfg := chartWeight_contDiffAt hf hr hr1 U
    have hψ := psi_contDiffAt zero_mem_ball
    have hm : ContDiffAt ℝ ∞ (fun z => psi z+L*f (centeredChart r U z)) 0 :=
      hψ.add (contDiffAt_const.mul hfg)
    have hn := baseHessian_chart_normalize hf L hr hr1 U
    change baseHessian (basePotential P a ε L Q ∘ centeredChart r U) =ᶠ[𝓝 (0:Base)]
      baseHessian (fun z => psi z+L*f (centeredChart r U z)) at hn
    have heq := hn.self_of_nhds
    rw [heq]
    constructor
    · have hpsh := testSeries_chart_psh a he hD hQ P hP hr hr1 U v
      erw [baseHessian_value_eq_jet hm,iteratedFDeriv_add_mul hψ hfg,map_add,map_smul,
        ← baseHessian_value_eq_jet hψ, ← baseHessian_value_eq_jet hfg,psi_baseHessian_value]
      simp only [smul_eq_mul,one_mul]
      exact le_add_of_nonneg_right (mul_nonneg hL hpsh)
    · have hb : ‖iteratedFDeriv ℝ 2 (fun z => psi z+L*f (centeredChart r U z)) 0‖ ≤ B₂ :=
        (norm_jet_add_mul hψ hfg hL 2).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hb₂ r hr hr1 U) hL))
      exact (base_matrix_value_bound hB₂ (fun i j => (norm_baseHessian_le hm i j).trans hb) v).trans
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _))
  · intro r hr hr1 U i j k l
    have hfg := chartWeight_contDiffAt hf hr hr1 U
    have hψ := psi_contDiffAt zero_mem_ball
    have hm : ContDiffAt ℝ ∞ (fun z => psi z+L*f (centeredChart r U z)) 0 :=
      hψ.add (contDiffAt_const.mul hfg)
    have hn := baseHessian_chart_normalize hf L hr hr1 U
    change baseHessian (basePotential P a ε L Q ∘ centeredChart r U) =ᶠ[𝓝 (0:Base)]
      baseHessian (fun z => psi z+L*f (centeredChart r U z)) at hn
    obtain ⟨hdz,hdbar,hdd⟩ := baseHessian_congr_derivatives hn i j k l
    rw [hdz,hdbar,hdd]
    have hb3 : ‖iteratedFDeriv ℝ 3 (fun z => psi z+L*f (centeredChart r U z)) 0‖ ≤ B₃ :=
      (norm_jet_add_mul hψ hfg hL 3).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hb₃ r hr hr1 U) hL))
    have hb4 : ‖iteratedFDeriv ℝ 4 (fun z => psi z+L*f (centeredChart r U z)) 0‖ ≤ B₄ :=
      (norm_jet_add_mul hψ hfg hL 4).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hb₄ r hr hr1 U) hL))
    exact (norm_baseHessian_derivatives_le hm i j k l).trans (by dsimp only [C]; linarith)

end PinchedHartogs.BaseConstruction

end

end OAI
