import OAI.NumberTheory.Ostmann.Supply.LocalKernelBlocks

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

theorem kernelScalar_distance_le (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ)
    (hlo : (1/3:ℝ)  ≤  density S) (hhi : density S  ≤  2/3) :
    ‖kernelScalar S t u v-1‖  ≤  ‖(u+v)*(t:ℂ)‖/(p:ℝ) +
      ‖u*v‖*(4*‖squaredLocalKernelOperator S t‖/(p:ℝ)) := by
  rw [kernelScalar_expansion S t u v (balanced_nonempty _ hlo)
    (balanced_nonempty _ (balanced_compl S hlo hhi).1)]
  have he (a b : ℂ) : 1+a+b-1 = a+b := by ring
  rw [he]
  calc
    _  ≤  ‖((u+v)*(t:ℂ))*inner ℂ (uniformVector S) (spectralProjection (largeSpectrum S) (uniformVector Sᶜ))‖ +
      ‖(u*v)*inner ℂ (uniformVector S) (squaredLocalKernelOperator S t (uniformVector Sᶜ))‖ := norm_add_le _ _
    _  ≤  ‖(u+v)*(t:ℂ)‖*(1/(p:ℝ)) + ‖u*v‖*(4*‖squaredLocalKernelOperator S t‖/(p:ℝ)) := by
      simp only [norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (spectralProjection_scalar_norm_le S (by linarith) (by linarith)) (by positivity))
        (mul_le_mul_of_nonneg_left (balanced_scalar_bound S _ hlo hhi) (by positivity))
    _ = _ := by ring

def sparseKernelScale : ℝ := 17/20

theorem sparseKernelScale_nonneg : 0  ≤  sparseKernelScale := by norm_num [sparseKernelScale]
theorem sparseKernelScale_le_one : sparseKernelScale  ≤  1 := by norm_num [sparseKernelScale]

theorem squaredSparseKernel_norm_le (S : Finset (ZMod p)) {ε : ℝ}
    (hlo : (1/3:ℝ)  ≤  density S) (hhi : density S  ≤  2/3)
    (hε : 0  ≤  ε) (hε' : ε  ≤  1) (hg : gamma S  ≤  ε^2) :
    ‖squaredLocalKernelOperator S sparseKernelScale‖  ≤  ε := by
  have h := squaredLocalKernelOperator_norm_le_sparse S sparseKernelScale hε hε' hg
    (by linarith) (by linarith)
  dsimp [sparseKernelScale] at h ⊢
  nlinarith

theorem sparseKernel_scalar_one_le (S : Finset (ZMod p)) {ε : ℝ}
    (hp : 2  ≤  p) (hlo : (1/3:ℝ)  ≤  density S) (hhi : density S  ≤  2/3)
    (hε : 0  ≤  ε) (hε' : ε  ≤  1) (hg : gamma S  ≤  ε^2) :
    ‖kernelScalar S sparseKernelScale 1 1‖  ≤ 
      1-((17/10:ℝ)*(1-ε^2)-4*ε)/(p:ℝ) := by
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr (by omega)
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp
  let a : ℝ := (p:ℝ)⁻¹^2 * ‖spectralProjection (largeSpectrum S) (normalizedVector S)‖^2
  have ha0 : 0 ≤ a := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have ha1 : a  ≤  1/(p:ℝ) := by
    have h := spectralProjection_scalar_norm_le S (by linarith) (by linarith)
    rw [spectralProjection_scalar S (by linarith) (by linarith)] at h
    have hh : abs (-a) ≤ 1/(p:ℝ) := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using h
    simpa only [abs_neg,abs_of_nonneg ha0] using hh
  have hal : (1-ε^2)/(p:ℝ)  ≤  a := by
    have h := spectralProjection_scalar_re_le S (by linarith) (by linarith)
    rw [spectralProjection_scalar S (by linarith) (by linarith),Complex.ofReal_re] at h
    have hh := div_le_div_of_nonneg_right (show 1-ε^2  ≤  1-gamma S by linarith) hp0.le
    change -a ≤ -(1-gamma S)/(p:ℝ) at h
    rw [neg_div] at h
    linarith
  have hab : a  ≤  1/2 := ha1.trans ((div_le_div_iff₀ hp0 (by norm_num : (0:ℝ)<2)).mpr (by linarith))
  have hbase : 0  ≤  1-(17/10:ℝ)*a := by linarith
  have hs : kernelScalar S sparseKernelScale 1 1 =
      ((1-(17/10:ℝ)*a:ℝ):ℂ) +
      inner ℂ (uniformVector S) (squaredLocalKernelOperator S sparseKernelScale (uniformVector Sᶜ)) := by
    rw [kernelScalar_expansion S sparseKernelScale 1 1 (balanced_nonempty _ hlo)
      (balanced_nonempty _ (balanced_compl S hlo hhi).1),
      spectralProjection_scalar S (by linarith) (by linarith)]
    dsimp [sparseKernelScale,a]
    push_cast
    ring
  rw [hs]
  calc
    _  ≤  ‖((1-(17/10:ℝ)*a:ℝ):ℂ)‖ +
      ‖inner ℂ (uniformVector S) (squaredLocalKernelOperator S sparseKernelScale (uniformVector Sᶜ))‖ := norm_add_le _ _
    _  ≤  1-(17/10:ℝ)*a+4*ε/(p:ℝ) := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hbase]
      exact add_le_add le_rfl ((balanced_scalar_bound S _ hlo hhi).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (squaredSparseKernel_norm_le S hlo hhi hε hε' hg) (by norm_num)) hp0.le))
    _ ≤ 1-(17/10:ℝ)*((1-ε^2)/(p:ℝ))+4*ε/(p:ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hal (show (0:ℝ)≤17/10 by norm_num)
      linarith
    _ = _ := by ring

end Ostmann.Supply

end

end OAI
