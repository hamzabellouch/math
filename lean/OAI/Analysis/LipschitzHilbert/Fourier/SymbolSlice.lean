import OAI.Analysis.LipschitzHilbert.Fourier.SymbolWeights
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace OAI

/-! Restricting one fixed Schwartz symbol to the two scale parameters.
The restriction does not enlarge any Schwartz seminorm. -/
noncomputable section
open scoped FourierTransform ContDiff
namespace LipschitzHilbert.PacketRepresentation

abbrev MasterSymbolSpace := SymbolSpace × (ℝ × ℝ)

def symbolInclusion : SymbolSpace →L[ℝ] MasterSymbolSpace :=
  ContinuousLinearMap.inl ℝ SymbolSpace (ℝ × ℝ)

theorem symbolInclusion_norm : ‖symbolInclusion‖≤1 :=
  ContinuousLinearMap.norm_inl_le_one ℝ SymbolSpace (ℝ × ℝ)

theorem symbolSlice_temperate (p : ℝ × ℝ) :
    Function.HasTemperateGrowth (fun q : SymbolSpace => (q,p)) := by
  have h := symbolInclusion.hasTemperateGrowth.add
    (Function.HasTemperateGrowth.const (E := SymbolSpace) (0,p))
  change Function.HasTemperateGrowth (fun q => symbolInclusion q+(0,p)) at h
  simpa only [Pi.add_apply, symbolInclusion, ContinuousLinearMap.inl_apply, Prod.mk_add_mk,
    add_zero, zero_add] using h

theorem symbolSlice_antilipschitz (p : ℝ × ℝ) :
    AntilipschitzWith 1 (fun q : SymbolSpace => (q,p)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one, one_mul, Prod.dist_eq]
  exact le_max_left _ _

def symbolSlice (F : SchwartzMap MasterSymbolSpace ℂ) (p : ℝ × ℝ) :
    SchwartzMap SymbolSpace ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (symbolSlice_temperate p)
    (symbolSlice_antilipschitz p) F

@[simp] theorem symbolSlice_apply (F : SchwartzMap MasterSymbolSpace ℂ)
    (p : ℝ × ℝ) (q : SymbolSpace) : symbolSlice F p q=F (q,p) := rfl

theorem symbolSlice_derivative_bound (F : SchwartzMap MasterSymbolSpace ℂ)
    (p : ℝ × ℝ) (n : ℕ) (q : SymbolSpace) :
    ‖iteratedFDeriv ℝ n (symbolSlice F p) q‖≤‖iteratedFDeriv ℝ n F (q,p)‖ := by
  have hid : (symbolSlice F p : SymbolSpace → ℂ)=
      (fun z : MasterSymbolSpace => F (z+(0,p))) ∘ symbolInclusion := by
    ext x
    simp [symbolInclusion]
  have hs : ContDiff ℝ ∞ (fun z : MasterSymbolSpace => F (z+(0,p))) := by fun_prop
  have hd := symbolInclusion.iteratedFDeriv_comp_right
    (f := fun z : MasterSymbolSpace => F (z+(0,p))) hs q (i := n) (mod_cast le_top)
  rw [hid, hd]
  rw [iteratedFDeriv_comp_add_right]
  have h := (iteratedFDeriv ℝ n F (symbolInclusion q+(0,p))).norm_compContinuousLinearMap_le
    (fun _ : Fin n => symbolInclusion)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have hp : ‖symbolInclusion‖^n≤1 := pow_le_one₀ (norm_nonneg _) symbolInclusion_norm
  exact h.trans ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (by
    simp [symbolInclusion]))

theorem symbolSlice_seminorm (F : SchwartzMap MasterSymbolSpace ℂ)
    (p : ℝ × ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (symbolSlice F p)≤SchwartzMap.seminorm ℝ k n F := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (apply_nonneg _ _)
  intro q
  calc
    _ ≤ ‖q‖^k*‖iteratedFDeriv ℝ n F (q,p)‖ :=
      mul_le_mul_of_nonneg_left (symbolSlice_derivative_bound F p n q) (pow_nonneg (norm_nonneg _) _)
    _ ≤ ‖(q,p)‖^k*‖iteratedFDeriv ℝ n F (q,p)‖ := by
      gcongr
      exact le_max_left _ _
    _ ≤ _ := SchwartzMap.le_seminorm ℝ k n F (q,p)

/-- The Fourier coefficient bound is uniform over both parameters.
Only finitely many seminorms of the single master symbol enter. -/
theorem symbolSlice_coefficient_uniform (F : SchwartzMap MasterSymbolSpace ℂ) (q : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ × ℝ, symbolCoefficientBound (symbolSlice F p) q≤C := by
  let Q : Seminorm ℝ (SchwartzMap SymbolSpace ℂ) :=
    ((Finset.Iic (4*q,0)).sup (schwartzSeminormFamily ℝ SymbolSpace ℂ)).comp
      (FourierTransform.fourierCLM ℝ (SchwartzMap SymbolSpace ℂ)).toLinearMap
  have hQ : Continuous Q :=
    (Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℝ SymbolSpace ℂ).continuous_seminorm i)).comp
        (FourierTransform.fourierCLM ℝ (SchwartzMap SymbolSpace ℂ)).continuous
  obtain ⟨s,A,_hA,hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ SymbolSpace ℂ) Q hQ
  let M := (s.sup (schwartzSeminormFamily ℝ MasterSymbolSpace ℂ)) F
  refine ⟨2^(4*q)*((A:ℝ)*M)+1, by dsimp [M]; positivity, ?_⟩
  intro p
  have hs : (s.sup (schwartzSeminormFamily ℝ SymbolSpace ℂ)) (symbolSlice F p)≤M := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact (symbolSlice_seminorm F p i.1 i.2).trans
      (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ MasterSymbolSpace ℂ) (x := F) hi)
  have hb := (Seminorm.le_def.mp hbound) (symbolSlice F p)
  change Q (symbolSlice F p)≤(A:ℝ)*
    (s.sup (schwartzSeminormFamily ℝ SymbolSpace ℂ)) (symbolSlice F p) at hb
  have hfinal := hb.trans (mul_le_mul_of_nonneg_left hs A.coe_nonneg)
  change (Finset.Iic (4*q,0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕 (symbolSlice F p))≤(A:ℝ)*M at hfinal
  unfold symbolCoefficientBound
  exact add_le_add (mul_le_mul_of_nonneg_left hfinal (show (0:ℝ)≤2^(4*q) by positivity)) le_rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
