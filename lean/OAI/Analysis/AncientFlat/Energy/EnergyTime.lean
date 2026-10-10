import OAI.Analysis.AncientFlat.Energy.EnergyQuadratic

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BoundedContinuousFunction Laplacian
namespace ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V]
lemma bounded_bcf [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (f : V →ᵇ ℂ) : Bounded (f : V → ℂ) :=
  ⟨‖f‖,norm_nonneg _,f.norm_coe_le_norm⟩
variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma pair_comm (f g : V → ℂ) : pair f g=pair g f := by
  unfold pair
  congr 1; funext x; rw [real_inner_comm]
lemma pair_self (f : V → ℂ) : pair f f=mass f := by
  simp only [pair,mass,real_inner_self_eq_norm_sq]
lemma pair_add_left (f g h : V →ᵇ ℂ) : pair (↑(f+g)) h=pair f h+pair g h := by
  simp only [pair,BoundedContinuousFunction.coe_add,Pi.add_apply,inner_add_left,mul_add]
  exact integral_add (integrable_pair f.continuous h.continuous (bounded_bcf _) (bounded_bcf _))
    (integrable_pair g.continuous h.continuous (bounded_bcf _) (bounded_bcf _))
lemma pair_smul_left (c : ℝ) (f g : V →ᵇ ℂ) : pair (↑(c•f)) g=c*pair f g := by
  simp only [pair,BoundedContinuousFunction.coe_smul,real_inner_smul_left]
  rw [←integral_const_mul]
  congr 1; funext x; ring
lemma pair_add_right (f g h : V →ᵇ ℂ) : pair f (↑(g+h))=pair f g+pair f h := by
  rw [pair_comm f (↑(g+h)),pair_add_left,pair_comm g f,pair_comm h f]
lemma pair_smul_right (c : ℝ) (f g : V →ᵇ ℂ) : pair f (↑(c•g))=c*pair f g := by
  rw [pair_comm f (↑(c•g)),pair_smul_left,pair_comm g f]
def pairLM : (V →ᵇ ℂ) →ₗ[ℝ] (V →ᵇ ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => pair f g) pair_add_left pair_smul_left pair_add_right pair_smul_right
lemma cross_bcf_le (f g : V →ᵇ ℂ) : cross f g≤(∫ x : V, weight x)*‖f‖*‖g‖ := by
  calc
    _ ≤ ∫ x : V, weight x*(‖f‖*‖g‖) := by
      apply integral_mono (integrable_cross f.continuous g.continuous (bounded_bcf _) (bounded_bcf _))
        (integrable_weight.mul_const _)
      intro x
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (f.norm_coe_le_norm x) (g.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _))
        (weight_pos x).le
    _ = _ := by rw [integral_mul_const]; ring
lemma pair_bcf_bound (f g : V →ᵇ ℂ) : ‖pairLM f g‖≤(∫ x : V, weight x)*‖f‖*‖g‖ :=
  (abs_pair_le f.continuous g.continuous (bounded_bcf _) (bounded_bcf _)).trans (cross_bcf_le f g)
def pairCLM : (V →ᵇ ℂ) →L[ℝ] (V →ᵇ ℂ) →L[ℝ] ℝ :=
  pairLM.mkContinuous₂ (∫ x : V, weight x) pair_bcf_bound
@[simp] lemma pairCLM_apply (f g : V →ᵇ ℂ) : pairCLM f g=pair f g := rfl
lemma hasDerivAt_bilinear_diag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E →L[ℝ] ℝ) {u : ℝ → E} {v : E} {t : ℝ} (hu : HasDerivAt u v t) :
    HasDerivAt (fun s => P (u s) (u s)) (P v (u t)+P (u t) v) t := by
  have h1 : HasDerivAt (fun s => P (u s)) (P v) t :=
    P.hasFDerivAt.comp_hasDerivAt t hu
  exact h1.clm_apply hu
lemma hasDerivAt_mass {u : ℝ → V →ᵇ ℂ} {v : V →ᵇ ℂ} {t : ℝ}
    (hu : HasDerivAt u v t) : HasDerivAt (fun s => mass (u s : V → ℂ)) (2*pair (u t) v) t := by
  have h2 := hasDerivAt_bilinear_diag (pairCLM (V := V)) hu
  simpa only [pairCLM_apply,pair_self,pair_comm (v : V → ℂ) (u t : V → ℂ),←two_mul] using h2
lemma continuousOn_mass {u : ℝ → V →ᵇ ℂ} {s : Set ℝ} (hu : ContinuousOn u s) :
    ContinuousOn (fun t => mass (u t : V → ℂ)) s := by
  have hh := ((pairCLM (V := V)).continuous.comp_continuousOn hu).clm_apply hu
  simpa only [Function.comp_apply,pairCLM_apply,pair_self] using hh
lemma mass_eq_zero_bcf {f : V →ᵇ ℂ} (hf : mass (f : V → ℂ)=0) : f=0 := by
  have hnon : ∀ x : V, 0≤weight x*‖f x‖^2 := fun x => mul_nonneg (weight_pos x).le (sq_nonneg _)
  have hae : (fun x : V => weight x*‖f x‖^2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hnon (integrable_mass f.continuous (bounded_bcf f))).mp hf
  have he := MeasureTheory.Measure.eq_of_ae_eq hae
    ((contDiff_weight 0).continuous.mul (f.continuous.norm.pow 2)) continuous_const
  apply BoundedContinuousFunction.ext
  intro x
  have hh := congrFun he x
  change weight x*‖f x‖^2=0 at hh
  have hz : ‖f x‖^2=0 := (mul_eq_zero.mp hh).resolve_left (weight_pos x).ne'
  have hn : ‖f x‖=0 := by nlinarith [norm_nonneg (f x)]
  change f x=0
  exact norm_eq_zero.mp hn
end ParametrixUniqueness

end

end OAI
