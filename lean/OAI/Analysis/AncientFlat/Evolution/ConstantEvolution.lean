import OAI.Analysis.AncientFlat.Kernel.ClassicalBase
import OAI.Analysis.AncientFlat.Evolution.MovingUnique
import OAI.Analysis.AncientFlat.Evolution.DilationCore

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction SchwartzMap Laplacian Convolution
namespace BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma evolution_bounded_jets (t : ℝ) (ht : 0<t) (f : C₀(V,ℂ)) (n : ℕ) :
    ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (fun y => evolution t f y) x‖≤M := by
  let g := heatKernel (V := V) t ht
  let g' := SchwartzDerivatives.iterated g n
  have he : (fun y => evolution t f y)=
      ScaledSchwartzConvolution.value (fun _ : V => (1:ℝ))
        (ContinuousLinearMap.lsmul ℝ ℂ) f.toBCF g 0 := by
    rw [evolution_coe_convolution t ht]
    funext x
    simp only [ScaledSchwartzConvolution.value,convolution_def,inv_one,one_pow,
      one_smul,ContinuousLinearMap.lsmul_apply,ContinuousLinearMap.mul_apply',smul_eq_mul,g]
  refine ⟨‖f‖*(∫ y : V, ‖g' y‖),fun x => ?_⟩
  rw [he,ScaledSchwartzConvolution.iteratedFDeriv_value_smul_apply
    zero_lt_one (fun _ : V => (1:ℝ)) continuous_const (fun _ => ⟨le_rfl,le_rfl⟩)]
  simp only [inv_one,one_pow,one_smul]
  have hi : Integrable (fun y : V => ‖f‖*‖g' (x-y)‖) :=
    (g'.integrable.norm.comp_sub_left x).const_mul ‖f‖
  calc
    _ ≤ ∫ y : V, ‖f‖*‖g' (x-y)‖ := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards with y
      rw [norm_smul]
      rw [←SchwartzDerivatives.iterated_apply]
      exact mul_le_mul_of_nonneg_right (f.toBCF.norm_coe_le_norm y) (norm_nonneg (g' (x-y)))
    _ = _ := by rw [integral_const_mul,integral_sub_left_eq_self (fun y : V => ‖g' y‖) volume x]

lemma evolution_smul (t : ℝ) (ht : 0<t) (a : ℂ) (f : C₀(V,ℂ)) :
    evolution t (a • f)=a • evolution t f := by
  rw [evolution_eq_convolve t ht,evolution_eq_convolve t ht,C0Convolution.convolve_smul]
end BiharmonicKernel
namespace FlatSimilarity
open BiharmonicKernel ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def constantTheta (c t : ℝ) : ℝ := c^2/16*(1-Real.exp (-t))
lemma constantTheta_zero (c : ℝ) : constantTheta c 0=0 := by simp [constantTheta]
lemma constantTheta_pos {c t : ℝ} (hc : 0<c) (ht : 0<t) : 0<constantTheta c t := by
  have he : Real.exp (-t)<1 := by simpa using Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  unfold constantTheta
  positivity
lemma constantTheta_deriv (c t : ℝ) :
    HasDerivAt (constantTheta c) (Real.exp (-t)/16*c^2) t := by
  have he : HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-t)) t := by
    convert (hasDerivAt_id t).neg.exp using 1 <;> simp
  exact ((he.const_sub 1).const_mul (c^2/16)).congr_deriv (by ring)

def constantMoving (c : ℝ) (d : C₀(V,ℂ)) (t : ℝ) : C₀(V,ℂ) :=
  (Real.exp (-t/2) : ℝ) • evolution (constantTheta c t) d

def toBCFReal : C₀(V,ℂ) →L[ℝ] (V →ᵇ ℂ) := LinearMap.mkContinuous
    { toFun := ZeroAtInftyContinuousMap.toBCF
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun f => by
        change ‖f.toBCF‖≤1*‖f‖
        simp)
omit [MeasurableSpace V] [BorelSpace V] in
lemma bilaplacian_real_smul {f : V → ℂ} (hf : ContDiff ℝ 4 f) (a : ℝ) :
    Δ (Δ (fun y => a • f y))=fun y => a • Δ (Δ f) y := by
  have h2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have h1 : Δ (fun y => a • f y)=fun y => a • Δ f y :=
    funext (fun y => InnerProductSpace.laplacian_smul a (h2.contDiffAt (x := y)))
  rw [h1]
  exact funext (fun y => InnerProductSpace.laplacian_smul a
    ((ClassicalIBP.contDiff_laplacian f 2 hf).contDiffAt (x := y)))
lemma constantMoving_deriv (c : ℝ) (hc : 0<c) (d : C₀(V,ℂ)) (t : ℝ) (ht : 0<t) :
    ∃ p : V →ᵇ ℂ, HasDerivAt (fun r => (constantMoving c d r).toBCF) p t ∧
      ∀ x, p x=-((Real.exp (-t)/16*c^2 : ℝ) : ℂ)*
        Δ (Δ (fun y => constantMoving c d t y)) x-(1/2+(0:ℂ))*constantMoving c d t x := by
  let θ := constantTheta c t
  have hθ : 0<θ := constantTheta_pos hc ht
  let v := -C0Convolution.convolve (Δ (Δ (heatKernel (V := V) θ hθ) : SchwartzMap V ℂ) : SchwartzMap V ℂ) d
  have hv := (evolution_hasDerivAt θ hθ d).scomp t (constantTheta_deriv c t)
  have he : HasDerivAt (fun r : ℝ => Real.exp (-r/2)) (-Real.exp (-t/2)/2) t := by
    convert ((hasDerivAt_id t).neg.div_const 2).exp using 1 <;>
      simp [Pi.neg_apply,div_eq_mul_inv]
  have hu := he.smul hv
  let p : C₀(V,ℂ) := Real.exp (-t/2) • ((Real.exp (-t)/16*c^2) • v)+
    (-Real.exp (-t/2)/2) • evolution θ d
  refine ⟨p.toBCF,?_,fun x => ?_⟩
  · exact (toBCFReal (V := V)).hasFDerivAt.comp_hasDerivAt t hu
  · have hvx : v x=-Δ (Δ (fun y => evolution θ d y)) x := by
      have h1 := (evolution_heat_equation θ hθ d x)
      have h2 := ((C0Convolution.eval x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ
        (evolution_hasDerivAt θ hθ d)
      exact h2.unique h1
    dsimp only [p]
    simp only [ZeroAtInftyContinuousMap.toBCF_apply,ZeroAtInftyContinuousMap.add_apply,
      ZeroAtInftyContinuousMap.smul_apply,hvx]
    change _=-((Real.exp (-t)/16*c^2 : ℝ) : ℂ)*
      Δ (Δ (fun y => Real.exp (-t/2) • evolution θ d y)) x-
        (1/2+(0:ℂ))*(Real.exp (-t/2) • evolution θ d x)
    have hsp : ContDiff ℝ 4 (fun y => evolution θ d y) :=
      (evolution_smooth θ hθ d).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (4:ℕ∞)≤⊤))
    rw [bilaplacian_real_smul hsp]
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_mul,
      Complex.ofReal_neg,Complex.ofReal_ofNat,add_zero]
    ring

lemma constantMoving_classical (c : ℝ) (hc : 0<c) (d : C₀(V,ℂ)) :
    MovesClassically (fun _ => c^2) (fun _ => 0) d (constantMoving c d) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [constantMoving,constantTheta_zero,evolution_zero]
  · exact ((Real.continuous_exp.comp (continuous_neg.div_const 2)).smul
      ((evolution_continuous d).comp (by unfold constantTheta; fun_prop))).continuousOn
  · intro t ht
    exact contDiff_const.smul ((evolution_smooth _ (constantTheta_pos hc ht.1) d).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (4:ℕ∞)≤⊤)))
  · intro t ht n hn
    obtain ⟨M,hM⟩ := evolution_bounded_jets (constantTheta c t) (constantTheta_pos hc ht.1) d n
    refine ⟨|Real.exp (-t/2)| * M,fun x => ?_⟩
    change ‖iteratedFDeriv ℝ n (fun y => Real.exp (-t/2) • evolution (constantTheta c t) d y) x‖≤_
    rw [iteratedFDeriv_const_smul_apply'
      ((evolution_smooth _ (constantTheta_pos hc ht.1) d).of_le
        (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
  · intro t ht
    exact constantMoving_deriv c hc d t ht.1
end FlatSimilarity

end

end OAI
