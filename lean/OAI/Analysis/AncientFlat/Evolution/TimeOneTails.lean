import OAI.Analysis.AncientFlat.Kernel.AdjointPairEstimate
import OAI.Analysis.AncientFlat.Kernel.KernelMollifier

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ZeroAtInfty
namespace FlatSimilarity
open FlatDuality BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma endpoint_eq_of_dilated {P : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)} {d : C₀(V,ℂ)} {u : ℝ → C₀(V,ℂ)}
    (he : ∀ x, P d x=u 1 (Real.exp (-(1:ℝ)/4) • x)) (x : V) :
    u 1 x=P d (Real.exp ((1:ℝ)/4) • x) := by
  rw [he,smul_smul,←Real.exp_add]
  norm_num
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma endpoint_difference_lipschitz {P Pc : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)}
    (K Kc : ℝ) (_hK : 0≤K) (_hKc : 0≤Kc)
    (hP : ∀ d : C₀(V,ℂ), ∀ x y, ‖P d x-P d y‖≤K*‖d‖*‖x-y‖)
    (hPc : ∀ d : C₀(V,ℂ), ∀ x y, ‖Pc d x-Pc d y‖≤Kc*‖d‖*‖x-y‖)
    (d : C₀(V,ℂ)) (u v : ℝ → C₀(V,ℂ))
    (he : ∀ x, P d x=u 1 (Real.exp (-(1:ℝ)/4) • x))
    (hec : ∀ x, Pc d x=v 1 (Real.exp (-(1:ℝ)/4) • x)) :
    ∀ x y, ‖(u 1-v 1) x-(u 1-v 1) y‖≤((K+Kc)*Real.exp ((1:ℝ)/4))*‖d‖*‖x-y‖ := by
  intro x y
  have he' : (u 1-v 1) x-(u 1-v 1) y=(u 1 x-u 1 y)-(v 1 x-v 1 y) := by
    simp only [ZeroAtInftyContinuousMap.sub_apply]
    ring
  rw [he']
  calc
    _ ≤ ‖u 1 x-u 1 y‖+‖v 1 x-v 1 y‖ := norm_sub_le _ _
    _ ≤ K*‖d‖*‖Real.exp ((1:ℝ)/4) • x-Real.exp ((1:ℝ)/4) • y‖+
        Kc*‖d‖*‖Real.exp ((1:ℝ)/4) • x-Real.exp ((1:ℝ)/4) • y‖ := by
      simp_rw [endpoint_eq_of_dilated he,endpoint_eq_of_dilated hec]
      exact add_le_add (hP d _ _) (hPc d _ _)
    _=_ := by rw [←smul_sub,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]; ring
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma decayWeight_small (C η : ℝ) (hC : 0≤C) (hη : 0<η) :
    ∃ R : ℝ, 0≤R ∧ ∀ x : V, R≤‖x‖ → C*decayWeight x≤η := by
  refine ⟨C/η,div_nonneg hC hη.le,fun x hx => ?_⟩
  have hn : 0<1+‖x‖ := by positivity
  unfold decayWeight
  rw [←div_eq_mul_inv,div_le_iff₀ hn]
  have hb : C≤‖x‖*η := (div_le_iff₀ hη).mp hx
  nlinarith
lemma TimeOneMap.uniform_tails_difference {c : ℝ} {Af Bf : V → ℝ}
    (h : SymbolBounds c Af Bf) {P Pc : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)}
    (hP : TimeOneMap Af Bf P) (hPc : TimeOneMap (fun _ => c^2) (fun _ => 0) Pc) :
    ∀ η : ℝ, 0<η → ∃ R : ℝ, 0≤R ∧ ∀ d : C₀(V,ℂ), ‖d‖≤1 →
      ∀ x : V, R≤‖x‖ → ‖(P-Pc) d x‖≤η := by
  obtain ⟨K,hK,hKb⟩ := hP.uniform_lipschitz h
  obtain ⟨Kc,hKc,hKcb⟩ := hPc.uniform_lipschitz (SymbolBounds.constant h.1)
  let L := (K+Kc)*Real.exp ((1:ℝ)/4)
  have hL : 0≤L := by dsimp [L]; positivity
  let M := kernelMoment (V := V)
  have hM : 0≤M := kernelMoment_nonneg
  intro η hη
  let r := η/(2*(L*M+1))
  have hr : 0<r := by dsimp [r]; positivity
  have hrb : L*r*M≤η/2 := by
    have hp : 0<L*M+1 := by positivity
    have he : r*(2*(L*M+1))=η := div_mul_cancel₀ _ (by positivity)
    nlinarith [mul_nonneg hr.le hL, mul_nonneg hr.le hM]
  obtain ⟨C,hC,hCb⟩ := adjoint_pair_uniform_estimate h (r^4) (by positivity)
  obtain ⟨R,hR,hRb⟩ := decayWeight_small (V := V) C (η/2) hC (by positivity)
  let qscale := Real.exp (-(1:ℝ)/4)
  have hqscale : 0<qscale := Real.exp_pos _
  refine ⟨R/qscale,div_nonneg hR hqscale.le,fun d hd x hx => ?_⟩
  obtain ⟨u,hu,hue⟩ := hP d
  obtain ⟨v,hv,hve⟩ := hPc d
  have hz : R≤‖qscale • x‖ := by
    rw [norm_smul,Real.norm_of_nonneg hqscale.le]
    nlinarith [(div_le_iff₀ hqscale).mp hx]
  have hg := endpoint_difference_lipschitz K Kc hK hKc hKb hKcb d u v hue hve
  have hmol := norm_kernel_pair_sub_le r hr (u 1-v 1) (L*‖d‖) (mul_nonneg hL (norm_nonneg _)) hg (qscale • x)
  have hpair := hCb d u v hu hv (qscale • x)
  have hval : (P-Pc) d x=(u 1-v 1) (qscale • x) := by
    simp only [sub_apply,ZeroAtInftyContinuousMap.sub_apply,hue,hve]
    rfl
  rw [hval]
  calc
    ‖(u 1-v 1) (qscale • x)‖ ≤ ‖∫ y, kernel (r^4) (y-qscale • x)*(u 1-v 1) y‖+
        ‖(∫ y, kernel (r^4) (y-qscale • x)*(u 1-v 1) y)-(u 1-v 1) (qscale • x)‖ :=
      by simpa only [norm_sub_rev] using (norm_le_insert' ((u 1-v 1) (qscale • x)) (∫ y, kernel (r^4) (y-qscale • x)*(u 1-v 1) y))
    _ ≤ C*decayWeight (qscale • x)*‖d‖+(L*‖d‖)*r*M := add_le_add hpair hmol
    _ ≤ η/2+η/2 := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_right (hRb _ hz) (norm_nonneg _)).trans
          ((mul_le_mul_of_nonneg_left hd (by positivity)).trans_eq (mul_one _))
      · calc
          _ = (L*r*M)*‖d‖ := by ring
          _ ≤ (η/2)*1 := mul_le_mul hrb hd (norm_nonneg _) (by positivity)
          _ = _ := mul_one _
    _ = η := by ring
end FlatSimilarity

end

end OAI
