import OAI.Analysis.AncientFlat.Kernel.AdjointKernel
import OAI.Analysis.AncientFlat.Evolution.MovingNorm

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap Laplacian ZeroAtInfty BoundedContinuousFunction NNReal
namespace FlatDuality
open BiharmonicKernel InnerProductSpace
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma continuousOn_adjoint_pair (c ε : ℝ) (hε : 0<ε) (z : V) (u : ℝ → C₀(V,ℂ))
    (hu : ContinuousOn u (Icc (0:ℝ) 1)) (M : ℝ) (_hM : 0≤M)
    (hb : ∀ s ∈ Icc (0:ℝ) 1, ∀ x, ‖u s x‖≤M) :
    ContinuousOn (fun s => ∫ x, kernelTest (adjointTime c ε) adjointAmplitude z s x*u s x) (Icc (0:ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict] at hu ⊢
  obtain ⟨B,hBi,hBn,hBb⟩ := FrozenParametrix.kernel_majorant_nonneg (V := V) ε (ε+c^2/16) hε
  apply continuous_of_dominated (bound := fun x => B (x-z)*M)
  · intro s
    exact ((continuous_kernelTest _ _ z s (hε.trans_le (adjointTime_bounds c ε s.property).1)).mul
      (u s).continuous).aestronglyMeasurable
  · intro s
    filter_upwards with x
    rw [norm_mul]
    have hk : ‖kernelTest (adjointTime c ε) adjointAmplitude z s x‖≤B (x-z) := by
      unfold kernelTest
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (adjointAmplitude_bounds s.property).1.le]
      exact (mul_le_mul (adjointAmplitude_bounds s.property).2
        (hBb _ (adjointTime_bounds c ε s.property) _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    exact mul_le_mul hk (hb s s.property x) (norm_nonneg _) (hBn _)
  · exact (hBi.comp_sub_right z).mul_const M
  · filter_upwards with x
    apply Continuous.mul
    · unfold kernelTest
      exact ((Complex.continuous_ofReal.comp contDiff_adjointAmplitude.continuous).comp continuous_subtype_val).mul
        (continuous_kernel_comp (fun s : Icc (0:ℝ) 1 => adjointTime c ε s) (fun _ => x-z)
          ((contDiff_adjointTime c ε).continuous.comp continuous_subtype_val) continuous_const
          (fun s => hε.trans_le (adjointTime_bounds c ε s.property).1))
    · exact (FlatCompactness.eval0 x).continuous.comp hu

lemma norm_endpoints_le {f : ℝ → ℂ} {C : ℝ} (hC : 0≤C)
    (hc : ContinuousOn f (Icc (0:ℝ) 1))
    (hd : ∀ s ∈ Ioo (0:ℝ) 1, ∃ v : ℂ, HasDerivAt f v s ∧ ‖v‖≤C) :
    ‖f 1-f 0‖≤C := by
  have hl : LipschitzOnWith ⟨C,hC⟩ f (Ioo (0:ℝ) 1) := by
    apply (convex_Ioo (0:ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
    · intro s hs
      obtain ⟨v,hv,_⟩ := hd s hs
      exact hv.differentiableAt
    · intro s hs
      obtain ⟨v,hv,hb⟩ := hd s hs
      change ‖deriv f s‖≤C
      rw [hv.deriv]
      exact hb
  have hcl : closure (Ioo (0:ℝ) 1)=Icc (0:ℝ) 1 := closure_Ioo (by norm_num)
  have hl' := LipschitzOnWith.closure (s := Ioo (0:ℝ) 1) (by rwa [hcl]) hl
  rw [hcl] at hl'
  simpa using! hl'.norm_sub_le (show (1:ℝ)∈Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)
    (show (0:ℝ)∈Icc (0:ℝ) 1 from ⟨le_rfl,zero_le_one⟩)
end FlatDuality

end

end OAI
