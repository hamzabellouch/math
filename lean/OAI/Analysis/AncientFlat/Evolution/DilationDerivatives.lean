import OAI.Analysis.AncientFlat.Evolution.TraceFour

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
omit [FiniteDimensional ℝ V] in
lemma iteratedFDeriv_scale (r : ℝ) (f : V → ℂ) (hf : ContDiff ℝ 4 f)
    (n : ℕ) (hn : n≤4) (x : V) :
    iteratedFDeriv ℝ n (fun y => f (r • y)) x=
      r^n • iteratedFDeriv ℝ n f (r • x) := by
  let g : V →L[ℝ] V := r • ContinuousLinearMap.id ℝ V
  have hg := g.iteratedFDeriv_comp_right hf x (show (n : WithTop ℕ∞)≤4 by exact_mod_cast hn)
  change iteratedFDeriv ℝ n (f ∘ g) x=_
  rw [hg]
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply, g,
    ContinuousLinearMap.id_apply]
  simpa using (iteratedFDeriv ℝ n f (r • x)).map_smul_univ (fun _ => r) m

lemma bilaplacian_scale (r : ℝ) (f : V → ℂ) (hf : ContDiff ℝ 4 f) (x : V) :
    Δ (Δ (fun y => f (r • y))) x=r^4 • Δ (Δ f) (r • x) := by
  have hg : ContDiff ℝ 4 (fun y => f (r • y)) := hf.comp (contDiff_const.smul contDiff_id)
  rw [ClassicalIBP.bilaplacian_eq_traceFour _ hg,
    iteratedFDeriv_scale r f hf 4 le_rfl,
    map_smul, ClassicalIBP.bilaplacian_eq_traceFour _ hf]

omit [FiniteDimensional ℝ V] in
lemma bounded_jets_scale (r : ℝ) (f : V → ℂ) (hf : ContDiff ℝ 4 f)
    (hb : ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖≤M) :
    ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => f (r • y)) x‖≤M := by
  intro n hn
  obtain ⟨M,hM⟩ := hb n hn
  refine ⟨‖r^n‖*M,fun x => ?_⟩
  rw [iteratedFDeriv_scale r f hf n hn x,norm_smul]
  exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
end ParametrixDilation

end

end OAI
