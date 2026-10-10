import OAI.Analysis.AncientFlat.Kernel.SchwartzIBP

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Laplacian
namespace FlatDuality
open ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma norm_iterated_dir_le (n : ℕ) (v : V) (f : V → E)
    (hf : ContDiff ℝ (n+1) f) (x : V) :
    ‖iteratedFDeriv ℝ n (dir v f) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (n+1) f x‖ := by
  have hd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by rfl)
  calc
    _ ≤ ‖v‖*‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ :=
      norm_iteratedFDeriv_clm_apply_const hd.contDiffAt le_rfl
    _ = _ := by rw [norm_iteratedFDeriv_fderiv]
variable [FiniteDimensional ℝ V]
lemma norm_iterated_laplacian_le (n : ℕ) (f : V → ℂ) (hf : ContDiff ℝ (n+2) f) (x : V) :
    ‖iteratedFDeriv ℝ n (Δ f) x‖ ≤ (Module.finrank ℝ V : ℝ)*‖iteratedFDeriv ℝ (n+2) f x‖ := by
  let e := stdOrthonormalBasis ℝ V
  have hc : ∀ i, ContDiff ℝ (n+1) (dir (e i) f) := by
    intro i
    apply contDiff_dir
    convert hf using 1
    ring
  have hd : ∀ i, ContDiff ℝ n (dir (e i) (dir (e i) f)) := by
    intro i
    apply contDiff_dir
    exact hc i
  rw [laplacian_eq_sum_dir f (hf.of_le (by exact_mod_cast Nat.le_add_left 2 n))]
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => (hd i).contDiffAt)]
  calc
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ n (dir (e i) (dir (e i) f)) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ V), ‖iteratedFDeriv ℝ (n+2) f x‖ := by
      apply Finset.sum_le_sum
      intro i _
      have h1 := norm_iterated_dir_le n (e i) (dir (e i) f) (hc i) x
      have hf' : ContDiff ℝ ((n+1)+1) f := by
        convert hf using 1
        ring
      have h2 := norm_iterated_dir_le (n+1) (e i) f hf' x
      simp only [OrthonormalBasis.norm_eq_one,one_mul] at h1 h2
      exact h1.trans (by simpa only [Nat.add_assoc] using h2)
    _ = _ := by simp
lemma norm_bilaplacian_le (f : V → ℂ) (hf : ContDiff ℝ 4 f) (x : V) :
    ‖Δ (Δ f) x‖≤(Module.finrank ℝ V : ℝ)^2*‖iteratedFDeriv ℝ 4 f x‖ := by
  have h0 := norm_iterated_laplacian_le 0 (Δ f) (ClassicalIBP.contDiff_laplacian f 2 hf) x
  simp only [norm_iteratedFDeriv_zero] at h0
  have h2 := norm_iterated_laplacian_le 2 f hf x
  calc
    _ ≤ (Module.finrank ℝ V : ℝ)*‖iteratedFDeriv ℝ 2 (Δ f) x‖ := h0
    _ ≤ (Module.finrank ℝ V : ℝ)*((Module.finrank ℝ V : ℝ)*‖iteratedFDeriv ℝ 4 f x‖) :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    _ = _ := by ring
omit [FiniteDimensional ℝ V] in
lemma temperate_of_bounded_jets (f : V → ℝ) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖≤C) : f.HasTemperateGrowth := by
  refine ⟨hf,fun n => ?_⟩
  obtain ⟨C,hC⟩ := hb n
  exact ⟨0,C,by simpa using hC⟩
end FlatDuality

end

end OAI
