import OAI.Dynamics.StandardMap.BridgeEligibility

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma eligible_dirichlet_bound (v : ℕ → ℝ) (M D : ℝ) (B J : ℕ)
    (hM : 1 < M) (hJ : 1 ≤ J) (hJB : J ≤ B+1)
    (hD : M^((49/50:ℝ)*(B:ℝ)) ≤ D)
    (hv : ∀ p, 1 ≤ p → p ≤ B → |v p|+1 ≤ M)
    (s : ℂ) (hs : ‖s‖=1) (hver : |s.re| ≤ 1/4)
    (hpref : ∀ p, 1 ≤ p → p ≤ B → ‖transferProduct v p s‖ ≤ 3*M^(-(47/50:ℝ)*(p:ℝ)))
    (row : ℂ →L[ℝ] ℝ) (hroweq : ∀ z, row z=linearSolution v z.im z.re J)
    (hsmall : |row s| ≤ D⁻¹) (hrow : D/3 ≤ |row 1|) :
    tSolution v J ≠ 0 ∧ ∀ p, 1 ≤ p → p < J →
      |dirichletSolution v J p| ≤ 12*M^(-(9/10:ℝ)*(p:ℝ)) := by
  have hMp : 0 < M := by linarith
  have hDp : 0 < D := (Real.rpow_pos_of_pos hMp _).trans_le hD
  have ht : tSolution v J ≠ 0 := by
    have hr : row 1≠0 := abs_pos.mp (by linarith : 0 < |row 1|)
    simpa only [hroweq,Complex.one_im,Complex.one_re,tSolution] using hr
  obtain ⟨u,e,hui,hru,heq,he⟩:=normalized_kernel_from_stable row s D hDp hs hver hrow hsmall
  have huj : linearSolution v 1 u.re J=0 := by simpa only [hroweq,hui] using hru
  have heqU :=initial_kernel_dirichlet v J u hui hJ huj ht
  refine ⟨ht,?_⟩
  intro p hp hpJ
  have hpB : p ≤ B := by omega
  have hup : ‖transferProduct v p‖ ≤ M^(p:ℝ) := by
    simpa only [Real.rpow_natCast] using (transferProduct_norm_bounds v M p (by linarith)
      (fun i hi hip => hv i hi (by omega))).2
  have hc:=eligible_row_contraction (transferProduct v) s u e M D B p hp hpB hM hs hver heq he
    hD (hpref p hp hpB) hup
  have hu3 : (⟨u.re,1⟩:ℂ)=u := by apply Complex.ext <;> simp [hui]
  have he : (transferProduct v p u).im=dirichletSolution v J p := by
    rw [← hu3,transferProduct_pair]
    exact heqU p
  calc
    _ = |(transferProduct v p u).im| := congrArg abs he.symm
    _ ≤ ‖transferProduct v p u‖ := Complex.abs_im_le_norm _
    _ ≤ 12*M^(-(47/50:ℝ)*(p:ℝ)) := hc
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM.le ?_) (by norm_num)
      have : (0:ℝ) ≤ p := Nat.cast_nonneg _
      linarith

lemma fast_prefix_dirichlet (v : ℕ → ℝ) (M : ℝ) (B : ℕ)
    (hB : 2 ≤ B) (hM : 1 < M) (hq : M^(-(49/25:ℝ)) ≤ 1/2)
    (hsmall : 3*M^(-(47/50:ℝ)) ≤ 1/4)
    (hv : ∀ i, 1 ≤ i → i ≤ B → |v i|+1 ≤ M)
    (hg : ∀ i, 1 ≤ i → i ≤ B → M^((49/50:ℝ)*(i:ℝ)) ≤ ‖transferProduct v i‖) :
    ∃ J : ℕ, (J=B ∨ J=B+1) ∧ tSolution v J ≠ 0 ∧
      ∀ p, 1 ≤ p → p < J → |dirichletSolution v J p| ≤ 12*M^(-(9/10:ℝ)*(p:ℝ)) := by
  obtain ⟨s,hu,hver,hs,hpref⟩:=prefix_stable_vertical v M B (by omega) hM hq hsmall hv hg
  have helig:=(transferProduct_area v B).eligible_row s hu hver hs
  rcases helig with hleft|hright
  · refine ⟨B+1,Or.inr rfl,?_⟩
    apply eligible_dirichlet_bound v M ‖transferProduct v B‖ B (B+1) hM (by omega) le_rfl
      (hg B (by omega) le_rfl) hv s hu hver hpref (Complex.reCLM.comp (transferProduct v B)) ?_ ?_ hleft
    · intro z
      change (transferProduct v B z).re=linearSolution v z.im z.re (B+1)
      have hz : (⟨z.re,z.im⟩:ℂ)=z := rfl
      rw [← hz,transferProduct_pair]
    · exact (Complex.abs_re_le_norm _).trans_eq hs
  · refine ⟨B,Or.inl rfl,?_⟩
    apply eligible_dirichlet_bound v M ‖transferProduct v B‖ B B hM (by omega) (by omega)
      (hg B (by omega) le_rfl) hv s hu hver hpref (Complex.imCLM.comp (transferProduct v B)) ?_ ?_ hright
    · intro z
      change (transferProduct v B z).im=linearSolution v z.im z.re B
      have hz : (⟨z.re,z.im⟩:ℂ)=z := rfl
      rw [← hz,transferProduct_pair]
    · exact (Complex.abs_im_le_norm _).trans_eq hs
end StandardMapEntropy

end OAI
