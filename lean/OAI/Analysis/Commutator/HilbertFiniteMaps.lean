import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

namespace Kadison.HilbertFiniteMaps

variable {H G K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ι : Type*) [Fintype ι]

abbrev Copies (H ι : Type*) := PiLp 2 (fun _ : ι => H)

def column (T : ι → H →L[ℂ] G) : H →L[ℂ] Copies G ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => G)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi T)

omit [CompleteSpace H] [CompleteSpace G] [Fintype ι] in
@[simp] lemma column_apply (T : ι → H →L[ℂ] G) (x : H) (i : ι) : column ι T x i=T i x := rfl

lemma adjoint_column_apply (T : ι → H →L[ℂ] G) (y : Copies G ι) :
    (column ι T).adjoint y=∑ i,(T i).adjoint (y i) := by
  apply ext_inner_right ℂ
  intro x
  simp only [ContinuousLinearMap.adjoint_inner_left,PiLp.inner_apply,column_apply,sum_inner]

lemma adjoint_column_comp (T : ι → H →L[ℂ] G) :
    (column ι T).adjoint.comp (column ι T)=∑ i,(T i).adjoint.comp (T i) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,adjoint_column_apply,column_apply,sum_apply]

lemma column_norm_le_one (T : ι → H →L[ℂ] G)
    (hT : ‖∑ i,(T i).adjoint.comp (T i)‖≤1) : ‖column ι T‖≤1 := by
  rw [←adjoint_column_comp,ContinuousLinearMap.norm_adjoint_comp_self] at hT
  nlinarith [norm_nonneg (column ι T)]

def amplify (T : H →L[ℂ] G) : Copies H ι →L[ℂ] Copies G ι :=
  column ι (fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i))

omit [CompleteSpace H] [CompleteSpace G] in
@[simp] lemma amplify_apply (T : H →L[ℂ] G) (x : Copies H ι) (i : ι) :
    amplify ι T x i=T (x i) := rfl

omit [CompleteSpace H] [CompleteSpace G] in
lemma amplify_norm_le (T : H →L[ℂ] G) : ‖amplify ι T‖≤‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hs : ‖amplify ι T x‖^2≤(‖T‖*‖x‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2,mul_pow,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by
      rw [amplify_apply,←mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (x i)) 2)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg x))).mp hs

omit [CompleteSpace H] [CompleteSpace G] [CompleteSpace K] in
lemma amplify_comp (T : H →L[ℂ] G) (U : G →L[ℂ] K) :
    amplify ι (U.comp T)=(amplify ι U).comp (amplify ι T) := by ext x i; rfl

lemma amplify_adjoint (T : H →L[ℂ] G) : amplify ι T.adjoint=(amplify ι T).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,amplify_apply,ContinuousLinearMap.adjoint_inner_left]

omit [CompleteSpace H] [CompleteSpace G] in
lemma amplify_sub (T U : H →L[ℂ] G) : amplify ι (T-U)=amplify ι T-amplify ι U := by
  ext x i
  rfl

end Kadison.HilbertFiniteMaps

end

end
end

end OAI
