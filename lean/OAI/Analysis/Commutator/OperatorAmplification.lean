import Mathlib
import OAI.Analysis.Commutator.BicommutantOrbit
import OAI.Analysis.Commutator.CyclicMatrix

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

abbrev SumSpace := PiLp 2 (fun _ : ι => H)

def single (i : ι) : H →L[ℂ] SumSpace (H:=H) ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma single_apply (i : ι) (x : H) (j : ι) :
    single ι i x j=if j=i then x else 0 := by
  simp [single]

def diagonal : (H →L[ℂ] H) →⋆ₐ[ℂ] (SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) where
  toFun T := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i)))
  map_zero' := by ext x i; simp
  map_one' := by ext x i; simp
  map_add' _ _ := by ext x i; simp
  map_mul' _ _ := by ext x i; simp
  commutes' _ := by ext x i; simp [Algebra.algebraMap_eq_smul_one]
  map_star' T := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp [PiLp.inner_apply,
      ContinuousLinearMap.adjoint_inner_left]

omit [DecidableEq ι] in
@[simp] lemma diagonal_apply (T : H →L[ℂ] H) (x : SumSpace (H:=H) ι) (i : ι) :
    diagonal (H:=H) ι T x i=T (x i) := by simp [diagonal]

lemma diagonal_single (T : H →L[ℂ] H) (i : ι) (x : H) :
    diagonal (H:=H) ι T (single ι i x)=single ι i (T x) := by
  ext j
  by_cases h : j=i <;> simp [h]

omit [CompleteSpace H] in
lemma sum_single (x : SumSpace (H:=H) ι) : ∑ i, single ι i (x i)=x := by
  ext j
  simp

def entry (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (i j : ι) : H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (T.comp (single ι j))

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma entry_apply (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (i j : ι) (x : H) : entry ι T i j x=T (single ι j x) i := rfl

omit [CompleteSpace H] in
lemma apply_eq_sum_entries (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (x : SumSpace (H:=H) ι) (i : ι) : T x i=∑ j, entry ι T i j (x j) := by
  conv_lhs => rw [←sum_single ι x]
  simp

omit [CompleteSpace H] in
lemma reconstruct (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) :
    CyclicColumns.matrixAction (entry ι T)=T := by
  ext x i
  simpa only [CyclicColumns.matrixAction_apply] using (apply_eq_sum_entries ι T x i).symm

lemma entry_commutes (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (a : H →L[ℂ] H) (h : diagonal (H:=H) ι a*T=T*diagonal (H:=H) ι a) (i j : ι) :
    a*entry ι T i j=entry ι T i j*a := by
  ext x
  have he := congrArg (fun R : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι => R (single ι j x) i) h
  simpa only [mul_apply_eq_comp,diagonal_apply,diagonal_single,entry_apply] using he

lemma commutes_of_entries (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (a : H →L[ℂ] H) (h : ∀ i j, a*entry ι T i j=entry ι T i j*a) :
    diagonal (H:=H) ι a*T=T*diagonal (H:=H) ι a := by
  ext x i
  change a (T x i)=T (diagonal (H:=H) ι a x) i
  rw [apply_eq_sum_entries ι T x,apply_eq_sum_entries ι T]
  simp only [map_sum,diagonal_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun R : H →L[ℂ] H => R (x j)) (h i j)

lemma diagonal_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    diagonal (H:=H) ι T ∈ Set.centralizer (Set.centralizer ((S.map (diagonal (H:=H) ι)) : Set (SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι))) := by
  intro R hR
  apply (commutes_of_entries ι R T ?_).symm
  intro i j
  apply (hT _ ?_).symm
  intro a ha
  exact entry_commutes ι R a (hR (diagonal (H:=H) ι a) ⟨a,ha,rfl⟩) i j

theorem bicommutant_finite_approx (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x : SumSpace (H:=H) ι) (ε : ℝ) (hε : 0<ε) :
    ∃ a : H →L[ℂ] H, a∈S ∧ ‖diagonal (H:=H) ι a x-diagonal (H:=H) ι T x‖<ε := by
  have h := bicommutant_mem_cyclicSubspace (S.map (diagonal (H:=H) ι))
    (diagonal_bicommutant ι S hT) x
  change diagonal (H:=H) ι T x ∈ closure
    (orbitSubmodule (S.map (diagonal (H:=H) ι)) x : Set (SumSpace (H:=H) ι)) at h
  obtain ⟨y,⟨a,⟨b,hb,hba⟩,hay⟩,hy⟩ := Metric.mem_closure_iff.mp h ε hε
  subst a
  subst y
  refine ⟨b,hb,?_⟩
  rw [dist_eq_norm,norm_sub_rev] at hy
  exact hy

end Kadison.OperatorAmplification

end

end
end

end OAI
