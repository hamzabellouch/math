import Mathlib
import OAI.Analysis.FreeWords.TensorCalculus
import OAI.Analysis.FreeWords.TensorLieSpan

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators

noncomputable section

theorem prod_delta_eq {r d : ℕ} (s : Finset (Fin r)) (a b : Fin r → Fin d) :
    (∏ t ∈ s, if a t=b t then (1 : ℂ) else 0)=
      if ∀ t∈s, a t=b t then 1 else 0 := by
  classical
  by_cases h : ∀ t∈s, a t=b t
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one (fun t ht => ite_eq_left (h t ht))
  · rw [ite_eq_right h]
    obtain ⟨t,ht,hab⟩ : ∃ t∈s, a t ≠ b t := by
      by_contra hh
      apply h
      intro t ht
      by_contra hab
      exact hh ⟨t,ht,hab⟩
    exact Finset.prod_eq_zero ht (by simp [hab])

theorem lieMatrix_single_apply {r d : ℕ} (i j : Fin d) (a b : Fin r → Fin d) :
    lieMatrix (Matrix.single i j (1 : ℂ)) a b =
      ∑ s, if a s=i ∧ b=Function.update a s j then 1 else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro s _
  rw [prod_delta_eq,Matrix.single_apply]
  have hh : ((∀ t∈Finset.univ.erase s, a t=b t) ∧ (i=a s ∧ j=b s)) ↔
      (a s=i ∧ b=Function.update a s j) := by
    constructor
    · rintro ⟨hp,hi,hj⟩
      refine ⟨hi.symm,?_⟩
      funext t
      by_cases hts : t=s
      · subst t; simp [hj]
      · simpa [Function.update_of_ne hts] using (hp t (Finset.mem_erase.mpr ⟨hts,Finset.mem_univ t⟩)).symm
    · rintro ⟨hi,rfl⟩
      refine ⟨fun t ht => ?_,hi.symm,by simp⟩
      simp [Function.update_of_ne (Finset.mem_erase.mp ht).1]
  have hb (p q : Prop) [Decidable p] [Decidable q] :
      (if p then (1 : ℂ) else 0)*(if q then 1 else 0)=(if p ∧ q then 1 else 0) := by
    split_ifs <;> simp_all
  rw [hb]
  simp only [hh]

theorem lieMatrix_single_mul {r d : ℕ} (i j : Fin d)
    (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ) (a b : Fin r → Fin d) :
    (lieMatrix (r := r) (Matrix.single i j (1 : ℂ))*T) a b =
      ∑ s, if a s=i then T (Function.update a s j) b else 0 := by
  classical
  simp only [Matrix.mul_apply,lieMatrix_single_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : a s=i
  · simp [hs]
  · simp [hs]

theorem mul_lieMatrix_single {r d : ℕ} (i j : Fin d)
    (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ) (a b : Fin r → Fin d) :
    (T*lieMatrix (r := r) (Matrix.single i j (1 : ℂ))) a b =
      ∑ s, if b s=j then T a (Function.update b s i) else 0 := by
  classical
  simp only [Matrix.mul_apply,lieMatrix_single_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hx (x : Fin r → Fin d) :
      (if x s=i ∧ b=Function.update x s j then (1 : ℂ) else 0) =
      (if b s=j ∧ x=Function.update b s i then 1 else 0) := by
    exact if_congr (update_exchange x b s i j) rfl rfl
  simp only [hx]
  by_cases hs : b s=j
  · simp [hs]
  · simp [hs]

theorem lieInvariant_of_tensor_commute {r d : ℕ}
    (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ)
    (hT : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      Commute T (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ))) : LieInvariant T := by
  intro i j a b
  have he := congrFun (congrFun (commute_lieMatrix T hT (Matrix.single i j 1)).eq a) b
  simpa only [mul_lieMatrix_single,lieMatrix_single_mul] using he.symm

theorem tensor_permMatrix {r d : ℕ} (g : Equiv.Perm (Fin d)) (a b : Fin r → Fin d) :
    tensorMatrix (g.permMatrix ℂ) a b=if b=g ∘ a then 1 else 0 := by
  classical
  have hp : ∀ i j, g.permMatrix ℂ i j = if g i=j then (1 : ℂ) else 0 := by
    intro i j
    simp [Equiv.Perm.permMatrix,PEquiv.toMatrix,Equiv.toPEquiv_apply]
  simp only [tensorMatrix,hp]
  rw [prod_delta_eq]
  have hh : (∀ t∈(Finset.univ : Finset (Fin r)), g (a t)=b t) ↔ b=g ∘ a := by
    simp only [Finset.mem_univ,true_implies,funext_iff,Function.comp_apply]
    exact forall_congr' (fun _ => eq_comm)
  simp only [hh]

theorem labelInvariant_of_tensor_commute {r d : ℕ}
    (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ)
    (hT : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      Commute T (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)))
    (g : Equiv.Perm (Fin d)) (a b : Fin r → Fin d) :
    T (g ∘ a) (g ∘ b)=T a b := by
  classical
  have hp : g.permMatrix ℂ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_permMatrix,
      ← Matrix.permMatrix_mul]
    simp
  have hh (c : Fin r → Fin d) : g ∘ b=g ∘ c ↔ b=c := by
    constructor
    · intro he
      funext s
      exact g.injective (congrFun he s)
    · rintro rfl; rfl
  have he := congrFun (congrFun (hT ⟨g.permMatrix ℂ,hp⟩).eq a) (g ∘ b)
  simpa [Matrix.mul_apply,tensor_permMatrix,hh] using he.symm

theorem unitary_tensor_commutant (r d : ℕ) (hrd : r ≤ d)
    (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ)
    (hT : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      Commute T (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ))) :
    ∃ c : Equiv.Perm (Fin r) → ℂ, T = ∑ π, c π • positionMatrix π :=
  lie_label_span hrd T (lieInvariant_of_tensor_commute T hT) (labelInvariant_of_tensor_commute T hT)

end

end KKWeingarten
end

end OAI
