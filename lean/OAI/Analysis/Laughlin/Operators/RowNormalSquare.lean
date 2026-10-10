import OAI.Analysis.Laughlin.Fock.NormalSquare

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem create_create_inner (Q : ℕ) (i j : Fin (Q+1)) (y z : Space Q) :
    occupationInner Q (create i y) (create j z) =
      delta i j * occupationInner Q y z -
        occupationInner Q (annihilate j y) (annihilate i z) := by
  rw [create_annihilate_adjoint]
  change occupationInner Q y ((annihilate i * create j) z) = _
  rw [annihilate_create]
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    Module.End.mul_apply,occupationInner_sub_right,occupationInner_smul_right,
    annihilate_create_inner]

theorem row_normal_square {I : Type*} [Fintype I] [DecidableEq I]
    (Q : ℕ) (m : I → Fin (Q+1)) (hm : Function.Injective m)
    (ell : ℝ) (u : Space Q) (v : I → Space Q) :
    (occupationNormSq Q ((ell : ℂ) • u + ∑ i, create (m i) (v i)) : ℂ) =
      (ell : ℂ)^2 * (occupationNormSq Q u : ℂ) +
      (∑ i, (ell : ℂ) * (occupationInner Q (annihilate (m i) u) (v i) +
        occupationInner Q (v i) (annihilate (m i) u))) +
      (∑ i, (occupationNormSq Q (v i) : ℂ)) -
      ∑ i, ∑ j, occupationInner Q (annihilate (m j) (v i)) (annihilate (m i) (v j)) := by
  rw [← occupationInner_self]
  simp only [occupationInner_add_left,occupationInner_add_right,occupationInner_smul_left,
    occupationInner_smul_right,Complex.star_def,Complex.conj_ofReal,
    occupationInner_sum_left,occupationInner_sum_right]
  have hd (i j : I) : delta (m i) (m j) = if i=j then (1 : ℂ) else 0 := by
    simp only [delta,hm.eq_iff]
  have he : (∑ i, ∑ j, occupationInner Q (create (m i) (v i)) (create (m j) (v j))) =
      (∑ i, (occupationNormSq Q (v i) : ℂ)) -
      ∑ i, ∑ j, occupationInner Q (annihilate (m j) (v i)) (annihilate (m i) (v j)) := by
    simp_rw [create_create_inner,hd]
    simp [Finset.sum_sub_distrib,occupationInner_self]
  rw [Finset.sum_comm] at he
  simp only [Finset.sum_add_distrib]
  rw [he]
  simp only [create_annihilate_adjoint,annihilate_create_inner,occupationInner_self,
    Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  ring

end Laughlin.Fock

end OAI
