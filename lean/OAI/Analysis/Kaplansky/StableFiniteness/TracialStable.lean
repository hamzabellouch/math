import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

theorem stablyFinite_of_faithful_trace (τ : TracialState A)
    (hfaith : ∀ a : A, τ.functional (star a*a) = 0 → a=0) : StablyFinite A := by
  intro n hn v hv
  let tr (x : CStarMatrix (Fin n) (Fin n) A) := ∑ i, τ.functional (x i i)
  have hcyc (x y : CStarMatrix (Fin n) (Fin n) A) : tr (x*y) = tr (y*x) := by
    simp only [tr,CStarMatrix.mul_apply,map_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    exact τ.tracial _ _
  let q := v*star v
  have hq : q*q=q := by
    dsimp [q]
    calc
      v*star v*(v*star v) = v*(star v*v)*star v := by noncomm_ring
      _ = v*star v := by rw [hv,mul_one]
  let p := 1-q
  have hpstar : star p=p := by simp [p,q,star_mul]
  have hpp : star p*p=p := by
    rw [hpstar]
    change (1-q)*(1-q)=1-q
    calc
      _ = 1-q-q+q*q := by noncomm_ring
      _ = 1-q := by rw [hq]; abel
  have htr : tr p = 0 := by
    change ∑ i, τ.functional ((1-q) i i) = 0
    simp only [CStarMatrix.sub_apply,map_sub,Finset.sum_sub_distrib]
    change tr 1 - tr (v*star v) = 0
    rw [hcyc,hv,sub_self]
  have hz : ∑ i : Fin n, ∑ j : Fin n, τ.functional (star (p j i)*p j i) = 0 := by
    have he := hpp
    have ht := congrArg tr he
    simpa only [tr,CStarMatrix.mul_apply,CStarMatrix.star_apply,map_sum,htr] using ht.trans htr
  have hnon (i j : Fin n) : 0 ≤ τ.functional (star (p j i)*p j i) :=
    τ.functional.map_nonneg (star_mul_self_nonneg _)
  have hp : p=0 := by
    ext i j
    apply hfaith
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnon i j))).mp hz j (Finset.mem_univ j)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnon j k)).mp hi i (Finset.mem_univ i)
  exact (sub_eq_zero.mp hp).symm


end KaplanskyConsequences

end

end OAI
