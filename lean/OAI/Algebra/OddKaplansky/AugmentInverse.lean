import OAI.Algebra.OddKaplansky.FiniteInverse

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.LocalAlgebra
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {T : Type portUniverse2} {S : Type portUniverse3} [Field K] [CommGroup T] [sectionInstance49 : Fintype T] [sectionInstance50 : Fintype S] [sectionInstance51 : DecidableEq S]
variable (p : ℕ) [Fact p.Prime] [CharP K p] (hT : ∀ t : T, t^p=1)
variable (j : T →* Multiplicative (Fin 3 → ZMod p)) (hj : Function.Injective j)

def scalarMatrix (Q : Matrix S S (MonoidAlgebra K T)) : Matrix S S (MonoidAlgebra K T) :=
  (Q.map augment).map (algebraMap K (MonoidAlgebra K T))

def scalarInverse (Q : Matrix S S (MonoidAlgebra K T)) : Matrix S S (MonoidAlgebra K T) :=
  (Q.map augment)⁻¹.map (algebraMap K (MonoidAlgebra K T))
lemma scalar_map
    {K : Type contextUniverse1}
    {T : Type contextUniverse2}
    {S : Type contextUniverse3}
    [Field.{contextUniverse1} K]
    [CommGroup.{contextUniverse2} T]
    [Fintype.{contextUniverse2} T]
    [Fintype.{contextUniverse3} S]
    [DecidableEq.{contextUniverse3 + 1} S] (A : Matrix S S K) :
    (A.map (algebraMap K (MonoidAlgebra K T))).map augment=A := by
  ext s t
  exact (augment (K := K) (T := T)).commutes (A s t)
lemma scalar_products
    {K : Type contextUniverse1}
    {T : Type contextUniverse2}
    {S : Type contextUniverse3}
    [Field.{contextUniverse1} K]
    [CommGroup.{contextUniverse2} T]
    [Fintype.{contextUniverse2} T]
    [Fintype.{contextUniverse3} S]
    [DecidableEq.{contextUniverse3 + 1} S] (Q : Matrix S S (MonoidAlgebra K T)) (hQ : (Q.map augment).det ≠ 0) :
    scalarMatrix Q*scalarInverse Q=1 ∧ scalarInverse Q*scalarMatrix Q=1 := by
  have hu : IsUnit (Q.map augment).det := isUnit_iff_ne_zero.mpr hQ
  constructor
  · rw [scalarMatrix,scalarInverse,← Matrix.map_mul,Matrix.mul_nonsing_inv _ hu,Matrix.map_one] <;> simp only [map_zero,map_one]
  · rw [scalarMatrix,scalarInverse,← Matrix.map_mul,Matrix.nonsing_inv_mul _ hu,Matrix.map_one] <;> simp only [map_zero,map_one]
lemma error_entry_mem (Q : Matrix S S (MonoidAlgebra K T)) :
    ∀ s t, (scalarInverse Q*(Q-scalarMatrix Q)) s t∈RingHom.ker (augment (K := K) (T := T)).toRingHom := by
  have hh : (scalarInverse Q*(Q-scalarMatrix Q)).map augment=0 := by
    rw [Matrix.map_mul,Matrix.map_sub,scalarMatrix,scalar_map,sub_self,mul_zero] ; simp
  intro s t
  exact congrFun (congrFun hh s) t
include hT hj in
lemma error_nil (Q : Matrix S S (MonoidAlgebra K T)) :
    (scalarInverse Q*(Q-scalarMatrix Q))^(3*(p-1)+1)=0 := by
  funext s t
  have hm := FiniteMatrixInverse.pow_entry_mem (RingHom.ker (augment (K := K) (T := T)).toRingHom)
    (scalarInverse Q*(Q-scalarMatrix Q)) (error_entry_mem Q) (3*(p-1)+1) s t
  rw [kernel_nil_three p hT j hj] at hm
  exact hm
include hT hj in

lemma matrix_inverse_formula (Q : Matrix S S (MonoidAlgebra K T)) (hQ : (Q.map augment).det≠0) :
    Q⁻¹=FiniteMatrixInverse.series (scalarInverse Q*(Q-scalarMatrix Q)) (3*(p-1)+1)*scalarInverse Q :=
  FiniteMatrixInverse.inverse_formula Q (scalarMatrix Q) (scalarInverse Q)
    (scalar_products Q hQ).1 (scalar_products Q hQ).2 _ (error_nil p hT j hj Q)
end
end OddKaplansky.LocalAlgebra

end

end OAI
