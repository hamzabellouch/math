import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalCovariance
import OAI.Combinatorics.PolynomialVacuum.Algebra.Ring

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

theorem fusionPair_four_point (a b : ℂ) :
  fusionPair b a * fusionPair b (T*a) = fusionPair a b * fusionPair a (T*b) := by
 simp only [fusionPair,T,t]
 vacuum_ring_finish

theorem fusionPair_successor_zero (a : ℂ) : fusionPair (T*a) a=0 := by
 simp only [fusionPair,T,t]
 vacuum_ring_finish

theorem fusionPair_second_successor_zero (a : ℂ) : fusionPair a (T*(T*a))=0 := by
 simp only [fusionPair,T]
 ring

noncomputable def fusionProduct (a : ℂ) (X : ℕ → ℂ) (m : ℕ) : ℂ :=
 ∏ k ∈ Finset.range m, fusionPair a (X k)

noncomputable def naturalFusion (n i : ℕ) (X : ℕ → ℂ) : ℂ :=
 (1+T)*X i*fusionProduct (X i) (skipTwo i X) n

theorem fusionProduct_skipOne (a : ℂ) (X : ℕ → ℂ) (m i : ℕ) (hi : i ≤ m) :
  fusionProduct a (skipOne i X) m * fusionPair a (X i)=fusionProduct a X (m+1) := by
 let j : Fin (m+1) := ⟨i,by omega⟩
 have hv (k : Fin m) : (j.succAbove k).val=if k.val < i then k.val else k.val+1 := by
  simp only [Fin.succAbove,Fin.lt_def,j,Fin.val_castSucc]
  split_ifs <;> rfl
 have h := Fin.prod_univ_succAbove (fun k : Fin (m+1) => fusionPair a (X k.val)) j
 simp only [fusionProduct,← Fin.prod_univ_eq_prod_range,skipOne,← hv]
 simpa only [j,Fin.val_mk,mul_comm] using h.symm

end PolynomialVacuumAlgebra

end OAI
