import OAI.Analysis.Quantum.DimensionTen.EvaluationMinors

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def quadraticPairs : Fin 10 → Fin 4 × Fin 4 :=
  ![(0,0), (0,3), (0,2), (0,1), (3,3), (2,3), (2,2), (1,3), (1,2), (1,1)]

def quadraticIndex (i : Fin 10) : QuadraticIndex :=
  ⟨quadraticPairs i, by fin_cases i <;> decide⟩

lemma quadraticIndex_bijective : Function.Bijective quadraticIndex := by decide

def quadraticEquiv : Fin 10 ≃ QuadraticIndex := Equiv.ofBijective quadraticIndex quadraticIndex_bijective

lemma low_quadratic (t : Fin 3 → ℂ) (i : Fin 10) :
    low t (Fin.castLE (by decide) i) =
      chart t (quadraticEquiv i).val.1 * chart t (quadraticEquiv i).val.2 := by
  change _ = chart t (quadraticPairs i).1 * chart t (quadraticPairs i).2
  have hc2 : Fin.cons (α := fun _ : Fin 4 => ℂ) 1 t 2 = t 1 := rfl
  have hc3 : Fin.cons (α := fun _ : Fin 4 => ℂ) 1 t 3 = t 2 := rfl
  fin_cases i <;> simp [low, mon, monExps, quadraticPairs, chart, Fin.prod_univ_succ, hc2, hc3] <;> ring

lemma quadraticEval_low (q : QuadraticIndex → ℂ) (t : Fin 3 → ℂ) :
    quadraticEval q (chart t) =
      ∑ i : Fin 10, q (quadraticEquiv i) * low t (Fin.castLE (by decide) i) := by
  rw [quadraticEval, ← Equiv.sum_comp quadraticEquiv]
  apply Finset.sum_congr rfl
  intro i hi
  rw [low_quadratic, mul_assoc]

lemma quadraticCoeffs_ne {q : QuadraticIndex → ℂ} (hq : q ≠ 0) :
    q ∘ quadraticEquiv ≠ 0 := by
  intro h
  apply hq
  ext i
  obtain ⟨j, rfl⟩ := quadraticEquiv.surjective i
  exact congrFun h j

end DimensionTen.Border

end
end

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma quadratic_zero_bound (q : QuadraticIndex → ℂ) (hq : q ≠ 0) :
    (Finset.univ.filter (fun k : Fin 20 => quadraticEval q (chart (points k)) = 0)).card ≤ 9 := by
  classical
  by_contra hh
  obtain ⟨s, hs, hc⟩ := Finset.exists_subset_card_eq (show 10 ≤
    (Finset.univ.filter (fun k : Fin 20 => quadraticEval q (chart (points k)) = 0)).card by omega)
  let e : Fin 10 ≃ s := (Finset.equivFinOfCardEq hc).symm
  let b : Fin 10 → Fin 20 := fun i => e i
  have hb : Function.Injective b := Subtype.val_injective.comp e.injective
  let M : Matrix (Fin 10) (Fin 10) ℂ := fun i j => low (points (b j)) (firstTen i)
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (ten_complex_minor b hb))
  have hz : Matrix.vecMul (q ∘ quadraticEquiv) M = Matrix.vecMul 0 M := by
    rw [Matrix.zero_vecMul]
    ext j
    have hqj := (Finset.mem_filter.mp (hs (e j).property)).2
    rw [quadraticEval_low] at hqj
    exact hqj
  exact quadraticCoeffs_ne hq ((Matrix.vecMul_injective_iff_isUnit.mpr hunit) hz)

end DimensionTen.Border

end
end

end OAI
