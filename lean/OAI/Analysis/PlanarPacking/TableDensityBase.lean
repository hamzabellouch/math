import OAI.Analysis.PlanarPacking.Grid
import OAI.Analysis.PlanarPacking.BasisIntervals
import OAI.Analysis.PlanarPacking.Certificate.TableData

namespace OAI

/-!
# Finite cardinal densities

Finite rational coefficient families determine the densities used in the quadrature estimates.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
open scoped BigOperators

noncomputable def tableNum (i d : Bool) (n : ℕ) : ℤ :=
  if n=0 then (if d then (if i then -3680000000 else 4400000000) else (if i then 0 else 10000000000))
  else if d then (if i then (tableRaw n).2.2.2 else (tableRaw n).2.1)
    else (if i then (tableRaw n).2.2.1 else (tableRaw n).1)

lemma tableNum_coefficient (i d : Bool) (n : ℕ) :
    (tableNum i d n:ℝ)/10000000000 = (if d then (tableD i n:ℝ) else (tableC i n:ℝ)) := by
  cases i <;> cases d <;> by_cases hn : n=0 <;>
    simp [tableNum,tableD,tableC,hn] <;> norm_num

lemma scaled_table_basis {a : CBox} {n j : ℕ} {w t : ℝ} {d : Bool}
    (ha : a.Contains ((w:ℂ)*basisFunction d n j t)) (i : Bool) :
    (a.scale (tableNum i d n) 10000000000).Contains
      (((if d then (tableD i n:ℝ) else (tableC i n:ℝ)):ℂ)*((w:ℂ)*basisFunction d n j t)) := by
  have hh := CBox.contains_scale ha (tableNum i d n) 10000000000 (by norm_num)
  have hc := congrArg Complex.ofReal (tableNum_coefficient i d n)
  push_cast at hc
  cases d <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hc ⊢ <;>
    rw [← hc] <;> simpa only [Int.cast_ofNat] using hh

noncomputable def tableDensity (i : Bool) (j : ℕ) (t : ℂ) : ℂ :=
  finiteDensity (fun n => (tableC i n:ℝ)) (fun n => (tableD i n:ℝ)) j t

lemma tableDensity_weighted (i : Bool) (j : ℕ) (w t : ℝ) :
    (w:ℂ)*tableDensity i j t =
      ∑ n : Fin 101, (((tableC i n:ℝ):ℂ)*((w:ℂ)*basisFunction false n j t) +
        ((tableD i n:ℝ):ℂ)*((w:ℂ)*basisFunction true n j t)) := by
  rw [tableDensity,finiteDensity,Finset.mul_sum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [basisFunction,Bool.false_eq_true,ite_false,ite_true,complexU_ofReal,complexV_ofReal]
  ring

lemma cached_density_rule_contains
    {c k : Fin 6 → Fin 16 → Fin 16 → CBox} {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hc : ∀ j i v, (c j i v).Contains ((fejerWeight (16*i.val+v.val):ℂ)*
      f j.val (quadraturePoint j.val (16*i.val+v.val))))
    (hk : ∀ j i v, (k j i v).Contains (g (quadraturePoint j.val (16*i.val+v.val)))) :
    (cachedMomentRuleBox c k).Contains
      (∑ j : Fin 6, pieceRule (fun t => f j.val t*g t) j.val) := by
  unfold cachedMomentRuleBox pieceRule
  apply finSum_contains
  intro j
  have ht (v : ℕ) : diskAffine j.val (fejerNode v) = (quadraturePoint j.val v:ℂ) := by
    unfold diskAffine diskCenter quadraturePoint
    push_cast
    ring
  simp_rw [ht]
  rw [← sum_fin_square 16 (fun v => (fejerWeight v:ℂ)*(f j.val (quadraturePoint j.val v)*g (quadraturePoint j.val v)))]
  have hh := finSum_contains (fun i => finSum_contains (fun v => CBox.contains_mul (hc j i v) (hk j i v)))
  have hs := CBox.contains_scale hh 1 6 (by norm_num)
  simpa only [Int.cast_one,Int.cast_ofNat,mul_assoc] using hs

end SharpPlanar

namespace SharpPlanar
lemma table_range_mass (a : Bool) :
    ∑ n ∈ Finset.range 101, (|(tableC a n:ℝ)|+|(tableD a n:ℝ)|) ≤ 3 := by
  have hq : ∑ n ∈ Finset.range 101, (|tableC a n|+|tableD a n|) ≤ 3 := by
    cases a <;> decide +kernel
  exact_mod_cast hq
end SharpPlanar

end OAI
