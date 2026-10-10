import OAI.Geometry.TranslativeCovering.PoissonActualBound

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1

namespace BinnedTail
open Finset
open scoped BigOperators

lemma diagram_sum {I : Type u_1} [Fintype I] [DecidableEq I]
    (ν : I → ℝ) (D : I → I → ℝ) (bad : I → I → Prop) [DecidableRel bad]
    {a E g : ℝ} (ha : 0 < a) (hE : 0 ≤ E) (hg : 0 ≤ g)
    (hν : ∀ i,0 ≤ ν i ∧ ν i ≤ 2*a)
    (hself : ∀ i,D i i ≤ ν i^2*E)
    (hcross : ∀ i j,i ≠ j → D i j ≤ if bad i j then g*ν i*ν j else 0) :
    ∑ i,∑ j,D i j ≤ 4*(Fintype.card I:ℝ)*a^2*E+
      4*a^2*g*((univ : Finset (I×I)).filter (fun p => p.1 ≠ p.2 ∧ bad p.1 p.2)).card := by
  let S := (univ : Finset (I×I)).filter (fun p => p.1 ≠ p.2 ∧ bad p.1 p.2)
  have hself' (i : I) : D i i ≤ 4*a^2*E := by
    apply (hself i).trans
    apply mul_le_mul_of_nonneg_right _ hE
    nlinarith only [(hν i).1,(hν i).2]
  have hcross' (i j : I) (hij : i ≠ j) : D i j ≤ if bad i j then 4*a^2*g else 0 := by
    apply (hcross i j hij).trans
    split_ifs with h
    · have hh := mul_le_mul (hν i).2 (hν j).2 (hν j).1 (by linarith only [ha])
      have ht := mul_le_mul_of_nonneg_left hh hg
      nlinarith only [ht]
    · rfl
  have hp (i j : I) : D i j ≤ (if i = j then 4*a^2*E else 0)+
      (if (i,j) ∈ S then 4*a^2*g else 0) := by
    by_cases hij : i = j
    · subst j
      simpa [S] using hself' i
    · simpa only [S,mem_filter,Finset.mem_univ,true_and,hij,ite_false,ne_eq,not_false_eq_true,true_and,zero_add] using hcross' i j hij
  calc
    _ ≤ ∑ i,∑ j,((if i = j then 4*a^2*E else 0)+(if (i,j) ∈ S then 4*a^2*g else 0)) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => hp i j
    _ = _ := by
      simp_rw [sum_add_distrib]
      simp only [sum_ite_eq,Finset.mem_univ,ite_true,sum_const,card_univ,nsmul_eq_mul]
      rw [← Fintype.sum_prod_type (fun p : I×I => if p ∈ S then 4*a^2*g else 0)]
      simp only [← sum_filter,sum_const,nsmul_eq_mul]
      have he : univ.filter (fun p : I×I => p ∈ S) = S := by ext p; simp
      rw [he]
      dsimp [S]
      ring

lemma ratio {m a E h M Δ : ℝ} (hm : 0 < m) (ha : 0 < a) (hE : 0 < E)
    (hh : 0 ≤ h) (hM : m*a ≤ M) (hΔ : 0 < Δ)
    (hbound : Δ ≤ 4*m*a^2*E+40*m^2*a^2*h) :
    1/(8*(E/m+10*h)) ≤ M^2/(2*Δ) := by
  have hb : 0 < 8*(E/m+10*h) := by positivity
  have hma : 0 < m*a := mul_pos hm ha
  have hM2 : (m*a)^2 ≤ M^2 := (sq_le_sq₀ hma.le (hma.le.trans hM)).mpr hM
  apply (div_le_div_iff₀ hb (mul_pos (by norm_num) hΔ)).mpr
  have hi := mul_le_mul_of_nonneg_right hM2 hb.le
  have he : (m*a)^2*(8*(E/m+10*h)) = 2*(4*m*a^2*E+40*m^2*a^2*h) := by
    field_simp
    ring
  rw [he] at hi
  linarith only [hi,hbound]

end BinnedTail

end OAI
