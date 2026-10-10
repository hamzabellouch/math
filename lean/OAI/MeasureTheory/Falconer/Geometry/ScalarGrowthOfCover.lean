import OAI.MeasureTheory.Falconer.Geometry.ScalarNonporousCover

namespace OAI

/-! Projection growth from a bound on the original repeated sumset.
 The regularized subset incurs no repeated Pluennecke loss. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_projection_growth_of_sumset {B C P M copies J F : ℕ} {U K K0 κ : ℝ}
    (hC2 : 2 ≤ C) (hCB : C ≤ B) (hP : 18 ≤ P) (hM : 0 < M) (hBpos : 0 < B)
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 (B*M)) (hne : Q.Nonempty)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (k i) (n i))
    (hU : 18*(2:ℝ)^C ≤ U) (hJ : 0 < J)
    (hcontract : (1/2:ℝ)^B*(1+2*(J:ℝ)*U) ≤ 1)
    (hF : 4*(J:ℝ)*U ≤ (F:ℝ)) (hcopies : (2*F+1)*J ≤ copies)
    (X : Finset ℝ) (hQX : Q.image scalarPathCenter ⊆ X)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hlogJ : (1-κ/4)*(B:ℝ)*Real.log 2 ≤ Real.log (J+1:ℝ))
    (hsmall : Real.log ((scalarCells ((1/2:ℝ)^(B*M)) (copies • X)).card:ℝ) ≤
      (1-3*κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hK : 0 < K) (hK0 : 0 < K0)
    (hC : Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
      κ*(C:ℝ)*Real.log 2)
    (hB : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (hscale : 20*Real.log K0 ≤ (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2)
    (hpoint : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass (Q.image scalarPathCenter) u t ≤
        K0*t^κ*((Q.image scalarPathCenter).card:ℝ))
    (A : Finset ℝ) (hA : A.Nonempty) (hAb : ∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass A u t ≤ K*t^κ*(A.card : ℝ)) :
    ∃ t ∈ A, Real.exp ((κ/20)*(P:ℝ)*(M:ℝ)*Real.log 2)*(Q.card:ℝ) <
      ((scalarCells ((1/2:ℝ)^(B*M)) ((Q.image scalarPathCenter)+
        (Q.image scalarPathCenter).image (fun x => t*x))).card:ℝ) := by
  have hporous := scalar_porous_count_of_sumset Q hQ hne k n hlevel hU hJ
    hcontract hF hcopies X hQX hκ hκ1 hBpos hlogJ hsmall
  by_contra hn
  push Not at hn
  have hg := scalar_porous_log_growth hC2 hCB hP Q hQ hne k n hlevel hK hK0 hκ
    (Real.exp_pos _) hC hB hporous hscale hpoint A hA hAb hball hn
  rw [Real.log_exp] at hg
  have hp : (0:ℝ) < (P:ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hm : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hpos : 0 < κ*(P:ℝ)*(M:ℝ)*Real.log 2 :=
    mul_pos (mul_pos (mul_pos hκ hp) hm) (Real.log_pos (by norm_num))
  nlinarith

end Falconer.Regularization

end OAI
