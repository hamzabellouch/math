import OAI.Probability.DilutedSpin.ActualCharging
import OAI.Probability.DilutedSpin.ColoredAnchor

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

lemma expect_pi_comm {V R Ω : Type*} [Fintype V] [Fintype R] [Fintype Ω]
    [DecidableEq V] [DecidableEq R] (P : V → R → FiniteLaw Ω)
    (f : (V → R → Ω) → ℝ) :
    (pi (fun v => pi (P v))).expect f =
      (pi (fun r => pi (fun v => P v r))).expect (fun x => f (fun v r => x r v)) := by
  unfold expect
  apply Fintype.sum_equiv (Equiv.piComm (fun (_ : V) (_ : R) => Ω))
  intro x
  change (∏ v, ∏ r, (P v r).weight (x v r)) * f x =
    (∏ r, ∏ v, (P v r).weight (x v r)) * f x
  rw [Finset.prod_comm]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.MarkSelector
open scoped BigOperators

noncomputable def pathColor {C R : Type} [DecidableEq C] [Fintype R] {n : ℕ}
    (a b : R → C) (d : R → Fin n) (c : C) (y : FinitePath (R → Bool) n) : ℝ :=
  ∏ r, (if c = a r then sign (pathCoordinate n y (d r) r) else 1) *
    (if c = b r then sign (pathCoordinate n y (d r) r) else 1)

lemma abs_pathColor {C R : Type} [DecidableEq C] [Fintype R] {n : ℕ}
    (a b : R → C) (d : R → Fin n) (c : C) (y : FinitePath (R → Bool) n) :
    |pathColor a b d c y| = 1 := by
  unfold pathColor
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro r _
  rw [abs_mul]
  split_ifs <;> simp only [abs_sign,abs_one,mul_one]

end DilutedSpinGlass.MarkSelector

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
open MarkSelector
noncomputable local instance {n : ℕ} (S : PrescribedTree n) : DecidableEq (Edge S) := Classical.decEq _

 
theorem actual_tree_selector {C R : Type} [Fintype C] [DecidableEq C]
    [Fintype R] [DecidableEq R] {n : ℕ} (S : PrescribedTree n)
    (a b : R → C) (d : R → Fin n) (pos : C → S.Leaf) :
    (S.sampleLaw (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => rademacher)))).expect
      (fun x => ∏ c, pathColor a b d c (S.pathAt (pos c) x)) =
        ∏ r, if (d r).val+1 ≤ splitDepth S (pos (a r)) (pos (b r)) then (1:ℝ) else 0 := by
  have he (x : Sample (R → Bool) S) :
      (∏ c, pathColor a b d c (S.pathAt (pos c) x)) =
      ∏ r, sign (pathCoordinate n (S.pathAt (pos (a r)) x) (d r) r) *
        sign (pathCoordinate n (S.pathAt (pos (b r)) x) (d r) r) := by
    simp only [pathColor]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro r _
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq',Finset.mem_univ,ite_true]
  simp_rw [he]
  rw [expect_markPrior]
  simp_rw [coordinate_pathAt,vertexValues_of]
  rw [FiniteLaw.expect_pi_comm]
  rw [MarkSelector.requirements_selector]
  apply Finset.prod_congr rfl
  intro r _
  simp only [leafEdge_eq_iff]

/-- The same selector after adjoining the fresh mark prior to ANY previous
physical reservoir, including its complete existing mark alphabet and tilt. -/
theorem actual_tree_selector_prod {Ω C R : Type} [Fintype Ω]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b : R → C) (d : R → Fin n) (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    (S.sampleLaw (KernelTower.prod n T
      (markPrior n (fun _ => FiniteLaw.pi (fun _ : R => rademacher))))).expect
      (fun x => f (sampleFst S x) * ∏ c, pathColor a b d c
        (KernelTower.pathSnd n (S.pathAt (pos c) x))) =
      (S.sampleLaw T).expect f *
        ∏ r, if (d r).val+1 ≤ splitDepth S (pos (a r)) (pos (b r)) then (1:ℝ) else 0 := by
  simp_rw [← pathAt_sampleSnd]
  rw [expect_prod_separated S T _ f (fun x => ∏ c, pathColor a b d c (S.pathAt (pos c) x)),
    actual_tree_selector]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
