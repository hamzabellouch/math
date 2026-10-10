import Mathlib
import OAI.Computability.MinUncut.Estimates.InnerUniform
import OAI.Computability.MinUncut.Search.OuterParameters

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory GaussianHermite
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A] {m n : ℕ}
lemma firstError_nonneg (f : FoldedProof A) (σ η : ℝ) : 0 ≤ firstError (m := m) (n := n) f σ η := by
  exact Finset.expect_nonneg (fun B _ => integral_nonneg (fun c => (firstRejection_range f B σ η c).1))
lemma secondError_nonneg (f : FoldedProof A) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (σ η : ℝ) :
    0 ≤ secondError (m := m) (n := n) f a σ η := by
  exact Finset.expect_nonneg (fun B _ => Finset.expect_nonneg (fun C _ =>
    mul_nonneg (RowNoise.density_nonneg ha ha1 B C)
      (integral_nonneg (fun c => (secondRejection_range f B C σ η c).1))))
lemma thirdError_nonneg (f : FoldedProof A) (σ η : ℝ) : 0 ≤ thirdError (m := m) (n := n) f σ η := by
  exact Finset.expect_nonneg (fun B _ => integral_nonneg (fun c =>
    Finset.expect_nonneg (fun z _ => integral_nonneg (fun g => integral_nonneg
      (fun l => thirdFailure_nonneg f B η (c+σ•g) l z)))))
end MinUncut.Inner
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] firstError secondError thirdError fourthError atomProbability
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

inductive Test | first | second | third | fourth deriving DecidableEq
instance : Fintype Test where
  elems := {.first,.second,.third,.fourth}
  complete := by intro j; cases j <;> simp

def ProofFamily.testErrors {J : ℝ} (P : InnerParameters J) (O : OuterParameters J P)
    (f : ProofFamily Name I) (equations : S → Equation Name) : Test → ℝ
  | .first =>
  edgeMean equations O.k (fun U h pos => firstError (m := P.m) (n := P.n)
    (f.second (secondQuestion U h pos)) (sourceSigma J) (sourceEta J))
  | .second => edgeMean equations O.k (fun U h pos => secondError (m := P.m) (n := P.n)
    (f.second (secondQuestion U h pos)) ((sourceEta J)^2/P.m) (sourceSigma J) (sourceEta J))
  | .third => edgeMean equations O.k (fun U h pos => thirdError (m := P.m) (n := P.n)
    (f.second (secondQuestion U h pos)) (sourceSigma J) (sourceEta J))
  | .fourth => edgeMean equations O.k (f.fourthTotal (m := P.m) (n := P.n) (sourceSigma J) (sourceEta J))

def budgets {J : ℝ} (P : InnerParameters J) (O : OuterParameters J P) : Test → ℝ
  | .first => 10*sourceSigma J
  | .second => 10*(sourceEta J+sourceEta J)
  | .third => (Fintype.card (Code P.m P.n):ℝ)⁻¹
  | .fourth => O.b4

lemma budgets_pos {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J) (O : OuterParameters J P)
    (j : Test) : 0 < budgets P O j := by
  have hσ := sourceSigma_pos hJ
  have hη := sourceEta_pos hJ
  have hb := O.hb4
  cases j
  · exact mul_pos (by norm_num) hσ
  · exact mul_pos (by norm_num) (add_pos hη hη)
  · exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  · exact hb

omit [Nonempty S] in
lemma edgeMean_nonneg {I : Type*} [Fintype I] (equations : S → Equation Name) (k : ℕ)
    (F : EdgeStatistic Name I) (hF : ∀ U h pos, 0 ≤ F U h pos) : 0 ≤ edgeMean equations k F := by
  exact Finset.expect_nonneg (fun H _ => Finset.expect_nonneg (fun a _ =>
    Finset.expect_nonneg (fun pos _ => hF _ _ _)))

lemma fourthError_nonneg {V A W B : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
    [Fintype A] [AddCommGroup W] [Module F₂ W] [AddTorsor W B] [Fintype B]
    {m n : ℕ} (π : A →ᵃ[F₂] B) (f : FoldedProof A) (g : FoldedProof B) (σ η : ℝ) :
    0 ≤ fourthError (m := m) (n := n) π f g σ η := by
  unfold fourthError
  exact Finset.expect_nonneg (fun C _ => MeasureTheory.integral_nonneg
    (fun c => (comparisonRejection_range f g (pullbackFaces π C) C σ η c).1))

attribute [local irreducible] edgeMean

omit [Nonempty S] in
lemma ProofFamily.testErrors_nonneg {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J) (O : OuterParameters J P)
    (f : ProofFamily Name I) (equations : S → Equation Name) (j : Test) :
    0 ≤ f.testErrors P O equations j := by
  have hm : 0 < P.m := by have := P.hm; omega
  have ha := source_row_rate hJ hm
  cases j <;> rw [ProofFamily.testErrors] <;> apply edgeMean_nonneg <;> intro U h pos
  · exact firstError_nonneg (V := SecondAlphabet (secondQuestion U h pos)) _ _ _
  · exact secondError_nonneg (V := SecondAlphabet (secondQuestion U h pos)) _ ha.1 ha.2.1 _ _
  · exact thirdError_nonneg (V := SecondAlphabet (secondQuestion U h pos)) _ _ _
  · unfold ProofFamily.fourthTotal
    exact fourthError_nonneg (V := FirstDirection U) (W := SecondAlphabet (secondQuestion U h pos)) _ _ _ _ _

def ProofFamily.cost {J : ℝ} (P : InnerParameters J) (O : OuterParameters J P)
    (f : ProofFamily Name I) (equations : S → Equation Name) : ℝ :=
  ∑ j, f.testErrors P O equations j/budgets P O j

omit [Nonempty S] in
lemma ProofFamily.error_le_of_cost {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J) (O : OuterParameters J P)
    (f : ProofFamily Name I) (equations : S → Equation Name) (hcost : f.cost P O equations ≤ J)
    (j : Test) : f.testErrors P O equations j ≤ J*budgets P O j := by
  apply (div_le_iff₀ (budgets_pos hJ P O j)).mp
  exact (Finset.single_le_sum (fun i _ => div_nonneg (f.testErrors_nonneg hJ P O equations i)
    (budgets_pos hJ P O i).le) (Finset.mem_univ j)).trans hcost

attribute [local irreducible] ProofFamily.fourthTotal ProofFamily.atomTotal

lemma ProofFamily.cost_atom_lower {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J)
    (O : OuterParameters J P) (f : ProofFamily Name I) (equations : S → Equation Name)
    (hk : O.k ≤ Fintype.card I) (hc : f.cost P O equations ≤ J) :
    (P.p:ℝ) ≤ edgeMean equations O.k (f.atomTotal (m := P.m) (n := P.n) (sourceSigma J) (sourceEta J) P.θ) := by
  have h1 := f.error_le_of_cost hJ P O equations hc .first
  have h2 := f.error_le_of_cost hJ P O equations hc .second
  have h3 := f.error_le_of_cost hJ P O equations hc .third
  simp only [ProofFamily.testErrors,budgets] at h1 h2 h3
  rw [← div_eq_mul_inv] at h3
  exact f.atomTotal_lower equations hJ P hk h1 h2 h3

lemma ProofFamily.cost_atom_upper [Fintype Name] [Nonempty I] {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J)
    (O : OuterParameters J P) (f : ProofFamily Name I) (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    (hcard : Fintype.card I=O.t) (hc : f.cost P O equations ≤ J) :
    edgeMean equations O.k (f.atomTotal (m := P.m) (n := P.n) (sourceSigma J) (sourceEta J) P.θ) < (P.p:ℝ) := by
  have hk : O.k ≤ Fintype.card I := by simpa only [hcard] using O.hk
  have hm : 0 < P.m := by have := P.hm; omega
  have hn : 0 < P.n := by have := P.hn; omega
  have h4 := f.error_le_of_cost hJ P O equations hc .fourth
  simp only [ProofFamily.testErrors,budgets] at h4
  have hu := f.atomTotal_bound equations hsound hk hm hn (sourceSigma_pos hJ) O.hu P.hθ (sourceEta J)
  have hx := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 64/(P.θ^2*(sourceSigma J)^2))
  have hg := O.hgap
  simp only [hcard] at hu
  linarith

theorem ProofFamily.cost_gt [Fintype Name] [Nonempty I] {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J)
    (O : OuterParameters J P) (f : ProofFamily Name I) (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4) (hcard : Fintype.card I=O.t) :
    J < f.cost P O equations := by
  by_contra! hc
  exact (not_lt_of_ge (f.cost_atom_lower hJ P O equations (by simpa only [hcard] using O.hk) hc)) (f.cost_atom_upper hJ P O equations hsound hcard hc)
end MinUncut.Outer

end
end

end OAI
