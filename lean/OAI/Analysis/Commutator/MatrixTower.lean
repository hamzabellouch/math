import Mathlib
import OAI.Analysis.Commutator.MatrixStageExtension

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixTower

open TracialGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure Stage (M : VonNeumannAlgebra H) where
  I : Type
  finite : Fintype I
  dec : DecidableEq I
  nonempty : Nonempty I
  hom : Matrix I I ℂ →⋆ₐ[ℂ] M

attribute [instance] Stage.finite Stage.dec Stage.nonempty

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hnormal : NormalGNS.BoundedWOTContinuous M τ)
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
  (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)

include hτ hnormal hfaith hone hfac hdiffuse in
lemma exists_stage_extension (F : Stage M) (x : M) (hx : IsSelfAdjoint x)
    {ε : ℝ} (hε : 0<ε) :
    ∃ G : Stage M, 2*Fintype.card F.I≤Fintype.card G.I ∧ F.hom.range≤G.hom.range ∧
      ‖algebraVector τ (expectation G.hom x-τ x • (1:M))‖<ε := by
  obtain ⟨I,hI,hd,hn,φ,_,hc,hi,he⟩ :=
    MatrixStageExtension.exists_extension M τ hτ hnormal hfaith hone hfac hdiffuse F.hom x hx hε
  exact ⟨⟨I,hI,hd,hn,φ⟩,hc,hi,he⟩

def scalarStage : Stage M where
  I := Unit
  finite := inferInstance
  dec := inferInstance
  nonempty := inferInstance
  hom := MatrixUnits.representation (fun _ _ => (1:M)) (by intros; simp)
    (by intros; simp) (by simp)

variable (x : ℕ → M) (hx : ∀ j,IsSelfAdjoint (x j))

def next (n : ℕ) (F : Stage M) : Stage M :=
  Classical.choose (exists_stage_extension M τ hτ hnormal hfaith hone hfac hdiffuse F
    (x (Nat.unpair n).1) (hx _) (show 0<((Nat.unpair n).2+1:ℝ)⁻¹ by positivity))

lemma next_spec (n : ℕ) (F : Stage M) :
    2*Fintype.card F.I≤Fintype.card (next M τ hτ hnormal hfaith hone hfac hdiffuse x hx n F).I ∧
    F.hom.range≤(next M τ hτ hnormal hfaith hone hfac hdiffuse x hx n F).hom.range ∧
    ‖algebraVector τ (expectation (next M τ hτ hnormal hfaith hone hfac hdiffuse x hx n F).hom
      (x (Nat.unpair n).1)-τ (x (Nat.unpair n).1) • (1:M))‖<((Nat.unpair n).2+1:ℝ)⁻¹ :=
  Classical.choose_spec (exists_stage_extension M τ hτ hnormal hfaith hone hfac hdiffuse F
    (x (Nat.unpair n).1) (hx _) (show 0<((Nat.unpair n).2+1:ℝ)⁻¹ by positivity))

def tower : ℕ → Stage M
  | 0 => scalarStage M
  | n+1 => next M τ hτ hnormal hfaith hone hfac hdiffuse x hx n
      (tower n)

lemma tower_increasing : Monotone (fun n =>
    (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx n).hom.range) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (next_spec M τ hτ hnormal hfaith hone hfac hdiffuse x hx n _).2.1

lemma tower_size (n : ℕ) : n+1≤
    Fintype.card (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx n).I := by
  induction n with
  | zero => exact Fintype.card_pos (α:=Unit)
  | succ n ih =>
    have he := (next_spec M τ hτ hnormal hfaith hone hfac hdiffuse x hx n
      (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx n)).1
    change 2*Fintype.card (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx n).I≤
      Fintype.card (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx (n+1)).I at he
    omega

lemma tower_requirement (j : ℕ) {ε : ℝ} (hε : 0<ε) : ∃ n,
    ‖algebraVector τ (expectation (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx n).hom
      (x j)-τ (x j) • (1:M))‖<ε := by
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
  refine ⟨Nat.pair j k+1,?_⟩
  have he := (next_spec M τ hτ hnormal hfaith hone hfac hdiffuse x hx (Nat.pair j k)
    (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx (Nat.pair j k))).2.2
  simp only [Nat.unpair_pair] at he
  exact he.trans (by simpa only [one_div] using hk)

end Kadison.MatrixTower

end

end
end

end OAI
