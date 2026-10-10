import OAI.NumberTheory.Ostmann.Construction.InitialEtaPrior

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.RepeatedPriorBounds
open InitialEta

def positionEnvelope {b s : ℕ} {ι : Type*} (A B : ℝ) (i : Position b s ι) : ℝ :=
  match i.2 with
  | .inl _ => B
  | .inr (.inl _) => A
  | .inr (.inr (.inl _)) => A
  | .inr (.inr (.inr _)) => B

theorem positionEnvelope_prod {b s : ℕ} {ι : Type*} [Fintype ι] (A B : ℝ) :
    ∏i : Position b s ι,positionEnvelope A B i =
      A^(2*b+2*s)*B^(2+2*Fintype.card ι) := by
  simp only [Position,HalfPosition,Fintype.prod_prod_type,
    Fintype.prod_sum_type,positionEnvelope,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,Fintype.card_bool,Fintype.card_unique]
  simp only [two_mul,pow_add,pow_succ,pow_zero]
  ring

theorem jointPrior_mass_le (giant bulk spectator : PrimeSource) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (aux : ι → PrimeSource) (b s : ℕ)
    (A B : ℝ)
    (hg : ∀p : giant.Sample,giant.law.mass p≤B/(p:ℕ))
    (hb : ∀p : bulk.Sample,bulk.law.mass p≤A/(p:ℕ))
    (hs : ∀p : spectator.Sample,spectator.law.mass p≤A/(p:ℕ))
    (ha : ∀i,∀p : (aux i).Sample,(aux i).law.mass p≤B/(p:ℕ))
    (x : JointSample giant bulk spectator aux b s) :
    (jointPrior giant bulk spectator aux b s).mass x≤
      A^(2*b+2*s)*B^(2+2*Fintype.card ι)/(∏i,(tupleValues x i:ℝ)) := by
  rw [jointPrior_mass]
  calc
    _ ≤ ∏i : Position b s ι,positionEnvelope A B i/(tupleValues x i:ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact (tupleSource giant bulk spectator aux b s i).law.mass_nonneg _
      · intro i hi
        rcases i with ⟨h,i⟩
        rcases i with u | (j | (j | j))
        · exact hg _
        · exact hb _
        · exact hs _
        · exact ha j _
    _ = _ := by rw [Finset.prod_div_distrib,positionEnvelope_prod]

end Ostmann.Construction.RepeatedPriorBounds

end

end OAI
