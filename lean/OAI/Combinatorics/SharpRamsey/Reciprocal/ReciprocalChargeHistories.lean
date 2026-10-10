import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalActualCharges

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

def Law.revealRest (p : Law (ι→α)) (E : Finset ι) (z : E→α) : Law (↥(Eᶜ)→α) :=
  (p.cond (fun x (i:E) => x i) z).restrict Eᶜ

variable {A B : Type*} [Fintype A] [Fintype B]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
lemma tupleFlags_cond_restrict (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    (hf : tupleFlags p v w) (E : Finset ι) (z : E→A×B)
    (hz : (p.restrict E).mass z≠0) :
    tupleFlags (A:=A) (B:=B) (ι := ↥(Eᶜ)) (p.revealRest E z) v w := by
  intro x hx i
  obtain ⟨y,hy,rfl⟩ := (p.cond (fun x (i:E) => x i) z).map_support _ x hx
  exact hf y (p.cond_support _ z hz y hy).1 i

omit [FiniteDimensional K V] in

lemma rectangleBound_cond_restrict (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    {M : ℝ} (ho : rectangleBound p v w M) (E : Finset ι) (z : E→A×B)
    (hz : (p.restrict E).mass z≠0) :
    rectangleBound (A:=A) (B:=B) (ι := ↥(Eᶜ)) (p.revealRest E z) v w M := by
  intro x hx W
  obtain ⟨y,hy,rfl⟩ := (p.cond (fun x (i:E) => x i) z).map_support _ x hx
  have ht := ho y (p.cond_support _ z hz y hy).1 W
  refine le_trans ?_ ht
  apply Nat.cast_le.mpr
  apply card_le_card_of_injOn (fun (i : (Eᶜ : Finset ι)) => (i:ι))
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
  · exact Subtype.val_injective.injOn

lemma reciprocalCharges_history_sum (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    {ρ M : ℝ} (hρ : 0≤ρ) (hM : 0≤M) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (hf : tupleFlags p v w) (ho : rectangleBound p v w M)
    (E : Finset ι) (z : E→A×B) (hz : (p.restrict E).mass z≠0) :
    ∑ i,∑ j,(reciprocalCharges (A:=A) (B:=B) (ι := ↥(Eᶜ))
      (p.revealRest E z) v w ρ r s i j:ℝ)
      ≤2*Fintype.card ι*M := by
  have hh := reciprocalCharges_sum (A:=A) (B:=B) (ι := ↥(Eᶜ))
    (p.revealRest E z) v w hρ hsum
    (tupleFlags_cond_restrict p v w hf E z hz)
    (rectangleBound_cond_restrict p v w ho E z hz)
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_right _ hM
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Nat.cast_le.mpr (Fintype.card_subtype_le _)

end
end SharpLogRamsey.Selection

end

end OAI
