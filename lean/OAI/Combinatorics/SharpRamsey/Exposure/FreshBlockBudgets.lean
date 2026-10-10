import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.RemainingEmbedding

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {B X ι : Type*} [Fintype B] [Fintype X] [Fintype ι] [DecidableEq B] [DecidableEq ι]

theorem selected_absorption (e : B×X ↪ ι) (M : (B→X)→ι→ℝ)
    (hM : ∀ f i,0≤M f i)
    (hupdate : ∀ b x f y,M (Function.update f b y) (e (b,x))=M f (e (b,x))) :
    (Fintype.card X:ℝ)*(∑ f : B→X, ∑ i∈freshRepresentatives e f,M f i)≤
      ∑ f : B→X,∑ i,M f i := by
  have hsel (f : B→X) : (∑ i∈freshRepresentatives e f,M f i)=∑ b,M f (e (b,f b)) := by
    apply sum_image
    intro b _ c _ he
    exact (Prod.mk.inj (e.injective he)).1
  simp_rw [hsel]
  rw [sum_comm,mul_sum]
  have hb (b : B) : (Fintype.card X:ℝ)*(∑ f : B→X,M f (e (b,f b)))=
      ∑ f : B→X,∑ x : X,M f (e (b,x)) :=
    fresh_draw_identity b (fun x f => M f (e (b,x))) (hupdate b)
  simp_rw [hb]
  rw [sum_comm]
  apply sum_le_sum
  intro f _
  have hh := sum_le_sum_of_subset_of_nonneg (s:=univ.map e) (t:=univ)
    (f:=M f) (subset_univ _) (fun i _ _ => hM f i)
  simpa only [sum_map,Fintype.sum_prod_type] using hh

theorem selected_fixed_observable (e : B×X ↪ ι) (δ : ι→ℝ) (hδ : ∀ i,0≤δ i) :
    (Fintype.card X:ℝ)*(∑ f : B→X, ∑ i∈freshRepresentatives e f,δ i)≤
      (Fintype.card (B→X):ℝ)*∑ i,δ i := by
  simpa only [sum_const,card_univ,nsmul_eq_mul] using
    selected_absorption e (fun _=>δ) (fun _=>hδ) (by intros; rfl)

def maximumCharge (c : ι→ι→ℝ≥0) (i : ι) (J : Finset ι) : ℝ≥0 := J.sup (c i)

omit [Fintype ι] [DecidableEq ι] in
lemma maximumCharge_le_sum (c : ι→ι→ℝ≥0) (i : ι) (J : Finset ι) :
    (maximumCharge c i J:ℝ)≤∑ j∈J,(c i j:ℝ) := by
  have hh : maximumCharge c i J≤∑ j∈J,c i j := by
    apply Finset.sup_le
    intro j hj
    exact single_le_sum (fun j _ => (zero_le : (0:ℝ≥0)≤c i j)) hj
  exact_mod_cast hh

theorem selected_charge_absorption (e : B×X ↪ ι) (own : ι→Option B)
    (hown : ∀ b x,own (e (b,x))=some b) (c : ι→ι→ℝ≥0) :
    (Fintype.card X:ℝ)*(∑ f : B→X, ∑ i∈freshRepresentatives e f,
      (maximumCharge c i (otherRepresentatives e own f i):ℝ))≤
      ∑ f : B→X,∑ i,(maximumCharge c i (otherRepresentatives e own f i):ℝ) := by
  apply selected_absorption
  · intros; positivity
  · intro b x f y
    rw [otherRepresentatives_update e own hown]

end
end SharpLogRamsey.Selection

end

end OAI
