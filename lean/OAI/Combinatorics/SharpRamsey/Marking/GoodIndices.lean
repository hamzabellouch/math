import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.FreshBlockCollision

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {β B X ι : Type*} [Fintype β] [Fintype B] [Fintype X] [Fintype ι]
  [DecidableEq B] [DecidableEq ι]

def badIndices (p : Law (ι→β)) (e : B×X ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) (f : B→X) : Finset ι :=
  univ.filter (fun i => D<J-entropy (p.marginal i) ∨
    ∃ j∈otherRepresentatives e own f i,a<(pairInformation p i j:ℝ)+(c i j:ℝ))

omit [Fintype X] in
lemma not_badIndices (p : Law (ι→β)) (e : B×X ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) (f : B→X) (i : ι) :
    i∉badIndices p e own c J D a f ↔
      J-entropy (p.marginal i)≤D ∧
      ∀ j∈otherRepresentatives e own f i,(pairInformation p i j:ℝ)+(c i j:ℝ)≤a := by
  simp [badIndices]

omit [Fintype X] in
lemma badIndices_update_self (p : Law (ι→β)) (e : B×X ↪ ι)
    (own : ι→Option B) (hown : ∀ b x,own (e (b,x))=some b)
    (c : ι→ι→NNReal) (J D a : ℝ) (b : B) (x y : X) (f : B→X) :
    e (b,x)∈badIndices p e own c J D a (Function.update f b y) ↔
      e (b,x)∈badIndices p e own c J D a f := by
  simp only [badIndices,mem_filter]
  rw [otherRepresentatives_update e own hown]

theorem selected_bad_absorption (p : Law (ι→β)) (e : B×X ↪ ι)
    (own : ι→Option B) (hown : ∀ b x,own (e (b,x))=some b)
    (c : ι→ι→NNReal) (J D a : ℝ) :
    (Fintype.card X:ℝ)*(∑ f : B→X,
      ((freshRepresentatives e f∩badIndices p e own c J D a f).card:ℝ))≤
      ∑ f : B→X,((badIndices p e own c J D a f).card:ℝ) := by
  have hh := selected_absorption e
    (fun f i => if i∈badIndices p e own c J D a f then (1:ℝ) else 0)
    (by intros; split_ifs <;> norm_num) (by
      intro b x f y
      simp only [badIndices_update_self p e own hown c J D a b x y f])
  simpa only [sum_boole,filter_mem_eq_inter,univ_inter,Nat.cast_sum] using hh

omit [Fintype X] in

theorem badIndices_card (p : Law (ι→β)) (e : B×X ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) (hD : 0<D) (ha : 0<a)
    (hJ : ∀ i,entropy (p.marginal i)≤J) (f : B→X) :
    ((badIndices p e own c J D a f).card:ℝ)≤tupleDeficit J p/D+
      (∑ i,(maximumInformation p i (otherRepresentatives e own f i):ℝ))/a+
      (∑ i,(maximumCharge c i (otherRepresentatives e own f i):ℝ))/a := by
  let δ := fun i => J-entropy (p.marginal i)
  let I := fun i => (maximumInformation p i (otherRepresentatives e own f i):ℝ)
  let C := fun i => (maximumCharge c i (otherRepresentatives e own f i):ℝ)
  have hδ (i : ι) : 0≤δ i := sub_nonneg.mpr (hJ i)
  have hI (i : ι) : 0≤I i := NNReal.coe_nonneg _
  have hC (i : ι) : 0≤C i := NNReal.coe_nonneg _
  have hcost (i : ι) : 0≤δ i/D+I i/a+C i/a :=
    add_nonneg (add_nonneg (div_nonneg (hδ i) hD.le) (div_nonneg (hI i) ha.le))
      (div_nonneg (hC i) ha.le)
  have hib (i : ι) (hi : i∈badIndices p e own c J D a f) :
      1≤δ i/D+I i/a+C i/a := by
    rcases (mem_filter.mp hi).2 with hd | ⟨j,hj,hh⟩
    · have hh : 1≤δ i/D := (le_div_iff₀ hD).mpr (by simpa only [one_mul] using hd.le)
      linarith only [hh,div_nonneg (hI i) ha.le,div_nonneg (hC i) ha.le]
    · have hi' : (pairInformation p i j:ℝ)≤I i := by
        exact_mod_cast (Finset.le_sup (f:=pairInformation p i) hj)
      have hc' : (c i j:ℝ)≤C i := by
        exact_mod_cast (Finset.le_sup (f:=c i) hj)
      have hh' : 1≤(I i+C i)/a := (le_div_iff₀ ha).mpr (by linarith)
      rw [add_div] at hh'
      linarith only [hh',div_nonneg (hδ i) hD.le]
  calc
    _ = ∑ _i∈badIndices p e own c J D a f,(1:ℝ) := by simp
    _ ≤ ∑ i∈badIndices p e own c J D a f,(δ i/D+I i/a+C i/a) := sum_le_sum hib
    _ ≤ ∑ i,(δ i/D+I i/a+C i/a) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hcost i)
    _ = (∑ i,δ i)/D+(∑ i,I i)/a+(∑ i,C i)/a := by
      simp only [sum_add_distrib,←sum_div]
    _ ≤ _ := add_le_add (add_le_add
      (div_le_div_of_nonneg_right (marginal_deficit_sum p J) hD.le) le_rfl) le_rfl

end
end SharpLogRamsey.Selection

end

end OAI
