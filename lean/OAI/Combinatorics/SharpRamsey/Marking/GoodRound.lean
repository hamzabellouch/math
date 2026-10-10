import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.GoodIndices

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {β B ι : Type*} [Fintype β] [Fintype B] [Fintype ι] [DecidableEq B] [DecidableEq ι]

def roundBad {m : ℕ} (p : Law (ι→β)) (e : B×Fin m ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) : ℝ :=
  (∑ f : B→Fin m,((badIndices p e own c J D a f).card:ℝ))/Fintype.card (B→Fin m)

def roundSelectedBad {m : ℕ} (p : Law (ι→β)) (e : B×Fin m ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) : ℝ :=
  (∑ f : B→Fin m,
    ((freshRepresentatives e f∩badIndices p e own c J D a f).card:ℝ))/Fintype.card (B→Fin m)

theorem roundBad_le {m : ℕ} (hm : 0 < m) (p : Law (ι→β)) (e : B×Fin m ↪ ι)
    (own : ι→Option B) (c : ι→ι→NNReal) (J D a : ℝ) (hD : 0 < D) (ha : 0 < a)
    (hJ : ∀ i,entropy (p.marginal i)≤J) :
    roundBad p e own c J D a≤tupleDeficit J p/D+roundInformation p e own/a+
      (∑ i,∑ j,(c i j:ℝ))/((m:ℝ)*a) := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hm' : (0:ℝ) <  m := by exact_mod_cast hm
  have hN : (0:ℝ) <  Fintype.card (B→Fin m) := by exact_mod_cast Fintype.card_pos
  have HC : (∑ f : B→Fin m,∑ i,
        (maximumCharge c i (otherRepresentatives e own f i):ℝ))/Fintype.card (B→Fin m)≤
      (∑ i,∑ j,(c i j:ℝ))/(m:ℝ) := by
    apply (div_le_div_iff₀ hN hm').mpr
    have hh := collision_all_indices e own c
    simp only [Fintype.card_fin] at hh
    nlinarith only [hh]
  calc
    _ ≤ (∑ f : B→Fin m,(tupleDeficit J p/D+
        (∑ i,(maximumInformation p i (otherRepresentatives e own f i):ℝ))/a+
        (∑ i,(maximumCharge c i (otherRepresentatives e own f i):ℝ))/a))/
          Fintype.card (B→Fin m) := by
      apply div_le_div_of_nonneg_right _ hN.le
      exact sum_le_sum (fun f _ => badIndices_card p e own c J D a hD ha hJ f)
    _ = tupleDeficit J p/D+roundInformation p e own/a+
        ((∑ f : B→Fin m,∑ i,
          (maximumCharge c i (otherRepresentatives e own f i):ℝ))/Fintype.card (B→Fin m))/a := by
      simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,←sum_div,roundInformation]
      field_simp
    _ ≤ tupleDeficit J p/D+roundInformation p e own/a+
        ((∑ i,∑ j,(c i j:ℝ))/(m:ℝ))/a :=
      add_le_add le_rfl (div_le_div_of_nonneg_right HC ha.le)
    _ = _ := by rw [div_div]

theorem roundSelectedBad_le {m : ℕ} (p : Law (ι→β)) (e : B×Fin m ↪ ι)
    (own : ι→Option B) (hown : ∀ b x,own (e (b,x))=some b)
    (c : ι→ι→NNReal) (J D a : ℝ) :
    (m:ℝ)*roundSelectedBad p e own c J D a≤roundBad p e own c J D a := by
  unfold roundSelectedBad roundBad
  rw [←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [Fintype.card_fin] using selected_bad_absorption p e own hown c J D a

end
end SharpLogRamsey.Selection

end

end OAI
