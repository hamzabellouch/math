import OAI.NumberTheory.TotientAsymptotic.BandStates
import OAI.NumberTheory.TotientAsymptotic.TupleRecovery
import OAI.NumberTheory.TotientAsymptotic.ResidualFactorCount

namespace OAI

/-! Exact multiplicity bounds for the final smooth factor states. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def terminalRight {k : ℕ} (t : ShiftedPair k) : Fin (k+1) → ℕ :=
  Fin.cons t.remainder t.right

lemma terminalRight_product {k : ℕ} (t : ShiftedPair k) :
    (∏ j,terminalRight t j)=t.remainder*(∏ j,t.right j) := by
  simp only [terminalRight,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma terminal_state_encoding_injective {k : ℕ} :
    Function.Injective (fun t : ShiftedPair k => (t.left,terminalRight t)) := by
  intro t s he
  have hl : t.left=s.left := congrArg Prod.fst he
  have hr : terminalRight t=terminalRight s := congrArg Prod.snd he
  have he₀ : t.remainder=s.remainder := congrFun hr 0
  have he₁ : t.right=s.right := by
    funext j
    exact congrFun hr j.succ
  cases t
  cases s
  cases hl
  cases he₁
  cases he₀
  rfl

lemma terminal_state_card_le {k d s : ℕ} (hd : 0 < d) (hs : 0 < s)
    (Q : Finset (ShiftedPair k))
    (hQ : ∀ t ∈ Q,factorProduct t=s ∧ d*factorProduct t=t.remainder*(∏ j,t.right j)) :
    Q.card ≤ (k+1)^d.primeFactorsList.length*(k*(k+1))^s.primeFactorsList.length := by
  classical
  let L := Q.image (fun t => t.left)
  let R := Q.image terminalRight
  let E := Q.image (fun t => (t.left,terminalRight t))
  have hE : E ⊆ L ×ˢ R := by
    intro w hw
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩,Finset.mem_image.mpr ⟨t,ht,rfl⟩⟩
  have hc := ordered_factorization_pairs_card_le s (d*s) hs (Nat.mul_pos hd hs) L R
    (by
      intro f hf
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hf
      exact (hQ t ht).1)
    (by
      intro f hf
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hf
      rw [terminalRight_product,← (hQ t ht).2,(hQ t ht).1])
  have hcard : E.card=Q.card := Finset.card_image_of_injective Q terminal_state_encoding_injective
  calc
    Q.card=E.card := hcard.symm
    _ ≤ (L ×ˢ R).card := Finset.card_le_card hE
    _ ≤ k^s.primeFactorsList.length*(k+1)^(d*s).primeFactorsList.length := by
      simpa only [Fintype.card_fin] using hc
    _ = _ := by rw [omega_count_mul hd.ne' hs.ne',pow_add,mul_pow]; ring

end TotientAsymptotic

end

end OAI
