import Mathlib

namespace OAI

open scoped BigOperators
namespace Ostmann.Characters

theorem lift_residue_cover_to_interval (I : Finset ℕ) {s r n t : ℕ}
    (hs : 0<s) (h0 : 0∈I) (hmax : s∈I) (hI : ∀ x ∈ I, x ≤ s)
    (hr : r≤n) (htlo : r*s≤t) (hthi : t≤(n-r)*s)
    (hcover : ∀ z:ZMod s, ∃ f:Fin r→ℕ, (∀ i,f i∈I) ∧ ∑ i,(f i:ZMod s)=z) :
    ∃ l:List ℕ, l.length=n ∧ (∀ x ∈ l, x ∈ I) ∧ l.sum=t := by
  let : NeZero s := ⟨hs.ne'⟩
  obtain ⟨f,hf,hfmod⟩ := hcover (t:ZMod s)
  let u := ∑ i, f i
  have hu : u≤r*s := by
    calc
      _ ≤ ∑ _i:Fin r,s := Finset.sum_le_sum (fun i _ => hI _ (hf i))
      _ = _ := by simp
  have hut : u≤t := hu.trans htlo
  have hcast : ((t-u : ℕ) : ZMod s)=0 := by
    rw [Nat.cast_sub hut]
    have hc : (u:ZMod s)=(t:ZMod s) := by simpa [u] using hfmod
    rw [hc, sub_self]
  have hdiv : s ∣ t-u := (CharP.cast_eq_zero_iff (ZMod s) s (t-u)).mp hcast
  let d := (t-u)/s
  have hdu : d*s=t-u := Nat.div_mul_cancel hdiv
  have hdeq : u+d*s=t := by omega
  have hd : d≤n-r := by
    apply Nat.le_of_mul_le_mul_right _ hs
    nlinarith
  refine ⟨List.ofFn f ++ List.replicate d s ++ List.replicate (n-r-d) 0, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_ofFn, List.length_replicate]
    omega
  · intro x hx
    simp only [List.mem_append, List.mem_ofFn, List.mem_replicate] at hx
    rcases hx with (⟨i,rfl⟩ | ⟨_,rfl⟩) | ⟨_,rfl⟩
    · exact hf i
    · exact hmax
    · exact h0
  · simp only [List.sum_append, List.sum_ofFn, List.sum_replicate, nsmul_eq_mul,
      mul_zero, add_zero]
    exact hdeq
end Ostmann.Characters

end OAI
