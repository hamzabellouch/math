import OAI.NumberTheory.TotientAsymptotic.PreimageLoglogBound
import OAI.NumberTheory.TotientAsymptotic.SmoothCountingSplit

namespace OAI

/-! Smooth-preimage counting directly bounds distinct totient values. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ell_injOn_totients (Q : Finset ℕ) (hQ : ∀ v ∈ Q,IsTotient v) :
    Set.InjOn ell (↑Q : Set ℕ) := by
  intro a ha b hb he
  have hφ := congrArg Nat.totient he
  rwa [(ell_spec (hQ a ha)).2,(ell_spec (hQ b hb)).2] at hφ

lemma smooth_totient_count {K : ℕ} (hK : 2 ≤ K) (N : ℕ) (Z : ℝ)
    (Q : Finset ℕ) (hQ : ∀ v ∈ Q,IsTotient v ∧ ell v ≤ N ∧ largestPrimeFactor (ell v) ≤ K) :
    (Q.card:ℝ) ≤ Real.exp Z+
      N*Real.exp (-Z/(4*Real.log K))*(primeEulerProduct K)^4 := by
  classical
  let E := Q.image ell
  have hE : ∀ n ∈ E,0 < n ∧ n ≤ N ∧ largestPrimeFactor n ≤ K := by
    intro n hn
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    exact ⟨(ell_spec (hQ v hv).1).1,(hQ v hv).2⟩
  have hh := smooth_counting_split hK N Z E hE
  have he : E.card=Q.card := Finset.card_image_of_injOn (ell_injOn_totients Q (fun v hv => (hQ v hv).1))
  rwa [he] at hh

lemma smooth_totient_count_of_preimage {K N : ℕ} (hK : 2 ≤ K) (Z : ℝ)
    (Q : Finset ℕ)
    (hQ : ∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ n ≤ N ∧ largestPrimeFactor n ≤ K) :
    (Q.card:ℝ) ≤ Real.exp Z+
      N*Real.exp (-Z/(4*Real.log K))*(primeEulerProduct K)^4 := by
  classical
  choose f hf using fun v : {v // v ∈ Q} => hQ v.val v.property
  let E : Finset ℕ := Q.attach.image f
  have hE : ∀ n ∈ E,0 < n ∧ n ≤ N ∧ largestPrimeFactor n ≤ K := by
    intro n hn
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hn
    exact ⟨(hf v).1,(hf v).2.2⟩
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have hh := congrArg Nat.totient h
    rwa [(hf a).2.1,(hf b).2.1] at hh
  have he : E.card=Q.card := by simp only [E,Finset.card_image_of_injective _ hi,Finset.card_attach]
  have hh := smooth_counting_split hK N Z E hE
  rwa [he] at hh

end TotientAsymptotic

end

end OAI
