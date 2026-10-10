import OAI.NumberTheory.TwoPoint.Bounds.ResidueWordDependence
import OAI.NumberTheory.TwoPoint.Bounds.CommonResidueLift

namespace OAI

/-! One common integer realizes every attached numerical witness in a hybrid sample. -/

namespace TwoPointCorrelations

open scoped Classical

theorem attached_residue_words_common_origin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n B h : ℕ) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (x : ι → Fin B) (word : Fin n → List SignedStep) (attachment : Fin n → ℤ)
    (hsq : ∀ j t, t ∈ word j → Squarefree (t.padding * t.tuple))
    (hcover : ∀ j q, q ∈ wordDivisorPrimeSupport (word j) → ∃ i, p i = q)
    (htest : ∀ j, AttachedResiduePositiveWord p h (word j) (attachment j) B x) :
    ∃ origin : ℤ, ∀ j, PositiveWord h (origin + attachment j) (word j) := by
  let (i : ι) : NeZero (p i) := ⟨(hprime i).ne_zero⟩
  have hcop : Pairwise (fun i j => (p i).Coprime (p j)) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun he => hij (hinj he))
  let r (i : ι) : ZMod (p i) := ((x i).val : ZMod (p i))
  obtain ⟨origin, horigin⟩ := exists_common_integer_residue p hcop r
  refine ⟨origin, ?_⟩
  intro j
  let rj (i : ι) : ZMod (p i) := r i + (attachment j : ZMod (p i))
  have hj : ∀ i, ((origin + attachment j : ℤ) : ZMod (p i)) = rj i := by
    intro i
    simp only [Int.cast_add, horigin, rj]
  apply (residuePositiveWord_iff p h (word j) rj (origin + attachment j)
    hj (hsq j) (hcover j)).mp
  intro k i hi
  have ht := htest j k i hi
  change r i = -((attachment j + wordDisplacement h ((word j).take k.val) : ℤ) : ZMod (p i)) at ht
  rw [Int.cast_add] at ht
  change r i + (attachment j : ZMod (p i)) = _
  rw [ht]
  ring

end TwoPointCorrelations

end OAI
