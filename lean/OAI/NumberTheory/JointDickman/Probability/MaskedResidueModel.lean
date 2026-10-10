import OAI.NumberTheory.JointDickman.Arithmetic.ConditionedPrimeResidues
import OAI.NumberTheory.JointDickman.Probability.SiteConditionedRootProduct
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSiteTranspose

namespace OAI

/-! # Exact conditional law of the masked arithmetic residue model -/

namespace JointDickman
open Finset Classical

abbrev BlockPrimePatterns (B M : ℕ) := auxiliaryPrimes B → (univ : Finset (Fin M)).powerset

noncomputable def primePatternsSites {B M : ℕ} (H : BlockPrimePatterns B M)
    (i : Fin M) : Finset ℕ :=
  (primeSiteTranspose univ (auxiliaryPrimes B) H ⟨i,mem_univ _⟩).val

theorem primePatternsSites_mem {B M : ℕ} (H : BlockPrimePatterns B M)
    (p : auxiliaryPrimes B) (i : Fin M) :
    p.val ∈ primePatternsSites H i ↔ i ∈ (H p).val :=
  primeSiteTranspose_mem univ (auxiliaryPrimes B) H ⟨i,mem_univ _⟩ p

theorem primePatterns_empty_iff {B M : ℕ} (H : BlockPrimePatterns B M)
    (p : auxiliaryPrimes B) :
    H p = emptyBlockPrimeHit M ↔ ¬ ∃ i, p.val ∈ primePatternsSites H i := by
  constructor
  · intro h ⟨i,hi⟩
    have hh := (primePatternsSites_mem H p i).mp hi
    rw [h] at hh
    simp [emptyBlockPrimeHit] at hh
  · intro h
    apply Subtype.ext
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact h ⟨i,(primePatternsSites_mem H p i).mpr hi⟩

noncomputable def maskedPrimeRootFamily {B M : ℕ}
    (I : Finset (BlockCandidateIndex M)) (H : BlockPrimePatterns B M)
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) : auxiliaryPrimes B → I.powerset :=
  fun p => @maskedCandidatePrimeHit M I p.val
    ⟨auxiliaryPrimes_prime B p.val p.property⟩ (H p) (r p)

theorem maskedPrimeRootFamily_local {B M : ℕ}
    (I : Finset (BlockCandidateIndex M)) (H : BlockPrimePatterns B M)
    (p : auxiliaryPrimes B) [NeZero p.val] (hp : M < p.val) (R : I.powerset) :
    finitePushMass (totalUniformConditionalMass (blockPrimeHit M p.val) (H p))
      (@maskedCandidatePrimeHit M I p.val ⟨auxiliaryPrimes_prime B p.val p.property⟩ (H p)) R =
      @siteConditionedRootPrimeMass M I (primePatternsSites H) p.val
        ⟨auxiliaryPrimes_prime B p.val p.property⟩ R := by
  let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val p.property⟩
  rw [maskedCandidatePrimeHit_push I hp]
  have he := primePatterns_empty_iff H p
  unfold siteConditionedRootPrimeMass
  by_cases hh : H p = emptyBlockPrimeHit M
  · simp only [hh,ite_true,he.mp hh,ite_false]
  · have hn : ∃ i, p.val ∈ primePatternsSites H i := by simpa only [he,not_not] using hh
    simp only [hh,ite_false,hn,ite_true]

/-- The candidate set may depend on all exposed site patterns. The
remaining conditional prime law is still the proved product law. -/
theorem masked_residue_disintegration {B M : ℕ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (hlarge : ∀ p ∈ auxiliaryPrimes B, M < p)
    (I : BlockPrimePatterns B M → Finset (BlockCandidateIndex M))
    (F : (H : BlockPrimePatterns B M) → (auxiliaryPrimes B → (I H).powerset) → ℝ) :
    (∑ r : ∀ p : auxiliaryPrimes B, ZMod p.val,
      finiteProductMass (fun (p : auxiliaryPrimes B) (_ : ZMod p.val) => 1/(p.val : ℝ)) r *
        F (fun p => blockPrimeHit M p.val (r p))
          (maskedPrimeRootFamily (I (fun p => blockPrimeHit M p.val (r p)))
            (fun p => blockPrimeHit M p.val (r p)) r)) =
    ∑ H : BlockPrimePatterns B M,
      categoricalProductMass univ (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) H *
        ∑ R, siteConditionedRootProductMass B (I H) (primePatternsSites H) R * F H R := by
  have hinner (H : BlockPrimePatterns B M) :
      (∑ r, finiteProductMass
        (fun p : auxiliaryPrimes B => totalUniformConditionalMass (blockPrimeHit M p.val) (H p)) r *
          F H (maskedPrimeRootFamily (I H) H r)) =
      ∑ R, siteConditionedRootProductMass B (I H) (primePatternsSites H) R * F H R := by
    let a := fun p : auxiliaryPrimes B => totalUniformConditionalMass (blockPrimeHit M p.val) (H p)
    let f := fun p : auxiliaryPrimes B => @maskedCandidatePrimeHit M (I H) p.val
      ⟨auxiliaryPrimes_prime B p.val p.property⟩ (H p)
    have hmass : finiteProductMass (fun p => finitePushMass (a p) (f p)) =
        siteConditionedRootProductMass B (I H) (primePatternsSites H) := by
      funext R
      apply prod_congr rfl
      intro p _
      exact maskedPrimeRootFamily_local (I H) H p (hlarge p.val p.property) (R p)
    have ht := finiteProductMass_pushforward_test a f (fun R => (F H R : ℂ))
    rw [hmass] at ht
    exact_mod_cast ht.symm
  have hm (H : BlockPrimePatterns B M) :
      finiteProductMass (fun p : auxiliaryPrimes B => uniformImageMass (blockPrimeHit M p.val)) H =
        categoricalProductMass univ (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) H := by
    apply prod_congr rfl
    intro p _
    exact blockPrimeImageMass M p.val (hlarge p.val p.property) (H p)
  have hd := total_uniform_product_disintegration
    (fun p : auxiliaryPrimes B => blockPrimeHit M p.val)
    (fun H r => F H (maskedPrimeRootFamily (I H) H r))
  simp only [ZMod.card] at hd
  rw [hd]
  apply sum_congr rfl
  intro H _
  rw [hm H,hinner H]

noncomputable def arithmeticPrimePatterns (B M u : ℕ) : BlockPrimePatterns B M :=
  fun p => blockPrimeHit M p.val (u : ZMod p.val)

/-- The observed site types are exactly the auxiliary prime divisors of
all the translated integers in the block. -/
theorem primePatternsSites_arithmetic (B M u : ℕ) (i : Fin M) :
    primePatternsSites (arithmeticPrimePatterns B M u) i =
      coefficientPrimeSet B (u+(i.val+1)) := by
  ext p
  by_cases hp : p ∈ auxiliaryPrimes B
  · have hs := primePatternsSites_mem (arithmeticPrimePatterns B M u) ⟨p,hp⟩ i
    rw [hs]
    change i ∈ (blockPrimeHit M p (u : ZMod p)).val ↔ _
    rw [blockPrimeHit_divisibility]
    simp [coefficientPrimeSet,hp]
  · have hs : p ∉ primePatternsSites (arithmeticPrimePatterns B M u) i := by
      intro h
      exact hp (mem_powerset.mp
        (primeSiteTranspose univ (auxiliaryPrimes B) (arithmeticPrimePatterns B M u)
          ⟨i,mem_univ _⟩).property h)
    simp [hs,coefficientPrimeSet,hp]

/-- Exact identification with an average over the actual arithmetic CRT
period, still with the explicitly masked root tests. -/
theorem masked_arithmetic_crt {B M : ℕ}
    (hlarge : ∀ p ∈ auxiliaryPrimes B, M < p)
    (I : BlockPrimePatterns B M → Finset (BlockCandidateIndex M))
    (F : (H : BlockPrimePatterns B M) → (auxiliaryPrimes B → (I H).powerset) → ℝ) :
    (∑ u ∈ range (∏ p ∈ auxiliaryPrimes B, p),
      F (arithmeticPrimePatterns B M u)
        (maskedPrimeRootFamily (I (arithmeticPrimePatterns B M u))
          (arithmeticPrimePatterns B M u) (fun p => (u : ZMod p.val)))) /
      (∏ p ∈ auxiliaryPrimes B, (p : ℝ)) =
    ∑ H : BlockPrimePatterns B M,
      categoricalProductMass univ (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) H *
        ∑ R, siteConditionedRootProductMass B (I H) (primePatternsSites H) R * F H R := by
  let : ∀ p : auxiliaryPrimes B, NeZero p.val :=
    fun p => ⟨(auxiliaryPrimes_prime B p.val p.property).ne_zero⟩
  have hcop : Pairwise (fun p q : auxiliaryPrimes B => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (auxiliaryPrimes_prime B p.val p.property)
      (auxiliaryPrimes_prime B q.val q.property)).mpr (fun h => hpq (Subtype.ext h))
  have hc := crt_uniform_mean (fun p : auxiliaryPrimes B => p.val) hcop
    (fun r => F (fun p => blockPrimeHit M p.val (r p))
      (maskedPrimeRootFamily (I (fun p => blockPrimeHit M p.val (r p)))
        (fun p => blockPrimeHit M p.val (r p)) r))
  rw [(auxiliaryPrimes B).prod_coe_sort (fun p : ℕ => p),
    (auxiliaryPrimes B).prod_coe_sort (fun p : ℕ => (p : ℝ))] at hc
  exact hc.trans (masked_residue_disintegration hlarge I F)

end JointDickman

end OAI
