import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeSystem

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical Filter OrdinaryCorrelations.FiniteIntegration

def integerResidues (S : PrimeSystem) (n : ℤ) : S.Residues := fun p => (n : ZMod (p : ℕ))

def modulus (S : PrimeSystem) : ℕ := ∏ p : S.Index, (p : ℕ)

lemma modulus_pos (S : PrimeSystem) : 0 < S.modulus := by
  exact prod_pos (fun p _ => (S.prime_mem p p.property).pos)

lemma prime_dvd_modulus (S : PrimeSystem) (p : S.Index) : (p : ℕ) ∣ S.modulus :=
  dvd_prod_of_mem (fun p : S.Index => (p : ℕ)) (mem_univ p)

lemma integerResidues_periodic (S : PrimeSystem) :
    Function.Periodic S.integerResidues (S.modulus : ℤ) := by
  intro n
  funext p
  change ((n + (S.modulus : ℤ) : ℤ) : ZMod (p : ℕ)) = (n : ZMod (p : ℕ))
  rw [Int.cast_add]
  have hm : ((S.modulus : ℤ) : ZMod (p : ℕ)) = 0 := by
    rw [Int.cast_natCast,ZMod.natCast_eq_zero_iff]
    exact S.prime_dvd_modulus p
  rw [hm,add_zero]

lemma residue_surjective (S : PrimeSystem) :
    Function.Surjective (fun n : Fin S.modulus => S.integerResidues (n.val : ℤ)) := by
  intro x
  let a : S.Index → ℕ := fun p => (x p).val
  have hs : ∀ p : S.Index, p ∈ (univ : Finset S.Index) → (p : ℕ) ≠ 0 := by
    intro p _
    exact (S.prime_mem p p.property).ne_zero
  have hp : Set.Pairwise (↑(univ : Finset S.Index)) (fun p q : S.Index => Nat.Coprime (p : ℕ) (q : ℕ)) := by
    intro p _ q _ hn
    exact (S.prime_mem p p.property).coprime_iff_not_dvd.mpr (by
      intro hd
      have he := (Nat.dvd_prime (S.prime_mem q q.property)).mp hd
      rcases he with he | he
      · exact (S.prime_mem p p.property).ne_one he
      · exact hn (Subtype.ext he))
  let k := Nat.chineseRemainderOfFinset a (fun p : S.Index => (p : ℕ)) univ hs hp
  have hk : k.val < S.modulus := Nat.chineseRemainderOfFinset_lt_prod a _ hs hp
  refine ⟨⟨k.val,hk⟩,?_⟩
  funext p
  change ((k.val : ℤ) : ZMod (p : ℕ)) = x p
  rw [Int.cast_natCast,← ZMod.natCast_zmod_val (x p)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (k.property p (mem_univ p))

lemma residues_card (S : PrimeSystem) : Fintype.card S.Residues = S.modulus := by
  simp only [Residues,Fintype.card_pi,ZMod.card,modulus]

def residueEquiv (S : PrimeSystem) : Fin S.modulus ≃ S.Residues :=
  Equiv.ofBijective (fun n => S.integerResidues (n.val : ℤ))
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨S.residue_surjective,by rw [Fintype.card_fin,S.residues_card]⟩)

lemma period_mean (S : PrimeSystem) (F : S.Residues → ℝ) :
    (∑ n ∈ range S.modulus, F (S.integerResidues (n : ℤ))) / (S.modulus : ℝ) = avg F := by
  rw [← Fin.sum_univ_eq_sum_range]
  have he : (∑ n : Fin S.modulus, F (S.integerResidues (n.val : ℤ))) = ∑ x, F x :=
    (S.residueEquiv).sum_comp F
  rw [he,avg,S.residues_card]
  ring

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
