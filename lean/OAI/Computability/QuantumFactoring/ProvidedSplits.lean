import Mathlib
import OAI.Computability.QuantumFactoring.PrimalityCorrectness
import OAI.Computability.QuantumFactoring.SplitCandidate
import OAI.Computability.QuantumFactoring.FavorableSplit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open FactorController

/-- A guarded scan. Invalid proposals never change the arithmetic product
invariant of the factoring controller. -/
def firstProper (m : ℕ) : List ℕ→ℕ
  | [] => 0
  | d::ds => if ProperDivisor m d then d else firstProper m ds

lemma firstProper_of_mem {m d : ℕ} {ds : List ℕ} (hd : d∈ds)
    (hp : ProperDivisor m d) : ProperDivisor m (firstProper m ds) := by
  induction ds with
  | nil => simp at hd
  | cons a ds ih =>
    simp only [firstProper]
    split_ifs with ha
    · exact ha
    · rcases List.mem_cons.mp hd with rfl | ht
      · exact False.elim (ha hp)
      · exact ih ht

lemma firstProper_sound {m : ℕ} (ds : List ℕ) :
    firstProper m ds=0 ∨ ProperDivisor m (firstProper m ds) := by
  induction ds with
  | nil => exact Or.inl rfl
  | cons d ds ih =>
    simp only [firstProper]
    split_ifs with hd
    · exact Or.inr hd
    · exact ih

def orderSplit (m : ℕ) (ars : List (ℕ×ℕ)) : ℕ :=
  firstProper m (ars.map (fun ar => candidateDivisor m ar.1 ar.2))

/-- `ars` are the supplied list entries paired with the recorded order outputs.
When the good list entry has its true order, the actual guarded scan splits. -/
lemma orderSplit_good {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (hodd : Odd m)
    (p₀ : Component m) (ars : List (ℕ×ℕ))
    (u : (ZMod m)ˣ) (hf : FavorableUnit (by omega : m≠0) hb p₀ u)
    (hmem : ((u : ZMod m).val,orderOf u)∈ars) : ProperDivisor m (orderSplit m ars) := by
  let : NeZero m := ⟨by omega⟩
  have hh := favorable_split hm hb hodd p₀ u hf
  have he : candidateDivisor m (u : ZMod m).val (orderOf u)=splitGcd u :=
    candidateDivisor_trueOrder hm u (ZMod.natCast_zmod_val _) hh.1
  apply firstProper_of_mem (List.mem_map.mpr ⟨_,hmem,rfl⟩)
  exact he ▸ hh.2

/-- Root searches are clocked by the ORIGINAL input length n. -/
def rootProposals (m n : ℕ) : List ℕ :=
  (List.range (n+1)).map (fun e => Primality.boundedRoot m e n)

def rootSplit (m n : ℕ) : ℕ := firstProper m (rootProposals m n)

lemma perfectPower_proper {m b e : ℕ} (hb : 2 ≤ b) (he : 2 ≤ e) (hp : b^e=m) :
    ProperDivisor m b := by
  rcases e with _ | e
  · omega
  have he0 : 0 < e := by omega
  have hpow : 1 < b^e := by exact one_lt_pow₀ (by omega) (by omega)
  refine ⟨by omega,?_,?_⟩
  · rw [← hp,pow_succ]
    nlinarith
  · rw [← hp,pow_succ]
    exact dvd_mul_left b (b^e)

lemma rootSplit_good {m n : ℕ} (hb : m < 2^n) (hp : Primality.PerfectPower m) :
    ProperDivisor m (rootSplit m n) := by
  obtain ⟨b,e,hb2,he,hpow⟩ := hp
  have hen := Primality.perfectPower_exponent_lt hb hb2 hpow
  have hroot := Primality.boundedRoot_pow_eq (by omega : 0 < e) hb hpow
  apply firstProper_of_mem (d:=b)
  · apply List.mem_map.mpr
    refine ⟨e,List.mem_range.mpr (by omega),hroot⟩
  · exact perfectPower_proper hb2 he hpow

def suppliedDivisor (m n : ℕ) (ars : List (ℕ×ℕ)) : ℕ :=
  if 2∣m then 2 else
  if ProperDivisor m (rootSplit m n) then rootSplit m n else orderSplit m ars

lemma suppliedDivisor_good {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (hprime : ¬m.Prime)
    (ars : List (ℕ×ℕ))
    (hgood : Odd m → ¬Primality.PerfectPower m →
      ∃ (p₀ : Component m) (u : (ZMod m)ˣ),
        FavorableUnit (by omega : m≠0) hb p₀ u ∧ ((u : ZMod m).val,orderOf u)∈ars) :
    ProperDivisor m (suppliedDivisor m n ars) := by
  simp only [suppliedDivisor]
  split_ifs with htwo hroot
  · refine ⟨by decide,?_,htwo⟩
    by_contra h
    have : m=2 := by omega
    exact hprime (this ▸ Nat.prime_two)
  · exact hroot
  · have hodd : Odd m := Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using htwo)
    have hpow : ¬Primality.PerfectPower m := fun hp => hroot (rootSplit_good hb hp)
    obtain ⟨p₀,u,hf,hu⟩ := hgood hodd hpow
    exact orderSplit_good hm hb hodd p₀ ars u hf hu

/-- The all-good node completion used in the source. The chosen divisor is now
an actual even/root/order scan, not an assumed proper-divisor oracle. -/
theorem supplied_node_complete {N n : ℕ} (hN : 2 ≤ N) (hb : N < 2^n)
    (outputs : ℕ→ℕ→List (ℕ×ℕ))
    (hgood : ∀ i m (hm : 2 ≤ m) (hle : m ≤ N), ¬m.Prime → Odd m →
      ¬Primality.PerfectPower m →
      ∃ (p₀ : Component m) (u : (ZMod m)ˣ),
        FavorableUnit (by omega : m≠0) (hle.trans_lt hb) p₀ u ∧
        ((u : ZMod m).val,orderOf u)∈outputs i m) :
    ∃ ps, run (fun i m => suppliedDivisor m n (outputs i m)) (2*n) 0 [N]=some ps ∧
      (∀ p∈ps,p.Prime) ∧ ps.prod=N ∧ ps.length < n := by
  apply bounded_node_complete hN hb
  intro i m hm hle hp
  exact suppliedDivisor_good hm (hle.trans_lt hb) hp _ (hgood i m hm hle hp)

end ExactQuantumFactoring


end

end OAI
