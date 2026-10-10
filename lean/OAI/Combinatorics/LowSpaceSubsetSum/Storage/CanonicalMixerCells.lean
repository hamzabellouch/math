import OAI.Combinatorics.LowSpaceSubsetSum.Storage.IntervalDomainCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MixerPreparationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MixerParameterCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationParameterPreparation

namespace OAI

/-! # Complete canonical mixer preparation with shared domains

The three interval domains are built from the stored permutation, retained
while their half-array tournaments are counted, and passed directly to the
integer parameter stage. Every returned value and work counter agrees with
the input-only preparation used by the trial.
-/

namespace LowSpaceSubsetSum.CanonicalMixerCells

open scoped BigOperators
variable {n : ℕ}

def run (I : Instance n) (v : Vector (Fin n) n) :
    (RepresentationMixerPreparation.Result n × ℕ) × ℕ :=
  let domains := Vector.ofFn (fun i : Fin 3 =>
    IntervalDomainCells.run v (i.val*mixerSize n) (mixerSize n))
  let values := domains.map (fun d => d.1.1)
  let counts := MixerPreparationCells.run (fun j => (I.values j : ℤ)) values
  ((⟨values, counts.1.1⟩, (∑ i : Fin 3, domains[i.val].1.2)+counts.1.2),
    (∑ i : Fin 3, domains[i.val].2)+counts.2+12*n+64)

theorem run_value (I : Instance n) (v : Vector (Fin n) n) :
    (run I v).1 = RepresentationMixerPreparation.run (canonicalRepresentationData I) v := by
  have hdomains : (Vector.ofFn (fun i : Fin 3 =>
      IntervalDomainCells.run v (i.val*mixerSize n) (mixerSize n))).map (fun d => d.1.1) =
      (Vector.ofFn (fun i : Fin 3 =>
      IntervalDomainExecution.run v (i.val*mixerSize n) (mixerSize n))).map Prod.fst := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, IntervalDomainCells.run_value]
  rw [← IntervalDomainExecution.mixers_source]
  simp only [run, MixerPreparationCells.run_value, hdomains, MixerPreparationCells.source,
    IntervalDomainCells.run_value, IntervalDomainExecution.mixers,
    Vector.getElem_map, Vector.getElem_ofFn, Finset.sum_add_distrib, Nat.add_assoc]

private theorem scalar_bound (n u T core : ℕ) (peaks : Fin 3 → ℕ)
    (hn : 10000 ≤ n) (hu : n+2 ≤ u) (hT : 1 ≤ T)
    (hc : core ≤ u^6*T) (hp : ∀ i, peaks i ≤ 128*(n+1)^2) :
    (∑ i : Fin 3, peaks i)+core+12*n+64 ≤ u^7*T := by
  have hu0 : 10000 ≤ u := by omega
  have hu2 : 1 ≤ u^2 := Nat.one_le_pow _ _ (by omega)
  have hq := Nat.pow_le_pow_left (show n+1 ≤ u by omega) 2
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hp i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  have hpoly : 384*(n+1)^2+12*n+64 ≤ 400*u^2 := by
    nlinarith only [hq, hu, hu0, hu2]
  have hminor : (∑ i : Fin 3, peaks i)+12*n+64 ≤ u^6 := by
    calc
      _ ≤ 400*u^2 := by omega
      _ ≤ u*u^2 := Nat.mul_le_mul_right _ (by omega)
      _ = u^3 := (pow_succ' _ _).symm
      _ ≤ u^6 := pow_le_pow_right' (by omega) (by decide)
  have hminor' := hminor.trans (Nat.le_mul_of_pos_right _ hT)
  have hmajor : 2*u^6 ≤ u^7 := by
    calc
      _ ≤ u*u^6 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hfinal := Nat.mul_le_mul_right T hmajor
  simp only [Nat.mul_assoc] at hfinal
  omega

theorem run_cells (I : Instance n) (v : Vector (Fin n) n) (hn : 10000 ≤ n) :
    (run I v).2 ≤ inputScale I^7*2^((mixerSize n+1)/2) := by
  let domains := Vector.ofFn (fun i : Fin 3 =>
    IntervalDomainCells.run v (i.val*mixerSize n) (mixerSize n))
  let values := domains.map (fun d => d.1.1)
  have hm : mixerSize n ≤ n := by unfold mixerSize; omega
  have hlen (i : Fin 3) : values[i.val].length ≤ mixerSize n := by
    dsimp only [values, domains]
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    exact (IntervalDomainCells.run_length v _ _ (by
      have hi := i.isLt
      have hthree : 3*mixerSize n ≤ n := by unfold mixerSize; omega
      nlinarith)).le
  have hc := MixerPreparationCells.run_cells I (fun j => (I.values j : ℤ))
    values (mixerSize n) hn hm hlen
  have hp (i : Fin 3) : domains[i.val].2 ≤ 128*(n+1)^2 := by
    dsimp only [domains]
    simp only [Vector.getElem_ofFn]
    exact IntervalDomainCells.run_cells v _ _
  change (∑ i : Fin 3, domains[i.val].2)+
    (MixerPreparationCells.run (fun j => (I.values j : ℤ)) values).2+12*n+64 ≤ _
  exact scalar_bound n (inputScale I) (2^((mixerSize n+1)/2))
    (MixerPreparationCells.run (fun j => (I.values j : ℤ)) values).2
    (fun i => domains[i.val].2) hn (by unfold inputScale; omega) Nat.one_le_two_pow hc hp

def prepare (I : Instance n) (v : Vector (Fin n) n) :
    ((Vector (List (Fin n)) 3 × MixerParameterExecution.Parameters) × ℕ) × ℕ :=
  let mixers := run I v
  let out := MixerParameterCells.run n mixers.1.1.counts
  (((mixers.1.1.domains, out.1.1), mixers.1.2+out.1.2+3), mixers.2+out.2+6*n+32)

theorem prepare_value (I : Instance n) (v : Vector (Fin n) n) :
    (prepare I v).1 = RepresentationParameterPreparation.run (canonicalRepresentationData I) v := by
  simp only [prepare, run_value, MixerParameterCells.run_value,
    RepresentationParameterPreparation.run]

private theorem parameters_bound (n u T a b : ℕ) (hn : 10000 ≤ n) (hu : n+2 ≤ u)
    (hT : 1 ≤ T) (ha : a ≤ u^7*T) (hb : b ≤ 128) :
    a+b+6*n+32 ≤ u^8*T := by
  have hu0 : 10000 ≤ u := by omega
  have hs : 160+6*n ≤ u^7 := by
    have h2 : 1 ≤ u^2 := Nat.one_le_pow _ _ (by omega)
    have h27 : u^2 ≤ u^7 :=
      pow_le_pow_right' (by omega) (by decide)
    nlinarith only [hu, hu0, h2, h27]
  have hsT := hs.trans (Nat.le_mul_of_pos_right _ hT)
  have hf : 2*u^7 ≤ u^8 := by
    calc
      _ ≤ u*u^7 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hfT := Nat.mul_le_mul_right T hf
  simp only [Nat.mul_assoc] at hfT
  omega

theorem prepare_cells (I : Instance n) (v : Vector (Fin n) n) (hn : 10000 ≤ n) :
    (prepare I v).2 ≤ inputScale I^8*2^((mixerSize n+1)/2) := by
  change (run I v).2+(MixerParameterCells.run n (run I v).1.1.counts).2+6*n+32 ≤ _
  exact parameters_bound n (inputScale I) (2^((mixerSize n+1)/2))
    (run I v).2 (MixerParameterCells.run n (run I v).1.1.counts).2 hn
    (by unfold inputScale; omega) Nat.one_le_two_pow (run_cells I v hn)
    (MixerParameterCells.run_cells n (run I v).1.1.counts)

theorem half_capacity (n : ℕ) :
    2^((mixerSize n+1)/2) ≤ compressionDictionaryCapacity n := by
  unfold compressionDictionaryCapacity
  apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
  unfold mixerSize
  omega

theorem prepare_cells_capacity (I : Instance n) (v : Vector (Fin n) n) (hn : 10000 ≤ n) :
    (prepare I v).2 ≤ inputScale I^8*compressionDictionaryCapacity n :=
  (prepare_cells I v hn).trans (Nat.mul_le_mul_left _ (half_capacity n))

end LowSpaceSubsetSum.CanonicalMixerCells

end OAI
