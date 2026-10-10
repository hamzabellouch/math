import OAI.NumberTheory.Jacobsthal.Partitions.RealProgressionCoordinates
import OAI.NumberTheory.Jacobsthal.Primes.PrimeFibreInterval

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.BrunTitchmarshUpper

open _root_.Finset AffinePrimeSieve ProgressionPrimeUpper RealProgressionCoordinates

theorem finite_prime_set_upper : ∃ C B : ℝ, 0 < C ∧ 1 < B ∧
    ∀ (x H : ℝ) (q : ℕ) (r : ℤ) (P : Finset ℕ), 0 < q → B ≤ H/q →
      (∀ p ∈ P, p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ x+H ∧ Int.ModEq (q:ℤ) (p:ℤ) r) →
      (P.card:ℝ) ≤ C*H/((q.totient:ℝ)*Real.log (H/q)) := by
  obtain ⟨C,B,hC,hB,hupper⟩ := progression_prime_upper
  refine ⟨C,B,hC,hB,?_⟩
  intro x H q r P hq hBnd hP
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hJ : 1 < H/q := hB.trans_le hBnd
  have hH : 0 < H := by
    have h := (lt_div_iff₀ hqR).mp (lt_trans zero_lt_one hJ)
    simpa only [zero_mul] using h
  obtain ⟨N,a,index,hcount,hcoord⟩ := exists_coordinates x H q r hq hH.le
  let f : ℕ → ℕ := fun p => index (p:ℤ)
  have hdata : ∀ p ∈ P, f p < N ∧ value a q (f p) = (p:ℤ) := by
    intro p hp
    obtain ⟨_,hlo,hhi,hmod⟩ := hP p hp
    exact hcoord (p:ℤ) (by exact_mod_cast hlo) (by exact_mod_cast hhi) hmod
  have hinj : Set.InjOn f P := by
    intro p hp t ht heq
    have hz : (p:ℤ)=(t:ℤ) := (hdata p hp).2.symm.trans
      ((congrArg (value a q) heq).trans (hdata t ht).2)
    exact_mod_cast hz
  have hsub : P.image f ⊆ primeIndices N a q := by
    intro i hi
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (hdata p hp).1,?_⟩
    rw [(hdata p hp).2]
    simpa only [Int.natAbs_natCast] using And.intro (hP p hp).1 (Int.natCast_nonneg p)
  have hc : P.card ≤ (primeIndices N a q).card := by
    calc
      _ = (P.image f).card := (card_image_iff.mpr hinj).symm
      _ ≤ _ := card_le_card hsub
  have htR : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlog := Real.log_pos hJ
  calc
    (P.card:ℝ) ≤ ((primeIndices N a q).card:ℝ) := by exact_mod_cast hc
    _ ≤ C*(H/q)*((q:ℝ)/q.totient)/Real.log (H/q) := hupper N a q (H/q) hBnd hq hcount
    _ = _ := by field_simp

noncomputable def intervalPrimes (x H : ℝ) (q : ℕ) (r : ℤ) : Finset ℕ :=
  (range (⌊max (x+H) 0⌋₊+1)).filter (fun p =>
    p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ x+H ∧ Int.ModEq (q:ℤ) (p:ℤ) r)

theorem mem_intervalPrimes (x H : ℝ) (q : ℕ) (r : ℤ) (p : ℕ) :
    p ∈ intervalPrimes x H q r ↔
      p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ x+H ∧ Int.ModEq (q:ℤ) (p:ℤ) r := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le ?_),h⟩
    exact (Nat.le_floor_iff (le_max_right _ _)).mpr (h.2.2.1.trans (le_max_left _ _))

theorem brun_titchmarsh_upper : ∃ C B : ℝ, 0 < C ∧ 1 < B ∧
    ∀ (x H : ℝ) (q : ℕ) (r : ℤ), 0 < q → B ≤ H/q →
      ((intervalPrimes x H q r).card:ℝ) ≤ C*H/((q.totient:ℝ)*Real.log (H/q)) := by
  obtain ⟨C,B,hC,hB,h⟩ := finite_prime_set_upper
  exact ⟨C,B,hC,hB,fun x H q r hq hJ => h x H q r _ hq hJ
    (fun p hp => (mem_intervalPrimes x H q r p).mp hp)⟩

end ErdosPrimeInputs.BrunTitchmarshUpper

end

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable

noncomputable def residueFibre (P : Finset ℕ) (H C0 : ℝ) (m : ℤ) (M : ℕ) (b : ℤ) : Finset ℕ :=
  (geometricFibre P H C0 m).filter (fun p => Int.ModEq (M : ℤ) (p : ℤ) b)

theorem residue_fibre_prime_bound : ∃ C B : ℝ,0 < C ∧ 1 < B ∧
    ∀ (P : Finset ℕ) (R xi H C0 : ℝ) (m : ℤ) (M : ℕ) (b : ℤ),
      0 < R → 0 < xi → xi ≤ 1 → 0 < H → 0 < M →
      B ≤ 5*primeWidth R xi H C0/(M : ℝ) →
      (∀ p ∈ P,p.Prime ∧ R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R) →
      ((residueFibre P H C0 m M b).card : ℝ) ≤
        C*(5*primeWidth R xi H C0)/((M.totient : ℝ)*Real.log (5*primeWidth R xi H C0/(M : ℝ))) := by
  obtain ⟨C,B,hC,hB,hupper⟩ := ErdosPrimeInputs.BrunTitchmarshUpper.finite_prime_set_upper
  refine ⟨C,B,hC,hB,?_⟩
  intro P R xi H C0 m M b hR hxi hxi1 hH hM hRatio hP
  obtain ⟨x,hx⟩ := geometric_fibre_interval P R xi H C0 m hR hxi hxi1 hH (fun p hp => (hP p hp).2)
  apply hupper x (5*primeWidth R xi H C0) M b (residueFibre P H C0 m M b) hM hRatio
  intro p hp
  obtain ⟨hgeo,hmod⟩ := Finset.mem_filter.mp hp
  have hpP := (Finset.mem_filter.mp hgeo).1
  exact ⟨(hP p hpP).1,(hx p hgeo).1,(hx p hgeo).2,hmod⟩

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
