import OAI.NumberTheory.Jacobsthal.Partitions.RationalParameterInterval

namespace OAI

namespace Erdos970

section

namespace ErdosAlignedProgression
open ErdosInverseAlignment

def parameterOf (r : ℚ) (d t : ℕ) : ℤ := ((r.den : ℤ)*(t : ℤ)-r.num)/(d : ℤ)

theorem parameterOf_spec (a : ℕ → ℕ) (r : ℚ) (d t : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p)
    (ht : ∀ p ∈ d.primeFactors, t % p = a p % p) :
    (r.den : ℤ)*(t : ℤ) = r.num+(d : ℤ)*parameterOf r d t := by
  obtain ⟨m, hm⟩ := (required_hits_iff_parameter a r d t hd ha).mp ht
  have hdiv : (d : ℤ) ∣ (r.den : ℤ)*(t : ℤ)-r.num := ⟨m, by linarith⟩
  have he := Int.mul_ediv_cancel_of_dvd hdiv
  dsimp only [parameterOf]
  linarith

theorem parameterValue_parameterOf (a : ℕ → ℕ) (r : ℚ) (d t : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p)
    (ht : ∀ p ∈ d.primeFactors, t % p = a p % p) :
    parameterValue r d (parameterOf r d t) = t := by
  have he := parameterOf_spec a r d t hd ha ht
  have hD : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  rw [parameterValue, ← he, Int.mul_ediv_cancel_left _ hD, Int.toNat_natCast]

theorem parameterOf_parameterValue (Y : ℕ) (r : ℚ) (d : ℕ) (hd : 0 < d) (m : ℤ)
    (hm : m ∈ parameterInterval Y r d) (hdiv : (r.den : ℤ) ∣ r.num+(d : ℤ)*m) :
    parameterOf r d (parameterValue r d m) = m := by
  have hs := parameterValue_spec Y r d hd m hm hdiv
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [parameterOf, hs.2.2, add_sub_cancel_left, Int.mul_ediv_cancel_left _ hdZ]

end ErdosAlignedProgression

end

section

namespace ErdosAlignedProgression
open ErdosInverseAlignment ErdosInverseCounts
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def parameterCandidates (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d : ℕ) : Finset ℤ :=
  (parameterInterval Y r d).filter (fun m =>
    (r.den : ℤ) ∣ r.num+(d : ℤ)*m ∧ ∀ p ∈ small, parameterValue r d m % p ≠ a p % p)

theorem parameterOf_mem (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d t : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p)
    (ht : t ∈ modulusCandidates Y small a d) :
    parameterOf r d t ∈ parameterCandidates Y small a r d := by
  obtain ⟨ht1, htY, hhit, hsmall⟩ := (mem_modulusCandidates Y small a d t).mp ht
  have he := parameterOf_spec a r d t hd ha hhit
  have hD : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
  have ht1Z : (1 : ℤ) ≤ t := by exact_mod_cast ht1
  have htYZ : (t : ℤ) ≤ Y := by exact_mod_cast htY
  apply Finset.mem_filter.mpr
  refine ⟨(mem_parameterInterval Y r d (Nat.pos_of_ne_zero hd.ne_zero) _).mpr ?_, ?_, ?_⟩
  · rw [← he]
    constructor <;> nlinarith
  · exact ⟨(t : ℤ), he.symm⟩
  · rw [parameterValue_parameterOf a r d t hd ha hhit]
    exact hsmall

theorem parameterValue_mem (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d : ℕ) (m : ℤ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p)
    (hm : m ∈ parameterCandidates Y small a r d) :
    parameterValue r d m ∈ modulusCandidates Y small a d := by
  obtain ⟨hI, hdiv, hsmall⟩ := Finset.mem_filter.mp hm
  have hs := parameterValue_spec Y r d (Nat.pos_of_ne_zero hd.ne_zero) m hI hdiv
  apply (mem_modulusCandidates Y small a d _).mpr
  exact ⟨hs.1, hs.2.1, (required_hits_iff_parameter a r d _ hd ha).mpr ⟨m, hs.2.2⟩, hsmall⟩

theorem parameterCandidates_eq_image (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p) :
    parameterCandidates Y small a r d =
      (modulusCandidates Y small a d).image (parameterOf r d) := by
  ext m
  constructor
  · intro hm
    have ht := parameterValue_mem Y small a r d m hd ha hm
    obtain ⟨hI, hdiv, _hsmall⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_image.mpr ⟨parameterValue r d m, ht,
      parameterOf_parameterValue Y r d (Nat.pos_of_ne_zero hd.ne_zero) m hI hdiv⟩
  · intro hm
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hm
    exact parameterOf_mem Y small a r d t hd ha ht

theorem parameterOf_injOn (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p) :
    Set.InjOn (parameterOf r d) (modulusCandidates Y small a d : Set ℕ) := by
  intro t ht u hu he
  have ht' := ((mem_modulusCandidates Y small a d t).mp ht).2.2.1
  have hu' := ((mem_modulusCandidates Y small a d u).mp hu).2.2.1
  calc
    t = parameterValue r d (parameterOf r d t) := (parameterValue_parameterOf a r d t hd ha ht').symm
    _ = parameterValue r d (parameterOf r d u) := congrArg (parameterValue r d) he
    _ = u := parameterValue_parameterOf a r d u hd ha hu'

theorem modulusCount_eq_parameter_card (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (r : ℚ) (d : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p) :
    modulusCount Y small a d = ((parameterCandidates Y small a r d).card : ℤ) := by
  rw [modulusCount, parameterCandidates_eq_image Y small a r d hd ha,
    Finset.card_image_of_injOn (parameterOf_injOn Y small a r d hd ha)]

end ErdosAlignedProgression

end

end Erdos970

end OAI
