import OAI.NumberTheory.Jacobsthal.Sieve.AlignedPrimeCongruence

namespace OAI

namespace Erdos970

section

namespace ErdosAlignedProgression
attribute [local instance] Classical.decEq

def parameterLower (r : ℚ) (d : ℕ) : ℤ := -((r.num-(r.den : ℤ))/(d : ℤ))
def parameterUpper (Y : ℕ) (r : ℚ) (d : ℕ) : ℤ := ((r.den : ℤ)*(Y : ℤ)-r.num)/(d : ℤ)
noncomputable def parameterInterval (Y : ℕ) (r : ℚ) (d : ℕ) : Finset ℤ :=
  Finset.Icc (parameterLower r d) (parameterUpper Y r d)

theorem mem_parameterInterval (Y : ℕ) (r : ℚ) (d : ℕ) (hd : 0 < d) (m : ℤ) :
    m ∈ parameterInterval Y r d ↔
      (r.den : ℤ) ≤ r.num+(d : ℤ)*m ∧ r.num+(d : ℤ)*m ≤ (r.den : ℤ)*(Y : ℤ) := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  rw [parameterInterval, Finset.mem_Icc]
  have hl : parameterLower r d ≤ m ↔ (r.den : ℤ) ≤ r.num+(d : ℤ)*m := by
    unfold parameterLower
    constructor
    · intro h
      have hn : -m ≤ (r.num-(r.den : ℤ))/(d : ℤ) := by linarith
      have hh := (Int.le_ediv_iff_mul_le hdZ).mp hn
      nlinarith
    · intro h
      have hn : -m ≤ (r.num-(r.den : ℤ))/(d : ℤ) := by
        apply (Int.le_ediv_iff_mul_le hdZ).mpr
        nlinarith
      linarith
  have hu : m ≤ parameterUpper Y r d ↔ r.num+(d : ℤ)*m ≤ (r.den : ℤ)*(Y : ℤ) := by
    unfold parameterUpper
    rw [Int.le_ediv_iff_mul_le hdZ]
    constructor <;> intro h <;> nlinarith
  exact and_congr hl hu

def parameterValue (r : ℚ) (d : ℕ) (m : ℤ) : ℕ :=
  ((r.num+(d : ℤ)*m)/(r.den : ℤ)).toNat

theorem parameterValue_spec (Y : ℕ) (r : ℚ) (d : ℕ) (hd : 0 < d) (m : ℤ)
    (hm : m ∈ parameterInterval Y r d) (hdiv : (r.den : ℤ) ∣ r.num+(d : ℤ)*m) :
    1 ≤ parameterValue r d m ∧ parameterValue r d m ≤ Y ∧
      (r.den : ℤ)*(parameterValue r d m : ℤ) = r.num+(d : ℤ)*m := by
  have hb := (mem_parameterInterval Y r d hd m).mp hm
  have hD : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
  have hquot : (1 : ℤ) ≤ (r.num+(d : ℤ)*m)/(r.den : ℤ) := by
    apply (Int.le_ediv_iff_mul_le hD).mpr
    simpa only [one_mul] using hb.1
  have hcast : (parameterValue r d m : ℤ) = (r.num+(d : ℤ)*m)/(r.den : ℤ) :=
    Int.toNat_of_nonneg (by linarith)
  have he : (r.den : ℤ)*(parameterValue r d m : ℤ) = r.num+(d : ℤ)*m := by
    rw [hcast]
    exact Int.mul_ediv_cancel_of_dvd hdiv
  have hlo : (1 : ℤ) ≤ parameterValue r d m := by rw [hcast]; exact hquot
  have hhi : (parameterValue r d m : ℤ) ≤ Y := by
    have hm : (r.den : ℤ)*(parameterValue r d m : ℤ) ≤ (r.den : ℤ)*(Y : ℤ) := by
      rw [he]
      exact hb.2
    nlinarith
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi, he⟩

end ErdosAlignedProgression

end

end Erdos970

end OAI
