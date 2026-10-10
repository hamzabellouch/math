import OAI.NumberTheory.Ostmann.QuadraticSieveRowInflationDilation
import OAI.NumberTheory.Ostmann.QuadraticSieveRowInflationPrimes

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

def rowInflationTarget (M R : ℕ) : Finset ℕ :=
  (oddSquarefreeUpTo (32*R*M)).filter (fun v => R*M < v)

@[simp] theorem mem_rowInflationTarget {M R v : ℕ} :
    v ∈ rowInflationTarget M R ↔ R*M < v ∧ v ≤ 32*R*M ∧ Odd v ∧ Squarefree v := by
  simp only [rowInflationTarget,Finset.mem_filter,mem_oddSquarefreeUpTo]
  constructor
  · rintro ⟨⟨h1,h2,h3,h4⟩,h5⟩
    exact ⟨h5,h2,h3,h4⟩
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨⟨by omega,h2,h3,h4⟩,h1⟩

theorem primeDilation_mem_target {M R p v : ℕ} (hM : 0 < M) (hR : 2 ≤ R)
    (hp : p ∈ rowInflationPrimes R) (hv : v ∈ dyadicSquarefreeRows M) (hnd : ¬p∣v) :
    p*v ∈ rowInflationTarget M R := by
  obtain ⟨hpp,hRp,hpR⟩ := mem_rowInflationPrimes.mp hp
  obtain ⟨hMv,hvM,hvo,hvs⟩ := mem_dyadicSquarefreeRows.mp hv
  apply mem_rowInflationTarget.mpr
  refine ⟨?_,?_,(rowInflationPrimes_odd hR hp).mul hvo,?_⟩
  · have h1 := Nat.mul_lt_mul_of_pos_right hRp hM
    have h2 := Nat.mul_le_mul_left p hMv.le
    omega
  · have h := Nat.mul_le_mul hpR hvM
    nlinarith
  · exact (Nat.squarefree_mul (hpp.coprime_iff_not_dvd.mpr hnd)).mpr ⟨hpp.squarefree,hvs⟩

theorem rowInflationTarget_subset_dyadic_union (M R : ℕ) :
    rowInflationTarget M R ⊆ (Finset.range 5).biUnion
      (fun j => dyadicSquarefreeRows (2^j*(R*M))) := by
  classical
  intro v hv
  obtain ⟨hlo,hhi,hodd,hsq⟩ := mem_rowInflationTarget.mp hv
  have hhi' : v ≤ 32*(R*M) := by simpa only [Nat.mul_assoc] using hhi
  rw [Finset.mem_biUnion]
  by_cases h2 : v ≤ 2*(R*M)
  · refine ⟨0,by simp,?_⟩
    apply mem_dyadicSquarefreeRows.mpr
    simpa using (show R*M<v ∧ v≤2*(R*M) ∧ Odd v ∧ Squarefree v from ⟨hlo,h2,hodd,hsq⟩)
  by_cases h4 : v ≤ 4*(R*M)
  · refine ⟨1,by simp,?_⟩
    apply mem_dyadicSquarefreeRows.mpr
    norm_num
    exact ⟨by omega,by omega,hodd,hsq⟩
  by_cases h8 : v ≤ 8*(R*M)
  · refine ⟨2,by simp,?_⟩
    apply mem_dyadicSquarefreeRows.mpr
    norm_num
    exact ⟨by omega,by omega,hodd,hsq⟩
  by_cases h16 : v ≤ 16*(R*M)
  · refine ⟨3,by simp,?_⟩
    apply mem_dyadicSquarefreeRows.mpr
    norm_num
    exact ⟨by omega,by omega,hodd,hsq⟩
  · refine ⟨4,by simp,?_⟩
    apply mem_dyadicSquarefreeRows.mpr
    norm_num
    exact ⟨by omega,by omega,hodd,hsq⟩

end Ostmann.QuadraticSieve

end

end OAI
