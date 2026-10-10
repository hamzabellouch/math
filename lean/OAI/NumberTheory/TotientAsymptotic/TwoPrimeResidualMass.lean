import OAI.NumberTheory.TotientAsymptotic.FordCofactorStep
import OAI.NumberTheory.TotientAsymptotic.NormalityGridMass
import OAI.NumberTheory.TotientAsymptotic.TotientCountingEnvelope
import OAI.NumberTheory.TotientAsymptotic.PrimeReciprocalBound
import OAI.NumberTheory.TotientAsymptotic.MertensProduct

namespace OAI

/-! Residual values after one prime extension and their reciprocal mass. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def singlePrimeExtensions (P M : Finset ℕ) : Finset ℕ :=
  M ∪ M.biUnion (fun m => P.biUnion (fun p => {(p-1)*m,p*m}))

lemma singlePrimeExtensions_pos {P M : Finset ℕ}
    (hP : ∀ p ∈ P,p.Prime) (hM : ∀ m ∈ M,0 < m) :
    ∀ d ∈ singlePrimeExtensions P M,0 < d := by
  classical
  intro d hd
  rcases Finset.mem_union.mp hd with hd|hd
  · exact hM d hd
  · obtain ⟨m,hm,p,hp,hd⟩ := by
      simpa only [Finset.mem_biUnion] using hd
    have hp2 := (hP p hp).two_le
    simp only [Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with rfl|rfl <;> exact Nat.mul_pos (by omega) (hM m hm)

lemma singlePrimeExtensions_mass (P M : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) :
    (∑ d ∈ singlePrimeExtensions P M,(d:ℝ)⁻¹) ≤
    (1+2*∑ p ∈ P,((p-1:ℕ):ℝ)⁻¹)*(∑ m ∈ M,(m:ℝ)⁻¹) := by
  classical
  have hpair (m p : ℕ) (hp : p ∈ P) :
      (∑ d ∈ ({(p-1)*m,p*m}:Finset ℕ),(d:ℝ)⁻¹) ≤
      2*((p-1:ℕ):ℝ)⁻¹*(m:ℝ)⁻¹ := by
    have hh : (∑ d ∈ ({(p-1)*m,p*m}:Finset ℕ),(d:ℝ)⁻¹) ≤
        (((p-1)*m:ℕ):ℝ)⁻¹+((p*m:ℕ):ℝ)⁻¹ := by
      by_cases he : (p-1)*m=p*m
      · simp only [he,Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.sum_singleton]
        have hi : (0:ℝ) ≤ ((p*m:ℕ):ℝ)⁻¹ := by positivity
        linarith
      · rw [Finset.sum_pair he]
    have hp0 : 0 < p-1 := by have := (hP p hp).two_le; omega
    have hp' : (p:ℝ)⁻¹ ≤ ((p-1:ℕ):ℝ)⁻¹ :=
      inv_anti₀ (by exact_mod_cast hp0) (by exact_mod_cast Nat.sub_le p 1)
    simp only [Nat.cast_mul,mul_inv_rev] at hh
    have hm0 : 0 ≤ (m:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    nlinarith only [hh,mul_le_mul_of_nonneg_left hp' hm0]
  have hmass : (∑ d ∈ M.biUnion (fun m => P.biUnion (fun p => {(p-1)*m,p*m})),(d:ℝ)⁻¹) ≤
      (2*∑ p ∈ P,((p-1:ℕ):ℝ)⁻¹)*(∑ m ∈ M,(m:ℝ)⁻¹) := by
    calc
      _ ≤ ∑ m ∈ M,∑ d ∈ P.biUnion (fun p => {(p-1)*m,p*m}),(d:ℝ)⁻¹ :=
        reciprocal_sum_biUnion_le _ _
      _ ≤ ∑ m ∈ M,∑ p ∈ P,2*((p-1:ℕ):ℝ)⁻¹*(m:ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro m _
        exact (reciprocal_sum_biUnion_le _ _).trans (Finset.sum_le_sum (hpair m))
      _ = _ := by
        simp only [← Finset.sum_mul,← Finset.mul_sum]
  have hu := Finset.sum_union_inter (s₁:=M)
    (s₂:=M.biUnion (fun m => P.biUnion (fun p => {(p-1)*m,p*m})))
    (f:=fun d : ℕ => (d:ℝ)⁻¹)
  have hn : 0 ≤ ∑ d ∈ M ∩ M.biUnion (fun m => P.biUnion (fun p => {(p-1)*m,p*m})),(d:ℝ)⁻¹ :=
    Finset.sum_nonneg (fun d _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  unfold singlePrimeExtensions
  nlinarith only [hu,hmass,hn]

lemma cofactor_singlePrimeExtensions {n k : ℕ} {P M : Finset ℕ}
    (hM : (fordCofactor n (k+1)).totient ∈ M)
    (hP : (fordPrime n k).Prime → fordPrime n k ∈ P) :
    (fordCofactor n k).totient ∈ singlePrimeExtensions P M := by
  classical
  rcases fordCofactor_totient_cases n k with he|⟨hp,he⟩
  · exact Finset.mem_union_left _ (he ▸ hM)
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨(fordCofactor n (k+1)).totient,hM,?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨fordPrime n k,hP hp,?_⟩
    simpa only [Finset.mem_insert,Finset.mem_singleton] using he

end TotientAsymptotic

end

end OAI
