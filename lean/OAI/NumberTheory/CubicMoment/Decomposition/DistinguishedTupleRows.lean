import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedCoordinateReindex
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedPrimeCollection
import OAI.NumberTheory.CubicMoment.Estimates.PrimeComplementFibers

namespace OAI

/-! The original distinguished-role tuple sum is exactly the sum of the
free-prime rows; the global largest-prime and stopping tests are retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complementTuple_update_product (S : ι → Finset Eisenstein) (i : ι)
    {g : ι → Eisenstein} (hg : g ∈ coordinateComplementTuples S i) (p : Eisenstein) :
    (∏ l, Function.update g i p l) = (∏ l, g l)*p := by
  have hgi := ((coordinateComplement_mem S i g).mp hg).1
  have he : (∏ l, g l) = ∏ l ∈ Finset.univ.erase i, g l := by
    rw [←Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i),hgi,one_mul]
  rw [primeTuple_update_product,he,mul_comm]

theorem distinguished_tuple_stopped_rows [Nonempty ι]
    (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (d e : Eisenstein) (hd : primary d) (w : ι → Eisenstein → ℂ) (G : Eisenstein → ℂ) :
    (∑ f ∈ (Fintype.piFinset (fun _ : ι => primeCutoff B)).filter
        (fun f => Squarefree ((∏ l, f l)*d)),
      if largestPrimeChoice ((∏ l, f l)*d) ∣ ∏ l, f l then
        if IsCoprime ((∏ l, f l)*d) e ∧
          (a < norm ((∏ l, f l)*d) ∧ norm ((∏ l, f l)*d) ≤ b) ∧
          stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
            j₀ k h Z Q early (∏ l, f l) d ∧
          geometricPrimeBin ρ B (largestPrimeChoice ((∏ l, f l)*d)) = j
        then (∏ l, w l (f l))*G ((∏ l, f l)*d) else 0
      else 0) =
    ∑ i, ∑ g ∈ coordinateComplementTuples (fun _ : ι => primeCutoff B) i,
      (∏ l ∈ Finset.univ.erase i, w l (g l))*
      (if Squarefree ((∏ l, g l)*d) ∧ IsCoprime ((∏ l, g l)*d) e then
        ∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
            (∏ l, g l) d ((∏ l, g l)*(d*e)), w i p*G (((∏ l, g l)*p)*d)
      else 0) := by
  rw [distinguished_tuple_largest_reindex (fun _ : ι => primeCutoff B)
    (fun _ _ hp => (mem_primeCutoff.mp hp).1) hd]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro g hg
  let c := ∏ l, g l
  have hc : primary c := complementTuple_primary (fun _ : ι => primeCutoff B)
    (fun _ _ hp => (mem_primeCutoff.mp hp).1) i hg
  calc
    _ = (∏ l ∈ Finset.univ.erase i, w l (g l))*
        ∑ p ∈ primeCutoff B,
          if Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e ∧
            (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B p = j ∧
            largestPrimeChoice ((c*p)*d) = p then w i p*G ((c*p)*d) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [complementTuple_update_product _ i hg p,primeTuple_update_weight]
      change (if Squarefree ((c*p)*d) ∧ largestPrimeChoice ((c*p)*d) = p then
        if IsCoprime ((c*p)*d) e ∧ (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B (largestPrimeChoice ((c*p)*d)) = j
          then (w i p*(∏ l ∈ Finset.univ.erase i, w l (g l)))*G ((c*p)*d) else 0
        else 0) = _
      rw [←ite_and]
      have he : ((Squarefree ((c*p)*d) ∧ largestPrimeChoice ((c*p)*d) = p) ∧
          (IsCoprime ((c*p)*d) e ∧ (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B (largestPrimeChoice ((c*p)*d)) = j)) ↔
          (Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e ∧
            (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
            stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
              j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B p = j ∧
            largestPrimeChoice ((c*p)*d) = p) := by
        constructor
        · rintro ⟨⟨hs,he⟩,hc,hrange,hstop,hbin⟩
          rw [he] at hbin
          exact ⟨hs,hc,hrange,hstop,hbin,he⟩
        · rintro ⟨hs,hc,hrange,hstop,hbin,he⟩
          exact ⟨⟨hs,he⟩,hc,hrange,hstop,by simpa only [he] using hbin⟩
      have hh := if_congr he
        (Eq.refl ((w i p*(∏ l ∈ Finset.univ.erase i, w l (g l)))*G ((c*p)*d)))
        (Eq.refl (0:ℂ))
      apply hh.trans
      split_ifs <;> ring
    _ = _ := by
      rw [distinguished_prime_collection B ρ a b j j₀ k h Z Q early c d e hc hd]

end CubicFirstMoment

end

end OAI
