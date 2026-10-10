import OAI.NumberTheory.TotientAsymptotic.LocalResidualHeight
import OAI.NumberTheory.TotientAsymptotic.PrimeMassSplit

namespace OAI

/-! Both endpoint bounds for the actual suffix products of the local grid. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma prime_predecessor_le_seed_totient {r p d : ℕ} (hr : 0 < r)
    (hp : p.Prime) (hpr : p ∣ r) (hd : 0 < d) : p-1 ≤ d*r.totient := by
  have hdiv : p-1 ∣ r.totient := by
    simpa only [Nat.totient_prime hp] using Nat.totient_dvd_of_dvd hpr
  have hle := Nat.le_of_dvd (Nat.totient_pos.mpr hr) hdiv
  exact hle.trans (Nat.le_mul_of_pos_left _ hd)

theorem local_prime_suffix_value_bounds {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) :
    ∃ A : ℝ,0 < A ∧ ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ p ∈ gridPrimeTuples (localPrimeGrid x c L n),
      ∀ i : Fin n,
        (c/2)*(rho^(m x-i.val))⁻¹ ≤ B (p i) ∧
        p i-1 ≤ d*(∏ j,primeFinal p i.val j).totient ∧
        ((d*(∏ j,primeFinal p i.val j).totient:ℕ):ℝ) ≤
          Real.exp (Real.exp (localPrimeHeight (A+Real.log d+2) L (m x-i.val))) := by
  obtain ⟨A,hA,hcoords⟩ := local_prime_coordinates hc
  refine ⟨A,hA,?_⟩
  intro L
  filter_upwards [hcoords L] with H hH
  filter_upwards [hH] with x hx
  intro n hn p hp i
  obtain ⟨hpr,hgeom,_,hu⟩ := hx n hn p hp
  have hpos : 0 < ∏ j,primeFinal p i.val j := by
    exact Finset.prod_pos (fun j _ => (hpr _).pos)
  have hdiv : p i ∣ ∏ j,primeFinal p i.val j := by
    let j : Fin (n-i.val) := ⟨0,by have := i.isLt; omega⟩
    have he : primeFinal p i.val j=p i := by
      apply congrArg p
      apply Fin.ext
      simp [j]
    rw [←he]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  refine ⟨hgeom.2.1 i,prime_predecessor_le_seed_totient hpos (hpr i) hdiv hd,?_⟩
  apply local_residual_value_bound hA.le L (m x-i.val) d (n-i.val) hd (by omega)
    (primeFinal p i.val) (fun j => hpr _)
  intro j
  let k : Fin n := ⟨i.val+j.val,by have := j.isLt; omega⟩
  have hk : m x-k.val ≤ m x-i.val := Nat.sub_le_sub_left (by dsimp [k]; omega) _
  have he : B (primeFinal p i.val j) ≤ localPrimeHeight A L (m x-k.val) := by
    have hh := hu k
    change B (p k) ≤ _
    unfold localPrimeHeight
    change primePrefixCoord p k ≤ _
    linarith only [hh]
  exact he.trans (localPrimeHeight_mono hA.le L hk)

end TotientAsymptotic

end

end OAI
