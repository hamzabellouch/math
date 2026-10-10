import OAI.NumberTheory.Jacobsthal.Analysis.NormalizedCollisionSmallness
import OAI.NumberTheory.Jacobsthal.Primes.PrimeBinRationalList

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceCollision
open ErdosInversePrimeBin ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment ErdosConvexGraph

noncomputable def unalignedPrimes (P : Finset ℕ) (a : ℕ → ℤ) {l : PrimitiveIntegerLine}
    (r : InterceptReduction l) : Finset ℕ := by
  classical
  exact P.filter (fun p => ¬p ∣ l.denominator ∧ ¬aligns a r.rational p)

theorem uniform_actual_unaligned_incidence (eta alpha eps : ℝ)
    (heta : 0 < eta) (halpha : 0 < alpha) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ R xi S : ℝ,
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 →
      ∀ (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (l : PrimitiveIntegerLine) (r : InterceptReduction l)
        (X : Finset (ℤ × ℤ)), (∀ v ∈ X,l.Contains v) → (∀ v ∈ X,InSquare S v) →
        Set.InjOn Prod.fst (X : Set (ℤ × ℤ)) → S ≤ z^3 → z^((93 : ℝ)/100) ≤ (X.card : ℝ) →
        (∑ p ∈ primeBin R xi,((T p).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        (∑ p ∈ unalignedPrimes (primeBin R xi) a r,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤
          eps*((primeBin R xi).card : ℝ)*(X.card : ℝ) := by
  classical
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (uniform_prime_bin_count heta)
  have hs := uniform_normalized_collision (3/alpha) eta eps (by positivity) heta heps
  filter_upwards [hs,(tendsto_rpow_atTop halpha).eventually_ge_atTop R0] with z hz hzR
  refine ⟨hz.1,?_⟩
  intro R xi S hRlo hRhi hxi hxi1 a T l r X hline hbox hinj hS hN hthin
  have hb := hR0 R (hzR.trans hRlo)
  have hR : 1 < R := by linarith [hb.1]
  have hRpos : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hxipos : 0 ≤ xi := heta.le.trans hxi
  let P := primeBin R xi
  let U := unalignedPrimes P a r
  have hsub : U ⊆ P := Finset.filter_subset _ _
  have hprime (p : ℕ) (hp : p ∈ P) : Nat.Prime p := ((mem_primeBin hRpos.le hxipos p).mp hp).1
  have hplarge (p : ℕ) (hp : p ∈ P) : z^alpha ≤ (p : ℝ) :=
    hRlo.trans (((mem_primeBin hRpos.le hxipos p).mp hp).2.1.le)
  have hcount : eta*R/(4*Real.log R) ≤ (P.card : ℝ) := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hxi hRpos.le)
      (by positivity : 0 ≤ 4*Real.log R)).trans
    exact (hb.2 xi hxi hxi1).1
  have hcollision := actual_collision_bound r U X a T hline
    (fun p hp => hprime p (hsub hp))
    (fun _ hp => (Finset.mem_filter.mp hp).2.1)
    (fun _ hp => (Finset.mem_filter.mp hp).2.2)
    hinj S z alpha hbox hz.1 halpha (fun p hp => hplarge p (hsub hp)) hS
  have hKU : (∑ p ∈ U,((T p).card : ℝ)) ≤ ∑ p ∈ P,((T p).card : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  have hI : (∑ p ∈ U,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤ (P.card : ℝ)*(X.card : ℝ) :=
    (total_incidence_le_product U X a T).trans (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (Finset.card_le_card hsub)) (Nat.cast_nonneg _))
  exact hz.2 _ _ R _ _ hR hRhi hN hcount (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
    hcollision (hKU.trans hthin) hI

end ErdosSourceCollision

end

end Erdos970

end OAI
