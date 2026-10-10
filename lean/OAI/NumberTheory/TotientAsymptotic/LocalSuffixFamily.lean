import OAI.NumberTheory.TotientAsymptotic.LocalBadCover
import OAI.NumberTheory.TotientAsymptotic.LocalSuffixBounds

namespace OAI

/-! The distinct bad suffixes retain the local value bounds and normality. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def localBadSuffixValues (x c : ℝ) (d L H : ℕ) (i : Fin (m x-H)) : Finset ℕ :=
  (localBadSuffixTuples x c d L H i).image (fun p => ∏ j,primeFinal p i.val j)

lemma local_bad_suffix_normality {x c : ℝ} {d L H : ℕ}
    (i : Fin (m x-H)) {r : ℕ} (hr : r ∈ localBadSuffixValues x c d L H i) :
    PPTBadResidual d r ∧ ∀ q : ℕ,q.Prime → q ∣ r →
      IsNormalPrime (localNormalityScale (m x-i.val)) q := by
  classical
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨hp,hbad⟩ := Finset.mem_filter.mp hp
  refine ⟨hbad,?_⟩
  intro q hq hdiv
  obtain ⟨j,_,hqj⟩ := (hq.prime.dvd_finsetProd_iff (primeFinal p i.val)).mp hdiv
  let k : Fin (m x-H) := ⟨i.val+j.val,by have := j.isLt; omega⟩
  have hnorm := local_regular_normality hp i k (by change i.val ≤ i.val+j.val; omega)
  have he : q=primeFinal p i.val j :=
    (Nat.prime_dvd_prime_iff_eq hq hnorm.1).mp hqj
  exact he ▸ hnorm

theorem local_bad_suffix_value_bounds {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) :
    ∃ A : ℝ,0 < A ∧ ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ i : Fin (m x-H),∀ r ∈ localBadSuffixValues x c d L H i,
        ((d*r.totient:ℕ):ℝ) ≤
          Real.exp (Real.exp (localPrimeHeight (A+Real.log d+2) L (m x-i.val))) ∧
        ∃ p : ℕ,p.Prime ∧ p-1 ≤ d*r.totient ∧
          (c/2)*(rho^(m x-i.val))⁻¹ ≤ B p := by
  classical
  obtain ⟨A,hA,hbound⟩ := local_prime_suffix_value_bounds hc d hd
  refine ⟨A,hA,?_⟩
  intro L
  filter_upwards [hbound L] with H hH
  filter_upwards [hH,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i r hr
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
  have hregular := (Finset.mem_filter.mp hp).1
  have hpgrid := (Finset.mem_sdiff.mp hregular).1
  have hh := hx _ (Nat.sub_add_cancel hm) p hpgrid i
  refine ⟨hh.2.2,p i,?_,hh.2.1,hh.1⟩
  exact (local_regular_normality hregular i i le_rfl).1

end TotientAsymptotic

end

end OAI
