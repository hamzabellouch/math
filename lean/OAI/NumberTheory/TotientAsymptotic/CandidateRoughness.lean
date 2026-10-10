import OAI.NumberTheory.TotientAsymptotic.CandidateProperties
import OAI.NumberTheory.TotientAsymptotic.PPTTrivialFibers

namespace OAI

/-! Fixed-seed roughness of the counted candidates. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem raw_candidate_rough {c : ℝ} (hc : 0 < c) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,∀ b ∈ rawCandidates x c d H,
      ∀ p : ℕ,p.Prime → p ∣ b → d+1 < p := by
  filter_upwards [raw_candidate_prime_data hc d hd,
    geometric_dominates_polynomial (half_pos hc) ((d:ℝ)+2) 0] with H hH hlarge
  filter_upwards [hH,m_tendsto.eventually (eventually_ge_atTop (H+1))]
    with x hx hm
  intro b hb
  obtain ⟨p,q,rfl,hp,_,hr,_,_,hq,hqp,_⟩ := hx b hb
  have hn : 0 < m x-H := by omega
  have htail (i : Fin (m x-H)) : d+1 < p i := by
    have hi := i.isLt
    have hdH : H ≤ m x-i.val := by omega
    have hl := hlarge (m x-i.val) hdH
    simp only [pow_zero,mul_one] at hl
    have hp1 : (1:ℝ) ≤ p i := by exact_mod_cast (hp i).one_le
    have hcoord : primePrefixCoord p i ≤ p i :=
      (Real.log_le_self (Real.log_nonneg hp1)).trans (Real.log_le_self (Nat.cast_nonneg _))
    have hh := hl.trans ((hr.2.1 i).trans hcoord)
    have hh' : (d:ℝ)+1 < p i := by linarith only [hh]
    exact_mod_cast hh'
  have hhead : d+1 < q := (htail ⟨0,hn⟩).trans (hqp ⟨0,hn⟩)
  intro r hpr hdvd
  rcases hpr.dvd_mul.mp hdvd with hdiv|hdiv
  · have he : r=q := (Nat.prime_dvd_prime_iff_eq hpr hq).mp hdiv
    exact he ▸ hhead
  · exact primeProduct_rough Finset.univ p d (fun i _ => hp i)
      (fun i _ => htail i) r hpr hdiv

end TotientAsymptotic

end

end OAI
