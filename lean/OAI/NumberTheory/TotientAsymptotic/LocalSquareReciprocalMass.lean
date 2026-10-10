import OAI.NumberTheory.TotientAsymptotic.LocalSquareDecay
import OAI.NumberTheory.TotientAsymptotic.ResidualDyadicMass
import OAI.NumberTheory.TotientAsymptotic.LocalNormalityMass

namespace OAI

/-! Sum square exceptions over their occupied local dyadic layers. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_square_witness_mass (K : ℕ) : ∃ z₀ : ℝ,256 ≤ z₀ ∧
    ∀ (d h L : ℕ) (T : ℝ),0 < T →
      ∀ (R : Finset ℕ) (F : ℕ → ℕ),Set.InjOn F (R : Set ℕ) →
      (∀ r ∈ R,1 < d*r.totient ∧ ((d*r.totient:ℕ):ℝ) ≤ (2:ℝ)^L) →
      (∀ r ∈ R,let z := (2:ℝ)^(Nat.clog 2 (d*r.totient));
        z₀ ≤ z ∧ T ≤ B z ∧ (localSquareCutoff z:ℝ) ≤ localNormalityScale h) →
      (∀ r ∈ R,0<F r ∧ (F r).totient=d*r.totient) →
      (∀ r ∈ R,∃ p : ℕ,p.Prime ∧ localNormalityScale h<p ∧
        (p^2 ∣ F r ∨ p^2 ∣ (F r).totient)) →
      (∑ r ∈ R,(r.totient:ℝ)⁻¹) ≤
        (4*d/Real.log 2)*T^(-(K:ℝ))*(1+Real.log L) := by
  classical
  obtain ⟨z₀,hz₀⟩ := eventually_atTop.mp (local_square_witness_power_saving (K:ℝ))
  refine ⟨max z₀ 256,le_max_right _ _,?_⟩
  intro d h L T hT R F hinj hrange hlocal hF hbad
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : 0 ≤ T^(-(K:ℝ))/Real.log 2 :=
    div_nonneg (Real.rpow_pos_of_pos hT _).le hlog2.le
  have hcount (k : ℕ) (hk : k ∈ Finset.Icc 1 L) :
      ((R.filter (fun r => Nat.clog 2 (d*r.totient)=k)).card:ℝ) ≤
        (T^(-(K:ℝ))/Real.log 2)*(2:ℝ)^k/k := by
    let Q := R.filter (fun r => Nat.clog 2 (d*r.totient)=k)
    by_cases hQ : Q.Nonempty
    · obtain ⟨r,hr⟩ := hQ
      have he := (Finset.mem_filter.mp hr).2
      have hloc := hlocal r (Finset.mem_filter.mp hr).1
      dsimp only at hloc
      rw [he] at hloc
      have hz0 : z₀ ≤ (2:ℝ)^k := (le_max_left _ _).trans hloc.1
      have hc := hz₀ ((2:ℝ)^k) hz0 Q F
        (hinj.mono (Finset.filter_subset _ _)) (by
          intro s hs
          obtain ⟨hs,he⟩ := Finset.mem_filter.mp hs
          refine ⟨(hF s hs).1,?_⟩
          rw [(hF s hs).2]
          have hh := (dyadic_nat_bounds (hrange s hs).1).2.2
          rwa [he] at hh) (by
          intro s hs
          have hsR := (Finset.mem_filter.mp hs).1
          obtain ⟨p,hp,hlarge,hsq⟩ := hbad s hsR
          refine ⟨p,hp,?_,hsq⟩
          exact_mod_cast hloc.2.2.trans_lt hlarge)
      have hpow : (B ((2:ℝ)^k))^(-(K:ℝ)) ≤ T^(-(K:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hT hloc.2.1 (neg_nonpos.mpr (Nat.cast_nonneg K))
      have hfac : 0 ≤ (2:ℝ)^k/Real.log ((2:ℝ)^k) := by
        rw [dyadic_endpoint_log]
        positivity
      apply (hc.trans (mul_le_mul_of_nonneg_left hpow hfac)).trans_eq
      rw [dyadic_endpoint_log]
      ring
    · have he : Q=∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
      change (Q.card:ℝ) ≤ _
      rw [he]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  apply (residual_dyadic_mass R d L hcoef hrange hcount).trans_eq
  ring

end TotientAsymptotic

end

end OAI
