import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorRows
import OAI.NumberTheory.CubicMoment.Estimates.SmallBCoreHybrid
import OAI.NumberTheory.CubicMoment.Estimates.NoncubeCutoffMass
import OAI.NumberTheory.CubicMoment.Estimates.AllFrequencyOuterSieve

namespace OAI

/-! The nonempty divisor rows use their actual quotient length. Small
cores admit the elementary coefficient bound; larger cores retain the
hybrid ordinary/cubic-sieve saving. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedDivisorSlice_empty (X l b : ℝ) (e d : Eisenstein)
    (hsmall : b/norm d < 1) : stoppedDivisorSlice ι X l b e d = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have hp := stoppedDivisorSlice_spec X l b e d hn
  exact (not_lt_of_ge ((one_le_norm (primary_ne_zero hp.1)).trans hp.2.2)) hsmall

theorem stopped_filtered_outer_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X w z l b u M B : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e d : Eisenstein), primary d → 0 ≤ b → 1 ≤ B → 1 ≤ b/norm d →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) →
      ∀ H : Finset Eisenstein, (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B) →
      (∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n),
        stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2) ≤
      K*(2*B*(b/norm d))^ε*
        (B+(B*(b/norm d))^(2/3:ℝ)+B^(1/3:ℝ)*(b/norm d))*(b/norm d)*M^2 := by
  obtain ⟨K,hK,hbound⟩ := all_frequency_outer_sieve hε
  refine ⟨18*K,by positivity,?_⟩
  intro X w z l b u M B W selected e d hd hb hB hN hcoeff H hH
  have hm := hbound (stoppedDivisorSlice ι X l b e d) H B (b/norm d) hB hN
    (fun n hn => stoppedDivisorSlice_spec X l b e d hn) hH
    (fun n => stoppedRowCoefficient X w z u W selected (d*n))
  have he := stopped_slice_energy X w z l b u M W selected e d hb hcoeff
  apply (Finset.sum_le_sum (fun v _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
    (stopped_divisor_character_norm_le X w z l b u W selected e v hd) 2)).trans
      (hm.trans _)
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring)

theorem stopped_filtered_core_blocks (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X w z l b u M V B : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e d : Eisenstein), primary d → 0 ≤ b → 0 < V → 0 ≤ B →
      65536 ≤ b/norm d → 8*B ≤ (b/norm d)^(3/4:ℝ) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) →
      ∀ H : Finset Eisenstein,
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n),
        stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2) ≤
      104976*V*B^(1/3:ℝ)*(b/norm d)^2*M^2+
      K*((largeCoreDyadicIndices V B).card:ℝ)*B^(1/3:ℝ)*
        ((b/norm d)*(V/5832)^(-(1/4:ℝ))+(b/norm d)^(1-1/20000:ℝ))*
          (b/norm d)*M^2 := by
  obtain ⟨K,hK,hcore⟩ := smallB_core_hybrid_sieve hHuxley
  refine ⟨18*K,by positivity,?_⟩
  intro X w z l b u M V B W selected e d hd hb hV hB hN hsize hcoeff H hH
  let N := b/norm d
  let S := stoppedDivisorSlice ι X l b e d
  let β := fun n => stoppedRowCoefficient X w z u W selected (d*n)
  let f := fun v => ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n),
    stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2
  have hNp : 0 < N := by dsimp [N]; linarith
  have henergy : (∑ n ∈ S, ‖β n‖^2) ≤ 18*N*M^2 :=
    stopped_slice_energy X w z l b u M W selected e d hb hcoeff
  have hcard : (S.card:ℝ) ≤ 18*N := primary_support_card_le S hNp.le
    (fun n hn => ⟨(stoppedDivisorSlice_spec X l b e d hn).1,
      (stoppedDivisorSlice_spec X l b e d hn).2.2⟩)
  have hshift (v : Eisenstein) : f v ≤ ‖∑ n ∈ S, β n*cubicSymbol n v‖^2 :=
    pow_le_pow_left₀ (_root_.norm_nonneg _)
      (stopped_divisor_character_norm_le X w z l b u W selected e v hd) 2
  have htrivial (v : Eisenstein) : f v ≤ 324*N^2*M^2 := by
    apply (hshift v).trans
    apply (cubic_character_row_sq S
      (fun n hn => (stoppedDivisorSlice_spec X l b e d hn).1) β v).trans
    exact (mul_le_mul hcard henergy (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (by positivity)).trans_eq (by ring)
  have hsmall : (∑ v ∈ H.filter (fun v => v ∈ lowNoncubeSupport V (B^(1/3:ℝ))), f v) ≤
      104976*V*B^(1/3:ℝ)*N^2*M^2 := by
    have hc : ((H.filter (fun v => v ∈ lowNoncubeSupport V (B^(1/3:ℝ)))).card:ℝ) ≤
        324*V*B^(1/3:ℝ) :=
      (Nat.cast_le.mpr (Finset.card_le_card (by
        intro v hv
        exact (Finset.mem_filter.mp hv).2))).trans
          (lowNoncubeSupport_card hV.le (Real.rpow_nonneg hB _))
    calc
      _ ≤ ∑ _v ∈ H.filter (fun v => v ∈ lowNoncubeSupport V (B^(1/3:ℝ))),
          324*N^2*M^2 := Finset.sum_le_sum (fun v _ => htrivial v)
      _ = ((H.filter (fun v => v ∈ lowNoncubeSupport V (B^(1/3:ℝ)))).card:ℝ)*
          (324*N^2*M^2) := by simp
      _ ≤ (324*V*B^(1/3:ℝ))*(324*N^2*M^2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have hrow (q : ℕ × ℕ) (hq : q ∈ largeCoreDyadicIndices V B) :
      (∑ v ∈ coreDyadicBlock B q.1 q.2, f v) ≤
      (18*K)*B^(1/3:ℝ)*(N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*N*M^2 := by
    have hq' := (Finset.mem_filter.mp hq).2
    have hm := hcore S (coreDyadicBlock B q.1 q.2) β N B V q.1 q.2 hN hB hV
      (fun n hn => stoppedDivisorSlice_spec X l b e d hn) hq'.1.le
      ((mul_le_mul_of_nonneg_left hq'.2 (by norm_num : (0:ℝ) ≤ 8)).trans hsize)
      (Finset.Subset.refl _)
    apply (Finset.sum_le_sum (fun v _ => hshift v)).trans (hm.trans _)
    exact (mul_le_mul_of_nonneg_left henergy (by positivity)).trans_eq (by ring)
  have hlarge := Finset.sum_le_sum hrow
  simp only [Finset.sum_const,nsmul_eq_mul] at hlarge
  apply (noncube_frequency_mass_split H hH f (fun _ => sq_nonneg _)).trans
    ((add_le_add hsmall hlarge).trans_eq _)
  dsimp only [N]
  ring

end CubicFirstMoment

end

end OAI
