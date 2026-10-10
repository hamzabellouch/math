import OAI.NumberTheory.JointDickman.Probability.CandidateSquareMoment

namespace OAI

/-! # The integrated square bound for an admissible latent edge -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- The full edge square has the manuscript's power saving. Both cited
inputs remain explicit; all representation and remainder steps are proved. -/
theorem candidateSquareMoment_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 10000 ≤ L) {η cap : ℝ} (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ K : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧ 0 < K ∧
      ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        ∀ (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
        ∀ (i t : Fin M), i < t → t.val-i.val ≤ auxiliaryCutoff B →
          ((t.val-i.val : ℕ) : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ ((t.val-i.val : ℕ) : ℝ) →
          candidateSquareMoment B L T H τ C χ i t ≤
            K/(T : ℝ)*(B : ℝ)^(-(21/100 : ℝ))*singularFactor 24 (t.val-i.val) := by
  obtain ⟨τ,hτ,hτcap,hτsampling,hcount⟩ := tiltedCandidatePairCount_bound hFord hM hL hη hcap
  obtain ⟨K,hK,hfirst⟩ := candidateFirstPairMass_bound hFord hM
  refine ⟨τ,2*K,hτ,hτcap,hτsampling,by positivity,?_⟩
  filter_upwards [hcount,hfirst,candidateSquareMoment_le_multiplicity hM
    (show 1 ≤ L by omega) hτ.le hτsampling,eventually_ge_atTop 10]
    with B hcount hfirst hsquare hB
  intro T H M C hT hTs χ hχ i t hit hcut hjB hjlow
  have hTlarge : (T : ℝ) ≤ Real.exp B := hTs.trans (Real.exp_le_exp.mpr (by
    nlinarith [show (0 : ℝ) ≤ B from Nat.cast_nonneg B]))
  have hj : 0 < t.val-i.val := Nat.sub_pos_of_lt hit
  have hweighted := candidateMultiplicityMoment_le_firstMass χ (fun e => (hχ e).1) i t hit
    (Q := 2*(B : ℝ)^(8/1000 : ℝ)) (by
      intro A hA D hD he ha hd
      have hsizeA : (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) := by
        obtain ⟨_,_,_,hc,_,_,_,_,_,_,hclo,hchi,hlo,hhi,_,_⟩ := he
        exact endpointCoefficientWindow_size hB hTs ⟨_,hc,hclo,hchi,hlo,hhi⟩
      have hsizeD : (∏ p ∈ D, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) := by
        obtain ⟨_,_,_,hc,_,_,_,_,_,_,hclo,hchi,_,_,hlo,hhi⟩ := he
        exact endpointCoefficientWindow_size hB hTs ⟨_,hc,hclo,hchi,hlo,hhi⟩
      exact hcount T H M C i t A D hTlarge (mem_powerset.mp hA) (mem_powerset.mp hD)
        ha hd hsizeA hsizeD hj hcut hjB hjlow)
  have hbpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hpower : (B : ℝ)^(-(22/100 : ℝ))*(B : ℝ)^(8/1000 : ℝ) ≤
      (B : ℝ)^(-(21/100 : ℝ)) := by
    rw [← Real.rpow_add hbpos]
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ B))
    norm_num
  have hbase : 0 ≤ 2*K/(T : ℝ)*singularFactor 24 (t.val-i.val) :=
    mul_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg T))
      (zero_le_one.trans (singularFactor_one_le (by norm_num) _))
  calc
    _ ≤ (B : ℝ)^(-(22/100 : ℝ))*candidateMultiplicityMoment B L T H τ C χ i t :=
      hsquare T H M C χ hχ i t hit
    _ ≤ (B : ℝ)^(-(22/100 : ℝ))*(2*(B : ℝ)^(8/1000 : ℝ)*candidateFirstPairMass B L T H τ C χ i t) :=
      mul_le_mul_of_nonneg_left hweighted (Real.rpow_nonneg hbpos.le _)
    _ ≤ (B : ℝ)^(-(22/100 : ℝ))*(2*(B : ℝ)^(8/1000 : ℝ)*
        (K/(T : ℝ)*singularFactor 24 (t.val-i.val))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hbpos.le _)
      exact mul_le_mul_of_nonneg_left (hfirst L T H M τ C hT hTs χ (fun e => (hχ e).2) i t hit)
        (by positivity)
    _ = (2*K/(T : ℝ)*singularFactor 24 (t.val-i.val))*
        ((B : ℝ)^(-(22/100 : ℝ))*(B : ℝ)^(8/1000 : ℝ)) := by ring
    _ ≤ (2*K/(T : ℝ)*singularFactor 24 (t.val-i.val))*(B : ℝ)^(-(21/100 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpower hbase
    _ = _ := by ring

end JointDickman

end OAI
