import OAI.Probability.InvariantIsing.Fields.SpinSliceComparison
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPressure

namespace OAI

/-! Finite unions of spin constraints approximate the full partition function
with an explicit spin-projection error and a finite-union cost. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma sum_biUnion_le_sum_of_nonneg {X J : Type*} [DecidableEq X]
    (B : Finset J) (S : J → Finset X) (f : X → ℝ) (hf : ∀ x, 0≤f x) :
    ∑ x ∈ B.biUnion S, f x ≤ ∑ j ∈ B, ∑ x ∈ S j, f x := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | @insert j B hj ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hj]
    have hu := Finset.sum_union_inter (s₁ := S j) (s₂ := B.biUnion S) (f := f)
    have hp : 0≤∑ x ∈ S j ∩ B.biUnion S, f x :=
      Finset.sum_nonneg (fun x _ => hf x)
    linarith

lemma restrictedSpinLog_finite_union_le {N : ℕ} {J : Type*}
    (B : Finset J) (hB : B.Nonempty) (S : J → Finset (Spin N))
    (hS : ∀ j ∈ B, (S j).Nonempty) (H : Spin N → ℝ) (M : ℝ)
    (hM : ∀ j ∈ B, restrictedSpinLog (S j) H ≤ M) :
    restrictedSpinLog (B.biUnion S) H ≤ M+Real.log B.card := by
  classical
  have hU : (B.biUnion S).Nonempty := by
    obtain ⟨j,hj⟩ := hB
    obtain ⟨σ,hσ⟩ := hS j hj
    exact ⟨σ, Finset.mem_biUnion.mpr ⟨j,hj,hσ⟩⟩
  have hsum (j : J) (hj : j∈B) :
      (∑ σ ∈ S j, Real.exp (H σ)) ≤ Real.exp (M+N*Real.log 2) := by
    have hp : 0<∑ σ ∈ S j, Real.exp (H σ) :=
      Finset.sum_pos (fun σ _ => Real.exp_pos _) (hS j hj)
    have he := Real.exp_le_exp.mpr (show Real.log (∑ σ ∈ S j, Real.exp (H σ)) ≤
      M+N*Real.log 2 by have := hM j hj; unfold restrictedSpinLog at this; linarith)
    rwa [Real.exp_log hp] at he
  have hb : (0:ℝ)<B.card := Nat.cast_pos.mpr hB.card_pos
  have hu : 0<∑ σ ∈ B.biUnion S, Real.exp (H σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) hU
  have he : (∑ σ ∈ B.biUnion S, Real.exp (H σ)) ≤
      (B.card : ℝ)*Real.exp (M+N*Real.log 2) := by
    apply (sum_biUnion_le_sum_of_nonneg B S (fun σ => Real.exp (H σ))
      (fun _ => (Real.exp_pos _).le)).trans
    simpa using Finset.sum_le_sum hsum
  have hl := Real.log_le_log hu he
  rw [Real.log_mul hb.ne' (Real.exp_ne_zero _), Real.log_exp] at hl
  unfold restrictedSpinLog
  linarith

lemma full_pressure_le_finite_cover {N : ℕ} (hN : 0<N) {J : Type*}
    (B : Finset J) (hB : B.Nonempty) (S : J → Finset (Spin N))
    (hS : ∀ j ∈ B, (S j).Nonempty) (f : Spin N → Spin N) (d : ℕ)
    (hf : ∀ σ, f σ ∈ B.biUnion S) (hd : ∀ σ, hammingDist σ (f σ) ≤ d)
    (eig c : Fin N → ℝ) (U : Rotation N) {K C t M : ℝ}
    (hK : 0≤K) (hC : 0≤C) (ht : 0≤t)
    (heig : ∀ i, |eig i|≤K) (hc : ∀ i, |c i|≤C)
    (hM : ∀ j ∈ B, restrictedRotatedPressure (S j) eig U c ≤ M) :
    rotatedPressure eig U c ≤ M+(N:ℝ)⁻¹*(Real.log B.card+
      2*K*Real.sqrt ((N:ℝ)*d)+2*C*d+t*d)+Real.log (1+Real.exp (-t)) := by
  classical
  have hU : (B.biUnion S).Nonempty := ⟨f (fun _ => false), hf _⟩
  have hb := restricted_spin_pressure_map_le Finset.univ (B.biUnion S)
    Finset.univ_nonempty hU f eig c U d hK hC ht heig hc
    (fun σ _ => hf σ) (fun σ _ => hd σ)
  have hm : ∀ j∈B, restrictedSpinLog (S j)
      (fun σ => rotatedEnergy eig U σ+fieldEnergy c σ) ≤ N*M := by
    intro j hj
    have h := hM j hj
    unfold restrictedRotatedPressure at h
    exact (inv_mul_le_iff₀ (by exact_mod_cast hN : (0:ℝ)<N)).mp h
  have hu := restrictedSpinLog_finite_union_le B hB S hS _ ((N:ℝ)*M) hm
  rw [restrictedSpinLog_univ] at hb
  have hi : (0:ℝ)≤(N:ℝ)⁻¹ := by positivity
  have hb' : logPartition (fun σ => rotatedEnergy eig U σ+fieldEnergy c σ) ≤
      N*M+Real.log B.card+(2*K*Real.sqrt ((N:ℝ)*d)+2*C*d)+
        t*d+N*Real.log (1+Real.exp (-t)) := by linarith
  have hh := mul_le_mul_of_nonneg_left hb' hi
  change (N:ℝ)⁻¹*logPartition (fun σ => rotatedEnergy eig U σ+fieldEnergy c σ) ≤ _
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  convert hh using 1
  field_simp
  ring

end InvariantIsing

end

end OAI
