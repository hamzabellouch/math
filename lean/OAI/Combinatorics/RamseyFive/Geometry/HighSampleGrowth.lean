import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.HighPairVariance
import OAI.Combinatorics.RamseyFive.Entropy.FiniteGrowth

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] in
lemma nongrowth_avoids {n : ℕ} (y : ℙ K (Dual K V)) (W : Submodule K (Dual K V))
    (x : Fin n→SampleFlag (K:=K) (V:=V)) (hr : finrank K (growSpan y W x)≤finrank K W) :
    ∀ i,x i∉newHits y W := by
  intro i hi
  obtain ⟨hi,hn⟩:=(Finset.mem_filter.mp hi).2
  apply hn
  rw [←growSpan_eq_of_rank_le y W x hr]
  exact hit_le_growSpan y W x i hi

lemma block_growth_failure (p : Law (SampleFlag (K:=K) (V:=V)))
    (y : ℙ K (Dual K V)) (B : ℝ) (hB : 0≤B) (hp : ∀ b,second p b≤B)
    (hy : y∉lowHits (first p)) (hsmall : 2*(Nat.card K:ℝ)^2*B≤1/(20*(Nat.card K:ℝ)))
    (n : ℕ) (W : Submodule K (Dual K V)) :
    eventWeight (iid p (Fin n)) (failedGrowth (growSpan (n:=n) y) (fun W : Submodule K (Dual K V)=>finrank K W) 4 W)≤
      (1-1/(5*(Nat.card K:ℝ)))^n := by
  have hq : 2≤(Nat.card K:ℝ) := by exact_mod_cast Finite.one_lt_card (α:=K)
  have hc : 0≤1-1/(5*(Nat.card K:ℝ)) := by
    have hh : 1/(5*(Nat.card K:ℝ))≤1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  by_cases hr : finrank K W<4
  · calc
      _ ≤ eventWeight (iid p (Fin n)) (fun x=>∀ i,x i∉newHits y W) :=
        eventWeight_mono _ _ _ (fun x hx=>nongrowth_avoids y W x hx.2)
      _ = (1-eventMass p (newHits y W))^n := iid_avoidance p _ n
      _ ≤ _ := pow_le_pow_left₀ (sub_nonneg.mpr (eventMass_le_one p _))
        (by linarith [newHits_mass p y W B hr hB hp hy hsmall]) n
  · have he : eventWeight (iid p (Fin n))
        (failedGrowth (growSpan (n:=n) y) (fun W : Submodule K (Dual K V)=>finrank K W) 4 W)=0 := by
      simp only [eventWeight,failedGrowth,hr,false_and,ite_false,Finset.sum_const_zero]
    rw [he]
    exact pow_nonneg hc _

def sampleSpan {n t : ℕ} (x : Fin t→Fin n→SampleFlag (K:=K) (V:=V))
    (y : ℙ K (Dual K V)) : Submodule K (Dual K V) :=
  runSamples (growSpan y) y.submodule x

theorem sampled_span_rank_failure (p : Law (SampleFlag (K:=K) (V:=V)))
    (y : ℙ K (Dual K V)) (B : ℝ) (hB : 0≤B) (hp : ∀ b,second p b≤B)
    (hy : y∉lowHits (first p)) (hsmall : 2*(Nat.card K:ℝ)^2*B≤1/(20*(Nat.card K:ℝ)))
    (n : ℕ) :
    eventWeight (iid (iid p (Fin n)) (Fin 3))
      (fun x=>finrank K (sampleSpan x y)<4)≤3*(1-1/(5*(Nat.card K:ℝ)))^n := by
  exact iid_growth_failure (iid p (Fin n)) (growSpan y) (fun W : Submodule K (Dual K V)=>finrank K W) 4
    (fun W x=>rank_growSpan_mono y W x) _
    (fun W=>block_growth_failure p y B hB hp hy hsmall n W) y.submodule 3
    (by rw [y.finrank_submodule])
end
end SharpRamseyFive.HighSamples

end OAI
