import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalHistoryDrift
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalHistorySurvival
import OAI.Combinatorics.KMedian.Geometry.RationalHistoryValid
import OAI.Combinatorics.KMedian.Geometry.RationalCompletedCost

namespace OAI


                                                 
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential CopyState Completion.Rational
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j Δ : ℕ}
local instance rationalHistoryCompletionCopyOrder : LinearOrder (Copy (F := F) Δ) := copyOrder

def completed (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (B : Fin j → Finset (Copy (F := F) Δ)) (hB : ∀ c, (B c).Nonempty)
    (g β : ℚ) (z : SparseHistories.History (State F Δ g β)) : Finset F :=
  Completion.Rational.output d R z.1.1 B hB

theorem histories_completion (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (Copy (F := F) Δ)) (B : Fin j → Finset (Copy (F := F) Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty) (T : ℕ) (x : ℕ → ℝ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hBA : ∀ c, B c⊆A)
    (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1≤R c)
    (a : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) :
    let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val];
    let O := completed d R B hB g β z;
    ((O.card:ℝ)≤ mass (g:ℝ) z.1.1) ∧
    (0<j → O.Nonempty) ∧
    (score d O:ℝ) ≤ ∑ c, (
      potential (x T) (g:ℝ) (fun i : Copy (F := F) Δ => dist (client c) (location i.1))
        (replay g β x (fun (_ : Unit) f => dist (client c) (location f)) (fun _ => B c) z ())
        (GroupCap.cap (R c:ℝ) (fun f => dist (client c) (location f)) (integral Δ z.1.1))+
      5*(R c:ℝ)*mass (g:ℝ)
        (replay g β x (fun (_ : Unit) f => dist (client c) (location f)) (fun _ => B c) z ())) := by
  let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val]
  have hbackup : ∀ c, (¬∃ f∈integral Δ z.1.1, d c f≤5*R c) → B c⊆z.1.1 := by
    intro c hn
    have hv := histories_valid d₀ location (fun (_ : Unit) => client c) hd₀ g β p φ P hp hφ hupper A
      (fun _ => B c) (fun _ => (R c:ℝ)) T x hg hunit hP hP1 hA (fun _ => hBA c)
      (fun _ => by exact_mod_cast hR c) (fun _ => hm c)
      (fun _ i hi => by rw [hd]; exact_mod_cast hdR c i hi) a
    apply hv.2.2.2 ()
    intro h
    obtain ⟨f,hf,hfd⟩ := h
    rw [hd] at hfd
    dsimp only at hfd
    exact hn ⟨f,hf,by exact_mod_cast hfd⟩
  obtain ⟨_,hc,hn⟩ := output_spec d R location client hd hR hg.le hunit z.1.1 B hB hm hdR hbackup
  refine ⟨hc,?_,?_⟩
  · intro hj
    obtain ⟨f,hf,_⟩ := hn ⟨0,hj⟩
    exact ⟨f,hf⟩
  · exact output_potential d R location client hd hR hg.le hunit z.1.1 B
      (fun c => replay g β x (fun (_ : Unit) f => dist (client c) (location f))
        (fun _ => B c) z ()) hB hm hdR hbackup

theorem histories_completed_expectation (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (Copy (F := F) Δ)) (B : Fin j → Finset (Copy (F := F) Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty) (T : ℕ)
    {h ζ : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ)≤1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hh0 : 0 ≤ h) (hh1 : h≤1) (hφ1 : (φ:ℝ)≤1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
    (hsurv : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ<1/4)
    (he : ∀ t<T, |(P t:ℝ)-Analytic.P (Real.exp (-(t:ℝ)*h))|≤ζ)
    (hBA : ∀ c, B c⊆A) (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1≤R c) (hatt : ∀ c, ∃ i∈B c, R c=d c i.1) :
    (histories d₀ g β p φ P hp hφ hupper A T).expectation
      (fun z => (score d (completed d R B hB g β z):ℝ)) ≤
    ∑ c, ((1+2/Real.exp 1)*PhysicalPotential.cost (g:ℝ) (fun i : Copy (F := F) Δ => dist (client c) (location i.1)) (B c)+
      (T:ℝ)*(h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i : Copy (F := F) Δ => dist (client c) (location i.1)) (B c)+
        FixedBatch.batchConstant Δ*h*((φ:ℝ)+h)*(R c:ℝ))+5*(R c:ℝ)*(1-h/2)^T) := by
  let μ := histories d₀ g β p φ P hp hφ hupper A T
  let x := fun t : ℕ => Real.exp (-(t:ℝ)*h)
  let L := fun c z => replay g β x (fun (_ : Unit) f => dist (client c) (location f)) (fun _ => B c) z ()
  let V := fun c z => potential (x T) (g:ℝ)
    (fun i : Copy (F := F) Δ => dist (client c) (location i.1)) (L c z)
    (GroupCap.cap (R c:ℝ) (fun f => dist (client c) (location f)) (integral Δ z.1.1))
  have hc : μ.expectation (fun z => (score d (completed d R B hB g β z):ℝ)) ≤
      μ.expectation (fun z => ∑ c, (V c z+5*(R c:ℝ)*mass (g:ℝ) (L c z))) := by
    apply μ.realIndex.expect_mono
    intro a
    exact (histories_completion d₀ d location client hd₀ hd g β p φ P hp hφ hupper A B R hB T x
      hg hunit hP hP1 hA hBA hR hm hdR a).2.2
  apply hc.trans
  rw [SparseIntegerLaw.expectation,FiniteLaw.expect_sum]
  apply sum_le_sum
  intro c _
  rw [FiniteLaw.expect_add,FiniteLaw.expect_mul]
  have hv := histories_drift d₀ location (client c) hd₀ g β p φ P hp hφ hupper A (B c) T
    hprob hg hg1 hunit hP hP1 hA hh0 hh1 hφ1 hsmall hζ0 hζ1 he (hBA c) (hm c)
    (R := (R c:ℝ)) (by exact_mod_cast hR c) (fun i hi => by rw [hd]; exact_mod_cast hdR c i hi) (by
      obtain ⟨i,hi,hiR⟩ := hatt c
      refine ⟨i,hi,?_⟩
      rw [hd]
      exact_mod_cast hiR)
  have hs := histories_survival d₀ location hd₀ g β p φ P hp hφ hupper A (B c) T x
    (fun f => dist (client c) (location f)) hprob hg hunit hP hP1 hh0 hh1 hφ1 hA hsurv (hBA c)
  rw [hm c,mul_one] at hs
  exact add_le_add hv (mul_le_mul_of_nonneg_left hs (by exact_mod_cast mul_nonneg (by norm_num : (0:ℚ)≤5) (hR c)))

end MetricKMedian.RationalPhysicalKernel
end

end OAI
