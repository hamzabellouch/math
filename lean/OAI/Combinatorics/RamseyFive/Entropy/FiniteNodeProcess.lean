import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.AmbientEviction

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {Ω : Type*} [Fintype Ω]

noncomputable def gateOutputLaw (ready : Prop) (p : Law (Option Ω)) : Law (Option Ω) :=
  if ready then p else pureLaw none
lemma gateOutput_event_le (ready : Prop) (p : Law (Option Ω)) (P : Option Ω→Prop)
    (hn : ¬P none) (B : ℝ) (hB : 0≤B)
    (hp : eventMass p (Finset.univ.filter P)≤B) :
    eventMass (gateOutputLaw ready p) (Finset.univ.filter P)≤B := by
  unfold gateOutputLaw
  split_ifs
  · exact hp
  · rw [eventMass_pure_filter_of_not none P hn]
    exact hB
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem finiteNode_first_process {ι κ Θ : Type*} [Fintype ι] [Fintype κ] [Fintype Θ]
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (p : Law (ℙ K V)) (r : Law (ℙ K (Dual K V))) (μ : Law ι) (ν : Law κ)
    (X : ι→Finset (ℙ K V)) (Y : κ→Finset (ℙ K (Dual K V))) (hXnon : ∀i,(X i).Nonempty)
    (prior : ι→κ→Law Θ) (active : ι→κ→Θ→Prop)
    (B₀ UB : ι→κ→Θ→Finset (ℙ K (Dual K V))) (UA : ι→κ→Θ→Finset (ℙ K V))
    (hBnon : ∀i j θ,(B₀ i j θ).Nonempty)
    (pred : ι→κ→Θ→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (c δ τ L : ℝ) (M : ι→κ→Θ→ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ)
    (hτ : 1000*τ≤c*δ^2) (hL : 0≤L)
    (hX : ∀a,(∑i,μ i*uniformWeight (X i) a)≤L*p a)
    (hY : ∀b,(∑j,ν j*uniformWeight (Y j) b)≤L*r b) :
    (∑i,∑j,μ i*ν j*(∑θ,prior i j θ*(∑out,
      gateOutputLaw (active i j θ)
        (guardedNodeLaw (pred i j θ) σ hσ hq hd.le (X i) (UA i j θ) (B₀ i j θ) (UB i j θ)
          (hXnon i) (hBnon i j θ) c δ τ (M i j θ) hδ) out*
        evictionFraction (Y j) (ambientTest (out.map Prod.fst)))))≤
      (50*(Nat.card K:ℝ)/(9*(c*δ)))*L^2*relationMass Incident p r := by
  refine adaptive_ambient_eviction Incident p r μ ν X Y prior
    (fun i j θ=>gateOutputLaw (active i j θ)
      (guardedNodeLaw (pred i j θ) σ hσ hq hd.le (X i) (UA i j θ) (B₀ i j θ) (UB i j θ)
        (hXnon i) (hBnon i j θ) c δ τ (M i j θ) hδ))
    (fun out=>out.map Prod.fst) (50*(Nat.card K:ℝ)/(9*(c*δ))) L
    (by positivity) hL hX hY ?_
  intro i j θ b
  have h := (guardedNode_original (pred i j θ) σ hσ hq hd hq3 (X i) (UA i j θ)
    (B₀ i j θ) (UB i j θ) (hXnon i) (hBnon i j θ) c δ τ (M i j θ) hc hc9 hδ hτ).1 b
  have hh := gateOutput_event_le (active i j θ) _ (fun out=>Excludes b (out.map Prod.fst))
    (by simp [Excludes]) _ (by positivity) h
  have he : (Finset.univ.filter (fun a=>Incident a b))∩X i=(X i).filter (fun a=>Incident a b) := by
    ext a;simp [and_comm]
  simpa only [he] using hh

theorem finiteNode_second_process {ι κ Θ : Type*} [Fintype ι] [Fintype κ] [Fintype Θ]
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (p : Law (ℙ K (Dual K V))) (r : Law (ℙ K V)) (μ : Law ι) (ν : Law κ)
    (X : ι→Finset (ℙ K (Dual K V))) (Y : κ→Finset (ℙ K V)) (hXnon : ∀i,(X i).Nonempty)
    (prior : ι→κ→Law Θ) (active : ι→κ→Θ→Prop)
    (A₀ UA : ι→κ→Θ→Finset (ℙ K V)) (UB : ι→κ→Θ→Finset (ℙ K (Dual K V)))
    (hAnon : ∀i j θ,(A₀ i j θ).Nonempty)
    (pred : ι→κ→Θ→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (c δ τ L : ℝ) (M : ι→κ→Θ→ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ)
    (hτ : 1000*τ≤c*δ^2) (hL : 0≤L)
    (hX : ∀a,(∑i,μ i*uniformWeight (X i) a)≤L*p a)
    (hY : ∀b,(∑j,ν j*uniformWeight (Y j) b)≤L*r b) :
    (∑i,∑j,μ i*ν j*(∑θ,prior i j θ*(∑out,
      gateOutputLaw (active i j θ)
        (guardedNodeLaw (pred i j θ) σ hσ hq hd.le (A₀ i j θ) (UA i j θ) (X i) (UB i j θ)
          (hAnon i j θ) (hXnon i) c δ τ (M i j θ) hδ) out*
        evictionFraction (Y j) (ambientTest (out.map Prod.snd)))))≤
      (50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ)))*L^2*relationMass (fun b a=>Incident a b) p r := by
  refine adaptive_ambient_eviction (fun b a=>Incident a b) p r μ ν X Y prior
    (fun i j θ=>gateOutputLaw (active i j θ)
      (guardedNodeLaw (pred i j θ) σ hσ hq hd.le (A₀ i j θ) (UA i j θ) (X i) (UB i j θ)
        (hAnon i j θ) (hXnon i) c δ τ (M i j θ) hδ))
    (fun out=>out.map Prod.snd) (50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ))) L
    (by positivity) hL hX hY ?_
  intro i j θ a
  have h := (guardedNode_original (pred i j θ) σ hσ hq hd hq3 (A₀ i j θ) (UA i j θ)
    (X i) (UB i j θ) (hAnon i j θ) (hXnon i) c δ τ (M i j θ) hc hc9 hδ hτ).2 a
  have hh := gateOutput_event_le (active i j θ) _ (fun out=>Excludes a (out.map Prod.snd))
    (by simp [Excludes]) _ (by positivity) h
  have he : (Finset.univ.filter (Incident a))∩X i=(X i).filter (Incident a) := by
    ext b;simp [and_comm]
  simpa only [he] using hh
end SharpRamseyFive.ProjectiveIncidence

end OAI
