import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.FiniteNodeProcess
import OAI.Combinatorics.RamseyFive.Geometry.OrientedNodeCaps
import OAI.Combinatorics.RamseyFive.Geometry.GuardedNode

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def orientedGuardedNodeLaw
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ) (hδ : 0<δ) :
    Law (Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))) :=
  map (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
    (orientedGuardedNodeEncoded f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t).map
      (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t))

theorem orientedNode_first_process {ι κ Θ : Type*} [Fintype ι] [Fintype κ] [Fintype Θ]
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (p : Law (ℙ K V)) (r : Law (ℙ K (Dual K V))) (μ : Law ι) (ν : Law κ)
    (X : ι→Finset (ℙ K V)) (Y : κ→Finset (ℙ K (Dual K V))) (hXnon : ∀i,(X i).Nonempty)
    (prior : ι→κ→Law Θ) (active : ι→κ→Θ→Prop)
    (B₀ UB : ι→κ→Θ→Finset (ℙ K (Dual K V))) (UA : ι→κ→Θ→Finset (ℙ K V))
    (hBnon : ∀i j θ,(B₀ i j θ).Nonempty)
    (pred : ι→κ→Θ→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (rev : ι→κ→Θ→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (c δ τ L : ℝ) (M : ι→κ→Θ→ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ)
    (hτ : 1000*τ≤c*δ^2) (hL : 0≤L)
    (hX : ∀a,(∑i,μ i*uniformWeight (X i) a)≤L*p a)
    (hY : ∀b,(∑j,ν j*uniformWeight (Y j) b)≤L*r b) :
    (∑i,∑j,μ i*ν j*(∑θ,prior i j θ*(∑out,
      gateOutputLaw (active i j θ)
        (orientedGuardedNodeLaw (pred i j θ) (rev i j θ) σ hσ hq hd.le (X i) (UA i j θ) (B₀ i j θ) (UB i j θ)
          (hXnon i) (hBnon i j θ) c δ τ (M i j θ) hδ) out*
        evictionFraction (Y j) (ambientTest (out.map Prod.fst)))))≤
      (50*(Nat.card K:ℝ)/(9*(c*δ)))*L^2*relationMass Incident p r := by
  refine adaptive_ambient_eviction Incident p r μ ν X Y prior
    (fun i j θ=>gateOutputLaw (active i j θ)
      (orientedGuardedNodeLaw (pred i j θ) (rev i j θ) σ hσ hq hd.le (X i) (UA i j θ) (B₀ i j θ) (UB i j θ)
        (hXnon i) (hBnon i j θ) c δ τ (M i j θ) hδ))
    (fun out=>out.map Prod.fst) (50*(Nat.card K:ℝ)/(9*(c*δ))) L
    (by positivity) hL hX hY ?_
  intro i j θ b
  have h := (orientedGuardedNode_original (pred i j θ) (rev i j θ) σ hσ hq hd hq3 (X i) (UA i j θ)
    (B₀ i j θ) (UB i j θ) (hXnon i) (hBnon i j θ) c δ τ (M i j θ) hc hc9 hδ hτ).1 b
  have hh := gateOutput_event_le (active i j θ) _ (fun out=>Excludes b (out.map Prod.fst))
    (by simp [Excludes]) _ (by positivity) h
  have he : (Finset.univ.filter (fun a=>Incident a b))∩X i=(X i).filter (fun a=>Incident a b) := by
    ext a;simp [and_comm]
  simpa only [he,orientedGuardedNodeLaw] using hh

theorem orientedNode_second_process {ι κ Θ : Type*} [Fintype ι] [Fintype κ] [Fintype Θ]
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (p : Law (ℙ K (Dual K V))) (r : Law (ℙ K V)) (μ : Law ι) (ν : Law κ)
    (X : ι→Finset (ℙ K (Dual K V))) (Y : κ→Finset (ℙ K V)) (hXnon : ∀i,(X i).Nonempty)
    (prior : ι→κ→Law Θ) (active : ι→κ→Θ→Prop)
    (A₀ UA : ι→κ→Θ→Finset (ℙ K V)) (UB : ι→κ→Θ→Finset (ℙ K (Dual K V)))
    (hAnon : ∀i j θ,(A₀ i j θ).Nonempty)
    (pred : ι→κ→Θ→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (rev : ι→κ→Θ→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (c δ τ L : ℝ) (M : ι→κ→Θ→ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ)
    (hτ : 1000*τ≤c*δ^2) (hL : 0≤L)
    (hX : ∀a,(∑i,μ i*uniformWeight (X i) a)≤L*p a)
    (hY : ∀b,(∑j,ν j*uniformWeight (Y j) b)≤L*r b) :
    (∑i,∑j,μ i*ν j*(∑θ,prior i j θ*(∑out,
      gateOutputLaw (active i j θ)
        (orientedGuardedNodeLaw (pred i j θ) (rev i j θ) σ hσ hq hd.le (A₀ i j θ) (UA i j θ) (X i) (UB i j θ)
          (hAnon i j θ) (hXnon i) c δ τ (M i j θ) hδ) out*
        evictionFraction (Y j) (ambientTest (out.map Prod.snd)))))≤
      (50*(Nat.card K:ℝ)/(9*(c*δ)))*L^2*relationMass (fun b a=>Incident a b) p r := by
  refine adaptive_ambient_eviction (fun b a=>Incident a b) p r μ ν X Y prior
    (fun i j θ=>gateOutputLaw (active i j θ)
      (orientedGuardedNodeLaw (pred i j θ) (rev i j θ) σ hσ hq hd.le (A₀ i j θ) (UA i j θ) (X i) (UB i j θ)
        (hAnon i j θ) (hXnon i) c δ τ (M i j θ) hδ))
    (fun out=>out.map Prod.snd) (50*(Nat.card K:ℝ)/(9*(c*δ))) L
    (by positivity) hL hX hY ?_
  intro i j θ a
  have h := (orientedGuardedNode_original (pred i j θ) (rev i j θ) σ hσ hq hd hq3 (A₀ i j θ) (UA i j θ)
    (X i) (UB i j θ) (hAnon i j θ) (hXnon i) c δ τ (M i j θ) hc hc9 hδ hτ).2 a
  have hh := gateOutput_event_le (active i j θ) _ (fun out=>Excludes a (out.map Prod.snd))
    (by simp [Excludes]) _ (by positivity) h
  have he : (Finset.univ.filter (Incident a))∩X i=(X i).filter (Incident a) := by
    ext b;simp [and_comm]
  simpa only [he,orientedGuardedNodeLaw] using hh
end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

theorem orientedGuardedNode_flags
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c τ P b : ℝ)
    (hc : 0<c) (hc9 : c≤9/10) (hb : 0≤b)
    (hp : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card)
    (t : OrientedNodeTape f r (1000*(Nat.card K)^2) (Nat.card K))
    (m : OrientedNodeMessage f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c (9/10) τ P
      (by norm_num) t=some m) :
    (incidences
      (UA∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).2)
      (UB∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).1):ℝ)≤
      2*((320/c+320)^2)*(Nat.card K:ℝ)^4*Real.exp (b+1) := by
  have hready := (orientedGuardedNode_original_capture f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀
    c (9/10) τ P (by norm_num) t m hm).1
  obtain ⟨hAcap,hBcap⟩ := orientedGuardedNode_caps f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀
    c (9/10) τ P hc hc9 (by norm_num) t m hm
  have hnA := nonempty_of_positive_trim _ _ hA₀ (9/10) (by norm_num) hready.1
  have hnB := nonempty_of_positive_trim _ _ hB₀ (9/10) (by norm_num) hready.2.1
  have hC : 1≤320/c+320 := by
    have hh : 0≤320/c := by positivity
    linarith only [hh]
  have hC2 : 1≤(320/c+320)^2 := by nlinarith only [hC]
  apply reciprocal_rectangle_flags hd _ _ _ (b+1) hC2 (by linarith only [hb])
  have hQ : (0:ℝ)<(Nat.card K:ℝ)^5 := by rw [←hq]; positivity
  have hh := reciprocal_cap_product ((Nat.card K:ℝ)^5) (A₀∩UA).card (B₀∩UB).card _ _
    (320/c+320) (320/c+320) (b+1) hQ
    (by exact_mod_cast hnA.card_pos) (by exact_mod_cast hnB.card_pos)
    (by positivity) (by positivity) (by linarith only [hC]) (by linarith only [hC])
    (ready_trimmed_product A₀ UA B₀ UB τ b hready hp) hAcap hBcap
  simpa only [pow_two] using hh

end SharpRamseyFive.ProjectiveIncidence

end OAI
