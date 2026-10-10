import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.GuardedNode

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {Ω α : Type*} [Fintype Ω] [Fintype α]
lemma map_decoded_none_event {M : Ω → Type*} (p : Law Ω)
    (enc : ∀ t, Option (M t)) (dec : ∀ t, M t → α) :
    map p (fun t => (enc t).map (dec t)) none =
      eventMass p (Finset.univ.filter (fun t => enc t = none)) := by
  simp only [map, eventMass, Finset.sum_filter, Option.map_eq_none_iff]
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
noncomputable section
local instance (priority := high) actualReadyFailurePropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem eventually_oriented_ready_encoded_failure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
      (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      OriginalNodeReady A₀ UA B₀ UB (9/10) (σ^(-1000*beta η)) →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card →
      let f := fourFinitePredictor hd σ UA UB (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ UB
        (UA.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      eventMass (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K))
        (Finset.univ.filter (fun t => orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀
          (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) t = none)) ≤
            5*Real.exp (-(Nat.card K:ℝ)) := by
  filter_upwards [eventually_oriented_guarded_node_failure hη hη' Cb hCb] with σ hn
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ _ hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hprod
  have hh := hn D b R L₀ q K V hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hprod
  dsimp only at hh ⊢
  rw [map_decoded_none_event] at hh
  convert hh using 1
  congr 1
  ext t
  simp only [Finset.mem_filter]
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
