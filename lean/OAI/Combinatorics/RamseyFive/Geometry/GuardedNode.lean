import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.GuardedNodeOriginal
import OAI.Combinatorics.RamseyFive.Geometry.ReadyRefinement

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_guarded_node_failure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (hd : finrank K V=5) (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
      (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      OriginalNodeReady A₀ UA B₀ UB (9/10) (σ^(-1000*beta η)) →
      (A₀∩UA).card≤(B₀∩UB).card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card →
      let f := fourFinitePredictor hd σ UA UB (P η σ D R) (σ^(-800*beta η)) R L₀
      guardedNodeLaw f σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ (9/100000) (9/10)
        (σ^(-1000*beta η)) (((A₀∩UA).card:ℝ)*Real.exp (10*P η σ D R)) (by norm_num) none≤
          5*Real.exp (-(Nat.card K:ℝ)) := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-200*beta η)≤(9/10:ℝ)^2 := by
    have hp : 0<200*beta η := mul_pos (by norm_num) (beta_pos hη)
    exact ((tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<(9/10:ℝ)^2)).mono (fun σ h=>by simpa only [neg_mul] using h.le)
  filter_upwards [eventually_finite_node hη hη' (Cb+1) (by linarith),ht] with σ hn ht
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hAB hprod
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hD : 1≤D := (Real.one_le_rpow hσ (beta_pos hη).le).trans hr.dlo
  have hF : 1≤σ^(6*beta η) := Real.one_le_rpow hσ (by positivity [beta_pos hη])
  have hb' : b+1≤(Cb+1)*D*σ^(6*beta η) := by
    have hx := mul_le_mul hD hF (by norm_num : (0:ℝ)≤1) (by linarith : 0≤D)
    nlinarith only [hbhi,hx]
  have hτ : σ^(-1000*beta η)≤σ^(-800*beta η)*(9/10:ℝ)^2 := by
    have hm := mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hs.le (-800*beta η))
    rw [←Real.rpow_add hs] at hm
    simpa only [show -800*beta η+(-200*beta η)=-1000*beta η by ring] using hm
  have hdens := ready_trimmed_density A₀ UA B₀ UB _ _ (Real.rpow_nonneg hs.le _) hτ hready
  have hp := ready_trimmed_product A₀ UA B₀ UB _ b hready hprod
  obtain ⟨hnA,hnB,hf,_,_⟩ := hn D (b+1) (σ^(-800*beta η)) R L₀ q K V hd (A₀∩UA) UA (B₀∩UB) UB
    hcard (hq.trans (by exact_mod_cast hcard)) hr hL (by linarith) hb'
    (Real.rpow_pos_of_pos hs _) le_rfl Finset.inter_subset_right Finset.inter_subset_right hAB hdens hp
  simpa only [guardedNodeLaw,dite_eq_left hready] using hf

theorem eventually_oriented_guarded_node_failure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
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
      map (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
        (orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ (9/100000)
          (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) t).map
          (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t)) none≤
            5*Real.exp (-(Nat.card K:ℝ)) := by
  filter_upwards [eventually_guarded_node_failure hη hη' Cb hCb] with σ hn
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ _ hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hprod
  dsimp only
  rw [orientedGuardedNode_law]
  split_ifs with hAB
  · exact hn D b R L₀ q K V hd A₀ UA B₀ UB hA₀ hB₀ hσ hq hcard hr hL hb hbhi hready hAB hprod
  · rw [map_option_none]
    apply hn D b R L₀ q K (Dual K V) (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map
      hσ hq hcard hr hL hb hbhi
    · exact (ready_bidual A₀ UA B₀ UB _ _).mpr hready
    · simpa only [←Finset.map_inter,Finset.card_map] using (le_of_not_ge hAB)
    · simpa only [Finset.card_map,mul_comm (B₀.card:ℝ) (A₀.card:ℝ)] using hprod
end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma reverseNodePair_excludes_first
    (out : Option (Finset (ℙ K (Dual K (Dual K V)))×Finset (ℙ K (Dual K V))))
    (b : ℙ K (Dual K V)) :
    Excludes b ((out.map reverseNodePair).map Prod.fst) ↔ Excludes b (out.map Prod.snd) := by
  cases out <;> simp [reverseNodePair,Excludes]
omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma reverseNodePair_excludes_second
    (out : Option (Finset (ℙ K (Dual K (Dual K V)))×Finset (ℙ K (Dual K V))))
    (a : ℙ K V) :
    Excludes a ((out.map reverseNodePair).map Prod.snd) ↔
      Excludes (bidualPoint a) (out.map Prod.fst) := by
  cases out <;> simp [reverseNodePair,Excludes]

theorem orientedGuardedNode_original
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ)
    (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2) :
    let p := map (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
      (orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t).map
        (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t))
    (∀b,eventMass p (Finset.univ.filter fun out=>Excludes b (out.map Prod.fst))≤
        (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card)) ∧
    (∀a,eventMass p (Finset.univ.filter fun out=>Excludes a (out.map Prod.snd))≤
        (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card)) := by
  have hconst : 50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ))≤50*(Nat.card K:ℝ)/(9*(c*δ)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hc9 hδ.le]
  dsimp only
  rw [orientedGuardedNode_law]
  split_ifs with hAB
  · obtain ⟨h1,h2⟩ := guardedNode_original f σ hσ hq hd hq3 A₀ UA B₀ UB
      hA₀ hB₀ c δ τ (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hc hc9 hδ hτ
    refine ⟨h1,fun a=>(h2 a).trans ?_⟩
    exact mul_le_mul_of_nonneg_right hconst (by positivity)
  · obtain ⟨h1,h2⟩ := guardedNode_original r σ hσ hq (by simpa using hd) hq3 B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map
      c δ τ (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hc hc9 hδ hτ
    constructor
    · intro b
      rw [eventMass_map_filter]
      simp only [reverseNodePair_excludes_first]
      have hh := h2 b
      simp only [Finset.filter_map,Finset.card_map,Function.comp_def,Equiv.toEmbedding_apply,
        incident_bidual] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hconst (by positivity))
    · intro a
      rw [eventMass_map_filter]
      simp only [reverseNodePair_excludes_second]
      simpa only [incident_bidual] using h1 (bidualPoint a)

end SharpRamseyFive.ProjectiveIncidence

end OAI
