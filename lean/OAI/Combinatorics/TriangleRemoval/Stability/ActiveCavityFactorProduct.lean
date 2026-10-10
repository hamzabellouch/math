import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TriangleHypergraphReindex
import OAI.Combinatorics.TriangleRemoval.Stability.CavityWeight
import OAI.Combinatorics.TriangleRemoval.Process.PathRequired

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

lemma active_cavity_factor_product {n : ℕ} (G : Graph n) (e : G) (T : triangles G) (t : ℝ) :
    (∏ f ∈ (triangleHypergraph G T.val).erase e.val,
      cavityLimit (triangleHypergraph G) f (some T.val) t) =
    ∏ f ∈ (activeHypergraph G T).erase e, cavityLimit (activeHypergraph G) f (some T) t := by
  change (∏ f ∈ (triangleHypergraph G (triangleEmbedding G T)).erase (edgeEmbedding G e), _) = _
  rw [triangleHypergraph_reindex,← Finset.map_erase,Finset.prod_map]
  apply Finset.prod_congr rfl
  intro f _
  exact active_cavity_eq G f (some T) t

lemma active_messageIntegral {n : ℕ} (G : Graph n) (e : G) (T : triangles G) (t : ℝ) :
    messageIntegral (triangleHypergraph G) (cavityLimit (triangleHypergraph G)) e.val T.val t =
    messageIntegral (activeHypergraph G) (cavityLimit (activeHypergraph G)) e T t := by
  unfold messageIntegral
  apply intervalIntegral.integral_congr
  intro s _
  exact active_cavity_factor_product G e T s

lemma goodPrefix_full_continuous_rows {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 < prefixD n ∧
      ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ (e T : Finset (Fin n)), e ∈ triangleHypergraph G T →
        messageIntegral (triangleHypergraph G) (cavityLimit (triangleHypergraph G)) e T t ≤ 1/16 ∧
        (∏ f ∈ (triangleHypergraph G T).erase e,
          cavityLimit (triangleHypergraph G) f (some T) t) ≤
          (17/16 : ℝ)*cavityWeight (prefixD n) t := by
  filter_upwards [goodPrefix_continuous_rows hc] with n hn
  refine ⟨hn.1,?_⟩
  intro C G hG t ht e T he
  have heG := triangleHypergraph_subset G T he
  have hT : T ∈ triangles G := by
    by_contra hT
    simp only [triangleHypergraph,hT,ite_false,Finset.notMem_empty] at he
  let ee : G := ⟨e,heG⟩
  let TT : triangles G := ⟨T,hT⟩
  have heact : ee ∈ activeHypergraph G TT := by
    have hh : edgeEmbedding G ee ∈ (activeHypergraph G TT).map (edgeEmbedding G) := by
      rw [← triangleHypergraph_reindex]
      exact he
    exact Finset.mem_map.mp hh |>.elim (fun _ ha => (edgeEmbedding G).injective ha.2 ▸ ha.1)
  obtain ⟨h1,h2⟩ := hn.2 C G hG t ht
  rw [show e = ee.val from rfl,show T = TT.val from rfl,
    active_messageIntegral,active_cavity_factor_product]
  exact ⟨h1 ee TT heact,h2 ee TT heact⟩

theorem goodPrefix_full_grid_rows {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
        GridRowQuality (triangleHypergraph G) N
          (fun k => cavityWeight (prefixD n) ((k : ℝ)/N)) := by
  filter_upwards [goodPrefix_full_continuous_rows hc] with n hn
  intro C G h
  let H := triangleHypergraph G
  let A : ℝ := (Fintype.card (Finset (Fin n)) : ℝ)*gridUniformError H +
    (Fintype.card (Finset (Fin n)) : ℝ)*Fintype.card (Finset (Fin n))
  let B : ℝ := 2*gridUniformError H
  have hA : Tendsto (fun N : ℕ => A/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hB : Tendsto (fun N : ℕ => B/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall : ∀ᶠ N : ℕ in atTop, A/(N : ℝ) ≤ 1/16 ∧
      B/(N : ℝ) ≤ cavityWeight (prefixD n) 1/16 := by
    filter_upwards [hA.eventually_le_const (by norm_num : (0 : ℝ) < 1/16),
      hB.eventually_le_const (show 0 < cavityWeight (prefixD n) 1/16 from
        div_pos (cavityWeight_pos hn.1.le zero_le_one) (by norm_num))]
      with N ha hb
    exact ⟨ha,hb⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hsmall
  refine ⟨N₀,?_⟩
  intro N _ hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ht (k : ℕ) (hk : k ≤ N) : (k : ℝ)/N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity,(div_le_one hNpos).mpr (by exact_mod_cast hk)⟩
  obtain ⟨ha,hb⟩ := hN₀ N hN
  constructor
  · intro k hk e T he
    obtain ⟨hi,_⟩ := hn.2 C G h _ (ht k hk) e T he
    have herr := gridCandidateFailure_error H N k hk e T
    change |gridCandidateFailure H N k e T - _| ≤ A/(N : ℝ) at herr
    have hh := (abs_le.mp herr).1
    dsimp only [H] at hh
    linarith
  · intro k hk e T he
    obtain ⟨_,hp⟩ := hn.2 C G h _ (ht k hk) e T he
    have hT : T ∈ triangles G := by
      by_contra hh
      simp only [triangleHypergraph,hh,ite_false,Finset.notMem_empty] at he
    have hcard : ((H T).erase e).card = 2 := by
      rw [Finset.card_erase_of_mem he]
      simp only [triangleHypergraph,hT,ite_true,Finset.card_powersetCard,(mem_triangles.mp hT).1]
      decide
    have herr := gridAnswer_uniform_error H N k hk ((H T).erase e) (some T)
    rw [hcard] at herr
    have herr' := (abs_le.mp herr).2
    have hbl := cavityWeight_lower hn.1.le (ht k hk)
    dsimp only [B,H] at hb herr'
    linarith

end SharpTerminalLeave

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

end

end OAI
