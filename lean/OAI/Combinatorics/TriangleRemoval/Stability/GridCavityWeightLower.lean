import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.CanonicalCollisionSingletonSum
import OAI.Combinatorics.TriangleRemoval.Stability.ActiveCavityFactorProduct
import OAI.Combinatorics.TriangleRemoval.Stability.ContinuousCavityWeightClip
import OAI.Combinatorics.TriangleRemoval.Probability.PmfMeanLiminfTendsto

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma grid_cavityWeight_lower {D : ℝ} (hD : 0 ≤ D) (N : ℕ) [NeZero N] :
    ∀ t ≤ N, 1 ≤ (1+2*D)*cavityWeight D ((t : ℝ)/N) := by
  intro t ht
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hmem : (t : ℝ)/N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity,(div_le_one hNr).mpr (by exact_mod_cast ht)⟩
  have hh := mul_le_mul_of_nonneg_left (cavityWeight_lower hD hmem)
    (show 0 ≤ 1+2*D by positivity)
  have heq : (1+2*D)*cavityWeight D 1 = 1 := by
    unfold cavityWeight
    rw [mul_one,mul_one_div_cancel (by positivity : 1+2*D ≠ 0)]
  rwa [heq] at hh

lemma grid_collision_majorant_tendsto (K : ℝ) {D : ℝ} (hD : 0 < D) :
    Tendsto (fun j : ℕ => (K*(1+2*D)^3/D^50)*
      Real.exp (45*D*prefixWeight (fun t => (2/((j+1 : ℕ) : ℝ))*
        cavityWeight D ((t : ℝ)/(j+1 : ℕ))) (j+1)))
      atTop (𝓝 (K*(1+2*D)^48/D^50)) := by
  have hh := (Real.continuous_exp.continuousAt.tendsto.comp
    ((grid_prefixWeight_tendsto hD).const_mul (45*D))).const_mul
    (K*(1+2*D)^3/D^50)
  have he : (K*(1+2*D)^3/D^50)*Real.exp (45*D*(2*witnessMu D)) =
      K*(1+2*D)^48/D^50 := by
    calc
      _ = K*((1+2*D)^3*Real.exp (45*D*(2*witnessMu D)))/D^50 := by ring
      _ = _ := by rw [collision_exponential_identity hD]
  rwa [he] at hh

theorem averaged_disjoint_collisionCost (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ hne : G.Nonempty,
    pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f => if Disjoint e f then
        collisionCost (triangleHypergraph G) {e,f} none else 0)) ≤
      65536*(1+2*prefixD n)^48/prefixD n^50 := by
  classical
  filter_upwards [averaged_disjoint_grid_collision c₀ C₀ hc₀,
    goodPrefix_full_grid_rows hc₀,goodPrefix_full_continuous_rows hc₀] with n hfinite hrows hn
  intro G hGood hne
  let D := prefixD n
  let P := PMF.uniformOfFinset G hne
  let PP := P.bind (fun e => P.map (Prod.mk e))
  let f : (Finset (Fin n) × Finset (Fin n)) → ℕ → ℝ := fun ef j =>
    if Disjoint ef.1 ef.2 then gridCollision (triangleHypergraph G) {ef.1,ef.2} none j else 0
  let g : ℕ → ℝ := fun j => (65536*(1+2*D)^3/D^50)*
    Real.exp (45*D*prefixWeight (fun t => (2/((j+1 : ℕ) : ℝ))*
      cavityWeight D ((t : ℝ)/(j+1 : ℕ))) (j+1))
  have hbound (ef : Finset (Fin n) × Finset (Fin n)) (j : ℕ) : 0 ≤ f ef j := by
    dsimp only [f]
    split_ifs <;> first | exact (gridCollision_mem_unit _ _ _ _).1 | rfl
  obtain ⟨N₀,hN₀⟩ := hrows C₀ G hGood
  have hupper : ∀ᶠ j : ℕ in atTop, pmfMean PP (fun ef => f ef j) ≤ g j := by
    filter_upwards [eventually_ge_atTop N₀] with j hj
    dsimp only [PP]
    rw [pmfMean_bind]
    simp_rw [pmfMean_map]
    have hh := hfinite G hGood hne (j+1)
      (fun t => cavityWeight D ((t : ℝ)/(j+1 : ℕ)))
      (fun t => (cavityWeight_pos hn.1.le (by positivity)).le)
      (hN₀ (j+1) (by omega)) (1+2*D)
      (by dsimp only [D]; linarith [hn.1]) (grid_cavityWeight_lower hn.1.le (j+1))
      (j+1) (j+1) le_rfl le_rfl
    simpa only [gridCollision_eq_trace,P,f,g,D] using hh
  have hh := pmfMean_liminf_le_of_tendsto_upper PP f hbound g
    (grid_collision_majorant_tendsto 65536 hn.1) hupper
  dsimp only [PP] at hh
  rw [pmfMean_bind] at hh
  simp_rw [pmfMean_map] at hh
  have hf (e f' : Finset (Fin n)) : Filter.liminf (f (e,f')) atTop =
      if Disjoint e f' then collisionCost (triangleHypergraph G) {e,f'} none else 0 := by
    by_cases hd : Disjoint e f'
    · simp only [f,hd,ite_true,collisionCost]
    · simp only [f,hd,ite_false,Filter.liminf_const]
  simp_rw [hf] at hh
  exact hh

theorem averaged_singleton_collisionCost (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ hne : G.Nonempty,
    pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        collisionCost (triangleHypergraph G) {e} none) ≤
      8192*(1+2*prefixD n)^48/prefixD n^50 := by
  classical
  filter_upwards [averaged_singleton_grid_collision c₀ C₀ hc₀,
    goodPrefix_full_grid_rows hc₀,goodPrefix_full_continuous_rows hc₀] with n hfinite hrows hn
  intro G hGood hne
  let D := prefixD n
  let P := PMF.uniformOfFinset G hne
  let f : Finset (Fin n) → ℕ → ℝ := fun e j => gridCollision (triangleHypergraph G) {e} none j
  let g : ℕ → ℝ := fun j => (8192*(1+2*D)^3/D^50)*
    Real.exp (45*D*prefixWeight (fun t => (2/((j+1 : ℕ) : ℝ))*
      cavityWeight D ((t : ℝ)/(j+1 : ℕ))) (j+1))
  have hbound (e : Finset (Fin n)) (j : ℕ) : 0 ≤ f e j :=
    (gridCollision_mem_unit _ _ _ _).1
  obtain ⟨N₀,hN₀⟩ := hrows C₀ G hGood
  have hupper : ∀ᶠ j : ℕ in atTop, pmfMean P (fun e => f e j) ≤ g j := by
    filter_upwards [eventually_ge_atTop N₀] with j hj
    have hh := hfinite G hGood hne (j+1)
      (fun t => cavityWeight D ((t : ℝ)/(j+1 : ℕ)))
      (fun t => (cavityWeight_pos hn.1.le (by positivity)).le)
      (hN₀ (j+1) (by omega)) (1+2*D)
      (by dsimp only [D]; linarith [hn.1]) (grid_cavityWeight_lower hn.1.le (j+1))
      (j+1) (j+1) le_rfl le_rfl
    simpa only [gridCollision_eq_trace,P,f,g,D] using hh
  exact pmfMean_liminf_le_of_tendsto_upper P f hbound g
    (grid_collision_majorant_tendsto 8192 hn.1) hupper

end SharpTerminalLeave

end

end OAI
