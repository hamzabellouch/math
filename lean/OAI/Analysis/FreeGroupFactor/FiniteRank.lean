import OAI.Analysis.FreeGroupFactor.RankTwoCoefficients

namespace OAI

namespace FreeGroupFactorMain

noncomputable section

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

attribute [local instance] Classical.propDecidable

open UnitaryEvaluation
theorem one_step_of_coefficient_estimate (n : ℕ)
    (hc : ∀ η : ℝ, 0 < η → ∃ (w : FreeGroup (Fin n)) (h : Coeff (FreeGroup (Fin n))),
      coefficientNorm h < η ∧
        coefficientNorm (freeCocycle (firstCoefficients h) w-Finsupp.single 1 1) < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : groupVonNeumann (FreeGroup (Option (Fin n))) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option (Fin n))),
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin n))))
        (groupUltraweakTopology (FreeGroup (Option (Fin n)))) α ∧
      ∃ w : FreeGroup (Fin n),
        (∀ j : Fin n, ‖α (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map Option.some w)) - groupUnitary (FreeGroup.of none)) < ε := by
  obtain ⟨l,hl0,hlS,hln,z,hze⟩ := haar_centered_laurent (G := FreeGroup (Option (Fin n)))
    (generatorUnitary (none : Option (Fin n))) (generator_haar (none : Option (Fin n))) (half_pos hε)
  rw [← laurentValue_eq_value] at hlS hln hze
  obtain ⟨w,h,hh,hw⟩ := hc ((ε/2)/(3*(2*(Real.pi+1)))) (by positivity)
  exact one_step_from_laurent n hε l hl0 hlS hln z hze w h hh hw

theorem one_step_two {ε : ℝ} (hε : 0 < ε) :
    ∃ α : groupVonNeumann (FreeGroup (Option (Fin 2))) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option (Fin 2))),
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin 2))))
        (groupUltraweakTopology (FreeGroup (Option (Fin 2)))) α ∧
      ∃ w : FreeGroup (Fin 2),
        (∀ j : Fin 2, ‖α (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map Option.some w)) - groupUnitary (FreeGroup.of none)) < ε :=
  one_step_of_coefficient_estimate 2 smallCocycleTwo hε

theorem one_step_ge_two (n : ℕ) (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : groupVonNeumann (FreeGroup (Option (Fin n))) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option (Fin n))),
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin n))))
        (groupUltraweakTopology (FreeGroup (Option (Fin n)))) α ∧
      ∃ w : FreeGroup (Fin n),
        (∀ j : Fin n, ‖α (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map Option.some w)) - groupUnitary (FreeGroup.of none)) < ε := by
  by_cases h : n = 2
  · subst n
    exact one_step_two hε
  · exact one_step n (by omega) hε

namespace Generation

theorem orbit_step_ge_two (n : ℕ) (hn : 2 ≤ n)
    (Φ : Ambient n ≃⋆ₐ[ℂ] Ambient n)
    (ht : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) {θ : ℝ} (hθ : 0 < θ) :
    ∃ V ∈ orbit n, dist V (mapTuple Φ (initial n)) < θ ∧
      ∃ w : FreeGroup (Fin n), ∀ j : Option (Fin n),
        twoNorm ((wordTuple V (fun j => j.elim w FreeGroup.of) j : Ambient n) -
          (mapTuple Φ generatorUnitary j : Ambient n)) < θ := by
  obtain ⟨α,hαt,_hαn,w,hgen,hword⟩ := one_step_ge_two n hn hθ
  let V : Tuple n := mapTuple (α.trans Φ) (initial n)
  have hdist : dist V (mapTuple Φ (initial n)) < θ := by
    apply (dist_pi_lt_iff hθ).mpr
    intro j
    change dist (Φ (α (groupUnitary (FreeGroup.of (some j))))) (Φ (groupUnitary (FreeGroup.of (some j)))) < θ
    have hnorm (T : Ambient n) : ‖Φ T‖ = ‖T‖ :=
      NonUnitalStarAlgHom.norm_map Φ.toStarAlgHom Φ.injective T
    rw [dist_eq_norm, ← map_sub, hnorm]
    exact hgen j
  refine ⟨V,⟨α.trans Φ,?_,rfl⟩,hdist,w,?_⟩
  · intro T
    simp only [StarAlgEquiv.trans_apply,ht,hαt]
  · intro j
    cases j with
    | none =>
      change twoNorm (word V w-Φ (groupUnitary (FreeGroup.of none))) < θ
      rw [show V = mapTuple (α.trans Φ) (initial n) from rfl,word_mapTuple,
        word_initial,StarAlgEquiv.trans_apply,← map_sub,twoNorm_iso Φ ht]
      exact hword
    | some j =>
      change twoNorm ((V j : Ambient n)-Φ (groupUnitary (FreeGroup.of (some j)))) < θ
      have hj := (dist_pi_lt_iff hθ).mp hdist j
      change dist (V j : Ambient n) (Φ (groupUnitary (FreeGroup.of (some j)))) < θ at hj
      rw [dist_eq_norm] at hj
      exact (twoNorm_le_norm _).trans_lt hj

theorem orbit_local_approximation_ge_two (n : ℕ) (hn : 2 ≤ n)
    (U : Tuple n) (hU : U ∈ orbit n) (δ : ℝ) (hδ : 0 < δ)
    (g : FreeGroup (Option (Fin n))) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ orbit n, dist V U < δ ∧ ∃ p : FreeGroup (Fin n) →₀ ℂ,
      dist (groupL2 (poly V p)) (lp.single 2 g (1 : ℂ)) < ε := by
  classical
  obtain ⟨Φ,ht,rfl⟩ := hU
  obtain ⟨p,hp⟩ := automorphism_poly_dense Φ ht (groupUnitary g) (half_pos hε)
  obtain ⟨K,hK,hbound⟩ := poly_twoNorm_bound (G := FreeGroup (Option (Fin n))) p
  let θ := min δ (ε/(2*(K+1)))
  have hθ : 0 < θ := lt_min hδ (div_pos hε (by positivity))
  obtain ⟨V,hV,hd,w,hw⟩ := orbit_step_ge_two n hn Φ ht hθ
  refine ⟨V,hV,hd.trans_le (min_le_left _ _),substitute (fun j => j.elim w FreeGroup.of) p,?_⟩
  have hb := hbound (wordTuple V (fun j => j.elim w FreeGroup.of)) (mapTuple Φ generatorUnitary)
    θ hθ.le (fun j => (hw j).le)
  have hθe : θ*(2*(K+1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 2*(K+1))).mp (min_le_right _ _)
  have hKe : K*θ < ε/2 := by nlinarith
  rw [dist_eq_norm,← groupL2_groupUnitary g,← map_sub]
  change twoNorm (poly V (substitute (fun j => j.elim w FreeGroup.of) p)-groupUnitary g) < ε
  rw [poly_substitute]
  have he : poly (wordTuple V (fun j => j.elim w FreeGroup.of)) p-groupUnitary g =
      (poly (wordTuple V (fun j => j.elim w FreeGroup.of)) p-poly (mapTuple Φ generatorUnitary) p)+
      (poly (mapTuple Φ generatorUnitary) p-groupUnitary g) := by abel
  rw [he]
  exact (twoNorm_add_le _ _).trans_lt (by linarith)

end Generation

open Generation

theorem generating_haar_tuple_ge_two (n : ℕ) (hn : 2 ≤ n) :
    ∃ U : Tuple n,
      (∀ g : FreeGroup (Fin n), canonicalTrace (word U g) = if g = 1 then 1 else 0) ∧
      ⊤ ≤ (Submodule.span ℂ (Set.range (fun g => groupL2 (word U g)))).topologicalClosure := by
  classical
  obtain ⟨U,hU,happrox⟩ := baire_local_approximation (orbit n) (orbit_nonempty n)
    (fun p U => groupL2 (poly U p)) (poly_groupL2_continuous n)
    (fun g : FreeGroup (Option (Fin n)) => lp.single 2 g (1 : ℂ))
    (orbit_local_approximation_ge_two n hn)
  exact ⟨U,closure_orbit_trace n U hU,total_of_poly_approx U happrox⟩

theorem rank_step_option_ge_two (n : ℕ) (hn : 2 ≤ n) :
    HasNormalTracialIso (FreeGroupRank n) (FreeGroup (Option (Fin n))) := by
  classical
  obtain ⟨U,htrace,htotal⟩ := generating_haar_tuple_ge_two n hn
  apply normalTracialIso_of_haar_total (word U)
  · intro g
    exact (word_inv U g).symm
  · exact htrace
  · exact htotal

theorem rank_step_ge_two (n : ℕ) (hn : 2 ≤ n) :
    HasNormalTracialIso (FreeGroupRank n) (FreeGroupRank (n+1)) :=
  (rank_step_option_ge_two n hn).trans (normalTracialIso_of_groupEquiv (optionRankEquiv n))

theorem rankTwo : HasNormalTracialIso (FreeGroupRank 2) (FreeGroupRank 3) :=
  rank_step_ge_two 2 le_rfl

theorem rankStep (n : ℕ) (hn : 3 ≤ n) :
    HasNormalTracialIso (FreeGroupRank n) (FreeGroupRank (n + 1)) := rank_step n hn

end

end FreeGroupFactorMain

end OAI
