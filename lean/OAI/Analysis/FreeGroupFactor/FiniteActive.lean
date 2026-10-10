import OAI.Analysis.FreeGroupFactor.FiniteMoments

namespace OAI

noncomputable section

universe uA uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain.FiniteActive

section
open UnitaryEvaluation
open scoped ENNReal
 theorem original_generators_mem {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t)
    (E : StarSubalgebra ℂ (Ambient ι κ)) (hE : IsClosed (E : Set (Ambient ι κ)))
    (hC : (generatorUnitary (none : Option (ι ⊕ κ)) : Ambient ι κ) ∈ E)
    (t₀ : ℝ) (hXt : ∀ i, X t₀ i ∈ E)
    (hpass : ∀ k : κ, (generatorUnitary (some (Sum.inr k) : Option (ι ⊕ κ)) : Ambient ι κ) ∈ E) :
    ∀ i : Option (ι ⊕ κ), (generatorUnitary i : Ambient ι κ) ∈ E := by
  have hXS := PolynomialFlow.solution_mem_subalgebra E hE
    (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) hS
    (laurentValue_mem E _ hC l) h X hX hU t₀ hXt
  intro i
  cases i with
  | none => exact hC
  | some j =>
    cases j with
    | inl i =>
      change groupUnitary (FreeGroup.of (some (Sum.inl i))) ∈ E
      simpa only [hX₀] using hXS 0 i
    | inr k => exact hpass k

 theorem orbit_total {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → groupVonNeumann (FreeGroup (Option (ι ⊕ κ))))
    (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option (ι ⊕ κ)))))
    (hX₀ : X 0 = fun j => groupUnitary (FreeGroup.of (some (Sum.inl j))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) (t₀ : ℝ) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (fun g : FreeGroup (Option (ι ⊕ κ)) =>
      ((wordHom (extendUnitary (fun j => ⟨tuple (X t₀) j,tuple_unitary (X t₀) (hU t₀) j⟩)
        (generatorUnitary none)) g : groupVonNeumann (FreeGroup (Option (ι ⊕ κ)))) :
          GroupOperator (FreeGroup (Option (ι ⊕ κ)))) deltaOne))).topologicalClosure := by
  classical
  let U := extendUnitary (fun j => ⟨tuple (X t₀) j,tuple_unitary (X t₀) (hU t₀) j⟩) (generatorUnitary none)
  let ρ : FreeGroup (Option (ι ⊕ κ)) →* GroupOperator (FreeGroup (Option (ι ⊕ κ))) :=
    (groupVonNeumann _).subtype.toMonoidHom.comp (wordHom U)
  let K := (Submodule.span ℂ (Set.range (fun g => ρ g deltaOne))).topologicalClosure
  let E := (reducingAlgebra K).comap (groupVonNeumann _).subtype
  have hK : IsClosed (K : Set (GroupHilbert (FreeGroup (Option (ι ⊕ κ))))) :=
    Submodule.isClosed_topologicalClosure _
  have hE : IsClosed (E : Set (groupVonNeumann (FreeGroup (Option (ι ⊕ κ))))) :=
    (reducingAlgebra_isClosed K hK).preimage continuous_subtype_val
  have hρ (g) : wordHom U g ∈ E := by
    constructor
    · exact closedSpan_invariant ρ deltaOne g
    · have he : star (ρ g) = ρ g⁻¹ := by
        change ((star (wordHom U g) : groupVonNeumann (FreeGroup (Option (ι ⊕ κ)))) :
          GroupOperator (FreeGroup (Option (ι ⊕ κ)))) = _
        rw [← wordHom_inv]
        rfl
      change ∀ x ∈ K, (star (ρ g)) x ∈ K
      rw [he]
      exact closedSpan_invariant ρ deltaOne g⁻¹
  have hC : (generatorUnitary (none : Option (ι ⊕ κ)) : groupVonNeumann _) ∈ E := by
    simpa only [wordHom_of, U, extendUnitary, Option.elim_none] using hρ (FreeGroup.of none)
  have hXt : ∀ j, X t₀ j ∈ E := by
    intro j
    simpa only [wordHom_of, U, extendUnitary, Option.elim_some,tuple,Sum.elim_inl] using hρ (FreeGroup.of (some (Sum.inl j)))
  have hpass (k : κ) : (generatorUnitary (some (Sum.inr k) : Option (ι ⊕ κ)) : Ambient ι κ) ∈ E := by
    change groupUnitary (FreeGroup.of (some (Sum.inr k))) ∈ E
    simpa only [wordHom_of,U,extendUnitary,Option.elim_some,tuple,Sum.elim_inr]
      using hρ (FreeGroup.of (some (Sum.inr k)))
  have hgen := original_generators_mem h l hS X hU hX₀ hX E hE hC t₀ hXt hpass
  change ⊤ ≤ K
  apply canonical_total_of_reducing K hK _ hgen
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

end
open UnitaryEvaluation

theorem extension_at_time {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) (t : ℝ) :
    ∃ Φ : Ambient ι κ ≃⋆ₐ[ℂ] Ambient ι κ,
        (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
        @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ))))
          (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ)))) Φ ∧
        ∀ g, Φ (groupUnitary g) = wordHom
          (extendUnitary (fun j => ⟨tuple (X t) j,tuple_unitary (X t) (hU t) j⟩)
            (generatorUnitary none)) g := by
  exact iso_extension_of_haar_total
    (wordHom (extendUnitary (fun j => ⟨tuple (X t) j,tuple_unitary (X t) (hU t) j⟩)
      (generatorUnitary none)))
    (fun g => (wordHom_inv _ g).symm)
    (moments h l hS X hU hX₀ hX t)
    (orbit_total h l hS X hU hX₀ hX t)

theorem basis_solution {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l)) :
    ∃ (X : ℝ → ι → Ambient ι κ),
      X 0 = (fun i => groupUnitary (FreeGroup.of (some (Sum.inl i)))) ∧
      (∀ t, HasDerivAt X (PolynomialFlow.field
        (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) ∧
      ∀ t i, X t i ∈ unitary (Ambient ι κ) := by
  exact PolynomialFlow.global_unitary_solution (A := Ambient ι κ)
    (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) hS h
    (fun i => groupUnitary (FreeGroup.of (some (Sum.inl i)))) (fun _ => groupUnitary_mem_unitary _)

theorem automorphisms {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l)) :
    ∃ (X : ℝ → ι → Ambient ι κ)
      (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ)),
      X 0 = (fun i => groupUnitary (FreeGroup.of (some (Sum.inl i)))) ∧
      (∀ t, HasDerivAt X (PolynomialFlow.field
        (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) ∧
      ∀ t, ∃ Φ : Ambient ι κ ≃⋆ₐ[ℂ] Ambient ι κ,
        (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
        @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ))))
          (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ)))) Φ ∧
        ∀ g, Φ (groupUnitary g) = wordHom
          (extendUnitary (fun j => ⟨tuple (X t) j,tuple_unitary (X t) (hU t) j⟩)
            (generatorUnitary none)) g := by
  obtain ⟨X,hX₀,hX,hU⟩ := basis_solution (ι := ι) (κ := κ) h l hS
  refine ⟨X,hU,hX₀,hX,?_⟩
  intro t
  exact extension_at_time h l hS X hU hX₀ hX t

end FreeGroupFactorMain.FiniteActive

namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} {κ : Type uκ}

theorem hamiltonianLinear_mapDomain (S : A) (U : κ → unitary A)
    (f : ι → κ) (k : FreeGroup ι →₀ ℝ) :
    hamiltonianLinear S U (Finsupp.mapDomain (FreeGroup.map f) k) =
      hamiltonianLinear S (U ∘ f) k := by
  classical
  simp only [hamiltonianLinear,Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapDomain_index (fun g => by simp)
    (fun g a b => by simp [add_smul])]
  apply Finsupp.sum_congr
  intro g hg
  rw [wordHom_map]

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain.FiniteActive

section
open UnitaryEvaluation
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] in
theorem flow_bound (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (K : ℝ) (hK : 0 ≤ K)
    (hn : ‖laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l‖ ≤ K)
    (U : ι → unitary (Ambient ι κ))
    (Φ : Ambient ι κ ≃⋆ₐ[ℂ] Ambient ι κ)
    (hΦ : ∀ g, Φ (groupUnitary g) = wordHom
      (extendUnitary (fun j => ⟨tuple (fun i => (U i : Ambient ι κ)) j,
        tuple_unitary _ (fun i => (U i).property) j⟩) (generatorUnitary none)) g)
    (k : FreeGroup ι →₀ ℝ) :
    ‖hamiltonianLinear (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) U k‖ ≤
      3*K*Real.sqrt (k.sum (fun _ r => r^2)) := by
  let V : (ι ⊕ κ) → unitary (Ambient ι κ) := fun j =>
    ⟨tuple (fun i => (U i : Ambient ι κ)) j,tuple_unitary _ (fun i => (U i).property) j⟩
  have hb := flow_iso_hamiltonian_bound l h0 hS K hK hn V Φ hΦ
    (Finsupp.mapDomain (FreeGroup.map Sum.inl) k)
  rw [hamiltonianLinear_mapDomain,
    Finsupp.sum_mapDomain_index_inj (FreeGroup.map_injective Sum.inl_injective)] at hb
  exact hb

theorem bounded_solution (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (K : ℝ) (hK : 0 ≤ K)
    (hn : ‖laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l‖ ≤ K)
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) :
    ∀ t k, ‖hamiltonianLinear
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l)
        (fun i => ⟨X t i,hU t i⟩) k‖ ≤ 3*K*Real.sqrt (k.sum (fun _ r => r^2)) := by
  intro t k
  obtain ⟨Φ,_ht,_hc,hΦ⟩ := extension_at_time (ι := ι) (κ := κ) h l hS X hU hX₀ hX t
  exact flow_bound (ι := ι) (κ := κ) l h0 hS K hK hn (fun i => ⟨X t i,hU t i⟩) Φ hΦ k

theorem bounded_flow (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (K : ℝ) (hK : 0 ≤ K)
    (hn : ‖laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l‖ ≤ K) :
    ∃ U : ℝ → ι → unitary (Ambient ι κ),
      U 0 = (fun i => generatorUnitary (some (Sum.inl i) : Option (ι ⊕ κ))) ∧
      (∀ t, HasDerivAt (fun t i => (U t i : Ambient ι κ))
        (PolynomialFlow.field (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l)
          h (fun i => (U t i : Ambient ι κ))) t) ∧
      (∀ t k, ‖hamiltonianLinear
        (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) (U t) k‖ ≤
          3*K*Real.sqrt (k.sum (fun _ r => r^2))) ∧
      ∃ β : Ambient ι κ ≃⋆ₐ[ℂ] Ambient ι κ,
        (∀ T, canonicalTrace (β T) = canonicalTrace T) ∧
        @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ))))
          (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ)))) β ∧
        ∀ g, β (groupUnitary g) = wordHom
          (extendUnitary (fun j => ⟨tuple (fun i => (U 1 i : Ambient ι κ)) j,
            tuple_unitary _ (fun i => (U 1 i).property) j⟩) (generatorUnitary none)) g := by
  obtain ⟨X,hX₀,hX,hU⟩ := basis_solution (ι := ι) (κ := κ) h l hS
  let U (t : ℝ) : ι → unitary (Ambient ι κ) := fun i => ⟨X t i,hU t i⟩
  refine ⟨U,?_,hX,?_,?_⟩
  · funext i
    exact Subtype.ext (congrFun hX₀ i)
  · exact bounded_solution (ι := ι) (κ := κ) h l h0 hS K hK hn X hU hX₀ hX
  · exact extension_at_time (ι := ι) (κ := κ) h l hS X hU hX₀ hX 1

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem wordHom_active (w : FreeGroup ι) :
    wordHom (fun i => generatorUnitary (some (Sum.inl i) : Option (ι ⊕ κ))) w =
      groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w) := by
  rw [← wordHom_generatorUnitary,wordHom_map]
  rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem wordHom_tuple_active (U : ι → unitary (Ambient ι κ)) (w : FreeGroup ι) :
    wordHom (extendUnitary (fun j => ⟨tuple (fun i => (U i : Ambient ι κ)) j,
      tuple_unitary _ (fun i => (U i).property) j⟩) (generatorUnitary none))
          (FreeGroup.map (fun i => some (Sum.inl i)) w) = wordHom U w := by
  rw [wordHom_map]
  rfl

omit [DecidableEq κ] in
theorem displacements_from_bounds
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l)) (K : ℝ)
    (U : ℝ → ι → unitary (Ambient ι κ))
    (hU₀ : U 0 = fun j => generatorUnitary (some (Sum.inl j) : Option (ι ⊕ κ)))
    (hX : ∀ t, HasDerivAt (fun t j => (U t j : Ambient ι κ))
      (PolynomialFlow.field (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h
        (fun j => (U t j : Ambient ι κ))) t)
    (hbound : ∀ t k, ‖hamiltonianLinear (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) (U t) k‖ ≤
      3*K*Real.sqrt (k.sum (fun _ r => r^2))) :
    (∀ j, ‖(U 1 j : Ambient ι κ) - groupUnitary (FreeGroup.of (some (Sum.inl j)))‖ ≤
      3*K*Real.sqrt ((h j).sum (fun _ r => r^2))) ∧
    ∀ w : FreeGroup ι, ‖wordHom (U 1) w - NormedSpace.exp (Complex.I • laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) *
      groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)‖ ≤
      3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)) := by
  constructor
  · intro j
    have hd := generator_displacement (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h U hX
      (fun j => 3*K*Real.sqrt ((h j).sum (fun _ r => r^2)))
      (fun t j => hbound t (h j)) j
    rw [hU₀] at hd
    exact hd
  · intro w
    have hd := word_displacement (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) hS h U hX w
      (3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)))
      (fun t => hbound t (freeCocycle h w - Finsupp.single 1 1))
    rwa [hU₀, wordHom_active] at hd

theorem displacement (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (K : ℝ) (hK : 0 ≤ K)
    (hn : ‖laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l‖ ≤ K) :
    ∃ β : Ambient ι κ ≃⋆ₐ[ℂ] Ambient ι κ,
      (∀ T, canonicalTrace (β T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ))))
        (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ)))) β ∧
      β (groupUnitary (FreeGroup.of none)) = groupUnitary (FreeGroup.of none) ∧
      (∀ k : κ, β (groupUnitary (FreeGroup.of (some (Sum.inr k)))) =
        groupUnitary (FreeGroup.of (some (Sum.inr k)))) ∧
      (∀ i : ι, ‖β (groupUnitary (FreeGroup.of (some (Sum.inl i) : Option (ι ⊕ κ)))) -
        groupUnitary (FreeGroup.of (some (Sum.inl i) : Option (ι ⊕ κ)))‖ ≤
          3*K*Real.sqrt ((h i).sum (fun _ r => r^2))) ∧
      ∀ w : FreeGroup ι, ‖β (groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)) -
        NormedSpace.exp (Complex.I • laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) *
          groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)‖ ≤
            3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)) := by
  obtain ⟨U,hU₀,hX,hbound,β,hβt,hβc,hβ⟩ := bounded_flow (ι := ι) (κ := κ) h l h0 hS K hK hn
  obtain ⟨hgen,hword⟩ := displacements_from_bounds (ι := ι) (κ := κ) h l hS K U hU₀ hX hbound
  refine ⟨β,hβt,hβc,?_,?_,?_,?_⟩
  · exact (hβ (FreeGroup.of (none : Option (ι ⊕ κ)))).trans (wordHom_of _ _)
  · intro k
    exact (hβ (FreeGroup.of (some (Sum.inr k) : Option (ι ⊕ κ)))).trans (wordHom_of _ _)
  · intro i
    rw [hβ]
    simpa only [wordHom_of,extendUnitary,Option.elim_some,tuple,Sum.elim_inl] using hgen i
  · intro w
    rw [hβ]
    simpa only [wordHom_tuple_active] using hword w

end

open UnitaryEvaluation

 theorem one_step_from_laurent {κ : Type uκ} [DecidableEq κ]
    (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (l : ℤ →₀ ℂ) (hl0 : l 0 = 0)
    (hlS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (Fin n ⊕ κ))) l))
    (hln : ‖laurentValue (generatorUnitary (none : Option (Fin n ⊕ κ))) l‖ ≤ 2*(Real.pi+1))
    (z : unitary ℂ) (hze : twoNorm (NormedSpace.exp (Complex.I • laurentValue
      (generatorUnitary (none : Option (Fin n ⊕ κ))) l) -
        (z : ℂ) • groupUnitary (FreeGroup.of none)) < ε/2)
    (w : FreeGroup (Fin n)) (h : Coeff (FreeGroup (Fin n)))
    (hh : coefficientNorm h < (ε/2)/(3*(2*(Real.pi+1))))
    (hw : coefficientNorm (freeCocycle (firstCoefficients h) w-Finsupp.single 1 1) <
      (ε/2)/(3*(2*(Real.pi+1)))) :
    ∃ α : Ambient (Fin n) κ ≃⋆ₐ[ℂ] Ambient (Fin n) κ,
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      (∀ k : κ, α (groupUnitary (FreeGroup.of (some (Sum.inr k)))) =
        groupUnitary (FreeGroup.of (some (Sum.inr k)))) ∧
      ∃ w : FreeGroup (Fin n),
        (∀ i : Fin n, ‖α (groupUnitary (FreeGroup.of (some (Sum.inl i)))) -
          groupUnitary (FreeGroup.of (some (Sum.inl i)))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)) -
          groupUnitary (FreeGroup.of none)) < ε := by
  let K : ℝ := 2*(Real.pi+1)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨β,hβt,_hβn,_hβC,hβpass,hβgen,hβword⟩ :=
    displacement (κ := κ) (firstCoefficients h) l hl0 hlS K hK.le hln
  obtain ⟨γ,hγt,_hγn,_hγi,hγgen,hγC⟩ :=
    gauged_nielsen_iso (ι := Fin n ⊕ κ) (FreeGroup.map Sum.inl w) z
  have hmap : FreeGroup.map (Option.some : Fin n ⊕ κ → Option (Fin n ⊕ κ))
      (FreeGroup.map Sum.inl w) = FreeGroup.map (fun i => some (Sum.inl i)) w := by
    have he : (FreeGroup.map (Option.some : Fin n ⊕ κ → Option (Fin n ⊕ κ))).comp
        (FreeGroup.map Sum.inl) = FreeGroup.map (fun i => some (Sum.inl i)) := by
      apply FreeGroup.ext_hom
      intro i
      simp
    exact DFunLike.congr_fun he w
  rw [hmap] at hγC
  refine ⟨β.trans γ.symm,?_,?_,w,?_,?_⟩
  · intro T
    change canonicalTrace (γ.symm (β T)) = canonicalTrace T
    rw [trace_symm γ hγt,hβt]
  · intro k
    change γ.symm (β (groupUnitary (FreeGroup.of (some (Sum.inr k))))) = _
    rw [hβpass,← hγgen (Sum.inr k),γ.symm_apply_apply]
    exact (hγgen (Sum.inr k)).symm
  · intro i
    exact one_step_generator_estimate β γ _ (hγgen (Sum.inl i)) hK hε (hβgen i)
      ((firstCoefficients_norm_le h i).trans_lt hh)
  · exact one_step_word_estimate β γ hγt
      (generatorUnitary (none : Option (Fin n ⊕ κ)))
      (groupUnitaryUHom (FreeGroup (Option (Fin n ⊕ κ)))
        (FreeGroup.map (fun i => some (Sum.inl i)) w))
      _ z hγC hK (hβword w) hw hze

theorem one_step_of_coefficient_estimate {κ : Type uκ} [DecidableEq κ] (n : ℕ)
    (hc : ∀ η : ℝ, 0 < η → ∃ (w : FreeGroup (Fin n)) (h : Coeff (FreeGroup (Fin n))),
      coefficientNorm h < η ∧ coefficientNorm (freeCocycle (firstCoefficients h) w-Finsupp.single 1 1) < η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ α : Ambient (Fin n) κ ≃⋆ₐ[ℂ] Ambient (Fin n) κ,
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      (∀ k : κ, α (groupUnitary (FreeGroup.of (some (Sum.inr k)))) =
        groupUnitary (FreeGroup.of (some (Sum.inr k)))) ∧
      ∃ w : FreeGroup (Fin n),
        (∀ i : Fin n, ‖α (groupUnitary (FreeGroup.of (some (Sum.inl i)))) -
          groupUnitary (FreeGroup.of (some (Sum.inl i)))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)) -
          groupUnitary (FreeGroup.of none)) < ε := by
  obtain ⟨l,hl0,hlS,hln,z,hze⟩ := haar_centered_laurent
    (generatorUnitary (none : Option (Fin n ⊕ κ))) (generator_haar _) (half_pos hε)
  rw [← laurentValue_eq_value] at hlS hln hze
  obtain ⟨w,h,hh,hw⟩ := hc ((ε/2)/(3*(2*(Real.pi+1)))) (by positivity)
  exact one_step_from_laurent n hε l hl0 hlS hln z hze w h hh hw

theorem one_step {κ : Type uκ} [DecidableEq κ] (n : ℕ) (hn : 3 ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ α : Ambient (Fin n) κ ≃⋆ₐ[ℂ] Ambient (Fin n) κ,
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      (∀ k : κ, α (groupUnitary (FreeGroup.of (some (Sum.inr k)))) =
        groupUnitary (FreeGroup.of (some (Sum.inr k)))) ∧
      ∃ w : FreeGroup (Fin n),
        (∀ i : Fin n, ‖α (groupUnitary (FreeGroup.of (some (Sum.inl i)))) -
          groupUnitary (FreeGroup.of (some (Sum.inl i)))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)) -
          groupUnitary (FreeGroup.of none)) < ε := one_step_of_coefficient_estimate n (smallCocycle n hn) hε

end FreeGroupFactorMain.FiniteActive

end

end OAI
