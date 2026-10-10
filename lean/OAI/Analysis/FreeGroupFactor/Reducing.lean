import OAI.Analysis.FreeGroupFactor.NormalExtension

namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

section
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def reducingAlgebra (K : Submodule ℂ H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {T | (∀ x ∈ K, T x ∈ K) ∧ ∀ x ∈ K, (star T) x ∈ K}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    rintro T U ⟨hT,hT'⟩ ⟨hU,hU'⟩
    constructor
    · intro x hx; exact K.add_mem (hT x hx) (hU x hx)
    · intro x hx; simpa using K.add_mem (hT' x hx) (hU' x hx)
  mul_mem' := by
    rintro T U ⟨hT,hT'⟩ ⟨hU,hU'⟩
    constructor
    · intro x hx; exact hT _ (hU x hx)
    · intro x hx; simpa using hU' _ (hT' x hx)
  algebraMap_mem' := by
    intro c
    constructor
    · intro x hx; simpa using K.smul_mem c hx
    · intro x hx; simpa only [← algebraMap_star_comm, ContinuousLinearMap.algebraMap_apply] using K.smul_mem (star c) hx
  star_mem' := by
    rintro T ⟨hT,hT'⟩
    exact ⟨hT', by simpa using hT⟩

theorem reducingAlgebra_isClosed (K : Submodule ℂ H) (hK : IsClosed (K : Set H)) :
    IsClosed (reducingAlgebra K : Set (H →L[ℂ] H)) := by
  change IsClosed {T : H →L[ℂ] H | _ ∧ _}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _hx
    exact hK.preimage (ContinuousLinearMap.apply ℂ H x).continuous
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _hx
    exact hK.preimage ((ContinuousLinearMap.apply ℂ H x).continuous.comp continuous_star)

omit [CompleteSpace H] in

theorem closedSpan_invariant {G : Type uG} [Group G]
    (ρ : G →* (H →L[ℂ] H)) (ξ : H) (g : G) :
    ∀ x ∈ (Submodule.span ℂ (Set.range (fun a => ρ a ξ))).topologicalClosure,
      ρ g x ∈ (Submodule.span ℂ (Set.range (fun a => ρ a ξ))).topologicalClosure := by
  let K := (Submodule.span ℂ (Set.range (fun a => ρ a ξ))).topologicalClosure
  change K ≤ K.comap (ρ g).toLinearMap
  apply Submodule.topologicalClosure_minimal
  · rw [Submodule.span_le]
    rintro _ ⟨a,rfl⟩
    change ρ g (ρ a ξ) ∈ K
    have he : ρ g (ρ a ξ) = ρ (g*a) ξ := by rw [map_mul]; rfl
    rw [he]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g*a, rfl⟩)
  · exact (Submodule.isClosed_topologicalClosure _).preimage (ρ g).continuous

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}
 theorem wordHom_mem (E : StarSubalgebra ℂ A) (U : ι → unitary A)
    (hU : ∀ i, (U i : A) ∈ E) (g : FreeGroup ι) : wordHom U g ∈ E := by
  induction g using FreeGroup.induction_on with
  | one => rw [map_one]; exact one_mem E
  | of i => simpa only [wordHom_of] using hU i
  | inv_of i hi => rw [wordHom_inv]; exact star_mem hi
  | mul x y hx hy => rw [map_mul]; exact mul_mem hx hy

 theorem laurentValue_mem (E : StarSubalgebra ℂ A) (C : unitary A)
    (hC : (C : A) ∈ E) (l : ℤ →₀ ℂ) : laurentValue C l ∈ E := by
  have hp (k : ℤ) : ((C ^ k : unitary A) : A) ∈ E := by
    cases k with
    | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast]
      exact pow_mem hC n
    | negSucc n =>
      rw [zpow_negSucc]
      change star ((C : A) ^ (n+1)) ∈ E
      exact star_mem (pow_mem hC (n+1))
  classical
  change (∑ k ∈ l.support, l k • ((C ^ k : unitary A) : A)) ∈ E
  exact sum_mem fun k _ => E.smul_mem (hp k) _
end UnitaryEvaluation

open UnitaryEvaluation
open scoped ENNReal

 theorem flow_word_orbit_total {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l))
    (X : ℝ → ι → groupVonNeumann (FreeGroup (Option ι)))
    (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option ι))))
    (hX₀ : X 0 = fun j => groupUnitary (FreeGroup.of (some j)))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option ι)) l) h (X t)) t) (t₀ : ℝ) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (fun g : FreeGroup (Option ι) =>
      ((wordHom (extendUnitary (fun j => ⟨X t₀ j, hU t₀ j⟩)
        (generatorUnitary none)) g : groupVonNeumann (FreeGroup (Option ι))) :
          GroupOperator (FreeGroup (Option ι))) deltaOne))).topologicalClosure := by
  classical
  let U := extendUnitary (fun j => ⟨X t₀ j, hU t₀ j⟩) (generatorUnitary none)
  let ρ : FreeGroup (Option ι) →* GroupOperator (FreeGroup (Option ι)) :=
    (groupVonNeumann _).subtype.toMonoidHom.comp (wordHom U)
  let K := (Submodule.span ℂ (Set.range (fun g => ρ g deltaOne))).topologicalClosure
  let E := (reducingAlgebra K).comap (groupVonNeumann _).subtype
  have hK : IsClosed (K : Set (GroupHilbert (FreeGroup (Option ι)))) :=
    Submodule.isClosed_topologicalClosure _
  have hE : IsClosed (E : Set (groupVonNeumann (FreeGroup (Option ι)))) :=
    (reducingAlgebra_isClosed K hK).preimage continuous_subtype_val
  have hρ (g) : wordHom U g ∈ E := by
    constructor
    · exact closedSpan_invariant ρ deltaOne g
    · have he : star (ρ g) = ρ g⁻¹ := by
        change ((star (wordHom U g) : groupVonNeumann (FreeGroup (Option ι))) :
          GroupOperator (FreeGroup (Option ι))) = _
        rw [← wordHom_inv]
        rfl
      change ∀ x ∈ K, (star (ρ g)) x ∈ K
      rw [he]
      exact closedSpan_invariant ρ deltaOne g⁻¹
  have hC : (generatorUnitary (none : Option ι) : groupVonNeumann _) ∈ E := by
    simpa only [wordHom_of, U, extendUnitary, Option.elim_none] using hρ (FreeGroup.of none)
  have hXt : ∀ j, X t₀ j ∈ E := by
    intro j
    simpa only [wordHom_of, U, extendUnitary, Option.elim_some] using hρ (FreeGroup.of (some j))
  have hXS := PolynomialFlow.solution_mem_subalgebra E hE
    (laurentValue (generatorUnitary (none : Option ι)) l) hS
    (laurentValue_mem E _ hC l) h X hX hU t₀ hXt
  have hgen (i : Option ι) : (generatorUnitary i : groupVonNeumann _) ∈ E := by
    cases i with
    | none => exact hC
    | some j =>
      change groupUnitary (FreeGroup.of (some j)) ∈ E
      simpa only [hX₀] using hXS 0 j
  have hgroup (g : FreeGroup (Option ι)) : groupUnitary g ∈ E := by
    rw [← wordHom_generatorUnitary]
    exact wordHom_mem E generatorUnitary hgen g
  have hδ : deltaOne ∈ K := by
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨1, by simp⟩
  have hsingle (g : FreeGroup (Option ι)) : lp.single 2 g (1 : ℂ) ∈ K := by
    have hh := (hgroup g).1 deltaOne hδ
    have he : (leftRegular g) deltaOne = lp.single 2 g 1 := by
      ext x
      simp [deltaOne, lp.single_apply, Pi.single_apply, inv_mul_eq_one, eq_comm]
    change (leftRegular g) deltaOne ∈ K at hh
    rwa [he] at hh
  change ⊤ ≤ K
  intro ξ _hξ
  have hs := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ
  apply hK.mem_of_tendsto hs
  filter_upwards [] with s
  apply K.sum_mem
  intro g _hg
  have he : lp.single 2 g (ξ g) = (ξ g) • (lp.single 2 g (1 : ℂ) : GroupHilbert (FreeGroup (Option ι))) := by
    ext x
    simp [lp.single_apply, Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hsingle g)

open UnitaryEvaluation

theorem laurent_flow_automorphisms {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l)) :
    ∃ (X : ℝ → ι → groupVonNeumann (FreeGroup (Option ι)))
      (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option ι)))),
      X 0 = (fun j => groupUnitary (FreeGroup.of (some j))) ∧
      (∀ t, HasDerivAt X (PolynomialFlow.field
        (laurentValue (generatorUnitary (none : Option ι)) l) h (X t)) t) ∧
      ∀ t, ∃ Φ : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ]
          groupVonNeumann (FreeGroup (Option ι)),
        (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
        @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
          (groupUltraweakTopology (FreeGroup (Option ι))) Φ ∧
        ∀ g, Φ (groupUnitary g) = wordHom
          (extendUnitary (fun j => ⟨X t j, hU t j⟩) (generatorUnitary none)) g := by
  classical
  obtain ⟨X,hU,hX₀,hX,hm⟩ := actual_laurent_flow_moments h l hS
  refine ⟨X,hU,hX₀,hX,?_⟩
  intro t
  apply iso_extension_of_haar_total
    (wordHom (extendUnitary (fun j => ⟨X t j, hU t j⟩) (generatorUnitary none)))
  · intro g
    exact (wordHom_inv _ g).symm
  · exact hm t
  · exact flow_word_orbit_total h l hS X hU hX₀ hX t

end

end FreeGroupFactorMain

end OAI
