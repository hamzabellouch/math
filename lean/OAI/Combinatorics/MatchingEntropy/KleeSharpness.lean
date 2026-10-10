import OAI.Combinatorics.MatchingEntropy.TriangleExpansion

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

section ColoredSupport
variable {V : Type uV} {E : Type uE} [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] in
theorem colorMatching_indicator (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (i : Fin 3) : G.indicator (colorMatching G c hc i) = coloredVector c i := by
  ext e
  simp [LooplessGraph.indicator,colorMatching,colorEdges,coloredVector]

omit [DecidableEq V] [DecidableEq E] in
theorem colorMatching_injective (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) : Function.Injective (colorMatching G c hc) := by
  intro i j hij
  have he : vertexColorEdge G c hc v i ∈ (colorMatching G c hc i).val := by
    simp [colorMatching,colorEdges,(vertexColorEdge_spec G c hc v i).2]
  rw [hij] at he
  have hh : c (vertexColorEdge G c hc v i) = j := by simpa [colorMatching,colorEdges] using he
  exact (vertexColorEdge_spec G c hc v i).2.symm.trans hh

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem coloredVector_linearIndependent (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) : LinearIndependent ℝ (coloredVector c) := by
  rw [linearIndependent_iff']
  intro s w hw i hi
  have he := congrFun hw (vertexColorEdge G c hc v i)
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,coloredVector,
    (vertexColorEdge_spec G c hc v i).2,mul_ite,mul_one,mul_zero] at he
  simpa [Finset.sum_ite_eq,hi] using he

omit [DecidableEq V] in
theorem colored_uniform_mean (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) :
    G.mean (fiberMass (uniformLaw (Fin 3)) (colorMatching G c hc)) = fun _ => 1/3 := by
  ext e
  rw [LooplessGraph.mean,fiberMass_expect]
  simp_rw [colorMatching_indicator]
  simp only [uniformLaw,Fintype.card_fin,coloredVector,mul_ite,mul_one,mul_zero]
  simp [Finset.sum_ite_eq]

omit [DecidableEq E] in
theorem expanded_colorMatching (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) (i : Fin 3) :
    expandMatching G c v (colorMatching G c hc i) =
      colorMatching (triangleExpansion G c v) (expandedColor c) (cubicColoring_expansion G c hc v) i := by
  have he : c (incidentChoice G (colorMatching G c hc i) v) = i := by
    simpa [colorMatching,colorEdges] using (incidentChoice_spec G (colorMatching G c hc i) v).1
  apply Subtype.ext
  change (colorEdges c i).disjSum {c (incidentChoice G (colorMatching G c hc i) v)} =
    colorEdges (expandedColor c) i
  rw [he]
  ext e
  rcases e with e | j <;> simp! [colorEdges,expandedColor]

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem triangleExtension_colored (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) (i : Fin 3) :
    triangleExtension G c hc v (coloredVector c i) = coloredVector (expandedColor c) i := by
  ext e
  rcases e with e | j
  · rfl
  · simp only [triangleExtension,LinearMap.coe_mk,AddHom.coe_mk,Sum.elim_inr,coloredVector,expandedColor,(vertexColorEdge_spec G c hc v j).2]
    rfl

end ColoredSupport

theorem kleeEDecEq_succ (n : ℕ) : kleeEDecEq (n+1) = inferInstanceAs (DecidableEq (KleeE n ⊕ Fin 3)) := Subsingleton.elim _ _
theorem kleeVDecEq_succ (n : ℕ) : kleeVDecEq (n+1) = inferInstanceAs (DecidableEq (KleeV n ⊕ Fin 2)) := Subsingleton.elim _ _
theorem kleeEDecEq_zero : kleeEDecEq 0 = inferInstanceAs (DecidableEq (Fin 3)) := Subsingleton.elim _ _

theorem klee_law_eq_fiber (n : ℕ) :
    kleeLaw n = fiberMass (uniformLaw (Fin 3)) (colorMatching (kleeGraph n) (kleeColor n) (klee_cubic n)) := by
  ext M
  unfold kleeLaw fiberMass
  apply Finset.sum_congr rfl
  intro i _
  have he : colorMatching (kleeGraph n) (kleeColor n) (klee_cubic n) i = M ↔
      M.val = colorEdges (kleeColor n) i := by
    rw [Subtype.ext_iff]
    exact eq_comm
  simp [he,uniformLaw]

theorem klee_law_feasible (n : ℕ) : kleeLaw n ∈ (kleeGraph n).feasibleLaws (kleeUniform n) := by
  rw [klee_law_eq_fiber]
  exact ⟨fiberMass_mem_simplex uniformLaw_simplex _,colored_uniform_mean _ _ (klee_cubic n)⟩

theorem klee_uniform_mem (n : ℕ) : kleeUniform n ∈ (kleeGraph n).polytope :=
  ((kleeGraph n).mem_polytope_iff _).mpr ⟨_,klee_law_feasible n⟩

theorem klee_entropy_law (n : ℕ) : entropy (kleeLaw n) = Real.log 3 := by
  rw [klee_law_eq_fiber,entropy_fiberMass_injective _ _ (colorMatching_injective _ _ (klee_cubic n) (kleeRoot n)),uniformLaw_entropy]
  norm_num

theorem klee_uniform_extend (n : ℕ) :
    triangleExtension (kleeGraph n) (kleeColor n) (klee_cubic n) (kleeRoot n) (kleeUniform n) = kleeUniform (n+1) := by
  ext e
  rcases e with e | i <;> rfl

theorem klee_law_expand (n : ℕ) :
    fiberMass (kleeLaw n) (expandMatching (kleeGraph n) (kleeColor n) (kleeRoot n)) = kleeLaw (n+1) := by
  rw [klee_law_eq_fiber,klee_law_eq_fiber,fiberMass_comp]
  ext M
  unfold fiberMass
  apply Finset.sum_congr rfl
  intro i _
  rw [Function.comp_apply,expanded_colorMatching _ _ (klee_cubic n)]
  rw [kleeEDecEq_succ]
  rfl

theorem klee_triangle_expand (n : ℕ) :
    triangleExtension (kleeGraph n) (kleeColor n) (klee_cubic n) (kleeRoot n) '' kleeTriangle n = kleeTriangle (n+1) := by
  rw [kleeTriangle,LinearMap.image_convexHull,← Set.range_comp,kleeTriangle]
  congr 1
  apply congrArg Set.range
  funext i
  exact triangleExtension_colored _ _ (klee_cubic n) _ i

theorem klee_zero_matching (M : (kleeGraph 0).Matching) :
    ∃ i : Fin 3, M = colorMatching (kleeGraph 0) (kleeColor 0) (klee_cubic 0) i := by
  obtain ⟨i,hi,hu⟩ := M.property (0 : Fin 2)
  refine ⟨i,Subtype.ext ?_⟩
  ext e
  have he : (kleeGraph 0).Incident (0 : Fin 2) e := Or.inl rfl
  simp only [colorMatching,colorEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  change e ∈ M.val ↔ e = i
  exact ⟨fun h => hu e ⟨h,he⟩,fun h => h ▸ hi.1⟩

theorem klee_zero_polytope : (kleeGraph 0).polytope = kleeTriangle 0 := by
  unfold LooplessGraph.polytope kleeTriangle
  congr 1
  ext x
  constructor
  · rintro ⟨M,rfl⟩
    obtain ⟨i,rfl⟩ := klee_zero_matching M
    exact ⟨i,(colorMatching_indicator _ _ _ _).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨_,colorMatching_indicator _ _ (klee_cubic 0) i⟩

theorem klee_zero_minimal : minimalFace (kleeGraph 0) (kleeUniform 0) = (kleeGraph 0).polytope := by
  apply Set.Subset.antisymm (fun _ hy => hy.1)
  intro y hy
  refine ⟨hy,?_,?_⟩
  · intro e he
    norm_num [kleeUniform] at he
  · intro S hS _
    have hcard : S.card ≤ 2 := by
      have hh := Finset.card_le_univ S
      change S.card ≤ Fintype.card (Fin 2) at hh
      simpa using hh
    have h1 : S.card = 1 := by
      obtain ⟨k,hk⟩ := hS
      omega
    obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp h1
    rw [LooplessGraph.cutMass_singleton]
    exact ((kleeGraph 0).polytope_subset_constraintPolytope hy).2.1 v

theorem klee_minimal (n : ℕ) : minimalFace (kleeGraph n) (kleeUniform n) = kleeTriangle n := by
  induction n with
  | zero => exact klee_zero_minimal.trans klee_zero_polytope
  | succ n ih =>
    have he := ((expansion_face (kleeGraph n) (kleeColor n) (klee_cubic n) (kleeRoot n)).2.2
      (kleeUniform n) (klee_uniform_mem n)).1
    rw [klee_uniform_extend,ih,klee_triangle_expand] at he
    rw [kleeEDecEq_succ,kleeVDecEq_succ]
    exact he

theorem klee_dimension (n : ℕ) : faceDimension (kleeGraph n) (kleeUniform n) = 2 := by
  rw [faceDimension,klee_minimal,kleeTriangle,affineSpan_convexHull,direction_affineSpan]
  exact (coloredVector_linearIndependent _ _ (klee_cubic n) (kleeRoot n)).affineIndependent.finrank_vectorSpan (by decide)

theorem klee_zero_mean (p : (kleeGraph 0).Matching → ℝ) (i : KleeE 0) :
    (kleeGraph 0).mean p i =
      p (colorMatching (kleeGraph 0) (kleeColor 0) (klee_cubic 0) (kleeColor 0 i)) := by
  classical
  unfold LooplessGraph.mean
  rw [Finset.sum_eq_single
    (colorMatching (kleeGraph 0) (kleeColor 0) (klee_cubic 0) (kleeColor 0 i))]
  · rw [colorMatching_indicator]
    simp [coloredVector]
  · intro M _ hM
    obtain ⟨j,rfl⟩ := klee_zero_matching M
    rw [colorMatching_indicator]
    have hij : kleeColor 0 i ≠ j := fun h => hM (congrArg _ h.symm)
    simp [coloredVector,hij]
  · simp

theorem klee_unique_law (n : ℕ) : (kleeGraph n).feasibleLaws (kleeUniform n) = {kleeLaw n} := by
  apply Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr (klee_law_feasible n))
  induction n with
  | zero =>
    intro p hp
    apply Set.mem_singleton_iff.mpr
    ext M
    obtain ⟨i,rfl⟩ := klee_zero_matching M
    have hp' : p (colorMatching (kleeGraph 0) (kleeColor 0) (klee_cubic 0) i) = 1/3 :=
      (klee_zero_mean p i).symm.trans (congrFun hp.2 i)
    rw [hp',klee_law_eq_fiber,fiberMass_injective_apply _ _
      (colorMatching_injective _ _ (klee_cubic 0) (kleeRoot 0))]
    norm_num [kleeUniform,uniformLaw]
  | succ n ih =>
    intro p hp
    have hp' : p ∈ (triangleExpansion (kleeGraph n) (kleeColor n) (kleeRoot n)).feasibleLaws
        (triangleExtension (kleeGraph n) (kleeColor n) (klee_cubic n) (kleeRoot n) (kleeUniform n)) := by
      rw [klee_uniform_extend]
      rw [kleeEDecEq_succ] at hp
      exact hp
    obtain ⟨heq,hq⟩ := expanded_pull_feasible _ _ (klee_cubic n) _ (klee_uniform_mem n) hp'
    have hh := Set.mem_singleton_iff.mp (ih hq)
    rw [hh,klee_law_expand] at heq
    exact Set.mem_singleton_iff.mpr heq

theorem klee_maxEntropy (n : ℕ) : maxMatchingEntropy (kleeGraph n) (kleeUniform n) = Real.log 3 := by
  obtain ⟨p,hp,he⟩ := maxMatchingEntropy_attained _ (klee_uniform_mem n)
  rw [klee_unique_law,Set.mem_singleton_iff] at hp
  rw [← he,hp,klee_entropy_law]

theorem klee_entropy_terms (n : ℕ) :
    entropy (kleeUniform n) = (n + 1) * Real.log 3 ∧
    complementEntropy (kleeUniform n) = 2 * (n + 1) * Real.log (3 / 2) := by
  have hF : Real.negMulLog (1/3) = Real.log 3 / 3 := by
    norm_num [Real.negMulLog,Real.log_div]
    ring
  have hB : Real.negMulLog (1-1/3) = (2/3) * Real.log (3/2) := by
    norm_num [Real.negMulLog,Real.log_div]
    ring
  constructor
  · simp only [entropy,kleeUniform,hF,Finset.sum_const,Finset.card_univ,klee_cardE,nsmul_eq_mul,
      Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring
  · change (∑ _ : KleeE n, Real.negMulLog (1-1/3)) = _
    simp only [hB,Finset.sum_const,Finset.card_univ,klee_cardE,nsmul_eq_mul,
      Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring

theorem klee_sharp_face (n : ℕ) :
    kleeUniform n ∈ (kleeGraph n).polytope ∧
    minimalFace (kleeGraph n) (kleeUniform n) = kleeTriangle n ∧
    faceDimension (kleeGraph n) (kleeUniform n) = 2 ∧
    Fintype.card (KleeE n) - faceDimension (kleeGraph n) (kleeUniform n) = 3 * (n + 1) - 2 ∧
    (kleeGraph n).feasibleLaws (kleeUniform n) = {kleeLaw n} ∧
    maxMatchingEntropy (kleeGraph n) (kleeUniform n) = Real.log 3 ∧
    entropy (kleeUniform n) = (n + 1) * Real.log 3 ∧
    complementEntropy (kleeUniform n) = 2 * (n + 1) * Real.log (3 / 2) := by
  exact ⟨klee_uniform_mem n,klee_minimal n,klee_dimension n,by rw [klee_cardE,klee_dimension],
    klee_unique_law n,klee_maxEntropy n,klee_entropy_terms n⟩

theorem coefficient_obstruction_scalar (c : ℝ)
    (hc : ∀ n : ℕ, (n+2)*Real.log 3 - c*(2*(n+2)*Real.log (3/2)) ≤ Real.log 3) :
    Real.log 3 / (2 * Real.log (3 / 2)) ≤ c := by
  have hB : 0 < 2 * Real.log (3/2) := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  by_contra! hn
  have hd : 0 < Real.log 3 - c*(2*Real.log (3/2)) := sub_pos.mpr ((lt_div_iff₀ hB).mp hn)
  obtain ⟨n,hn⟩ := exists_nat_gt (Real.log 3 / (Real.log 3 - c*(2*Real.log (3/2))))
  have hh := (div_lt_iff₀ hd).mp hn
  have hc' := hc n
  nlinarith

theorem universal_coefficient_obstruction (c : ℝ)
    (hc : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessGraph V E) (x : E → ℝ), x ∈ G.polytope →
        entropy x - c * complementEntropy x ≤ maxMatchingEntropy G x) :
    Real.log 3 / (2 * Real.log (3 / 2)) ≤ c := by
  apply coefficient_obstruction_scalar c
  intro n
  have h := hc _ _ (kleeGraph (n+1)) (kleeUniform (n+1)) (klee_uniform_mem (n+1))
  rw [(klee_entropy_terms (n+1)).1,(klee_entropy_terms (n+1)).2,klee_maxEntropy] at h
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h

theorem simple_coefficient_obstruction (c : ℝ)
    (hc : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessGraph V E), IsSimpleLabelled G → ∀ x : E → ℝ, x ∈ G.polytope →
        entropy x - c * complementEntropy x ≤ maxMatchingEntropy G x) :
    Real.log 3 / (2 * Real.log (3 / 2)) ≤ c := by
  apply coefficient_obstruction_scalar c
  intro n
  have h := hc _ _ (kleeGraph (n+1)) (klee_simple (n+1) (by omega)) (kleeUniform (n+1)) (klee_uniform_mem (n+1))
  rw [(klee_entropy_terms (n+1)).1,(klee_entropy_terms (n+1)).2,klee_maxEntropy] at h
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h

end MatchingEntropyBounds.Refined

end

end OAI
