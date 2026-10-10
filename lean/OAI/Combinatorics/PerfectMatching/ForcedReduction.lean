import OAI.Combinatorics.PerfectMatching.SeparableCovariance

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators
namespace MatchingEntropy
namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def RemainingVertex (G : LooplessGraph V E) (e₀ : E) (v : V) : Prop :=
  ¬G.Incident v e₀

instance remainingVertexDecidable (G : LooplessGraph V E) (e₀ : E) (v : V) :
    Decidable (G.RemainingVertex e₀ v) := inferInstanceAs (Decidable (¬G.Incident v e₀))

def RemainingEdge (G : LooplessGraph V E) (e₀ e : E) : Prop :=
  G.RemainingVertex e₀ (G.left e) ∧ G.RemainingVertex e₀ (G.right e)

instance remainingEdgeDecidable (G : LooplessGraph V E) (e₀ e : E) :
    Decidable (G.RemainingEdge e₀ e) := inferInstanceAs
      (Decidable (G.RemainingVertex e₀ (G.left e) ∧ G.RemainingVertex e₀ (G.right e)))

def deleteEndpoints (G : LooplessGraph V E) (e₀ : E) :
    LooplessGraph {v // G.RemainingVertex e₀ v} {e // G.RemainingEdge e₀ e} where
  left e := ⟨G.left e.val, e.property.1⟩
  right e := ⟨G.right e.val, e.property.2⟩
  loopless e he := G.loopless e.val (congrArg Subtype.val he)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem remainingEdge_ne (G : LooplessGraph V E) (e₀ : E)
    {e : E} (he : G.RemainingEdge e₀ e) : e ≠ e₀ := by
  rintro rfl
  exact he.1 (Or.inl rfl)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem remaining_of_incident (G : LooplessGraph V E) (e₀ : E)
    {e : E} (he : G.RemainingEdge e₀ e) {v : V} (hv : G.Incident v e) :
    G.RemainingVertex e₀ v := by
  rcases hv with h | h
  · exact h ▸ he.1
  · exact h ▸ he.2

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem deleteEndpoints_incident (G : LooplessGraph V E) (e₀ : E)
    (v : {v // G.RemainingVertex e₀ v}) (e : {e // G.RemainingEdge e₀ e}) :
    (G.deleteEndpoints e₀).Incident v e ↔ G.Incident v.val e.val := by
  simp only [Incident, deleteEndpoints, Subtype.ext_iff]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem matching_common_vertex (G : LooplessGraph V E) (M : G.Matching)
    {e f : E} (he : e ∈ M.val) (hf : f ∈ M.val) {v : V}
    (hve : G.Incident v e) (hvf : G.Incident v f) : e=f := by
  obtain ⟨g, _, hg⟩ := M.property v
  exact (hg e ⟨he,hve⟩).trans (hg f ⟨hf,hvf⟩).symm

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in

theorem matching_remaining (G : LooplessGraph V E) (e₀ : E) (M : G.Matching)
    (h₀ : e₀ ∈ M.val) {e : E} (he : e ∈ M.val) (hne : e ≠ e₀) :
    G.RemainingEdge e₀ e := by
  constructor
  · intro hv
    exact hne (G.matching_common_vertex M he h₀ (Or.inl rfl) hv)
  · intro hv
    exact hne (G.matching_common_vertex M he h₀ (Or.inr rfl) hv)

def addForced (G : LooplessGraph V E) (e₀ : E) (N : (G.deleteEndpoints e₀).Matching) :
    G.Matching := by
  refine ⟨insert e₀ (N.val.image Subtype.val), ?_⟩
  intro v
  by_cases hv : G.Incident v e₀
  · refine ⟨e₀, ⟨by simp, hv⟩, ?_⟩
    rintro f ⟨hf,hfv⟩
    rcases Finset.mem_insert.mp hf with h | h
    · exact h
    · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp h
      exact False.elim (G.remaining_of_incident e₀ g.property hfv hv)
  · let v' : {v // G.RemainingVertex e₀ v} := ⟨v,hv⟩
    obtain ⟨f,⟨hf,hfv⟩, hu⟩ := N.property v'
    refine ⟨f.val, ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨f,hf,rfl⟩),
      (G.deleteEndpoints_incident e₀ v' f).mp hfv⟩, ?_⟩
    rintro g ⟨hg,hgv⟩
    rcases Finset.mem_insert.mp hg with h | h
    · exact False.elim (hv (h ▸ hgv))
    · obtain ⟨g',hg',rfl⟩ := Finset.mem_image.mp h
      exact congrArg Subtype.val (hu g' ⟨hg', (G.deleteEndpoints_incident e₀ v' g').mpr hgv⟩)

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_addForced (G : LooplessGraph V E) (e₀ : E)
    (N : (G.deleteEndpoints e₀).Matching) (e : E) :
    e ∈ (G.addForced e₀ N).val ↔ e=e₀ ∨ ∃ h : G.RemainingEdge e₀ e, ⟨e,h⟩ ∈ N.val := by
  simp only [addForced, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨f,hf,rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨f.property,hf⟩
  · rintro (h | ⟨h,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨e,h⟩,he,rfl⟩

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_addForced_remaining (G : LooplessGraph V E) (e₀ : E)
    (N : (G.deleteEndpoints e₀).Matching) (e : {e // G.RemainingEdge e₀ e}) :
    e.val ∈ (G.addForced e₀ N).val ↔ e ∈ N.val := by
  rw [mem_addForced]
  simp only [G.remainingEdge_ne e₀ e.property, false_or]
  exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨e.property,h⟩⟩

def removeForced (G : LooplessGraph V E) (e₀ : E)
    (M : {M : G.Matching // e₀ ∈ M.val}) : (G.deleteEndpoints e₀).Matching := by
  refine ⟨M.val.val.subtype (G.RemainingEdge e₀), ?_⟩
  intro v
  obtain ⟨e,⟨he,hev⟩,hu⟩ := M.val.property v.val
  have hne : e ≠ e₀ := by rintro rfl; exact v.property hev
  have hrem := G.matching_remaining e₀ M.val M.property he hne
  refine ⟨⟨e,hrem⟩, ⟨by simpa using he,
    (G.deleteEndpoints_incident e₀ v ⟨e,hrem⟩).mpr hev⟩, ?_⟩
  rintro f ⟨hf,hfv⟩
  apply Subtype.ext
  exact hu f.val ⟨by simpa using hf, (G.deleteEndpoints_incident e₀ v f).mp hfv⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem mem_removeForced (G : LooplessGraph V E) (e₀ : E)
    (M : {M : G.Matching // e₀ ∈ M.val}) (e : {e // G.RemainingEdge e₀ e}) :
    e ∈ (G.removeForced e₀ M).val ↔ e.val ∈ M.val.val := by
  simp [removeForced]

def forcedMatchingEquiv (G : LooplessGraph V E) (e₀ : E) :
    (G.deleteEndpoints e₀).Matching ≃ {M : G.Matching // e₀ ∈ M.val} where
  toFun N := ⟨G.addForced e₀ N, (G.mem_addForced e₀ N e₀).mpr (Or.inl rfl)⟩
  invFun M := G.removeForced e₀ M
  left_inv N := by
    apply Subtype.ext
    ext e
    exact (G.mem_removeForced e₀ _ e).trans (G.mem_addForced_remaining e₀ N e)
  right_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    ext e
    rw [mem_addForced]
    constructor
    · rintro (rfl | ⟨h,he⟩)
      · exact M.property
      · exact (G.mem_removeForced e₀ M ⟨e,h⟩).mp he
    · intro he
      by_cases h : e=e₀
      · exact Or.inl h
      · exact Or.inr ⟨G.matching_remaining e₀ M.val M.property he h,
          (G.mem_removeForced e₀ M _).mpr he⟩

omit [Fintype V] [Fintype E] in
theorem addForced_injective (G : LooplessGraph V E) (e₀ : E) :
    Function.Injective (G.addForced e₀) := by
  intro N N' h
  apply (G.forcedMatchingEquiv e₀).injective
  exact Subtype.ext h

omit [Fintype E] [DecidableEq E] in
theorem remaining_vertex_card (G : LooplessGraph V E) (e₀ : E) :
    Fintype.card {v // G.RemainingVertex e₀ v} + 2 = Fintype.card V := by
  have he : Fintype.card {v // G.Incident v e₀}=2 := by
    rw [Fintype.card_subtype]
    have hf : Finset.univ.filter (fun v => G.Incident v e₀)={G.left e₀, G.right e₀} := by
      ext v
      simp [Incident, eq_comm]
    rw [hf, Finset.card_pair (G.loopless e₀)]
  have h := Fintype.card_subtype_compl (G.Incident · e₀)
  have hle := Fintype.card_subtype_le (G.Incident · e₀)
  change Fintype.card {v // ¬G.Incident v e₀} + 2 = Fintype.card V
  omega

omit [Fintype V] [Fintype E] in
@[simp] theorem range_addForced (G : LooplessGraph V E) (e₀ : E) (M : G.Matching) :
    M ∈ Set.range (G.addForced e₀) ↔ e₀ ∈ M.val := by
  constructor
  · rintro ⟨N,rfl⟩
    exact (G.mem_addForced e₀ N e₀).mpr (Or.inl rfl)
  · intro h
    refine ⟨G.removeForced e₀ ⟨M,h⟩, ?_⟩
    exact congrArg Subtype.val ((G.forcedMatchingEquiv e₀).apply_symm_apply ⟨M,h⟩)

omit [Fintype V] [DecidableEq V] in
theorem law_support_of_mean_one (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) {e₀ : E} (he : G.mean p e₀=1)
    (M : G.Matching) (hM : e₀ ∉ M.val) : p M=0 := by
  have hz : ∑ N, p N*(1-G.indicator N e₀)=0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp.2]
    change 1-G.mean p e₀=0
    rw [he, sub_self]
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun N (_ : N ∈ Finset.univ) =>
      mul_nonneg (hp.1 N) (sub_nonneg.mpr (G.indicator_le_one N e₀)))).mp hz M (by simp)
  simpa [indicator,hM] using hh

omit [Fintype V] in

theorem forcedLaw_feasible (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) (e₀ : E) (he : x e₀=1) :
    (fun N => p (G.addForced e₀ N)) ∈ (G.deleteEndpoints e₀).feasibleLaws
      (fun e => x e.val) := by
  have hs : ∀ M, e₀ ∉ M.val → p M=0 :=
    G.law_support_of_mean_one hp.1 (by rw [hp.2,he])
  refine ⟨⟨fun N => hp.1.1 _, ?_⟩, ?_⟩
  · rw [← hp.1.2]
    apply Fintype.sum_of_injective (G.addForced e₀) (G.addForced_injective e₀)
    · intro M hM
      exact hs M (fun hh => hM ((G.range_addForced e₀ M).mpr hh))
    · intro N
      rfl
  · funext e
    rw [← congrFun hp.2 e.val]
    apply Fintype.sum_of_injective (G.addForced e₀) (G.addForced_injective e₀)
    · intro M hM
      rw [hs M (fun hh => hM ((G.range_addForced e₀ M).mpr hh)),zero_mul]
    · intro N
      simp only [indicator,mem_addForced_remaining]

omit [Fintype V] [DecidableEq V] in

theorem forced_coordinate_zero (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) {e : E}
    (hneq : e ≠ e₀) (hrem : ¬G.RemainingEdge e₀ e) : x e=0 := by
  obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
  rw [← congrFun hp.2 e]
  apply Finset.sum_eq_zero
  intro M _
  by_cases hM : e₀ ∈ M.val
  · have hh : e ∉ M.val := fun hh => hrem (G.matching_remaining e₀ M hM hh hneq)
    simp [indicator,hh]
  · rw [G.law_support_of_mean_one hp.1 (by rw [hp.2,he]) M hM,zero_mul]

omit [Fintype V] in

theorem separableLower_forced (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) :
    separableLower (fun e : {e // G.RemainingEdge e₀ e} => x e.val)=separableLower x := by
  have hz : ∀ e, ¬G.RemainingEdge e₀ e →
      Real.negMulLog (x e)=0 ∧ Real.negMulLog (1-x e)=0 := by
    intro e h
    by_cases hneq : e=e₀
    · simp [hneq,he]
    · simp [G.forced_coordinate_zero hx e₀ he hneq h]
  unfold separableLower entropy
  rw [sum_subtype_supported _ _ (fun e h => (hz e h).1),
    sum_subtype_supported _ _ (fun e h => (hz e h).2)]

end LooplessGraph

theorem entropy_fiberMass_injective {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (hf : Function.Injective f) :
    entropy (fiberMass p f)=entropy p := by
  classical
  have hself (a : A) : fiberMass p f (f a)=p a := by
    simp [fiberMass,hf.eq_iff]
  have hzero (b : B) (hb : b ∉ Set.range f) : fiberMass p f b=0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact ite_eq_right (fun h => hb ⟨a,h⟩)
  symm
  apply Fintype.sum_of_injective f hf
  · intro b hb
    rw [hzero b hb,Real.negMulLog_zero]
  · intro a
    rw [hself]

namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
omit [Fintype V] in

theorem liftForced_feasible (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1)
    {q : (G.deleteEndpoints e₀).Matching → ℝ}
    (hq : q ∈ (G.deleteEndpoints e₀).feasibleLaws (fun e => x e.val)) :
    fiberMass q (G.addForced e₀) ∈ G.feasibleLaws x := by
  refine ⟨fiberMass_mem_simplex hq.1 _, ?_⟩
  funext e
  rw [mean,fiberMass_expect]
  by_cases heq : e=e₀
  · subst e
    simpa [indicator] using hq.1.2.trans he.symm
  · by_cases hr : G.RemainingEdge e₀ e
    · change (∑ N, q N*G.indicator (G.addForced e₀ N) e)=_
      have hm (N : (G.deleteEndpoints e₀).Matching) :
          G.indicator (G.addForced e₀ N) e = (G.deleteEndpoints e₀).indicator N ⟨e,hr⟩ := by
        simp only [indicator,G.mem_addForced_remaining e₀ N ⟨e,hr⟩]
      simp_rw [hm]
      exact congrFun hq.2 ⟨e,hr⟩
    · rw [G.forced_coordinate_zero hx e₀ he heq hr]
      apply Finset.sum_eq_zero
      intro N _
      simp [indicator,heq,hr]

omit [Fintype V] in

theorem maxMatchingEntropy_forced_le (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) :
    maxMatchingEntropy (G.deleteEndpoints e₀) (fun e => x e.val) ≤ maxMatchingEntropy G x := by
  obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
  have hr := G.forcedLaw_feasible hp e₀ he
  have hx' := ((G.deleteEndpoints e₀).mem_polytope_iff _).mpr ⟨_,hr⟩
  obtain ⟨q,hq,hopt⟩ := maxMatchingEntropy_attained (G.deleteEndpoints e₀) hx'
  rw [← hopt,← entropy_fiberMass_injective q _ (G.addForced_injective e₀)]
  exact entropy_le_maxMatchingEntropy G (G.liftForced_feasible hx e₀ he hq)

end LooplessGraph
end MatchingEntropy
end
end

end OAI
