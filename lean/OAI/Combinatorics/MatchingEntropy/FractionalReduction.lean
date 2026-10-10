import OAI.Combinatorics.MatchingEntropy.MinimalFace

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def FractionalVertex (G : LooplessGraph V E) (x : E → ℝ) (v : V) : Prop :=
  ∃ e, IsFractional x e ∧ G.Incident v e

instance fractionalVertexDecidable (G : LooplessGraph V E) (x : E → ℝ) :
    DecidablePred (FractionalVertex G x) := Classical.decPred _
instance fractionalEdgeDecidable (x : E → ℝ) : DecidablePred (IsFractional x) := Classical.decPred _

def fractionalGraph (G : LooplessGraph V E) (x : E → ℝ) :
    LooplessGraph {v // FractionalVertex G x v} {e // IsFractional x e} where
  left e := ⟨G.left e.val, e.val, e.property, Or.inl rfl⟩
  right e := ⟨G.right e.val, e.val, e.property, Or.inr rfl⟩
  loopless e h := G.loopless e.val (congrArg Subtype.val h)

def fractionalMean (x : E → ℝ) (e : {e // IsFractional x e}) : ℝ := x e.val

def fractionalExtension (x : E → ℝ) : ({e // IsFractional x e} → ℝ) →ᵃ[ℝ] (E → ℝ) where
  toFun z e := if h : IsFractional x e then z ⟨e,h⟩ else x e
  linear := {
    toFun := fun u e => if h : IsFractional x e then u ⟨e,h⟩ else 0
    map_add' := by intro u v; ext e; by_cases h : IsFractional x e <;> simp [h]
    map_smul' := by intro a u; ext e; by_cases h : IsFractional x e <;> simp [h] }
  map_vadd' := by intro z u; ext e; by_cases h : IsFractional x e <;> simp [h]

def fixedFace (G : LooplessGraph V E) (x : E → ℝ) : Set (E → ℝ) :=
  {y | y ∈ G.polytope ∧ ∀ e, ¬IsFractional x e → y e = x e}

omit [Fintype E] [DecidableEq E] in
@[simp] theorem fractionalExtension_apply_fractional (x : E → ℝ)
    (z : {e // IsFractional x e} → ℝ) (e : {e // IsFractional x e}) :
    fractionalExtension x z e.val = z e := by simp [fractionalExtension, e.property]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem fractionalExtension_apply_fixed (x : E → ℝ)
    (z : {e // IsFractional x e} → ℝ) {e : E} (he : ¬IsFractional x e) :
    fractionalExtension x z e = x e := by simp [fractionalExtension, he]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem fractionalExtension_mean (x : E → ℝ) :
    fractionalExtension x (fractionalMean x) = x := by
  ext e
  by_cases he : IsFractional x e <;> simp [fractionalExtension, fractionalMean, he]

omit [Fintype E] [DecidableEq E] in
theorem fractionalExtension_injective (x : E → ℝ) :
    Function.Injective (fractionalExtension x) := by
  intro z w h
  ext e
  simpa using congrFun h e.val

omit [Fintype E] [DecidableEq E] in
theorem fractionalLinear_injective (x : E → ℝ) :
    Function.Injective (fractionalExtension x).linear := by
  intro z w h
  ext e
  have := congrFun h e.val
  simpa [fractionalExtension, e.property] using this

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem fractional_incident (G : LooplessGraph V E) (x : E → ℝ)
    (v : {v // FractionalVertex G x v}) (e : {e // IsFractional x e}) :
    (fractionalGraph G x).Incident v e ↔ G.Incident v.val e.val := by
  simp only [LooplessGraph.Incident, fractionalGraph, Subtype.ext_iff]

omit [Fintype V] [DecidableEq V] in
theorem fixed_or_zero (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {e : E} (he : ¬IsFractional x e) : x e = 0 ∨ x e = 1 := by
  have h := G.coordinate_mem_Icc hx e
  dsimp [IsFractional] at he
  by_cases hz : x e = 0
  · exact Or.inl hz
  · exact Or.inr (le_antisymm h.2 (not_lt.mp (fun hh => he ⟨lt_of_le_of_ne h.1 (Ne.symm hz), hh⟩)))

omit [Fintype V] [DecidableEq V] in
theorem incident_forced_zero (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {v : V} {e₀ e : E} (h₀ : x e₀ = 1) (hv₀ : G.Incident v e₀)
    (hv : G.Incident v e) (hne : e ≠ e₀) : x e = 0 := by
  apply G.forced_coordinate_zero hx e₀ h₀ hne
  intro hr
  rcases hv with h | h
  · exact hr.1 (h ▸ hv₀)
  · exact hr.2 (h ▸ hv₀)

omit [Fintype V] [DecidableEq V] in
theorem fractional_no_forced (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {v : V} (hv : FractionalVertex G x v) {e : E} (he : x e = 1) : ¬G.Incident v e := by
  intro hi
  obtain ⟨f, hf, hif⟩ := hv
  have hne : f ≠ e := by intro h; subst f; exact (ne_of_lt hf.2) he
  have hz := incident_forced_zero G hx he hi hif hne
  exact (ne_of_gt hf.1) hz

omit [Fintype V] in
theorem positive_incident (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) (v : V) :
    ∃ e, G.Incident v e ∧ 0 < x e := by
  by_contra! hn
  have hc := G.polytope_subset_constraintPolytope hx
  have hz : G.degree x v = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    by_cases hi : G.Incident v e
    · simp [hi, le_antisymm (hn e hi) (hc.1 e)]
    · simp [hi]
  rw [hc.2.1 v] at hz
  norm_num at hz

omit [Fintype V] in
theorem fixed_at_vertex (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {v : V} (hv : ¬FractionalVertex G x v) : ∃! e, x e = 1 ∧ G.Incident v e := by
  obtain ⟨e, hi, he⟩ := positive_incident G hx v
  have hnot : ¬IsFractional x e := fun h => hv ⟨e, h, hi⟩
  have hone : x e = 1 := (fixed_or_zero G hx hnot).resolve_left (ne_of_gt he)
  refine ⟨e, ⟨hone, hi⟩, ?_⟩
  intro f hf
  by_contra hn
  have hz := incident_forced_zero G hx hone hi hf.2 hn
  linarith [hf.1]

def fractionalAdd (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (M : (fractionalGraph G x).Matching) : G.Matching := by
  classical
  let N := M.val.map (Function.Embedding.subtype (IsFractional x)) ∪
    Finset.univ.filter (fun e => x e = 1)
  have hmem (e : E) : e ∈ N ↔
      (∃ he : IsFractional x e, (⟨e,he⟩ : {e // IsFractional x e}) ∈ M.val) ∨ x e = 1 := by
    simp only [N, Finset.mem_union, Finset.mem_map, Function.Embedding.coe_subtype,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨f, hf, rfl⟩ | h)
      · exact Or.inl ⟨f.property, hf⟩
      · exact Or.inr h
    · rintro (⟨he, hm⟩ | h)
      · exact Or.inl ⟨⟨e,he⟩, hm, rfl⟩
      · exact Or.inr h
  refine ⟨N, ?_⟩
  intro v
  by_cases hv : FractionalVertex G x v
  · obtain ⟨e, ⟨he, hi⟩, hu⟩ := M.property ⟨v,hv⟩
    refine ⟨e.val, ⟨(hmem e.val).mpr (Or.inl ⟨e.property,he⟩),
      (fractional_incident G x _ _).mp hi⟩, ?_⟩
    intro f hf
    rcases (hmem f).mp hf.1 with ⟨hfrac, hm⟩ | hone
    · exact congrArg Subtype.val (hu ⟨f,hfrac⟩ ⟨hm, (fractional_incident G x _ _).mpr hf.2⟩)
    · exact (fractional_no_forced G hx hv hone hf.2).elim
  · obtain ⟨e, he, hu⟩ := fixed_at_vertex G hx hv
    refine ⟨e, ⟨(hmem e).mpr (Or.inr he.1), he.2⟩, ?_⟩
    intro f hf
    rcases (hmem f).mp hf.1 with ⟨hfrac, _⟩ | hone
    · exact (hv ⟨f,hfrac,hf.2⟩).elim
    · exact hu f ⟨hone,hf.2⟩

omit [Fintype V] in
theorem mem_fractionalAdd (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (M : (fractionalGraph G x).Matching) (e : E) :
    e ∈ (fractionalAdd G hx M).val ↔
      (∃ he : IsFractional x e, (⟨e,he⟩ : {e // IsFractional x e}) ∈ M.val) ∨ x e = 1 := by
  classical
  simp only [fractionalAdd, Finset.mem_union, Finset.mem_map, Function.Embedding.coe_subtype,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨f,hf,rfl⟩ | h)
    · exact Or.inl ⟨f.property,hf⟩
    · exact Or.inr h
  · rintro (⟨he,hm⟩ | h)
    · exact Or.inl ⟨⟨e,he⟩,hm,rfl⟩
    · exact Or.inr h

omit [Fintype V] in
@[simp] theorem mem_fractionalAdd_fractional (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (M : (fractionalGraph G x).Matching) (e : {e // IsFractional x e}) :
    e.val ∈ (fractionalAdd G hx M).val ↔ e ∈ M.val := by
  rw [mem_fractionalAdd]
  simp only [exists_prop, Subtype.coe_eta]
  constructor
  · rintro (⟨_, hm⟩ | h)
    · exact hm
    · exact ((ne_of_lt e.property.2) h).elim
  · intro h
    exact Or.inl ⟨e.property,h⟩

omit [Fintype V] in
theorem fractionalAdd_injective (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    Function.Injective (fractionalAdd G hx) := by
  intro M N h
  apply Subtype.ext
  ext e
  rw [← mem_fractionalAdd_fractional G hx M e, ← mem_fractionalAdd_fractional G hx N e, h]

def FixedMatching (G : LooplessGraph V E) (x : E → ℝ) (M : G.Matching) : Prop :=
  ∀ e, ¬IsFractional x e → (e ∈ M.val ↔ x e = 1)

def fractionalRemove (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (M : G.Matching) (hM : FixedMatching G x M) : (fractionalGraph G x).Matching := by
  classical
  refine ⟨Finset.univ.filter (fun e => e.val ∈ M.val), ?_⟩
  intro v
  obtain ⟨e, ⟨he, hi⟩, hu⟩ := M.property v.val
  have hefrac : IsFractional x e := by
    by_contra hn
    exact fractional_no_forced G hx v.property ((hM e hn).mp he) hi
  refine ⟨⟨e,hefrac⟩, ⟨by simpa using he, (fractional_incident G x _ _).mpr hi⟩, ?_⟩
  intro f hf
  apply Subtype.ext
  exact hu f.val ⟨by simpa using hf.1, (fractional_incident G x _ _).mp hf.2⟩

omit [Fintype V] in
theorem fractionalAdd_range (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (M : G.Matching) : M ∈ Set.range (fractionalAdd G hx) ↔ FixedMatching G x M := by
  constructor
  · rintro ⟨N,rfl⟩ e he
    rw [mem_fractionalAdd]
    simp [he]
  · intro hM
    refine ⟨fractionalRemove G hx M hM, ?_⟩
    apply Subtype.ext
    ext e
    by_cases he : IsFractional x e
    · rw [← (show (⟨e,he⟩ : {e // IsFractional x e}).val = e from rfl)]
      rw [mem_fractionalAdd_fractional]
      simp [fractionalRemove]
    · rw [mem_fractionalAdd]
      simp [he, hM e he]

omit [Fintype V] [DecidableEq V] in
theorem law_zero_of_mean_zero (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) {e : E} (he : G.mean p e = 0)
    (M : G.Matching) (hM : e ∈ M.val) : p M = 0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun N (_ : N ∈ Finset.univ) =>
    mul_nonneg (hp.1 N) (G.indicator_nonneg N e))).mp he M (by simp)
  simpa [LooplessGraph.indicator, hM] using hz

omit [Fintype V] [DecidableEq V] in
theorem fractional_law_support (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {z : {e // IsFractional x e} → ℝ} {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws (fractionalExtension x z)) {M : G.Matching} (hM : p M ≠ 0) :
    FixedMatching G x M := by
  intro e he
  have hm : G.mean p e = x e := by rw [hp.2, fractionalExtension_apply_fixed x z he]
  rcases fixed_or_zero G hx he with hz | ho
  · constructor
    · intro h
      exact (hM (law_zero_of_mean_zero G hp.1 (hm.trans hz) M h)).elim
    · intro h
      linarith
  · refine ⟨fun _ => ho, fun _ => ?_⟩
    by_contra hn
    exact hM (G.law_support_of_mean_one hp.1 (hm.trans ho) M hn)

theorem fiberMass_injective_apply {A : Type uA} {B : Type uB} [Fintype A] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (hf : Function.Injective f) (a : A) :
    fiberMass p f (f a) = p a := by
  classical
  simp [fiberMass, hf.eq_iff]

theorem fiberMass_outside {A : Type uA} {B : Type uB} [Fintype A] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (b : B) (hb : b ∉ Set.range f) : fiberMass p f b = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  exact ite_eq_right (fun h => hb ⟨a,h⟩)

theorem fiberMass_pullback {A : Type uA} {B : Type uB} [Fintype A] [DecidableEq B]
    (p : B → ℝ) (f : A → B) (hf : Function.Injective f)
    (hp : ∀ b, b ∉ Set.range f → p b = 0) :
    fiberMass (fun a => p (f a)) f = p := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a,rfl⟩ := hb
    exact fiberMass_injective_apply _ _ hf a
  · rw [fiberMass_outside _ _ _ hb, hp b hb]

theorem simplex_of_fiberMass {A : Type uA} {B : Type uB} [Fintype A] [Fintype B] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (hf : Function.Injective f)
    (hp : fiberMass p f ∈ probabilitySimplex B) : p ∈ probabilitySimplex A := by
  refine ⟨fun a => ?_, ?_⟩
  · simpa only [fiberMass_injective_apply p f hf] using hp.1 (f a)
  · rw [← fiberMass_sum p f]
    exact hp.2

omit [Fintype V] in
theorem fractionalAdd_indicator (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (M : (fractionalGraph G x).Matching) :
    G.indicator (fractionalAdd G hx M) = fractionalExtension x ((fractionalGraph G x).indicator M) := by
  ext e
  by_cases he : IsFractional x e
  · rw [← (show (⟨e,he⟩ : {e // IsFractional x e}).val = e from rfl),
      fractionalExtension_apply_fractional]
    simp only [LooplessGraph.indicator, mem_fractionalAdd_fractional G hx M ⟨e,he⟩]
  · rw [fractionalExtension_apply_fixed x _ he]
    simp only [LooplessGraph.indicator, mem_fractionalAdd]
    rcases fixed_or_zero G hx he with h | h <;> simp [he,h]

omit [Fintype V] in
theorem fractional_mean_push (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {q : (fractionalGraph G x).Matching → ℝ} (hq : q ∈ probabilitySimplex (fractionalGraph G x).Matching) :
    G.mean (fiberMass q (fractionalAdd G hx)) =
      fractionalExtension x ((fractionalGraph G x).mean q) := by
  ext e
  rw [LooplessGraph.mean, fiberMass_expect]
  simp_rw [fractionalAdd_indicator G hx]
  by_cases he : IsFractional x e
  · simp only [fractionalExtension, he, ↓reduceDIte, AffineMap.coe_mk]
    rfl
  · simp only [fractionalExtension_apply_fixed x _ he]
    rw [← Finset.sum_mul, hq.2, one_mul]

omit [Fintype V] in
theorem fractional_pull_feasible (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {z : {e // IsFractional x e} → ℝ} {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws (fractionalExtension x z)) :
    p = fiberMass (fun N => p (fractionalAdd G hx N)) (fractionalAdd G hx) ∧
    (fun N => p (fractionalAdd G hx N)) ∈ (fractionalGraph G x).feasibleLaws z := by
  have hinj := fractionalAdd_injective G hx
  have hpe : fiberMass (fun N => p (fractionalAdd G hx N)) (fractionalAdd G hx) = p := by
    apply fiberMass_pullback _ _ hinj
    intro M hM
    by_contra hn
    exact hM ((fractionalAdd_range G hx M).mpr (fractional_law_support G hx hp hn))
  have hsimplex : (fun N => p (fractionalAdd G hx N)) ∈ probabilitySimplex (fractionalGraph G x).Matching :=
    simplex_of_fiberMass _ _ hinj (by rw [hpe]; exact hp.1)
  refine ⟨hpe.symm, hsimplex, fractionalExtension_injective x ?_⟩
  rw [← fractional_mean_push G hx hsimplex, hpe, hp.2]

omit [Fintype V] in
theorem fractional_feasible_iff (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (z : {e // IsFractional x e} → ℝ) (q : (fractionalGraph G x).Matching → ℝ) :
    q ∈ (fractionalGraph G x).feasibleLaws z ↔
      fiberMass q (fractionalAdd G hx) ∈ G.feasibleLaws (fractionalExtension x z) := by
  constructor
  · intro hq
    exact ⟨fiberMass_mem_simplex hq.1 _, (fractional_mean_push G hx hq.1).trans (congrArg _ hq.2)⟩
  · intro hp
    have hq := (fractional_pull_feasible G hx hp).2
    simpa only [fiberMass_injective_apply q _ (fractionalAdd_injective G hx)] using hq

omit [Fintype V] in
theorem fractional_image_eq (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    fractionalExtension x '' (fractionalGraph G x).polytope = fixedFace G x := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨q,hq⟩ := ((fractionalGraph G x).mem_polytope_iff z).mp hz
    exact ⟨(G.mem_polytope_iff _).mpr ⟨_, (fractional_feasible_iff G hx z q).mp hq⟩,
      fun e he => fractionalExtension_apply_fixed x z he⟩
  · intro hy
    let z : {e // IsFractional x e} → ℝ := fun e => y e.val
    have hext : fractionalExtension x z = y := by
      ext e
      by_cases he : IsFractional x e
      · simp [fractionalExtension,he,z]
      · simp [fractionalExtension,he,hy.2 e he]
    obtain ⟨p,hp⟩ := (G.mem_polytope_iff _).mp hy.1
    have hp' : p ∈ G.feasibleLaws (fractionalExtension x z) := hext ▸ hp
    exact ⟨z, ((fractionalGraph G x).mem_polytope_iff z).mpr
      ⟨_,(fractional_pull_feasible G hx hp').2⟩, hext⟩

omit [Fintype V] in
theorem fractionalMean_mem (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    fractionalMean x ∈ (fractionalGraph G x).polytope := by
  have h : x ∈ fixedFace G x := ⟨hx,fun _ _ => rfl⟩
  rw [← fractional_image_eq G hx] at h
  obtain ⟨z,hz,he⟩ := h
  have : z = fractionalMean x := fractionalExtension_injective x (he.trans (fractionalExtension_mean x).symm)
  exact this ▸ hz

omit [Fintype V] [DecidableEq V] in
theorem fixedFace_extreme (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    IsExtreme ℝ G.polytope (fixedFace G x) := by
  refine ⟨fun _ h => h.1, ?_⟩
  intro y hy z hz w hw hseg
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hseg
  refine ⟨hy, ?_⟩
  intro e he
  have heq := hw.2 e he
  change a * y e + b * z e = x e at heq
  have hyb := G.coordinate_mem_Icc hy e
  have hzb := G.coordinate_mem_Icc hz e
  rcases hyb with ⟨hy0,hy1⟩
  rcases hzb with ⟨hz0,hz1⟩
  rcases fixed_or_zero G hx he with h | h
  · rw [h] at heq ⊢
    have := mul_nonneg hb.le hz0
    nlinarith
  · rw [h] at heq ⊢
    apply le_antisymm hy1
    by_contra! hn
    have hpos := mul_pos ha (sub_pos.mpr hn)
    have hnonneg := mul_nonneg hb.le (sub_nonneg.mpr hz1)
    nlinarith

section AffineFaces
variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]

theorem extreme_affine_image (f : A →ᵃ[ℝ] B) (hf : Function.Injective f)
    {P Q : Set A} (h : IsExtreme ℝ P Q) : IsExtreme ℝ (f '' P) (f '' Q) := by
  refine ⟨Set.image_mono h.subset, ?_⟩
  rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ hseg
  rw [← image_openSegment ℝ f] at hseg
  obtain ⟨w',hw',he⟩ := hseg
  have hww : w' = w := hf he
  exact ⟨u, h.left_mem_of_mem_openSegment hu hv hw (hww ▸ hw'), rfl⟩

theorem extreme_affine_preimage (f : A →ᵃ[ℝ] B) {P : Set A} {Q R : Set B}
    (hPQ : f '' P ⊆ Q) (hQR : IsExtreme ℝ Q R) :
    IsExtreme ℝ P (P ∩ f ⁻¹' R) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro u hu v hv w hw hseg
  refine ⟨hu, hQR.left_mem_of_mem_openSegment (hPQ ⟨u,hu,rfl⟩)
    (hPQ ⟨v,hv,rfl⟩) hw.2 ?_⟩
  rw [← image_openSegment ℝ f]
  exact ⟨w,hseg,rfl⟩
end AffineFaces

section FaceMaps
variable {W : Type uW} {D : Type uD} [Fintype W] [Fintype D] [DecidableEq W] [DecidableEq D]

theorem minimalFace_map (G : LooplessGraph V E) (H : LooplessGraph W D)
    (f : (D → ℝ) →ᵃ[ℝ] (E → ℝ)) (hf : Function.Injective f)
    (hP : IsExtreme ℝ G.polytope (f '' H.polytope))
    {z : D → ℝ} (hz : z ∈ H.polytope) :
    f '' minimalFace H z = minimalFace G (f z) := by
  have hfg : f z ∈ G.polytope := hP.subset ⟨z,hz,rfl⟩
  have ⟨hzz, _, hHz, hminH⟩ := minimalFace_spec H hz
  have ⟨hfz, _, hGz, hminG⟩ := minimalFace_spec G hfg
  apply Set.Subset.antisymm
  · have hp := extreme_affine_preimage f hP.subset hGz
    have hsub := hminH _ hp ⟨hz,hfz⟩
    rintro _ ⟨u,hu,rfl⟩
    exact (hsub hu).2
  · exact hminG _ (hP.trans (extreme_affine_image f hf hHz)) ⟨z,hzz,rfl⟩

theorem faceDimension_map (G : LooplessGraph V E) (H : LooplessGraph W D)
    (f : (D → ℝ) →ᵃ[ℝ] (E → ℝ)) (hf : Function.Injective f)
    (hP : IsExtreme ℝ G.polytope (f '' H.polytope))
    {z : D → ℝ} (hz : z ∈ H.polytope) :
    faceDimension H z = faceDimension G (f z) := by
  rw [faceDimension, faceDimension, ← minimalFace_map G H f hf hP hz,
    ← AffineSubspace.map_span, AffineSubspace.map_direction]
  exact (Submodule.equivMapOfInjective _ (f.linear_injective_iff.mpr hf) _).finrank_eq
end FaceMaps

theorem fractional_minimalFace (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    fractionalExtension x '' minimalFace (fractionalGraph G x) (fractionalMean x) = minimalFace G x := by
  have hextreme : IsExtreme ℝ G.polytope (fractionalExtension x '' (fractionalGraph G x).polytope) :=
    (fractional_image_eq G hx).symm ▸ fixedFace_extreme G hx
  simpa only [fractionalExtension_mean] using minimalFace_map G (fractionalGraph G x)
    (fractionalExtension x) (fractionalExtension_injective x) hextreme (fractionalMean_mem G hx)

theorem fractional_dimension (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    faceDimension (fractionalGraph G x) (fractionalMean x) = faceDimension G x := by
  have hextreme : IsExtreme ℝ G.polytope (fractionalExtension x '' (fractionalGraph G x).polytope) :=
    (fractional_image_eq G hx).symm ▸ fixedFace_extreme G hx
  simpa only [fractionalExtension_mean] using faceDimension_map G (fractionalGraph G x)
    (fractionalExtension x) (fractionalExtension_injective x) hextreme (fractionalMean_mem G hx)

omit [Fintype V] [DecidableEq V] in
theorem fractional_entropy_terms (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    entropy (fractionalMean x) = entropy x ∧
      complementEntropy (fractionalMean x) = complementEntropy x := by
  constructor
  · unfold entropy fractionalMean
    apply sum_subtype_supported (IsFractional x) (fun e => Real.negMulLog (x e))
    intro e he
    rcases fixed_or_zero G hx he with h | h <;> simp [h]
  · unfold complementEntropy
    unfold entropy fractionalMean
    apply sum_subtype_supported (IsFractional x) (fun e => Real.negMulLog (1-x e))
    intro e he
    rcases fixed_or_zero G hx he with h | h <;> simp [h]

omit [Fintype V] in
theorem fractional_maxEntropy (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {z : {e // IsFractional x e} → ℝ} (hz : z ∈ (fractionalGraph G x).polytope) :
    maxMatchingEntropy G (fractionalExtension x z) = maxMatchingEntropy (fractionalGraph G x) z := by
  obtain ⟨q,hq,hqopt⟩ := maxMatchingEntropy_attained (fractionalGraph G x) hz
  have hq' := (fractional_feasible_iff G hx z q).mp hq
  have hz' := (G.mem_polytope_iff _).mpr ⟨_,hq'⟩
  obtain ⟨p,hp,hpopt⟩ := maxMatchingEntropy_attained G hz'
  have ⟨hpe,hp'⟩ := fractional_pull_feasible G hx hp
  apply le_antisymm
  · rw [← hpopt, hpe, entropy_fiberMass_injective _ _ (fractionalAdd_injective G hx)]
    exact entropy_le_maxMatchingEntropy _ hp'
  · rw [← hqopt, ← entropy_fiberMass_injective q _ (fractionalAdd_injective G hx)]
    exact entropy_le_maxMatchingEntropy _ hq'

theorem fractional_laws {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    ∃ lift : (fractionalGraph G x).Matching → G.Matching, Function.Injective lift ∧
      (∀ z q, q ∈ (fractionalGraph G x).feasibleLaws z ↔
        fiberMass q lift ∈ G.feasibleLaws (fractionalExtension x z)) ∧
      (∀ z p, p ∈ G.feasibleLaws (fractionalExtension x z) →
        p = fiberMass (fun N => p (lift N)) lift ∧
        (fun N => p (lift N)) ∈ (fractionalGraph G x).feasibleLaws z) ∧
      (∀ z ∈ (fractionalGraph G x).polytope,
        maxMatchingEntropy G (fractionalExtension x z) = maxMatchingEntropy (fractionalGraph G x) z) ∧
      entropy (fractionalMean x) = entropy x ∧
      complementEntropy (fractionalMean x) = complementEntropy x := by
  exact ⟨fractionalAdd G hx, fractionalAdd_injective G hx, fractional_feasible_iff G hx,
    fun _ _ hp => fractional_pull_feasible G hx hp, fun _ hz => fractional_maxEntropy G hx hz,
    fractional_entropy_terms G hx⟩

theorem fractional_reduction (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    IsExtreme ℝ G.polytope (fixedFace G x) ∧
    Function.Injective (fractionalExtension x) ∧
    fractionalExtension x '' (fractionalGraph G x).polytope = fixedFace G x ∧
    fractionalExtension x '' minimalFace (fractionalGraph G x) (fractionalMean x) = minimalFace G x ∧
    faceDimension (fractionalGraph G x) (fractionalMean x) = faceDimension G x ∧
    ∃ m_f : ℕ, Fintype.card {v // FractionalVertex G x v} = 2 * m_f ∧
      (∑ e : {e // IsFractional x e}, x e.val) = (m_f : ℝ) ∧
      (0 < m_f → Fintype.card {e // IsFractional x e} + 2 ≤ faceDimension G x + 3 * m_f) ∧
      (m_f = 0 → ∃ M : G.Matching, G.indicator M = x ∧ faceDimension G x = 0) := by
  have hz := fractionalMean_mem G hx
  have hd := fractional_dimension G hx
  refine ⟨fixedFace_extreme G hx, fractionalExtension_injective x, fractional_image_eq G hx,
    fractional_minimalFace G hx, hd, ?_⟩
  obtain ⟨m,hm⟩ := even_of_mem (fractionalGraph G x) hz
  have hm' : Fintype.card {v // FractionalVertex G x v} = 2 * m := by omega
  refine ⟨m,hm',(fractionalGraph G x).marginal_sum hm' hz,?_,?_⟩
  · intro hm0
    have hr := minimalFace_rank (fractionalGraph G x) m hm0 hm' hz
    have hc : Fintype.card {e : {e // IsFractional x e} // 0 < fractionalMean x e} =
        Fintype.card {e // IsFractional x e} :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv (fun e => e.property.1))
    rwa [hc,hd] at hr
  · intro hm0
    have hvzero : Fintype.card {v // FractionalVertex G x v} = 0 := by omega
    have : IsEmpty {v // FractionalVertex G x v} := Fintype.card_eq_zero_iff.mp hvzero
    have : IsEmpty {e // IsFractional x e} := ⟨fun e => isEmptyElim ((fractionalGraph G x).left e)⟩
    obtain ⟨M⟩ := matching_nonempty_of_mem (fractionalGraph G x) hz
    refine ⟨fractionalAdd G hx M, ?_, ?_⟩
    · rw [fractionalAdd_indicator G hx]
      have hM : (fractionalGraph G x).indicator M = fractionalMean x := Subsingleton.elim _ _
      rw [hM, fractionalExtension_mean]
    · rw [← hd, faceDimension]
      have hle := (affineSpan ℝ (minimalFace (fractionalGraph G x) (fractionalMean x))).direction.finrank_le
      have hzdim : Module.finrank ℝ ({e // IsFractional x e} → ℝ) = 0 := by simp
      rw [hzdim] at hle
      exact Nat.eq_zero_of_le_zero hle

end MatchingEntropyBounds.Refined

end

end OAI
