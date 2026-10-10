import OAI.Combinatorics.MatchingEntropy.FractionalReduction

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def underlyingSimple (G : LooplessGraph V E) : SimpleGraph V where
  Adj v w := ∃ e, (G.left e = v ∧ G.right e = w) ∨ (G.left e = w ∧ G.right e = v)
  symm := ⟨by
    rintro v w ⟨e, h | h⟩
    · exact ⟨e, Or.inr h⟩
    · exact ⟨e, Or.inl h⟩⟩
  loopless := ⟨by
    rintro v ⟨e, h | h⟩ <;> exact G.loopless e (h.1.trans h.2.symm)⟩

abbrev Component (G : LooplessGraph V E) := (underlyingSimple G).ConnectedComponent
noncomputable instance componentFintype (G : LooplessGraph V E) : Fintype (Component G) := Fintype.ofFinite _
noncomputable instance componentDecidableEq (G : LooplessGraph V E) : DecidableEq (Component G) := Classical.decEq _

def componentOf (G : LooplessGraph V E) (v : V) : Component G :=
  (underlyingSimple G).connectedComponentMk v

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem component_edge_eq (G : LooplessGraph V E) (e : E) :
    componentOf G (G.left e) = componentOf G (G.right e) :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ⟨e, Or.inl ⟨rfl,rfl⟩⟩

def componentGraph (G : LooplessGraph V E) (c : Component G) :
    LooplessGraph {v // componentOf G v = c} {e // componentOf G (G.left e) = c} where
  left e := ⟨G.left e.val,e.property⟩
  right e := ⟨G.right e.val,(component_edge_eq G e.val).symm.trans e.property⟩
  loopless e h := G.loopless e.val (congrArg Subtype.val h)

def componentMean (G : LooplessGraph V E) (x : E → ℝ) (c : Component G) :
    {e // componentOf G (G.left e) = c} → ℝ := fun e => x e.val

def componentOrder (G : LooplessGraph V E) (c : Component G) : ℕ :=
  Fintype.card {v // componentOf G v = c} / 2

section ProductLaws
variable {I : Type uI} [Fintype I] [DecidableEq I] {A : I → Type uA}
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

def piLaw (q : ∀ i, A i → ℝ) (a : ∀ i, A i) : ℝ := ∏ i, q i (a i)

omit [∀ i, DecidableEq (A i)] in
theorem piLaw_simplex {q : ∀ i, A i → ℝ} (hq : ∀ i, q i ∈ probabilitySimplex (A i)) :
    piLaw q ∈ probabilitySimplex (∀ i, A i) := by
  refine ⟨fun a => Finset.prod_nonneg (fun i _ => (hq i).1 (a i)), ?_⟩
  change (∑ a : ∀ i, A i, ∏ i, q i (a i)) = 1
  rw [← Fintype.prod_sum]
  simp_rw [(hq _).2]
  simp

omit [∀ i, DecidableEq (A i)] in
theorem piLaw_expect {q : ∀ i, A i → ℝ} (hq : ∀ i, q i ∈ probabilitySimplex (A i))
    (k : I) (f : A k → ℝ) :
    (∑ a : ∀ i, A i, piLaw q a * f (a k)) = ∑ b, q k b * f b := by
  let r : ∀ i, A i → ℝ := Function.update q k (fun b => q k b * f b)
  have heq (a : ∀ i, A i) : (∏ i, r i (a i)) = piLaw q a * f (a k) := by
    rw [Fintype.prod_eq_mul_prod_compl k (fun i => r i (a i)),
      piLaw, Fintype.prod_eq_mul_prod_compl k (fun i => q i (a i))]
    have hr : r k (a k) = q k (a k) * f (a k) := by simp [r]
    rw [hr]
    have hprod : (∏ i ∈ ({k}ᶜ : Finset I), r i (a i)) = ∏ i ∈ ({k}ᶜ : Finset I), q i (a i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hik : i ≠ k := by simpa using hi
      simp [r, hik]
    rw [hprod]
    ring
  rw [← show (∑ a : ∀ i, A i, ∏ i, r i (a i)) = _ from Finset.sum_congr rfl (fun a _ => heq a),
    ← Fintype.prod_sum, Fintype.prod_eq_mul_prod_compl k]
  have hr : (∑ b, r k b) = ∑ b, q k b * f b := by simp [r]
  rw [hr]
  have hprod : (∏ i ∈ ({k}ᶜ : Finset I), ∑ b, r i b) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hik : i ≠ k := by simpa using hi
    simpa [r, hik] using (hq i).2
  rw [hprod, mul_one]

theorem piLaw_marginal {q : ∀ i, A i → ℝ} (hq : ∀ i, q i ∈ probabilitySimplex (A i))
    (k : I) : fiberMass (piLaw q) (fun a => a k) = q k := by
  ext b
  have h := piLaw_expect hq k (fun x => if x=b then 1 else 0)
  simpa [fiberMass, mul_ite] using h

theorem piLaw_crossEntropy (p : (∀ i, A i) → ℝ) (q : ∀ i, A i → ℝ)
    (hsupp : ∀ a, p a ≠ 0 → ∀ i, q i (a i) ≠ 0) :
    -(∑ a, p a * Real.log (piLaw q a)) =
      ∑ i, -(∑ b, fiberMass p (fun a => a i) b * Real.log (q i b)) := by
  have heq (a : ∀ i, A i) : p a * Real.log (piLaw q a) = ∑ i, p a * Real.log (q i (a i)) := by
    by_cases ha : p a = 0
    · simp [ha]
    · rw [piLaw, Real.log_prod (fun i _ => hsupp a ha i), Finset.mul_sum]
  simp_rw [heq]
  rw [Finset.sum_comm, Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (fiberMass_expect p (fun a => a i) (fun b => Real.log (q i b))).symm

theorem entropy_piLaw {q : ∀ i, A i → ℝ} (hq : ∀ i, q i ∈ probabilitySimplex (A i)) :
    entropy (piLaw q) = ∑ i, entropy (q i) := by
  rw [entropy_eq, piLaw_crossEntropy]
  · simp_rw [piLaw_marginal hq, ← entropy_eq]
  · intro a ha i
    exact (Finset.prod_ne_zero_iff.mp ha) i (Finset.mem_univ i)

theorem entropy_le_marginal_sum {p : (∀ i, A i) → ℝ}
    (hp : p ∈ probabilitySimplex (∀ i, A i)) :
    entropy p ≤ ∑ i, entropy (fiberMass p (fun a => a i)) := by
  let q : ∀ i, A i → ℝ := fun i => fiberMass p (fun a => a i)
  have hq : ∀ i, q i ∈ probabilitySimplex (A i) := fun i => fiberMass_mem_simplex hp _
  have hs : ∀ a, p a ≠ 0 → ∀ i, q i (a i) ≠ 0 := by
    intro a ha i
    exact ne_of_gt ((lt_of_le_of_ne (hp.1 a) (Ne.symm ha)).trans_le (le_fiberMass_self hp.1 _ a))
  have h := entropy_le_crossEntropy (piLaw_simplex hq) hp (fun a ha => by
    by_contra hpa
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hs a hpa i)) ha)
  rw [piLaw_crossEntropy p q hs] at h
  simpa only [q, ← entropy_eq] using h
end ProductLaws

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem component_incident_iff (G : LooplessGraph V E) (c : Component G)
    (v : {v // componentOf G v = c}) (e : {e // componentOf G (G.left e) = c}) :
    (componentGraph G c).Incident v e ↔ G.Incident v.val e.val := by
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem component_eq_of_incident (G : LooplessGraph V E) {v : V} {e : E} (h : G.Incident v e) :
    componentOf G (G.left e) = componentOf G v := by
  rcases h with h | h
  · rw [h]
  · rw [component_edge_eq G e, h]

def componentRestrict (G : LooplessGraph V E) (c : Component G) (M : G.Matching) :
    (componentGraph G c).Matching := by
  classical
  refine ⟨M.val.subtype (fun e => componentOf G (G.left e) = c), ?_⟩
  intro v
  obtain ⟨e,he,hu⟩ := M.property v.val
  have hc : componentOf G (G.left e) = c := (component_eq_of_incident G he.2).trans v.property
  refine ⟨⟨e,hc⟩, ⟨by simpa using he.1,(component_incident_iff G c v _).mpr he.2⟩, ?_⟩
  intro f hf
  exact Subtype.ext (hu f.val ⟨by simpa using hf.1,(component_incident_iff G c v f).mp hf.2⟩)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_componentRestrict (G : LooplessGraph V E) (c : Component G) (M : G.Matching)
    (e : {e // componentOf G (G.left e) = c}) :
    e ∈ (componentRestrict G c M).val ↔ e.val ∈ M.val := by
  simp [componentRestrict]

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem componentRestrict_indicator (G : LooplessGraph V E) (c : Component G) (M : G.Matching)
    (e : {e // componentOf G (G.left e) = c}) :
    (componentGraph G c).indicator (componentRestrict G c M) e = G.indicator M e.val := by
  simp [LooplessGraph.indicator]

def componentGlue (G : LooplessGraph V E) (M : ∀ c : Component G, (componentGraph G c).Matching) :
    G.Matching := by
  classical
  let N := Finset.univ.filter (fun e => (⟨e,rfl⟩ : {f // componentOf G (G.left f) = componentOf G (G.left e)}) ∈ (M (componentOf G (G.left e))).val)
  have hmem (c : Component G) (e : {e // componentOf G (G.left e) = c}) : e.val ∈ N ↔ e ∈ (M c).val := by
    obtain ⟨e,he⟩ := e
    subst c
    simp [N]
  refine ⟨N, ?_⟩
  intro v
  obtain ⟨e,he,hu⟩ := (M (componentOf G v)).property ⟨v,rfl⟩
  refine ⟨e.val,⟨(hmem _ e).mpr he.1,(component_incident_iff G _ _ e).mp he.2⟩,?_⟩
  intro f hf
  have hfc := component_eq_of_incident G hf.2
  exact congrArg Subtype.val (hu ⟨f,hfc⟩ ⟨(hmem _ _).mp hf.1,(component_incident_iff G _ _ _).mpr hf.2⟩)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_componentGlue (G : LooplessGraph V E)
    (M : ∀ c : Component G, (componentGraph G c).Matching) (c : Component G)
    (e : {e // componentOf G (G.left e) = c}) :
    e.val ∈ (componentGlue G M).val ↔ e ∈ (M c).val := by
  obtain ⟨e,he⟩ := e
  subst c
  simp [componentGlue]

def componentMatchingEquiv (G : LooplessGraph V E) :
    G.Matching ≃ (∀ c : Component G, (componentGraph G c).Matching) where
  toFun := fun M c => componentRestrict G c M
  invFun := componentGlue G
  left_inv M := by
    apply Subtype.ext
    ext e
    exact (mem_componentGlue G _ _ ⟨e,rfl⟩).trans (mem_componentRestrict G _ M ⟨e,rfl⟩)
  right_inv M := by
    funext c
    apply Subtype.ext
    ext e
    rw [mem_componentRestrict, mem_componentGlue]

omit [Fintype V] in
omit [DecidableEq V] in
theorem component_mean_marginal (G : LooplessGraph V E) (c : Component G) (p : G.Matching → ℝ) :
    (componentGraph G c).mean (fiberMass p (componentRestrict G c)) = componentMean G (G.mean p) c := by
  ext e
  rw [LooplessGraph.mean, fiberMass_expect]
  simp_rw [componentRestrict_indicator]
  rfl

omit [Fintype V] in
omit [DecidableEq V] in
theorem component_feasible (G : LooplessGraph V E) (c : Component G)
    {x : E → ℝ} {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) :
    fiberMass p (componentRestrict G c) ∈ (componentGraph G c).feasibleLaws (componentMean G x c) := by
  exact ⟨fiberMass_mem_simplex hp.1 _, by rw [component_mean_marginal, hp.2]⟩

section FiberComposition
variable {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
omit [Fintype C] in
theorem fiberMass_comp (p : A → ℝ) (f : A → B) (g : B → C) :
    fiberMass (fiberMass p f) g = fiberMass p (g ∘ f) := by
  ext c
  have h := fiberMass_expect p f (fun b => if g b = c then 1 else 0)
  simpa [fiberMass, mul_ite] using h
end FiberComposition

omit [DecidableEq V] in
theorem component_joint_entropy_bound (G : LooplessGraph V E)
    {p : G.Matching → ℝ} (hp : p ∈ probabilitySimplex G.Matching) :
    entropy p ≤ ∑ c : Component G, entropy (fiberMass p (componentRestrict G c)) := by
  have h := entropy_le_marginal_sum (fiberMass_mem_simplex hp (componentMatchingEquiv G))
  rw [entropy_fiberMass_injective _ _ (componentMatchingEquiv G).injective] at h
  simpa only [fiberMass_comp, Function.comp_def, componentMatchingEquiv, Equiv.coe_fn_mk] using h

omit [DecidableEq V] in
theorem component_product_feasible (G : LooplessGraph V E) {x : E → ℝ}
    {q : ∀ c : Component G, (componentGraph G c).Matching → ℝ}
    (hq : ∀ c, q c ∈ (componentGraph G c).feasibleLaws (componentMean G x c)) :
    fiberMass (piLaw q) (componentMatchingEquiv G).symm ∈ G.feasibleLaws x := by
  refine ⟨fiberMass_mem_simplex (piLaw_simplex (fun c => (hq c).1)) _, ?_⟩
  ext e
  let c := componentOf G (G.left e)
  let f : {e // componentOf G (G.left e) = c} := ⟨e,rfl⟩
  rw [LooplessGraph.mean, fiberMass_expect]
  have hi (M : ∀ c : Component G, (componentGraph G c).Matching) :
      G.indicator ((componentMatchingEquiv G).symm M) e = (componentGraph G c).indicator (M c) f := by
    simp only [LooplessGraph.indicator]
    change (if f.val ∈ (componentGlue G M).val then (1:ℝ) else 0) = _
    simp only [mem_componentGlue]
  simp_rw [hi]
  rw [piLaw_expect (fun c => (hq c).1) c (fun M => (componentGraph G c).indicator M f)]
  exact congrFun (hq c).2 f

omit [DecidableEq V] in
theorem component_maxEntropy (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    maxMatchingEntropy G x = ∑ c : Component G, maxMatchingEntropy (componentGraph G c) (componentMean G x c) := by
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  have hc (c : Component G) : componentMean G x c ∈ (componentGraph G c).polytope :=
    ((componentGraph G c).mem_polytope_iff _).mpr ⟨_,component_feasible G c hp⟩
  choose q hq hqo using fun c => maxMatchingEntropy_attained (componentGraph G c) (hc c)
  apply le_antisymm
  · rw [← hopt]
    exact (component_joint_entropy_bound G hp.1).trans (Finset.sum_le_sum (fun c _ =>
      entropy_le_maxMatchingEntropy _ (component_feasible G c hp)))
  · have hh := entropy_le_maxMatchingEntropy G (component_product_feasible G hq)
    rw [entropy_fiberMass_injective _ _ (componentMatchingEquiv G).symm.injective,
      entropy_piLaw (fun c => (hq c).1)] at hh
    simpa only [hqo] using hh

omit [DecidableEq V] [DecidableEq E] in
theorem component_entropy_terms (G : LooplessGraph V E) (x : E → ℝ) :
    entropy x = ∑ c : Component G, entropy (componentMean G x c) ∧
    complementEntropy x = ∑ c : Component G, complementEntropy (componentMean G x c) := by
  constructor
  · exact (Fintype.sum_fiberwise (fun e => componentOf G (G.left e)) (fun e => Real.negMulLog (x e))).symm
  · exact (Fintype.sum_fiberwise (fun e => componentOf G (G.left e)) (fun e => Real.negMulLog (1-x e))).symm

theorem component_additivity (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    (∀ c : Component G, 0 < componentOrder G c ∧
      Fintype.card {v // componentOf G v = c} = 2 * componentOrder G c ∧
      componentMean G x c ∈ (componentGraph G c).polytope) ∧
    maxMatchingEntropy G x = ∑ c : Component G, maxMatchingEntropy (componentGraph G c) (componentMean G x c) ∧
    entropy x = ∑ c : Component G, entropy (componentMean G x c) ∧
    complementEntropy x = ∑ c : Component G, complementEntropy (componentMean G x c) := by
  refine ⟨?_,component_maxEntropy G hx,component_entropy_terms G x⟩
  intro c
  obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
  have hr := (componentGraph G c).mean_mem_polytope (component_feasible G c hp).1
  rw [(component_feasible G c hp).2] at hr
  have hev := even_of_mem (componentGraph G c) hr
  obtain ⟨v,hv⟩ := c.exists_rep
  have hcpos : 0 < Fintype.card {v // componentOf G v = c} :=
    Fintype.card_pos_iff.mpr ⟨⟨v,hv⟩⟩
  refine ⟨?_,?_,hr⟩ <;> unfold componentOrder <;> obtain ⟨m,hm⟩ := hev <;> omega

theorem fractional_components (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    let R := fractionalGraph G x
    let z := fractionalMean x
    (∀ c : Component R, 0 < componentOrder R c ∧
      Fintype.card {v // componentOf R v = c} = 2 * componentOrder R c ∧
      componentMean R z c ∈ (componentGraph R c).polytope) ∧
    maxMatchingEntropy G x = ∑ c : Component R, maxMatchingEntropy (componentGraph R c) (componentMean R z c) ∧
    entropy x - (∑ c : Component R, (2 - 2 / (componentOrder R c : ℝ)) *
      complementEntropy (componentMean R z c)) ≤ maxMatchingEntropy G x ∧
    maxMatchingEntropy G x ≤ entropy x ∧
    (IsEmpty (Component R) → entropy x = 0 ∧ complementEntropy x = 0 ∧ maxMatchingEntropy G x = 0) := by
  dsimp only
  let R := fractionalGraph G x
  let z := fractionalMean x
  have hz := fractionalMean_mem G hx
  have ⟨ho,hH,hF,hB⟩ := component_additivity R hz
  have hHr : maxMatchingEntropy G x = maxMatchingEntropy R z := by
    simpa only [fractionalExtension_mean] using fractional_maxEntropy G hx hz
  have ⟨hFr,hBr⟩ := fractional_entropy_terms G hx
  refine ⟨ho,hHr.trans hH,?_,refined_upper G x hx,?_⟩
  · rw [hHr, hH, ← hFr, hF, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun c _ => refined_lower (componentGraph R c) (componentOrder R c)
      (ho c).1 (ho c).2.1 (componentMean R z c) (ho c).2.2)
  · intro hc
    have : IsEmpty (Component R) := hc
    constructor
    · rw [← hFr, hF]
      simp
    constructor
    · rw [← hBr, hB]
      simp
    · rw [hHr, hH]
      simp

end MatchingEntropyBounds.Refined

end

end OAI
