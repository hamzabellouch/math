import OAI.Combinatorics.TreewidthL1.ParticleLaws

namespace OAI

universe treewidthLevel1 treewidthLevel2 treewidthLevel3 treewidthLevel4

namespace BoundedTreewidthL1.AnchorTreeParticles
open MeasureTheory ParticleSchedule ParticleBatch
variable {I V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J]

noncomputable def retained (R : RootedForest I) (A : I → Finset J) (i : I) : Finset J :=
  (R.parent i).elim ∅ (fun p => A i ∩ A p)
noncomputable def fresh (R : RootedForest I) (A : I → Finset J) (i : I) : Finset J :=
  A i \ retained R A i
noncomputable def seed : (ι → V → ℝ) × (J → ι × ι) :=
  (fun _ _ => 0, fun _ => (Classical.choice inferInstance, Classical.choice inferInstance))
noncomputable def step (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) (S : (ι → V → ℝ) × (J → ι × ι)) :=
  launchBatch (bag i) (fresh R A i).toList (retained R A i) S.1 S.2 (g i)
noncomputable def state (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) : (ι → V → ℝ) × (J → ι × ι) :=
  R.run seed (step R bag A g) i

lemma retained_subset (R : RootedForest I) (A : I → Finset J) (i : I) :
    retained R A i ⊆ A i := by
  unfold retained
  cases R.parent i with
  | none => exact Finset.empty_subset _
  | some p => exact Finset.inter_subset_left

lemma batch_data (R : RootedForest I) (A : I → Finset J) (i : I)
    {q : ℕ} (hA : (A i).card ≤ q) :
    (fresh R A i).toList.Nodup ∧
    (∀ a ∈ (fresh R A i).toList, a ∉ retained R A i) ∧
    (retained R A i ∪ (fresh R A i).toList.toFinset).card ≤ q := by
  classical
  refine ⟨Finset.nodup_toList _, ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp ha)).2
  · simpa only [Finset.toList_toFinset, fresh,
      Finset.union_sdiff_of_subset (retained_subset R A i)] using hA

lemma state_eq
    {I : Type treewidthLevel1} {V : Type treewidthLevel2} {ι : Type treewidthLevel3}
    {J : Type treewidthLevel4} [Fintype V] [Fintype ι] [Nonempty ι] [DecidableEq ι] [DecidableEq J]
    (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) :
    state (ι := ι) R bag A g i = step R bag A g i
      ((R.parent i).elim seed (state R bag A g)) := RootedForest.run_eq _ _ _ _
/-- Actual branching preparation for anchor keys, launched at their own bag. Children use their own
copies of the parent's list; no consistency assumption on sampled bag laws. -/
theorem forest_particle_realization (R : RootedForest I) (bag : I → Finset V)
    (A : I → Finset J) (k q : ℕ) (hbag : ∀ i, (bag i).card ≤ k)
    (hA : ∀ i, (A i).card ≤ q) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : I → J → V → ℝ)
    (hLip : ∀ i a, ∀ u v, |g i a u - g i a v| ≤ L*d u v)
    (hHeight : ∀ i a v, |g i a v| ≤ H)
    (hzero : ∀ i a, ∀ v ∈ bag i, g i a v = 0) :
    let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
    let S := state (ι := ι) R bag A g
    (∀ i, FunctionParticleReachable d L H (S i).1) ∧
    (∀ i p, R.parent i = some p →
      particleTrace M (S i).1 (bag i) = particleTrace M (S p).1 (bag i)) ∧
    (∀ i p, R.parent i = some p → ∀ a ∈ A i ∩ A p,
      (S i).2 a = (S p).2 a ∧
      (S i).1 ((S i).2 a).1 = (S p).1 ((S p).2 a).1 ∧
      (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2) ∧
    (∀ i a, a ∈ fresh R A i →
      ((S i).2 a).1 ≠ ((S i).2 a).2 ∧
      ∀ v, (S i).1 ((S i).2 a).1 v - (S i).1 ((S i).2 a).2 v = 2*g i a v) := by
  classical
  dsimp only
  let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
  let S := state (ι := ι) R bag A g
  have hstep (i : I) (F : ι → V → ℝ) (p : J → ι × ι)
      (hF : FunctionParticleReachable d L H F) :=
    launchBatch_correct k q hN (bag i) (hbag i)
      (fresh R A i).toList (retained R A i)
      (batch_data R A i (hA i)).1 (batch_data R A i (hA i)).2.1
      (batch_data R A i (hA i)).2.2 d L H Δ hH hΔ F p hF (g i)
      (fun a _ => hLip i a) (fun a _ => hHeight i a) (fun a _ => hzero i a)
  have hreach : ∀ i, FunctionParticleReachable d L H (S i).1 := by
    apply R.run_invariant seed (step R bag A g) (fun S => FunctionParticleReachable d L H S.1)
    · exact FunctionParticleReachable.zero
    · intro i F hF
      exact (hstep i F.1 F.2 hF).1
  have hinput (i : I) : FunctionParticleReachable d L H
      ((R.parent i).elim seed S).1 := by
    cases hp : R.parent i with
    | none => exact FunctionParticleReachable.zero
    | some p => exact hreach p
  have hstate (i : I) :
      launchBatch (bag i) (fresh R A i).toList (retained R A i)
        ((R.parent i).elim seed S).1 ((R.parent i).elim seed S).2 (g i) = S i :=
    (state_eq R bag A g i).symm
  refine ⟨hreach, ?_, ?_, ?_⟩
  · intro i p hp
    have hj := (hstep i ((R.parent i).elim seed S).1
      ((R.parent i).elim seed S).2 (hinput i)).2.1
    rw [hstate] at hj
    simpa only [hp, Option.elim_some] using hj
  · intro i p hp a ha
    have hj := hstep i ((R.parent i).elim seed S).1
      ((R.parent i).elim seed S).2 (hinput i)
    dsimp only at hj
    rw [hstate] at hj
    have hm : a ∈ retained R A i := by simpa only [retained, hp, Option.elim_some] using ha
    have he := hj.2.2.1 a hm
    have hleft := hj.2.2.2.1 _ (first_mem_used hm ((R.parent i).elim seed S).2)
    have hright := hj.2.2.2.1 _ (second_mem_used hm ((R.parent i).elim seed S).2)
    have he' : (S i).2 a = (S p).2 a := by
      simpa only [hp, Option.elim_some] using he
    refine ⟨he', ?_, ?_⟩
    · rw [he']
      simpa only [hp, Option.elim_some] using hleft
    · rw [he']
      simpa only [hp, Option.elim_some] using hright
  · intro i a ha
    have hj := (hstep i ((R.parent i).elim seed S).1
      ((R.parent i).elim seed S).2 (hinput i)).2.2.2.2 a (Finset.mem_toList.mpr ha)
    rw [hstate] at hj
    exact hj
end BoundedTreewidthL1.AnchorTreeParticles

namespace BoundedTreewidthL1.AnchorTreeParticles
open MeasureTheory ParticleSchedule ParticleBatch
variable {I V ι J Ω : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J] [Fintype J] [MeasurableSpace Ω]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Measurability of the actual branching preparation, with all randomness
sampled beforehand. No measurable-choice assumption about the particle lists. -/
theorem measurable_state (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : Ω → I → J → V → ℝ)
    (hg : ∀ i a v, Measurable (fun ω => g ω i a v)) (i : I) :
    Measurable (fun ω => state (ι := ι) R bag A (g ω) i) := by
  apply R.run_measurable (fun _ => seed) (fun j ω S => step R bag A (g ω) j S)
    measurable_const
  intro j f hf
  exact measurable_launchBatch (bag j) (fresh R A j).toList (retained R A j)
    (fun ω => (f ω).1) (fun ω => (f ω).2) (fun ω => g ω j)
    (fun a v => (measurable_pi_apply v).comp ((measurable_pi_apply a).comp hf.fst))
    (fun a => (measurable_pi_apply a).comp hf.snd) (hg j)

end BoundedTreewidthL1.AnchorTreeParticles

namespace BoundedTreewidthL1.AnchorTreeParticles
variable {I J X : Type*} [DecidableEq J]
attribute [local instance] Classical.propDecidable

/-- The discrete launch location depends only on the rooted decomposition and
active keys. In particular it does not consult any preparatory randomness. -/
noncomputable def origin (R : RootedForest I) (A : I → Finset J) (root : I) : I → J → I :=
  R.run (fun _ => root) (fun i old a => if a ∈ retained R A i then old a else i)

lemma origin_eq (R : RootedForest I) (A : I → Finset J) (root i : I) (a : J) :
    origin R A root i a = if a ∈ retained R A i then
      ((R.parent i).elim (fun _ => root) (origin R A root)) a else i := by
  unfold origin
  rw [RootedForest.run_eq]

lemma origin_fresh (R : RootedForest I) (A : I → Finset J) (root i : I)
    (a : J) (ha : a ∈ A i) : a ∈ fresh R A (origin R A root i a) := by
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [origin_eq]
    by_cases hk : a ∈ retained R A i
    · rw [ite_eq_left hk]
      cases hp : R.parent i with
      | none => simp [retained,hp] at hk
      | some p =>
        simp only [Option.elim_some]
        have hap : a ∈ A p := (Finset.mem_inter.mp (by simpa [retained,hp] using hk)).2
        exact ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p hap rfl
    · rw [ite_eq_right hk]
      exact Finset.mem_sdiff.mpr ⟨ha,hk⟩

lemma origin_transport (R : RootedForest I) (A : I → Finset J) (root : I)
    (E : I → J → X)
    (hkeep : ∀ i p, R.parent i = some p → ∀ a ∈ A i ∩ A p, E i a = E p a)
    (i : I) (a : J) (ha : a ∈ A i) : E i a = E (origin R A root i a) a := by
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [origin_eq]
    by_cases hk : a ∈ retained R A i
    · rw [ite_eq_left hk]
      cases hp : R.parent i with
      | none => simp [retained,hp] at hk
      | some p =>
        simp only [Option.elim_some]
        have hap : a ∈ A i ∩ A p := by simpa [retained,hp] using hk
        exact (hkeep i p hp a hap).trans
          (ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p
            (Finset.mem_inter.mp hap).2 rfl)
    · rw [ite_eq_right hk]
end BoundedTreewidthL1.AnchorTreeParticles

namespace BoundedTreewidthL1.AnchorTreeParticles
open scoped BigOperators
variable {I V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J]

lemma two_particle_difference
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι] [Nonempty ι]
    [DecidableEq ι]
    (F : ι → V → ℝ) (a b : ι) (hab : a ≠ b)
    (g : V → ℝ) (hgap : ∀ v, F a v - F b v = 2*g v) (u v : V) :
    2*|g u-g v| ≤ ∑ t, |F t u-F t v| := by
  have hs : (∑ t ∈ ({a,b} : Finset ι), |F t u-F t v|) ≤ ∑ t, |F t u-F t v| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun t _ _ => abs_nonneg _)
  simp only [Finset.sum_pair hab] at hs
  have he : (F a u-F a v)-(F b u-F b v) = 2*(g u-g v) := by
    linarith [hgap u,hgap v]
  have ha := abs_sub (F a u-F a v) (F b u-F b v)
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ha
  exact ha.trans hs

/-- The actual active pair at any descendant supplies the original launch
separation. The origin is deterministic, so no conditioning on the particle
scheduler or sampled coefficients is required. -/
theorem origin_particle_gap (R : RootedForest I) (root : I) (bag : I → Finset V)
    (A : I → Finset J) (k q : ℕ) (hbag : ∀ i, (bag i).card ≤ k)
    (hA : ∀ i, (A i).card ≤ q) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : I → J → V → ℝ)
    (hLip : ∀ i a, ∀ u v, |g i a u - g i a v| ≤ L*d u v)
    (hHeight : ∀ i a v, |g i a v| ≤ H)
    (hzero : ∀ i a, ∀ v ∈ bag i, g i a v = 0)
    (i : I) (a : J) (ha : a ∈ A i) (u v : V) :
    2*|g (origin R A root i a) a u - g (origin R A root i a) a v| ≤
      ∑ t, |(state (ι := ι) R bag A g i).1 t u -
        (state (ι := ι) R bag A g i).1 t v| := by
  let S := state (ι := ι) R bag A g
  let o := origin R A root i a
  obtain ⟨hreach,htrace,hkeep,hnew⟩ := forest_particle_realization R bag A k q
    hbag hA hN d L H Δ hH hΔ g hLip hHeight hzero
  have hp : (S i).2 a = (S o).2 a :=
    origin_transport R A root (fun i a => (S i).2 a)
      (fun i p hip a ha => (hkeep i p hip a ha).1) i a ha
  have hl : (S i).1 ((S i).2 a).1 = (S o).1 ((S o).2 a).1 :=
    origin_transport R A root (fun i a => (S i).1 ((S i).2 a).1)
      (fun i p hip a ha => (hkeep i p hip a ha).2.1) i a ha
  have hr : (S i).1 ((S i).2 a).2 = (S o).1 ((S o).2 a).2 :=
    origin_transport R A root (fun i a => (S i).1 ((S i).2 a).2)
      (fun i p hip a ha => (hkeep i p hip a ha).2.2) i a ha
  have hn := hnew o a (origin_fresh R A root i a ha)
  apply two_particle_difference (S i).1 ((S i).2 a).1 ((S i).2 a).2
    (by rw [hp]; exact hn.1) (g o a) ?_ u v
  intro x
  rw [hl,hr]
  exact hn.2 x
end BoundedTreewidthL1.AnchorTreeParticles
namespace BoundedTreewidthL1.AnchorTreeParticles
open MeasureTheory ParticleLaws
open scoped BigOperators ENNReal
variable {I V ι J Ω : Type*} [Fintype I] [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq V] [DecidableEq ι] [DecidableEq J] [Fintype J] [MeasurableSpace Ω]

/-- Actual global averaged L1 realization of the branching preparation, with
an unconditional integral lower bound from each deterministic active origin. -/
theorem averaged_origin_realization
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (hT : T.IsTree) (root : I) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (A : I → Finset J) (k q : ℕ) (hbag : ∀ i, (B i).card ≤ k)
    (hA : ∀ i, (A i).card ≤ q) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (L H Δ : ℝ) (hL : 0 < L) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : Ω → I → J → V → ℝ) (hmeas : ∀ i a v, Measurable (fun ω => g ω i a v))
    (hLip : ∀ ω i a, ∀ u v, |g ω i a u - g ω i a v| ≤ L*shortestPathDistance G ℓ u v)
    (hHeight : ∀ ω i a v, |g ω i a v| ≤ H)
    (hzero : ∀ ω i a, ∀ v ∈ B i, g ω i a v = 0) :
    ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
      (∀ u v, ‖Φ u - Φ v‖ ≤
        (Fintype.card ι : ℝ)*L*((Fintype.card ι : ℝ)-1)*shortestPathDistance G ℓ u v) ∧
      ∀ i (a : J), a ∈ A i → ∀ (u v : B i),
        2*(∫ ω, |g ω (origin (RootedTree.forest T hT root) A root i a) a u -
          g ω (origin (RootedTree.forest T hT root) A root i a) a v| ∂ν) ≤
          ‖Φ u.val - Φ v.val‖ := by
  classical
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let R := RootedTree.forest T hT root
  let S := fun ω => state (ι := ι) R B A (g ω)
  let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
  have hreach : ∀ ω i, FunctionParticleReachable (shortestPathDistance G ℓ) L H (S ω i).1 := by
    intro ω
    exact (forest_particle_realization R B A k q hbag hA hN
      (shortestPathDistance G ℓ) L H Δ hH hΔ (g ω) (hLip ω) (hHeight ω) (hzero ω)).1
  have hsmeas : ∀ i t v, Measurable (fun ω => (S ω i).1 t v) := by
    intro i t v
    exact (measurable_pi_apply v).comp ((measurable_pi_apply t).comp
      (measurable_state R B A g hmeas i).fst)
  have hcons : ∀ ω i j, T.Adj i j →
      particleTrace M (S ω i).1 (B i ∩ B j) = particleTrace M (S ω j).1 (B i ∩ B j) := by
    intro ω i j hij
    have ht := (forest_particle_realization R B A k q hbag hA hN
      (shortestPathDistance G ℓ) L H Δ hH hΔ (g ω) (hLip ω) (hHeight ω) (hzero ω)).2.1
    rcases RootedTree.edge_orientation T hT root hij with hp | hp
    · exact trace_eq_of_subset M _ _ (B i) _ Finset.inter_subset_left (ht i j hp)
    · exact (trace_eq_of_subset M _ _ (B j) _ Finset.inter_subset_right (ht j i hp)).symm
  obtain ⟨n,Φ,hup,heq⟩ := averaged_particle_realization G hG ℓ hℓ T hT B hcover hedge hrun
    ν L H Δ hL hH hΔ (by omega : 1 ≤ Fintype.card ι) (fun ω i => (S ω i).1)
    hsmeas (by
      have hd : (Classical.decEq ι) = (inferInstance : DecidableEq ι) := Subsingleton.elim _ _
      rw [hd]
      exact hreach) hcons
  refine ⟨n,Φ,hup,?_⟩
  intro i a ha u v
  rw [heq i u v,← integral_const_mul]
  apply integral_mono
  · apply Integrable.const_mul
    apply Integrable.of_bound ((hmeas _ a u).sub (hmeas _ a v)).abs.aestronglyMeasurable (2*H)
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_abs]
    have hu := hHeight ω (origin R A root i a) a u
    have hv := hHeight ω (origin R A root i a) a v
    exact (abs_sub _ _).trans (by linarith)
  · apply integrable_finsetSum
    intro t ht
    apply Integrable.of_bound ((hsmeas i t u).sub (hsmeas i t v)).abs.aestronglyMeasurable
      (2*H*((Fintype.card ι : ℝ)-1))
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_abs]
    have hu := function_particles_height_bound hH (hreach ω i) t u
    have hv := function_particles_height_bound hH (hreach ω i) t v
    exact (abs_sub _ _).trans (by linarith)
  · intro ω
    exact origin_particle_gap R root B A k q hbag hA hN (shortestPathDistance G ℓ)
      L H Δ hH hΔ (g ω) (hLip ω) (hHeight ω) (hzero ω) i a ha u v
end BoundedTreewidthL1.AnchorTreeParticles

namespace BoundedTreewidthL1

lemma tree_path_mem_connected {I : Type*} (T : SimpleGraph I) (hT : T.IsTree)
    {S : Set I} (hS : (T.induce S).Connected) {A B P : I}
    (hA : A ∈ S) (hB : B ∈ S) (q : T.Walk A B) (hq : q.IsPath)
    (hP : P ∈ q.support) : P ∈ S := by
  obtain ⟨p, hp⟩ := hS.exists_isPath ⟨A, hA⟩ ⟨B, hB⟩
  let f := (SimpleGraph.Embedding.induce (G := T) S).toHom
  have hp' : (p.map f).IsPath := hp.map Subtype.val_injective
  have heq : p.map f = q := congrArg Subtype.val
    ((hT.isAcyclic.subsingleton_path A B).elim ⟨p.map f, hp'⟩ ⟨q, hq⟩)
  have hmem : P ∈ (p.map f).support := heq.symm ▸ hP
  rw [SimpleGraph.Walk.support_map] at hmem
  obtain ⟨z, _, hz⟩ := List.mem_map.mp hmem
  exact hz ▸ z.property

/-- The bags touched by the vertices of a graph walk form a connected subtree.
No bounded-width assumption is needed for this purely combinatorial fact. -/
lemma touched_bags_connected {V I : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : SimpleGraph I) (bag : I → Finset V)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    {u v : V} (p : G.Walk u v) :
    (T.induce {t | ∃ z ∈ p.support, z ∈ bag t}).Connected := by
  induction p with
  | @nil u =>
    have hset : {t | ∃ z ∈ ([u] : List V), z ∈ bag t} = {t | u ∈ bag t} := by
      ext t
      simp
    change (T.induce {t | ∃ z ∈ ([u] : List V), z ∈ bag t}).Connected
    rw [hset]
    exact hocc u
  | @cons u v w huv p ih =>
    have hset : {t | ∃ z ∈ (p.cons huv).support, z ∈ bag t} =
        {t | u ∈ bag t} ∪ {t | ∃ z ∈ p.support, z ∈ bag t} := by
      ext t
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, Set.mem_ofPred_eq,
        Set.mem_union]
      constructor
      · rintro ⟨z, rfl | hz, hb⟩
        · exact Or.inl hb
        · exact Or.inr ⟨z, hz, hb⟩
      · rintro (h | ⟨z, hz, hb⟩)
        · exact ⟨u, Or.inl rfl, h⟩
        · exact ⟨z, Or.inr hz, hb⟩
    rw [hset]
    apply SimpleGraph.induce_union_connected (hocc u).preconnected ih.preconnected
    obtain ⟨t, hut, hvt⟩ := hedge u v huv
    exact ⟨t, hut, v, p.start_mem_support, hvt⟩

theorem bag_separator {V I : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : SimpleGraph I) (bag : I → Finset V)
    (hT : T.IsTree)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    {A B P : I} (q : T.Walk A B) (hq : q.IsPath) (hP : P ∈ q.support)
    {u v : V} (hu : u ∈ bag A) (hv : v ∈ bag B) (p : G.Walk u v) :
    ∃ z, z ∈ p.support ∧ z ∈ bag P := by
  exact tree_path_mem_connected T hT (touched_bags_connected G T bag hedge hocc p)
    ⟨u, p.start_mem_support, hu⟩ ⟨v, p.end_mem_support, hv⟩ q hq hP

end BoundedTreewidthL1

namespace BoundedTreewidthL1

/-- Exact finite minimum distance to a nonempty bag in the original weighted metric. -/
noncomputable def bagDistance {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (A : Finset V) (hA : A.Nonempty) (x : V) : ℝ :=
  A.inf' hA (shortestPathDistance G ℓ x)

lemma bagDistance_attained {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (A : Finset V) (hA : A.Nonempty) (x : V) :
    ∃ a ∈ A, bagDistance G ℓ A hA x = shortestPathDistance G ℓ x a :=
  Finset.exists_mem_eq_inf' hA _

lemma bagDistance_le {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (A : Finset V) (hA : A.Nonempty) (x : V) {a : V} (ha : a ∈ A) :
    bagDistance G ℓ A hA x ≤ shortestPathDistance G ℓ x a :=
  Finset.inf'_le _ ha

lemma bagDistance_nonneg {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e) (A : Finset V) (hA : A.Nonempty) (x : V) :
    0 ≤ bagDistance G ℓ A hA x :=
  Finset.le_inf' hA _ (fun a _ => shortestPathDistance_nonneg G ℓ hG hℓ x a)

lemma bagDistance_triangle {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    (A : Finset V) (hA : A.Nonempty) (x y : V) :
    bagDistance G ℓ A hA x ≤ shortestPathDistance G ℓ x y + bagDistance G ℓ A hA y := by
  obtain ⟨a,ha,heq⟩ := bagDistance_attained G ℓ A hA y
  rw [heq]
  exact (bagDistance_le G ℓ A hA x ha).trans (shortestPathDistance_triangle G ℓ hG hℓ x y a)

lemma bagDistance_lipschitz {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    (A : Finset V) (hA : A.Nonempty) (x y : V) :
    |bagDistance G ℓ A hA x - bagDistance G ℓ A hA y| ≤ shortestPathDistance G ℓ x y := by
  have hxy := bagDistance_triangle G ℓ hG hℓ A hA x y
  have hyx := bagDistance_triangle G ℓ hG hℓ A hA y x
  rw [shortestPathDistance_comm G ℓ hG hℓ y x] at hyx
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma geodesic_split {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    {a b z : V} (p : G.Walk a b) (hmin : walkLength G ℓ p = shortestPathDistance G ℓ a b)
    (hz : z ∈ p.support) :
    shortestPathDistance G ℓ a z + shortestPathDistance G ℓ z b = shortestPathDistance G ℓ a b := by
  have heq : walkLength G ℓ (p.takeUntil z hz) + walkLength G ℓ (p.dropUntil z hz) =
      shortestPathDistance G ℓ a b := by
    rw [← walkLength_append,SimpleGraph.Walk.take_spec,hmin]
  have h1 := shortestPathDistance_le_walkLength G ℓ hℓ (p.takeUntil z hz)
  have h2 := shortestPathDistance_le_walkLength G ℓ hℓ (p.dropUntil z hz)
  have h3 := shortestPathDistance_triangle G ℓ hG hℓ a z b
  linarith

theorem separator_bag_geometry {V I : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (hG : G.Connected) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (bag : I → Finset V) (hne : ∀ i, (bag i).Nonempty)
    (hT : T.IsTree)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    {A B P : I} (q : T.Walk A B) (hq : q.IsPath) (hP : P ∈ q.support)
    {x : V} (hx : x ∈ bag B) :
    bagDistance G ℓ (bag P) (hne P) x ≤ bagDistance G ℓ (bag A) (hne A) x ∧
    ∃ z ∈ bag P, bagDistance G ℓ (bag A) (hne A) z + shortestPathDistance G ℓ z x =
      bagDistance G ℓ (bag A) (hne A) x
 := by
  have hnn : ∀ e, 0 ≤ ℓ e := fun e => (hℓ e).le
  obtain ⟨a,ha,haeq⟩ := bagDistance_attained G ℓ (bag A) (hne A) x
  obtain ⟨p,hp,hmin⟩ := shortestPathDistance_attained G ℓ hG a x
  obtain ⟨z,hzp,hzP⟩ := bag_separator G T bag hT hedge hocc q hq hP ha hx p
  have hsplit := geodesic_split G ℓ hG hnn p hmin hzp
  have hsym := shortestPathDistance_comm G ℓ hG hnn a x
  have hnear := bagDistance_le G ℓ (bag A) (hne A) z ha
  rw [shortestPathDistance_comm G ℓ hG hnn z a] at hnear
  have htri := bagDistance_triangle G ℓ hG hnn (bag A) (hne A) x z
  rw [shortestPathDistance_comm G ℓ hG hnn x z] at htri
  have hgeod : bagDistance G ℓ (bag A) (hne A) z + shortestPathDistance G ℓ z x =
      bagDistance G ℓ (bag A) (hne A) x := by linarith
  refine ⟨?_,z,hzP,hgeod⟩
  have hznonneg := bagDistance_nonneg G ℓ hG hnn (bag A) (hne A) z
  have hm := bagDistance_le G ℓ (bag P) (hne P) x hzP
  rw [shortestPathDistance_comm G ℓ hG hnn x z] at hm
  linarith
end BoundedTreewidthL1

namespace BoundedTreewidthL1.AnchorCache
variable {V : Type*} [DecidableEq V]

/-- Immediately follows a strict-to-weak threshold drop in the age-ordered list. -/
def Drop (C : Finset ℕ) (v : ℕ → ℝ) (τ : ℝ) (a : ℕ) : Prop :=
  a ∈ C ∧ v a ≤ τ ∧ ∃ b ∈ C, b < a ∧ τ < v b ∧
    ∀ c ∈ C, b < c → a ≤ c

noncomputable def protectedEntries (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ) : Finset ℕ := by
  classical
  exact (P.product P).biUnion fun pq => if pq.1 = pq.2 then ∅ else
    (Finset.univ : Finset Bool).biUnion fun b => C.filter
      (Drop C (v pq.1) (if b then J*d pq.1 pq.2 else d pq.1 pq.2/100))

def cacheBound (k : ℕ) : ℕ := 2*k^2+2

noncomputable def eligible (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ) : Finset ℕ := by
  classical
  exact C.filter (fun a => a ≠ 0 ∧ a ∉ protectedEntries P C d v J)

/-- Retain the inclusive list if space remains; otherwise evict its oldest
unprotected nonroot entry. The fallback is unreachable on admissible input. -/
noncomputable def trim (k : ℕ) (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ) : Finset ℕ := by
  classical
  exact if cacheBound k < C.card then
    if h : (eligible P C d v J).Nonempty then C.erase ((eligible P C d v J).min' h)
    else C
  else C

lemma drop_unique {C : Finset ℕ} {v : ℕ → ℝ} {τ : ℝ}
    (hmono : ∀ a ∈ C, ∀ b ∈ C, a ≤ b → v b ≤ v a)
    {a b : ℕ} (ha : Drop C v τ a) (hb : Drop C v τ b) : a = b := by
  have le_of_drop {a b : ℕ} (ha : Drop C v τ a) (hb : Drop C v τ b) : a ≤ b := by
    obtain ⟨haC,haτ,c,hcC,hca,hcτ,hnext⟩ := ha
    by_cases hcb : c < b
    · exact hnext b hb.1 hcb
    · have hbc : b ≤ c := Nat.le_of_not_gt hcb
      have hval := hmono b hb.1 c hcC hbc
      linarith [hb.2.1]
  exact Nat.le_antisymm (le_of_drop ha hb) (le_of_drop hb ha)

lemma drop_card_le {C : Finset ℕ} {v : ℕ → ℝ} {τ : ℝ}
    [DecidablePred (Drop C v τ)]
    (hmono : ∀ a ∈ C, ∀ b ∈ C, a ≤ b → v b ≤ v a) :
    (C.filter (Drop C v τ)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact drop_unique hmono (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

lemma protected_subset (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ) :
    protectedEntries P C d v J ⊆ C := by
  classical
  intro a ha
  simp only [protectedEntries, Finset.mem_biUnion] at ha
  obtain ⟨⟨p,q⟩,hpq,h⟩ := ha
  split_ifs at h with hpq'
  · simp at h
  · simp only [Finset.mem_biUnion] at h
    obtain ⟨b,hb,hd⟩ := h
    exact (Finset.mem_filter.mp hd).1

lemma protected_card (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ)
    (hmono : ∀ p ∈ P, ∀ a ∈ C, ∀ b ∈ C, a ≤ b → v p b ≤ v p a) :
    (protectedEntries P C d v J).card ≤ 2*P.card^2 := by
  classical
  unfold protectedEntries
  calc
    _ ≤ ∑ pq ∈ P.product P, (if pq.1 = pq.2 then (∅ : Finset ℕ) else
        (Finset.univ : Finset Bool).biUnion fun b => C.filter
          (Drop C (v pq.1) (if b then J*d pq.1 pq.2 else d pq.1 pq.2/100))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _pq ∈ P.product P, 2 := by
      apply Finset.sum_le_sum
      intro pq hpq
      split_ifs with heq
      · simp
      · calc
          _ ≤ ∑ b : Bool, (C.filter (Drop C (v pq.1)
              (if b then J*d pq.1 pq.2 else d pq.1 pq.2/100))).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ _b : Bool, 1 := Finset.sum_le_sum fun b _ =>
            drop_card_le (hmono pq.1 (Finset.mem_product.mp hpq).1)
          _ = 2 := by decide
    _ = _ := by simp [pow_two, Nat.mul_comm]

lemma eligible_nonempty (k : ℕ) (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ)
    (hP : P.card ≤ k) (hfull : cacheBound k < C.card)
    (hmono : ∀ p ∈ P, ∀ a ∈ C, ∀ b ∈ C, a ≤ b → v p b ≤ v p a) :
    (eligible P C d v J).Nonempty := by
  classical
  by_contra h
  have hempty : eligible P C d v J = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hsub : C ⊆ insert 0 (protectedEntries P C d v J) := by
    intro a ha
    by_cases ha0 : a = 0
    · simp [ha0]
    · have hmem : a ∈ protectedEntries P C d v J := by
        by_contra hn
        have : a ∈ eligible P C d v J := by simp [eligible,ha,ha0,hn]
        simp [hempty] at this
      exact Finset.mem_insert_of_mem hmem
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hp := protected_card P C d v J hmono
  have hsq : P.card^2 ≤ k^2 := Nat.pow_le_pow_left hP 2
  unfold cacheBound at hfull
  omega

theorem deterministic_cache_step (k : ℕ) (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ)
    (hP : P.card ≤ k) (hC : C.card ≤ cacheBound k + 1) (hroot : 0 ∈ C)
    (hmono : ∀ p ∈ P, ∀ a ∈ C, ∀ b ∈ C, a ≤ b → v p b ≤ v p a) :
    (trim k P C d v J).card ≤ cacheBound k ∧
    0 ∈ trim k P C d v J ∧ trim k P C d v J ⊆ C ∧
    (∀ a ∈ protectedEntries P C d v J, a ∈ trim k P C d v J) ∧
    (cacheBound k < C.card → ∃ e ∈ eligible P C d v J,
      (∀ a ∈ eligible P C d v J, e ≤ a) ∧ trim k P C d v J = C.erase e)
 := by
  classical
  by_cases hfull : cacheBound k < C.card
  · have he := eligible_nonempty k P C d v J hP hfull hmono
    let e := (eligible P C d v J).min' he
    have hem : e ∈ eligible P C d v J := Finset.min'_mem _ _
    have heC : e ∈ C := (Finset.mem_filter.mp hem).1
    have he0 : e ≠ 0 := (Finset.mem_filter.mp hem).2.1
    have heprot : e ∉ protectedEntries P C d v J := (Finset.mem_filter.mp hem).2.2
    have htrim : trim k P C d v J = C.erase e := by simp only [trim,hfull,↓reduceIte,he]; rfl
    rw [htrim]
    refine ⟨?_, ?_, Finset.erase_subset _ _, ?_, ?_⟩
    · rw [Finset.card_erase_of_mem heC]
      omega
    · simp [hroot, he0.symm]
    · intro a ha
      exact Finset.mem_erase.mpr ⟨by intro h; subst a; exact heprot ha,
        protected_subset P C d v J ha⟩
    · intro _
      exact ⟨e,hem,(fun a ha => Finset.min'_le _ _ ha),rfl⟩
  · have htrim : trim k P C d v J = C := by simp only [trim,hfull,↓reduceIte]
    rw [htrim]
    exact ⟨Nat.le_of_not_gt hfull, hroot, Finset.Subset.refl _,
      (fun _ h => protected_subset P C d v J h), (fun h => (hfull h).elim)⟩
end BoundedTreewidthL1.AnchorCache
namespace BoundedTreewidthL1.AnchorCache
variable {V : Type*} [DecidableEq V]

noncomputable def memory (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) : ℕ → Finset ℕ
  | 0 => {0}
  | t+1 => trim k (P (t+1)) (insert (t+1) (memory k P d v J t)) d (v (t+1)) J

/-- Incoming cache plus current proposal, before the release at this bag. -/
noncomputable def inclusiveCache (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) : ℕ → Finset ℕ
  | 0 => {0}
  | t+1 => insert (t+1) (memory k P d v J t)

def ValidInput (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last : ℕ) : Prop :=
  ∀ t ≤ last, (P t).card ≤ k ∧ ∀ p ∈ P t,
    ∀ a ∈ inclusiveCache k P d v J t, ∀ b ∈ inclusiveCache k P d v J t,
      a ≤ b → v t p b ≤ v t p a

lemma trim_subset (k : ℕ) (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ) : trim k P C d v J ⊆ C := by
  classical
  unfold trim
  split_ifs <;> first | exact Finset.Subset.refl _ | exact Finset.erase_subset _ _

lemma trim_removed_unique (k : ℕ) (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ)
    {a b : ℕ} (ha : a ∈ C) (hb : b ∈ C)
    (ha' : a ∉ trim k P C d v J) (hb' : b ∉ trim k P C d v J) : a = b := by
  classical
  unfold trim at ha' hb'
  split_ifs at ha' hb' with hc he
  · have hae : a = (eligible P C d v J).min' he := by
      by_contra h; exact ha' (Finset.mem_erase.mpr ⟨h,ha⟩)
    have hbe : b = (eligible P C d v J).min' he := by
      by_contra h; exact hb' (Finset.mem_erase.mpr ⟨h,hb⟩)
    exact hae.trans hbe.symm
  all_goals exact (ha' ha).elim

lemma memory_subset (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (t : ℕ) :
    memory k P d v J t ⊆ inclusiveCache k P d v J t := by
  cases t with
  | zero => exact Finset.Subset.refl _
  | succ t => exact trim_subset ..

lemma inclusive_self (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (t : ℕ) : t ∈ inclusiveCache k P d v J t := by
  cases t <;> simp [inclusiveCache]

lemma inclusive_age (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (t : ℕ) :
    ∀ a ∈ inclusiveCache k P d v J t, a ≤ t := by
  induction t with
  | zero => intro a ha; simpa [inclusiveCache] using ha
  | succ t ih =>
    intro a ha
    simp only [inclusiveCache,Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact le_rfl
    · exact (ih a (memory_subset k P d v J t ha)).trans (Nat.le_succ t)

lemma inclusive_backwards (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) {a t u : ℕ}
    (hatu : a ≤ t) (htu : t ≤ u) (ha : a ∈ inclusiveCache k P d v J u) :
    a ∈ inclusiveCache k P d v J t := by
  induction u with
  | zero =>
    have ht : t = 0 := by omega
    simpa [ht] using ha
  | succ u ih =>
    by_cases h : t = u+1
    · simpa [h] using ha
    · have htu' : t ≤ u := by omega
      simp only [inclusiveCache,Finset.mem_insert] at ha
      rcases ha with he | hm
      · omega
      · exact ih htu' (memory_subset k P d v J u hm)

lemma memory_invariant (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last : ℕ)
    (hvalid : ValidInput k P d v J last) (t : ℕ) (ht : t ≤ last) :
    (memory k P d v J t).card ≤ cacheBound k ∧ 0 ∈ memory k P d v J t := by
  induction t with
  | zero => simp [memory,cacheBound]
  | succ t ih =>
    have hprev := ih (by omega)
    have hinput := hvalid (t+1) ht
    have hcard : (insert (t+1) (memory k P d v J t)).card ≤ cacheBound k + 1 :=
      (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hprev.1 1)
    have hroot : 0 ∈ insert (t+1) (memory k P d v J t) := Finset.mem_insert_of_mem hprev.2
    have hstep := deterministic_cache_step k (P (t+1))
      (insert (t+1) (memory k P d v J t)) d (v (t+1)) J hinput.1 hcard hroot hinput.2
    exact ⟨hstep.1,hstep.2.1⟩

lemma inclusive_invariant (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last : ℕ)
    (hvalid : ValidInput k P d v J last) (t : ℕ) (ht : t ≤ last) :
    (inclusiveCache k P d v J t).card ≤ cacheBound k + 1 ∧
      0 ∈ inclusiveCache k P d v J t := by
  cases t with
  | zero => simp [inclusiveCache,cacheBound]
  | succ t =>
    have hmem := memory_invariant k P d v J last hvalid t (by omega)
    exact ⟨(Finset.card_insert_le _ _).trans (Nat.add_le_add_right hmem.1 1),
      Finset.mem_insert_of_mem hmem.2⟩

lemma memory_protected (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last : ℕ)
    (hvalid : ValidInput k P d v J last) (t : ℕ) (ht : t ≤ last) :
    protectedEntries (P t) (inclusiveCache k P d v J t) d (v t) J ⊆ memory k P d v J t := by
  cases t with
  | zero => exact protected_subset ..
  | succ t =>
    have hh := inclusive_invariant k P d v J last hvalid (t+1) ht
    have hin := hvalid (t+1) ht
    exact (deterministic_cache_step k (P (t+1)) (inclusiveCache k P d v J (t+1))
      d (v (t+1)) J hin.1 hh.1 hh.2 hin.2).2.2.2.1

noncomputable def activeTimes (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (last+1)).filter (fun t => a ∈ inclusiveCache k P d v J t)

noncomputable def lastActive (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last a : ℕ) : ℕ := by
  classical
  exact if h : (activeTimes k P d v J last a).Nonempty then
    (activeTimes k P d v J last a).max' h else a

lemma active_self (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last a : ℕ) (ha : a ≤ last) :
    a ∈ activeTimes k P d v J last a := by
  classical
  simp [activeTimes,ha,inclusive_self]

lemma lastActive_mem (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last a : ℕ) (ha : a ≤ last) :
    lastActive k P d v J last a ∈ activeTimes k P d v J last a := by
  classical
  have hn : (activeTimes k P d v J last a).Nonempty := ⟨a,active_self k P d v J last a ha⟩
  simp only [lastActive,hn,↓reduceDIte]
  exact Finset.max'_mem _ _

lemma le_lastActive (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last a t : ℕ)
    (ht : t ∈ activeTimes k P d v J last a) : t ≤ lastActive k P d v J last a := by
  classical
  have hn : (activeTimes k P d v J last a).Nonempty := ⟨t,ht⟩
  simp only [lastActive,hn,↓reduceDIte]
  exact Finset.le_max' _ _ ht

lemma inclusive_iff_interval (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last a t : ℕ) (ha : a ≤ last) (ht : t ≤ last) :
    a ∈ inclusiveCache k P d v J t ↔ a ≤ t ∧ t ≤ lastActive k P d v J last a := by
  classical
  constructor
  · intro hh
    refine ⟨inclusive_age k P d v J t a hh, le_lastActive k P d v J last a t ?_⟩
    simp [activeTimes,ht,hh]
  · rintro ⟨hat,htf⟩
    have hfm := lastActive_mem k P d v J last a ha
    simp only [activeTimes,Finset.mem_filter] at hfm
    exact inclusive_backwards k P d v J hat htf hfm.2
/-- Realizes the deterministic cache as the inclusive reservation path
needed by the youngest-crossing argument. -/
theorem cache_program_realizes (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last : ℕ)
    (hvalid : ValidInput k P d v J last) :
    ∃ R : BoundedTreewidthL1.ReservationPath, R.last = last ∧
      (∀ t ≤ last, R.inclusive t = inclusiveCache k P d v J t) ∧
      (∀ t, (R.inclusive t).card ≤ cacheBound k + 1) ∧
      (∀ t < last, ∀ a ∈ protectedEntries (P t) (inclusiveCache k P d v J t) d (v t) J,
        t < R.finish a)
 := by
  classical
  let f := lastActive k P d v J last
  have hfl (a : ℕ) (ha : a ≤ last) : a ≤ f a :=
    le_lastActive k P d v J last a a (active_self k P d v J last a ha)
  have hfu (a : ℕ) (ha : a ≤ last) : f a ≤ last := by
    have h := (Finset.mem_filter.mp (lastActive_mem k P d v J last a ha)).1
    exact Nat.le_of_lt_succ (Finset.mem_range.mp h)
  have hroot : f 0 = last := by
    apply Nat.le_antisymm (hfu 0 (Nat.zero_le _))
    apply le_lastActive
    simp only [activeTimes,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_self,true_and]
    exact (inclusive_invariant k P d v J last hvalid last le_rfl).2
  have hretained {a t : ℕ} (ht : t < last) (ha : a ∈ memory k P d v J t) : t < f a := by
    have hin : a ∈ inclusiveCache k P d v J (t+1) := Finset.mem_insert_of_mem ha
    have haage := inclusive_age k P d v J (t+1) a hin
    have happ := (inclusive_iff_interval k P d v J last a (t+1) (by omega) (by omega)).mp hin
    change a ≤ t+1 ∧ t+1 ≤ f a at happ
    exact (Nat.lt_succ_self t).trans_le happ.2
  have hrelease (a b t : ℕ) (hat : a ≤ t) (hbt : b ≤ t) (ht : t < last)
      (haf : f a = t) (hbf : f b = t) : a = b := by
    have ham := (inclusive_iff_interval k P d v J last a t (by omega) (by omega)).mpr ⟨hat,haf.ge⟩
    have hbm := (inclusive_iff_interval k P d v J last b t (by omega) (by omega)).mpr ⟨hbt,hbf.ge⟩
    have han : a ∉ memory k P d v J t := by intro h; have := hretained ht h; omega
    have hbn : b ∉ memory k P d v J t := by intro h; have := hretained ht h; omega
    cases t with
    | zero => exact (han ham).elim
    | succ t =>
      exact trim_removed_unique k (P (t+1)) (inclusiveCache k P d v J (t+1))
        d (v (t+1)) J ham hbm han hbn
  let R : BoundedTreewidthL1.ReservationPath := ⟨last,f,hfl,hfu,hrelease,hroot⟩
  have heq (t : ℕ) (ht : t ≤ last) : R.inclusive t = inclusiveCache k P d v J t := by
    ext a
    simp only [ReservationPath.inclusive,show R.last = last from rfl,ht,↓reduceIte,
      Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
    change (a ≤ t ∧ t ≤ f a) ↔ _
    by_cases ha : a ≤ last
    · exact (inclusive_iff_interval k P d v J last a t ha ht).symm
    · have hn : ¬a ≤ t := by omega
      have hm : a ∉ inclusiveCache k P d v J t := by
        intro h; exact hn (inclusive_age k P d v J t a h)
      simp [hn,hm]
  refine ⟨R,rfl,heq,?_,?_⟩
  · intro t
    by_cases ht : t ≤ last
    · rw [heq t ht]
      exact (inclusive_invariant k P d v J last hvalid t ht).1
    · simp [ReservationPath.inclusive,show R.last = last from rfl,ht]
  · intro t ht a ha
    exact hretained ht (memory_protected k P d v J last hvalid t ht.le ha)
end BoundedTreewidthL1.AnchorCache

namespace BoundedTreewidthL1.AnchorCache

theorem graph_cache_realizes {V I : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (hG : G.Connected) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (bag : I → Finset V) (hne : ∀ i, (bag i).Nonempty)
    (hT : T.IsTree)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    (k : ℕ) (hcard : ∀ i, (bag i).card ≤ k) (J : ℝ)
    {root endBag : I} (q : T.Walk root endBag) (hq : q.IsPath) :
    let P := fun t => bag (q.getVert t)
    let d := shortestPathDistance G ℓ
    let v := fun (_ : ℕ) (p : V) a => bagDistance G ℓ (bag (q.getVert a)) (hne _) p
    ∃ R : ReservationPath, R.last = q.length ∧
      (∀ t ≤ q.length, R.inclusive t = inclusiveCache k P d v J t) ∧
      (∀ t, (R.inclusive t).card ≤ cacheBound k + 1) ∧
      (∀ t < q.length, ∀ a ∈ protectedEntries (P t) (inclusiveCache k P d v J t) d (v t) J,
        t < R.finish a) := by
  classical
  dsimp only
  apply cache_program_realizes
  intro t ht
  refine ⟨hcard _,?_⟩
  intro p hp a ha b hb hab
  have hbt := inclusive_age k (fun t => bag (q.getVert t)) (shortestPathDistance G ℓ)
    (fun (_ : ℕ) (p : V) a => bagDistance G ℓ (bag (q.getVert a)) (hne _) p) J t b hb
  have hat : a ≤ t := hab.trans hbt
  have hsup : q.getVert b ∈ ((q.take t).drop a).support := by
    have hh := ((q.take t).drop a).getVert_mem_support (b-a)
    simpa only [SimpleGraph.Walk.drop_getVert,SimpleGraph.Walk.take_getVert,
      Nat.add_sub_of_le hab,inf_eq_right.mpr hbt] using hh
  have hgeo := separator_bag_geometry G ℓ hG hℓ T bag hne hT hedge hocc
    ((q.take t).drop a) ((hq.take t).drop a) hsup hp
  simpa only [SimpleGraph.Walk.take_getVert,inf_eq_right.mpr hat] using hgeo.1
end BoundedTreewidthL1.AnchorCache
namespace BoundedTreewidthL1.AnchorCache
variable {V : Type*} [DecidableEq V]

lemma drop_congr_on (C : Finset ℕ) (v w : ℕ → ℝ) (τ : ℝ)
    (hvw : ∀ a ∈ C, v a = w a) (a : ℕ) : Drop C v τ a ↔ Drop C w τ a := by
  constructor
  · rintro ⟨ha,hva,b,hb,hba,hτ,hnext⟩
    exact ⟨ha,by rw [← hvw a ha]; exact hva,b,hb,hba,
      by rw [← hvw b hb]; exact hτ,hnext⟩
  · rintro ⟨ha,hva,b,hb,hba,hτ,hnext⟩
    exact ⟨ha,by rw [hvw a ha]; exact hva,b,hb,hba,
      by rw [hvw b hb]; exact hτ,hnext⟩

lemma protected_congr_on (P : Finset V) (C : Finset ℕ) (d : V → V → ℝ)
    (v w : V → ℕ → ℝ) (J : ℝ) (hvw : ∀ x ∈ P, ∀ a ∈ C, v x a = w x a) :
    protectedEntries P C d v J = protectedEntries P C d w J := by
  classical
  unfold protectedEntries
  apply Finset.biUnion_congr rfl
  intro xy hxy
  split_ifs with he
  · rfl
  · apply Finset.biUnion_congr rfl
    intro b hb
    apply Finset.filter_congr
    intro a ha
    exact drop_congr_on C (v xy.1) (w xy.1) _
      (hvw xy.1 (Finset.mem_product.mp hxy).1) a

lemma trim_congr_on (k : ℕ) (P : Finset V) (C : Finset ℕ) (d : V → V → ℝ)
    (v w : V → ℕ → ℝ) (J : ℝ) (hvw : ∀ x ∈ P, ∀ a ∈ C, v x a = w x a) :
    trim k P C d v J = trim k P C d w J := by
  classical
  have he : eligible P C d v J = eligible P C d w J := by
    simp only [eligible, protected_congr_on P C d v w J hvw]
  simp only [trim, he]

lemma memory_prefix (k : ℕ) (P Q : ℕ → Finset V) (d : V → V → ℝ)
    (v w : ℕ → V → ℕ → ℝ) (J : ℝ) (l : ℕ)
    (hP : ∀ t < l, P t = Q t)
    (hv : ∀ t < l, ∀ x a, a ≤ t → v t x a = w t x a) :
    ∀ t < l, memory k P d v J t = memory k Q d w J t := by
  intro t
  induction t with
  | zero => intro ht; rfl
  | succ t ih =>
    intro ht
    rw [memory, memory, hP (t+1) ht, ih (by omega)]
    apply trim_congr_on
    intro x hx a ha
    exact hv (t+1) ht x a (inclusive_age k Q d w J (t+1) a ha)

lemma inclusiveCache_prefix (k : ℕ) (P Q : ℕ → Finset V) (d : V → V → ℝ)
    (v w : ℕ → V → ℕ → ℝ) (J : ℝ) (l : ℕ)
    (hP : ∀ t < l, P t = Q t)
    (hv : ∀ t < l, ∀ x a, a ≤ t → v t x a = w t x a) :
    ∀ t < l, inclusiveCache k P d v J t = inclusiveCache k Q d w J t := by
  intro t ht
  cases t with
  | zero => rfl
  | succ t =>
    simp only [inclusiveCache, memory_prefix k P Q d v w J l hP hv t (by omega)]

end BoundedTreewidthL1.AnchorCache

namespace BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.propDecidable
variable {I : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root : I)

noncomputable def downPath (i : I) : T.Walk root i := (path T hT root i).reverse
lemma downPath_isPath (i : I) : (downPath T hT root i).IsPath :=
  (path_isPath T hT root i).reverse
lemma downPath_length (i : I) : (downPath T hT root i).length = (forest T hT root).depth i := by
  simp only [downPath, SimpleGraph.Walk.length_reverse, path_length, forest]

lemma depth_parent {i p : I} (hp : (forest T hT root).parent i = some p) :
    (forest T hT root).depth i = (forest T hT root).depth p + 1 := by
  have hd := hT.dist_eq_dist_add_one_of_adj root (parent_adj T hT root hp)
  rw [SimpleGraph.dist_comm (u := root) (v := i),
    SimpleGraph.dist_comm (u := root) (v := p)] at hd
  have hlt := (forest T hT root).decreases i p hp
  change T.dist p root < T.dist i root at hlt
  change T.dist i root = T.dist p root + 1
  omega

lemma path_parent {i p : I} (hp : (forest T hT root).parent i = some p) :
    path T hT root i = (path T hT root p).cons (parent_adj T hT root hp) := by
  have hd := depth_parent T hT root hp
  have hlen : ((path T hT root p).cons (parent_adj T hT root hp)).length = T.dist i root := by
    simpa only [SimpleGraph.Walk.length_cons, path_length, forest] using hd.symm
  exact congrArg Subtype.val ((hT.isAcyclic.subsingleton_path i root).elim
    ⟨_, path_isPath T hT root i⟩ ⟨_, SimpleGraph.Walk.isPath_of_length_eq_dist _ hlen⟩)

lemma downPath_parent_getVert {i p : I} (hp : (forest T hT root).parent i = some p)
    (t : ℕ) (ht : t ≤ (forest T hT root).depth p) :
    (downPath T hT root i).getVert t = (downPath T hT root p).getVert t := by
  unfold downPath
  rw [path_parent T hT root hp, SimpleGraph.Walk.reverse_cons]
  rw [SimpleGraph.Walk.getVert_append']
  rw [SimpleGraph.Walk.length_reverse, path_length]
  exact ite_eq_left (show t ≤ T.dist p root from ht)

end BoundedTreewidthL1.RootedTree

namespace BoundedTreewidthL1.TreeCache
open AnchorCache _root_.OAI.BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V : Type*}

noncomputable def bags (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (i : I) (t : ℕ) := B ((downPath T hT root i).getVert t)
noncomputable def heights (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (D : I → V → ℝ) (i : I) (_ : ℕ) (v : V) (a : ℕ) := D ((downPath T hT root i).getVert a) v
noncomputable def inclusive (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (i : I) :=
  inclusiveCache k (bags T hT root B i) d (heights T hT root D i) J ((forest T hT root).depth i)
noncomputable def released (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (i : I) :=
  memory k (bags T hT root B i) d (heights T hT root D i) J ((forest T hT root).depth i)
noncomputable def active (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (i : I) :=
  (inclusive T hT root B D k d J i).image (downPath T hT root i).getVert
noncomputable def retained (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (i : I) :=
  (released T hT root B D k d J i).image (downPath T hT root i).getVert

lemma inclusive_parent (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
    {i p : I} (hp : (forest T hT root).parent i = some p) :
    inclusive T hT root B D k d J i =
      insert ((forest T hT root).depth i) (released T hT root B D k d J p) := by
  have hb (t : ℕ) (ht : t < (forest T hT root).depth p + 1) :
      bags T hT root B i t = bags T hT root B p t := by
    unfold bags
    rw [downPath_parent_getVert T hT root hp t (by omega)]
  have hv (t : ℕ) (ht : t < (forest T hT root).depth p + 1) (x : V) (a : ℕ)
      (ha : a ≤ t) : heights T hT root D i t x a = heights T hT root D p t x a := by
    unfold heights
    rw [downPath_parent_getVert T hT root hp a (by omega)]
  unfold inclusive released
  rw [depth_parent T hT root hp, inclusiveCache,
    memory_prefix k _ _ d _ _ J ((forest T hT root).depth p+1) hb hv _ (by omega)]

lemma active_parent (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
    {i p : I} (hp : (forest T hT root).parent i = some p) :
    active T hT root B D k d J i = insert i (retained T hT root B D k d J p) := by
  unfold active
  rw [inclusive_parent T hT root B D k d J hp, Finset.image_insert]
  have he : (downPath T hT root i).getVert ((forest T hT root).depth i) = i := by
    rw [← downPath_length, SimpleGraph.Walk.getVert_length]
  rw [he]
  congr 1
  apply Finset.image_congr
  intro a ha
  have hage : a ≤ (forest T hT root).depth p := inclusive_age k _ d _ J _ a
    (memory_subset k _ d _ J _ ha)
  exact downPath_parent_getVert T hT root hp a hage

lemma retained_subset (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (i : I) :
    retained T hT root B D k d J i ⊆ active T hT root B D k d J i :=
  Finset.image_subset_image (memory_subset k _ d _ J _)

lemma child_not_active (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
    {i p : I} (hp : (forest T hT root).parent i = some p) :
    i ∉ active T hT root B D k d J p := by
  intro h
  obtain ⟨a,ha,hai⟩ := Finset.mem_image.mp h
  have hage : a ≤ (forest T hT root).depth p := inclusive_age k _ d _ J _ a ha
  have he : (downPath T hT root i).getVert a =
      (downPath T hT root i).getVert ((forest T hT root).depth i) := by
    rw [downPath_parent_getVert T hT root hp a hage, ← downPath_length,
      SimpleGraph.Walk.getVert_length]
    exact hai
  have hh := (downPath_isPath T hT root i).getVert_injOn
    (by simp only [Set.mem_ofPred_eq,downPath_length]; have := depth_parent T hT root hp; omega)
    (by simp only [Set.mem_ofPred_eq,downPath_length,le_refl]) he
  have hd := depth_parent T hT root hp
  omega

end BoundedTreewidthL1.TreeCache

namespace BoundedTreewidthL1.TreeCache
open AnchorCache
open BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V : Type*}

lemma active_root (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) :
    active T hT root B D k d J root = {root} := by
  simp only [active, inclusive, forest, SimpleGraph.dist_self, inclusiveCache,
    Finset.image_singleton, SimpleGraph.Walk.getVert_zero]

lemma active_inter_parent (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
    {i p : I} (hp : (forest T hT root).parent i = some p) :
    active T hT root B D k d J i ∩ active T hT root B D k d J p =
      retained T hT root B D k d J p := by
  rw [active_parent T hT root B D k d J hp]
  ext a
  simp only [Finset.mem_inter, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | h,hp'⟩
    · exact False.elim (child_not_active T hT root B D k d J hp hp')
    · exact h
  · intro h
    exact ⟨Or.inr h, retained_subset T hT root B D k d J p h⟩

lemma active_sdiff_parent (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
    {i p : I} (hp : (forest T hT root).parent i = some p) :
    active T hT root B D k d J i \ active T hT root B D k d J p = {i} := by
  rw [active_parent T hT root B D k d J hp]
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | h,hp'⟩
    · rfl
    · exact False.elim (hp' (retained_subset T hT root B D k d J p h))
  · rintro rfl
    exact ⟨Or.inl rfl, child_not_active T hT root B D k d J hp⟩

/-- Width-only cache capacity on the actual root-to-node paths. -/
theorem graph_active_bound [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (hG : G.Connected) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (B : I → Finset V) (hne : ∀ i, (B i).Nonempty)
    (hT : T.IsTree) (root : I)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ B t ∧ v ∈ B t)
    (hocc : ∀ v, (T.induce {t | v ∈ B t}).Connected)
    (k : ℕ) (hcard : ∀ i, (B i).card ≤ k) (J : ℝ) (i : I) :
    (active T hT root B (fun a => bagDistance G ℓ (B a) (hne a)) k
      (shortestPathDistance G ℓ) J i).card ≤ cacheBound k + 1 := by
  let : DecidableEq V := Classical.decEq V
  obtain ⟨R,hR,heq,hbound,hprot⟩ := graph_cache_realizes G ℓ hG hℓ T B hne hT
    hedge hocc k hcard J (downPath T hT root i) (downPath_isPath T hT root i)
  apply (Finset.card_image_le).trans
  change (inclusiveCache k (bags T hT root B i) (shortestPathDistance G ℓ)
    (heights T hT root (fun a => bagDistance G ℓ (B a) (hne a)) i) J
    ((forest T hT root).depth i)).card ≤ _
  rw [← downPath_length]
  exact (heq _ le_rfl) ▸ hbound _
end BoundedTreewidthL1.TreeCache

end OAI
