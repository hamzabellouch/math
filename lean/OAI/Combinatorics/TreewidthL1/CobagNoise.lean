import OAI.Combinatorics.TreewidthL1.AnchorEmbedding

namespace OAI

universe treewidthLevel1 treewidthLevel2

namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

end BoundedTreewidthL1.ParticleLaws

namespace BoundedTreewidthL1.TreeParticles
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
end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.TreeParticles
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
    (hzero : ∀ i a, ∀ v ∈ interface R bag i, g i a v = 0)
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
end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.TreeParticles
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
    (hzero : ∀ ω i a, ∀ v ∈ interface (RootedTree.forest T hT root) B i, g ω i a v = 0) :
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
    · exact trace_eq_of_subset M _ _ (B j) _ Finset.inter_subset_right (ht i j hp)
    · exact (trace_eq_of_subset M _ _ (B i) _ Finset.inter_subset_left (ht j i hp)).symm
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
end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory Set
open scoped unitInterval

theorem uniform_coefficient_integral_lower (a b : ℝ) :
    a/4 ≤ ∫ t : I, |a * (t : ℝ) - b| := by
  rw [unitInterval.measurePreserving_coe.integral_comp
    unitInterval.measurableEmbedding_coe (fun t : ℝ => |a*t-b|)]
  change a/4 ≤ ∫ t in Icc (0:ℝ) 1, |a*t-b|
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hi : ∀ x y : ℝ, IntervalIntegrable (fun t : ℝ => |a*t-b|) volume x y :=
    fun _ _ => (by fun_prop : Continuous (fun t : ℝ => |a*t-b|)).intervalIntegrable _ _
  have hl := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1/2)
    ((by fun_prop : Continuous (fun t : ℝ => b-a*t)).intervalIntegrable _ _)
    (hi 0 (1/2)) (fun t _ => by simpa only [neg_sub] using neg_le_abs (a*t-b))
  have hr := intervalIntegral.integral_mono_on (by norm_num : (1/2:ℝ) ≤ 1)
    ((by fun_prop : Continuous (fun t : ℝ => a*t-b)).intervalIntegrable _ _)
    (hi (1/2) 1) (fun t _ => le_abs_self (a*t-b))
  have hs := intervalIntegral.integral_add_adjacent_intervals (hi 0 (1/2)) (hi (1/2) 1)
  have hli : (∫ t : ℝ in (0:ℝ)..(1/2:ℝ), b-a*t) = b/2-a/8 := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => a*t)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id]
    simp
    ring
  have hri : (∫ t : ℝ in (1/2:ℝ)..1, a*t-b) = 3*a/8-b/2 := by
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun t : ℝ => a*t)).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id]
    simp
    ring
  rw [hli] at hl
  rw [hri] at hr
  linarith
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open Metric MeasureTheory
open scoped unitInterval
variable {V J : Type*} [MetricSpace V] [Fintype J]

noncomputable def cobagBump (A E : Set V) (r : ℝ) (x : V) : ℝ := by
  classical
  exact if A.Nonempty then min (infDist x A) (bump E r x) else bump E r x
noncomputable def cobagNoise (A : Set V) (E : J → Set V) (r : ℝ)
    (U : J → ℝ) (x : V) : ℝ := ∑ i, U i * cobagBump A (E i) r x

lemma cobagBump_eq_diff (A E : Set V) (r : ℝ) (x : V) :
    cobagBump A E r x = bump (E \ A) r x := by
  classical
  by_cases hA : A.Nonempty
  · have hd : (E \ A)ᶜ.Nonempty := by
      obtain ⟨a, ha⟩ := hA
      exact ⟨a, fun h => h.2 ha⟩
    by_cases hE : Eᶜ.Nonempty
    · have hi : infDist x (E \ A)ᶜ = min (infDist x Eᶜ) (infDist x A) := by
        have he : (E \ A)ᶜ = Eᶜ ∪ A := by ext z; simp; tauto
        rw [he, infDist, infEDist_union, ENNReal.toReal_min (infEDist_ne_top hE)
          (infEDist_ne_top hA)]
        rfl
      simp only [cobagBump, hA, ↓reduceIte, bump, hE, hd, hi]
      simp only [min_left_comm, min_comm]
    · have he : E = Set.univ := by
        apply Set.eq_univ_of_forall
        intro z
        by_contra hz
        exact hE ⟨z, hz⟩
      have hec : (Set.univ \ A : Set V)ᶜ = A := by ext z; simp
      simp [cobagBump, hA, bump, he, hec, min_comm]
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    simp [cobagBump, he]

lemma cobagNoise_eq_diff (A : Set V) (E : J → Set V) (r : ℝ) (U : J → ℝ) :
    cobagNoise A E r U = noise (fun i => E i \ A) (fun _ => r) U := by
  funext x
  simp [cobagNoise, noise, cobagBump_eq_diff]

lemma cobag_diff_disjoint
    {V : Type treewidthLevel1} {J : Type treewidthLevel2} [MetricSpace V] [Fintype J]
    (A : Set V) (E : J → Set V)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) :
    Pairwise (fun i j => Disjoint (E i \ A) (E j \ A)) :=
  fun _ _ hij => (hE hij).mono Set.sdiff_subset Set.sdiff_subset

theorem cobag_partition_properties (A : Set V) (E : J → Set V) (r : ℝ)
    (hr : 0 ≤ r) (hE : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : ∀ x, ∃ i, x ∈ E i) (U : J → ℝ) (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1) :
    LipschitzWith 1 (cobagNoise A E r U) ∧
    (∀ x, 0 ≤ cobagNoise A E r U x ∧ cobagNoise A E r U x ≤ r) ∧
    (∀ x ∈ A, cobagNoise A E r U x = 0) := by
  rw [cobagNoise_eq_diff]
  have h := disjoint_noise (fun i => E i \ A) (fun _ => r) U
    (cobag_diff_disjoint A E hE) (fun _ => hr) hU
  refine ⟨h.1, fun x => ⟨h.2.1 x, ?_⟩, ?_⟩
  · by_cases hx : x ∈ A
    · rw [h.2.2.2 x (fun i h => h.2 hx)]
      exact hr
    · obtain ⟨i, hi⟩ := hcover x
      exact h.2.2.1 i x ⟨hi,hx⟩
  · intro x hx
    exact h.2.2.2 x (fun i h => h.2 hx)

lemma cobagBump_bounds (A E : Set V) (r : ℝ) (hr : 0 ≤ r) (x : V) :
    0 ≤ cobagBump A E r x ∧ cobagBump A E r x ≤ r := by
  rw [cobagBump_eq_diff]
  exact bump_bounds _ _ hr _

lemma cobagBump_zero (A E : Set V) (r : ℝ) (hr : 0 ≤ r) (x : V) (hx : x ∉ E) :
    cobagBump A E r x = 0 := by
  rw [cobagBump_eq_diff]
  exact bump_zero _ _ hr _ (fun h => hx h.1)

lemma cobagBump_padding (A E : Set V) (r a : ℝ) (x : V)
    (har : a ≤ r) (hball : ball x a ⊆ E) (hA : A.Nonempty → a ≤ infDist x A) :
    a ≤ cobagBump A E r x := by
  classical
  unfold cobagBump
  split_ifs with hne
  · exact le_min (hA hne) (bump_padding E r x a har hball)
  · exact bump_padding E r x a har hball

lemma coefficient_affine_integral_lower {m : ℕ} (j : Fin (m+1))
    (a : Fin (m+1) → ℝ) :
    a j / 4 ≤ ∫ U : Fin (m+1) → I, |∑ i, (U i:ℝ) * a i| := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => I) j
  let f : I × (Fin m → I) → ℝ := fun z =>
    |(z.1:ℝ)*a j + ∑ i, (z.2 i:ℝ)*a (j.succAbove i)|
  have hc : Continuous f := by unfold f; fun_prop
  have hi : Integrable f := hc.integrable_of_hasCompactSupport (.of_compactSpace _)
  have he : (∫ U : Fin (m+1) → I, |∑ i, (U i:ℝ)*a i|) = ∫ z, f z := by
    have hh := (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => I) j).integral_comp
      e.measurableEmbedding f
    convert hh using 1
    apply integral_congr_ae
    filter_upwards [] with U
    congr 1
    exact Fin.sum_univ_succAbove (fun i => (U i:ℝ)*a i) j
  rw [he]
  change a j / 4 ≤ ∫ z, f z ∂(volume.prod volume)
  rw [integral_prod_symm f hi]
  have hb (U : Fin m → I) : a j/4 ≤ ∫ t : I, f (t,U) := by
    convert uniform_coefficient_integral_lower (a j)
      (-(∑ i, (U i:ℝ)*a (j.succAbove i))) using 1
    congr 1
    funext t
    simp [f, mul_comm, sub_neg_eq_add]
  have hm := integral_mono (integrable_const (a j/4)) hi.integral_prod_right hb
  simpa using hm

theorem cobag_partition_averaging {m : ℕ} (A : Set V)
    (E : Fin (m+1) → Set V) (r α : ℝ) (hr : 0 < r) (_ : 0 < α) (hα1 : α ≤ 1)
    (_ : Pairwise (fun i j => Disjoint (E i) (E j)))
    (_ : ∀ x, ∃ i, x ∈ E i) (j : Fin (m+1)) (x y : V)
    (hx : ball x (α*r) ⊆ E j) (hy : y ∉ E j)
    (hA : A.Nonempty → α*r ≤ infDist x A) :
    α*r/4 ≤ ∫ U : Fin (m+1) → I,
      |cobagNoise A E r (fun i => (U i:ℝ)) x -
       cobagNoise A E r (fun i => (U i:ℝ)) y| := by
  classical
  let a : Fin (m+1) → ℝ := fun i => cobagBump A (E i) r x - cobagBump A (E i) r y
  have ha : α*r ≤ a j := by
    dsimp [a]
    rw [cobagBump_zero A (E j) r hr.le y hy, sub_zero]
    apply cobagBump_padding A (E j) r (α*r) x _ hx hA
    exact mul_le_of_le_one_left hr.le hα1
  have hsum (U : Fin (m+1) → I) :
      cobagNoise A E r (fun i => (U i:ℝ)) x -
      cobagNoise A E r (fun i => (U i:ℝ)) y = ∑ i, (U i:ℝ)*a i := by
    simp only [cobagNoise, a, mul_sub, Finset.sum_sub_distrib]
  simp_rw [hsum]
  exact (div_le_div_of_nonneg_right ha (by norm_num)).trans
    (coefficient_affine_integral_lower j a)
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory Metric
open scoped unitInterval ENNReal
attribute [local instance] Classical.propDecidable
noncomputable def cobagLocationLaw {n : ℕ} (μ : Fin n → ℝ) : Measure (Fin n) :=
  ∑ a, ENNReal.ofReal (μ a) • Measure.dirac a
noncomputable def cobagLaw {n : ℕ} (m : ℕ) (μ : Fin n → ℝ) :
    Measure (Fin n × (Fin (m+1) → I)) := (cobagLocationLaw μ).prod volume
noncomputable def cobagSample {V : Type*} [MetricSpace V] {n m : ℕ}
    (A : Set V) (P : Fin n → V → Fin (m+1)) (r : ℝ)
    (ω : Fin n × (Fin (m+1) → I)) (x : V) : ℝ :=
  cobagNoise A (fun j => {z | P ω.1 z = j}) r (fun j => (ω.2 j:ℝ)) x

lemma cobagLocationLaw_probability {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) :
    IsProbabilityMeasure (cobagLocationLaw μ) := by
  classical
  constructor
  simp only [cobagLocationLaw, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hμ a), hμ₁, ENNReal.ofReal_one]

lemma cobagLocationLaw_integral {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (f : Fin n → ℝ) :
    (∫ a, f a ∂cobagLocationLaw μ) = ∑ a, μ a * f a := by
  classical
  rw [cobagLocationLaw, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_smul_measure, integral_dirac]
    simp [ENNReal.toReal_ofReal (hμ a)]
  · intro a _
    exact (integrable_dirac (f := f) (by simp)).smul_measure (by simp)

lemma cobagSample_continuous {V : Type*} [MetricSpace V] {n m : ℕ}
    (A : Set V) (P : Fin n → V → Fin (m+1)) (r : ℝ) (x : V) :
    Continuous (fun ω => cobagSample A P r ω x) := by
  unfold cobagSample cobagNoise
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul
  · fun_prop
  · exact (continuous_of_discreteTopology (f := fun a : Fin n =>
      cobagBump A {z | P a z = j} r x)).comp continuous_fst

lemma cobagSample_integral {V : Type*} [MetricSpace V] {n m : ℕ}
    (A : Set V) (P : Fin n → V → Fin (m+1)) (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) (r : ℝ) (x y : V) :
    (∫ ω, |cobagSample A P r ω x - cobagSample A P r ω y| ∂cobagLaw m μ) =
      ∑ a, μ a * ∫ U : Fin (m+1) → I,
        |cobagSample A P r (a,U) x - cobagSample A P r (a,U) y| := by
  let := cobagLocationLaw_probability μ hμ hμ₁
  let : IsProbabilityMeasure (cobagLaw m μ) := by unfold cobagLaw; infer_instance
  have hc := ((cobagSample_continuous A P r x).sub (cobagSample_continuous A P r y)).abs
  have hi : Integrable (fun ω => |cobagSample A P r ω x - cobagSample A P r ω y|)
      (cobagLaw m μ) :=
    hc.integrable_of_hasCompactSupport (.of_compactSpace _)
  rw [cobagLaw, integral_prod _ hi, cobagLocationLaw_integral μ hμ]

theorem cobag_sampler {V : Type*} [MetricSpace V] {n m : ℕ}
    (A : Set V) (P : Fin n → V → Fin (m+1)) (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1)
    (r α π : ℝ) (hr : 0 < r) (hα : 0 < α) (hα1 : α ≤ 1)
    (hdiam : ∀ a, 0 < μ a → ∀ x y, P a x = P a y → dist x y ≤ r) :
    IsProbabilityMeasure (cobagLaw m μ) ∧ Measurable (cobagSample A P r) ∧
    (∀ ω, LipschitzWith 1 (cobagSample A P r ω) ∧
      (∀ x, 0 ≤ cobagSample A P r ω x ∧ cobagSample A P r ω x ≤ r) ∧
      (∀ x ∈ A, cobagSample A P r ω x = 0)) ∧
    ∀ x y, r < dist x y → (A.Nonempty → α*r ≤ infDist x A) →
      (π ≤ ∑ a, if (∀ z, dist x z ≤ α*r → P a z = P a x) then μ a else 0) →
      π*α*r/4 ≤ ∫ ω, |cobagSample A P r ω x - cobagSample A P r ω y| ∂cobagLaw m μ := by
  classical
  have hloc := cobagLocationLaw_probability μ hμ hμ₁
  let := hloc
  have hlaw : IsProbabilityMeasure (cobagLaw m μ) := by unfold cobagLaw; infer_instance
  refine ⟨hlaw, ?_, ?_, ?_⟩
  · exact Measurable.of_eval (fun x => (cobagSample_continuous A P r x).measurable)
  · intro ω
    have hdis : Pairwise (fun i j : Fin (m+1) =>
        Disjoint {z | P ω.1 z = i} {z | P ω.1 z = j}) := by
      intro i j hij
      exact Set.disjoint_left.mpr (fun z hi hj => hij (hi.symm.trans hj))
    exact cobag_partition_properties A (fun j => {z | P ω.1 z = j}) r hr.le
      hdis (fun x => ⟨P ω.1 x, rfl⟩) (fun j => (ω.2 j:ℝ))
      (fun j => ⟨(ω.2 j).property.1, (ω.2 j).property.2⟩)
  · intro x y hxy hA hpad
    rw [cobagSample_integral A P μ hμ hμ₁]
    let c : ℝ := α*r/4
    let q : Fin n → ℝ := fun a =>
      if (∀ z, dist x z ≤ α*r → P a z = P a x) then μ a else 0
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hterm (a : Fin n) : c*q a ≤ μ a * ∫ U : Fin (m+1) → I,
        |cobagSample A P r (a,U) x - cobagSample A P r (a,U) y| := by
      have hnon : 0 ≤ ∫ U : Fin (m+1) → I,
          |cobagSample A P r (a,U) x - cobagSample A P r (a,U) y| :=
        integral_nonneg (fun _ => abs_nonneg _)
      by_cases hg : ∀ z, dist x z ≤ α*r → P a z = P a x
      · have hq : q a = μ a := ite_eq_left hg
        rw [hq]
        rcases eq_or_lt_of_le (hμ a) with hz | hp
        · rw [← hz]; simp
        · have hdis : Pairwise (fun i j : Fin (m+1) =>
              Disjoint {z | P a z = i} {z | P a z = j}) := by
            intro i j hij
            exact Set.disjoint_left.mpr (fun z hi hj => hij (hi.symm.trans hj))
          have hav := cobag_partition_averaging A (fun j => {z | P a z = j})
            r α hr hα hα1 hdis (fun z => ⟨P a z, rfl⟩) (P a x) x y
            (fun z hz => hg z (le_of_lt (by simpa [dist_comm] using hz)))
            (fun hy => (not_le_of_gt hxy) (hdiam a hp x y hy.symm)) hA
          exact (mul_comm c (μ a)).le.trans (mul_le_mul_of_nonneg_left hav (hμ a))
      · simp only [q, ite_eq_right hg, mul_zero]
        exact mul_nonneg (hμ a) hnon
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hterm a)
    rw [← Finset.mul_sum] at hsum
    have hh : c*π ≤ c*∑ a, q a := mul_le_mul_of_nonneg_left hpad hc
    calc
      π*α*r/4 = c*π := by dsimp [c]; ring
      _ ≤ c*∑ a, q a := hh
      _ ≤ _ := hsum
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory Metric
open scoped unitInterval

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev FiniteSampleSpace (V : Type*) [Fintype V] :=
  Fin (Fintype.card (V → V)) × (Fin (Fintype.card V + 1) → I)

/-- Convert a finite padded partition law into the actual common sampler
space, without selecting a partition or adding a separation assumption. -/
theorem finite_padded_sampler {V : Type*} [Fintype V] [MetricSpace V]
    (A : Set V) (μ : (V → V) → ℝ) (r α π : ℝ)
    (hμ : ∀ P, 0 ≤ μ P) (hμ₁ : ∑ P, μ P = 1)
    (hr : 0 < r) (hα : 0 < α) (hα1 : α ≤ 1)
    (hdiam : ∀ P, 0 < μ P → ∀ x y, P x = P y → dist x y ≤ r)
    (hpad : ∀ x, π ≤ ∑ P, if (∀ z, dist x z ≤ α*r → P z = P x) then μ P else 0) :
    ∃ ν : Measure (FiniteSampleSpace V), ∃ g : FiniteSampleSpace V → V → ℝ,
      IsProbabilityMeasure ν ∧ Measurable g ∧
      (∀ ω, LipschitzWith 1 (g ω) ∧ (∀ x, 0 ≤ g ω x ∧ g ω x ≤ r) ∧
        (∀ x ∈ A, g ω x = 0)) ∧
      ∀ x y, r < dist x y → (A.Nonempty → α*r ≤ infDist x A) →
        π*α*r/4 ≤ ∫ ω, |g ω x - g ω y| ∂ν := by
  classical
  let e := Fintype.equivFin (V → V)
  let v := Fintype.equivFin V
  let P : Fin (Fintype.card (V → V)) → V → Fin (Fintype.card V + 1) :=
    fun a x => (v (e.symm a x)).castSucc
  let μ' : Fin (Fintype.card (V → V)) → ℝ := fun a => μ (e.symm a)
  have heq (a) (x y : V) : P a x = P a y ↔ e.symm a x = e.symm a y := by
    simp only [P, Fin.castSucc_inj, Equiv.apply_eq_iff_eq]
  have hsum : ∑ a, μ' a = 1 := by
    rw [show (∑ a, μ' a) = ∑ f, μ f from e.symm.sum_comp μ]
    exact hμ₁
  have hd : ∀ a, 0 < μ' a → ∀ x y, P a x = P a y → dist x y ≤ r := by
    intro a ha x y hxy
    exact hdiam (e.symm a) ha x y ((heq a x y).mp hxy)
  have hp (x : V) : π ≤ ∑ a, if (∀ z, dist x z ≤ α*r → P a z = P a x)
      then μ' a else 0 := by
    simp only [heq]
    change π ≤ ∑ a, (fun f : V → V => if (∀ z, dist x z ≤ α*r → f z = f x)
      then μ f else 0) (e.symm a)
    have he := e.symm.sum_comp (fun f : V → V => if (∀ z, dist x z ≤ α*r → f z = f x)
      then μ f else 0)
    convert (hpad x).trans_eq he.symm using 1
  obtain ⟨hν, hg, hprop, hgap⟩ := cobag_sampler A P μ' (fun a => hμ _) hsum
    r α π hr hα hα1 hd
  exact ⟨cobagLaw (Fintype.card V) μ', cobagSample A P r, hν, hg, hprop,
    fun x y hxy hx => hgap x y hxy hx (by
      convert hp x using 1
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> rfl)⟩

end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory Metric
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The required uniformly padded co-bag launch now has an unconditional
sampler in the original arbitrary-weight graph metric. -/
theorem graph_cobag_sampler :
    ∀ k : ℕ, 2 ≤ k → ∃ α π : ℝ, 0 < α ∧ α ≤ 1/8 ∧ 0 < π ∧ π ≤ 1 ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) (hG : G.Connected), HasTreeDecomposition G k →
      ∀ (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e),
      let : MetricSpace V := weightedMetricSpace G ℓ hG hℓ
      ∀ (A : Set V) (r : ℝ), 0 < r →
      ∃ ν : Measure (FiniteSampleSpace V), ∃ g : FiniteSampleSpace V → V → ℝ,
        IsProbabilityMeasure ν ∧ Measurable g ∧
        (∀ ω, LipschitzWith 1 (g ω) ∧ (∀ x, 0 ≤ g ω x ∧ g ω x ≤ r) ∧
          (∀ x ∈ A, g ω x = 0)) ∧
        ∀ x y, r < shortestPathDistance G ℓ x y →
          (A.Nonempty → α*r ≤ infDist x A) →
          π*α*r/4 ≤ ∫ ω, |g ω x - g ω y| ∂ν := by
  classical
  intro k hk
  obtain ⟨α,π,hα,hα8,hπ,hπ1,hpart⟩ := PaddedPartitions.uniform_padded_partitions k hk
  refine ⟨α,π,hα,hα8,hπ,hπ1,?_⟩
  intro V _ _ _ G hG hdec ℓ hℓ metric
  let _ : MetricSpace V := metric
  intro A r hr
  obtain ⟨μ,hμ,hμ1,hdiam,hpad⟩ := hpart V G hG hdec ℓ hℓ r hr
  have hd : ∀ P, 0 < μ P → ∀ x y, P x = P y → dist x y ≤ r := by
    intro P hP x y hxy
    exact hdiam P hP x y hxy
  have hp : ∀ x, π ≤ ∑ P, if (∀ z, dist x z ≤ α*r → P z = P x) then μ P else 0 := by
    intro x
    change π ≤ ∑ P, if (∀ z, shortestPathDistance G ℓ x z ≤ α*r → P z = P x) then μ P else 0
    have hx := hpad x
    unfold PaddedPartitions.paddingProbability PaddedPartitions.PaddedAt at hx
    convert! hx using 1
    apply Finset.sum_congr
    · ext; simp only [Finset.mem_univ]
    · intro P hP
      split_ifs <;> rfl
  refine finite_padded_sampler A μ r α π hμ ?_ hr hα (by linarith) hd ?_
  · convert! hμ1 using 1
    apply Finset.sum_congr
    · ext; simp only [Finset.mem_univ]
    · intro _ _; rfl
  · intro x
    convert! hp x using 1
    apply Finset.sum_congr
    · ext; simp only [Finset.mem_univ]
    · intro P hP
      split_ifs <;> rfl

end BoundedTreewidthL1.LaunchNoise

end OAI
