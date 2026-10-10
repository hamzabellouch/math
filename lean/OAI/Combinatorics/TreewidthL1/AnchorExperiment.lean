import OAI.Combinatorics.TreewidthL1.CachedEnsemble

namespace OAI

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles _root_.OAI.BoundedTreewidthL1.RootedTree TreeCache AnchorCache ParticleBatch ExpandedConstruction
open scoped ENNReal
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section

def count (k : ℕ) : ℕ := 2*(cacheBound k+1)+ k.factorial+2
instance count_neZero (k : ℕ) : NeZero (count k) := ⟨by dsimp [count]; omega⟩
def particleLip (k : ℕ) : ℝ := 3*((count k:ℝ)-1)
def upper (k : ℕ) : ℝ := (count k:ℝ)*particleLip k
lemma count_ge (k : ℕ) : 2 ≤ count k := by dsimp [count]; omega
lemma particleLip_pos (k : ℕ) : 0 < particleLip k := by
  have hh : (2:ℝ) ≤ count k := by exact_mod_cast count_ge k
  dsimp [particleLip]; linarith
lemma upper_pos (k : ℕ) : 0 < upper k := by
  have hh : 0 < count k := lt_of_lt_of_le (by omega) (count_ge k)
  exact mul_pos (by exact_mod_cast hh) (particleLip_pos k)

attribute [local instance 2000] Classical.decEq
variable {V : Type*} [Fintype V] [MetricSpace V] {n : ℕ}
variable (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (root : Fin (n+1))
  (B : Fin (n+1) → Finset V) (D : Fin (n+1) → V → ℝ) (k : ℕ) (J α π η : ℝ)
  (seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η)
variable {D α π η}
abbrev Space := (i : Fin (n+1)) → NoiseSpace (seed i).n (seed i).m
noncomputable def measure : Measure (Space seed) := Measure.pi (fun i => noiseLaw (seed i).m (seed i).mass)
instance probability : IsProbabilityMeasure (measure seed) := by
  let (i : Fin (n+1)) := (seed i).probability
  exact inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
variable (D α π η)
noncomputable def noise (ω : Space seed) (i : Fin (n+1)) (_ : Fin (n+1)) (v : V) : ℝ := noiseG (D i) (seed i).bump (ω i) v
noncomputable def states (ω : Space seed) := state (ι := Fin (count k)) (forest T hT root) B
  (active T hT root B D k dist J) (noise D α π η seed ω)
noncomputable def raw (cover : ∀ v, ∃ i, v ∈ B i) (H Δ : ℝ) (ω : Space seed) (x y : V) : ℝ :=
  cutDistance (ExpandedAnchor.law (ι := Fin (count k)) T hT root B (active T hT root B D k dist J)
    (noise D α π η seed ω) (H*((count k:ℝ)-1)+2*Δ))
    (ExpandedTree.assemble (fun i => (B i : Set V)) cover (ExpandedParticleLaw.label (ι := Fin (count k)))) x y

structure Model (cover : ∀ v, ∃ i, v ∈ B i) (run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected) where
  H : ℝ
  Δ : ℝ
  H_pos : 0 < H
  Δ_pos : 0 < Δ
  reach : ∀ ω i, FunctionParticleReachable dist 3 H (states T hT root B D k J α π η seed ω i).1
  trace : ∀ ω i p, (forest T hT root).parent i = some p →
    particleTrace (H*((count k:ℝ)-1)+2*Δ) (states T hT root B D k J α π η seed ω i).1 (B i) =
    particleTrace (H*((count k:ℝ)-1)+2*Δ) (states T hT root B D k J α π η seed ω p).1 (B i)
  pairs : ∀ ω i p, (forest T hT root).parent i = some p → ∀ a ∈
      active T hT root B D k dist J i ∩ active T hT root B D k dist J p,
    (states T hT root B D k J α π η seed ω i).2 a = (states T hT root B D k J α π η seed ω p).2 a ∧
    (states T hT root B D k J α π η seed ω i).1 ((states T hT root B D k J α π η seed ω i).2 a).1 =
      (states T hT root B D k J α π η seed ω p).1 ((states T hT root B D k J α π η seed ω p).2 a).1 ∧
    (states T hT root B D k J α π η seed ω i).1 ((states T hT root B D k J α π η seed ω i).2 a).2 =
      (states T hT root B D k J α π η seed ω p).1 ((states T hT root B D k J α π η seed ω p).2 a).2
  unique : ∀ ω i, PairUnique (active T hT root B D k dist J i) (states T hT root B D k J α π η seed ω i).2
  gap : ∀ ω i v,
    (states T hT root B D k J α π η seed ω i).1 ((states T hT root B D k J α π η seed ω i).2 i).1 v-
    (states T hT root B D k J α π η seed ω i).1 ((states T hT root B D k J α π η seed ω i).2 i).2 v =
    2*noise D α π η seed ω i i v
  nonneg : ∀ ω x y, 0 ≤ raw T hT root B D k J α π η seed cover H Δ ω x y
  integrable : ∀ x y, Integrable (fun ω => raw T hT root B D k J α π η seed cover H Δ ω x y) (measure seed)
  dim : ℕ
  map : V → PiLp (1 : ENNReal) (fun _ : Fin dim => ℝ)
  average : ∀ x y, ‖map x-map y‖ = ∫ ω, raw T hT root B D k J α π η seed cover H Δ ω x y ∂measure seed
  upper_bound : ∀ x y, ‖map x-map y‖ ≤ upper k*dist x y

namespace Model
variable {T hT root B D k J α π η seed} {cover : ∀ v, ∃ i, v ∈ B i}
  {run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected}
  (P : Model T hT root B D k J α π η seed cover run)
noncomputable def datum (ω : Space seed) :=
  CachedEnsemble.data T hT root B cover run D k dist J (states T hT root B D k J α π η seed ω)
    (P.H*((count k:ℝ)-1)+2*P.Δ) (P.pairs ω) (P.trace ω)
lemma datum_dist (ω : Space seed) (x y : V) :
    (P.datum ω).dist x y = raw T hT root B D k J α π η seed cover P.H P.Δ ω x y := rfl
lemma M_pos : 0 < P.H*((count k:ℝ)-1)+2*P.Δ := by
  have hh : (2:ℝ) ≤ count k := by exact_mod_cast count_ge k
  nlinarith [P.H_pos,P.Δ_pos]
lemma height (ω : Space seed) (i : Fin (n+1)) (r : Fin (count k)) (x : V) :
    |(states T hT root B D k J α π η seed ω i).1 r x| ≤ P.H*((count k:ℝ)-1) := by
  simpa only [Fintype.card_fin] using function_particles_height_bound P.H_pos (P.reach ω i) r x
include P
lemma lipschitz (ω : Space seed) (i : Fin (n+1)) (r : Fin (count k)) (x z : V) :
    |(states T hT root B D k J α π η seed ω i).1 r x-
      (states T hT root B D k J α π η seed ω i).1 r z| ≤ particleLip k*dist x z := by
  simpa only [Fintype.card_fin,particleLip] using function_particles_metric_bound (by norm_num : (0:ℝ)<3) (P.reach ω i) r x z
lemma pair_distinct (ω : Space seed) (i : Fin (n+1)) :
    ((states T hT root B D k J α π η seed ω i).2 i).1 ≠
    ((states T hT root B D k J α π η seed ω i).2 i).2 := by
  intro hh
  have hb := (P.unique ω i i (active_self T hT root B D k dist J i)
    i (active_self T hT root B D k dist J i) false true hh).2
  cases hb

lemma gap_probability (a : Fin (n+1)) (x : V) (C : Finset V)
    (t β γ : ℝ) (ht : 0 ≤ t) (hβ : 0 < β) (hγ : 0 < γ) (hπ : 0 ≤ π) (hx : 0 < D a x)
    (hamp : ∀ loc, GoodBump (D a) α η ((seed a).bump loc) x → ∀ s ∈ C,
      β ≤ |D a x-D a s| ∨ ∃ j, γ ≤ |(seed a).bump loc j x-(seed a).bump loc j s|)
    (hbudget : (C.card : ℝ)*(2*t/β+2*t/γ) ≤ 1/2) :
    ENNReal.ofReal (π/4) ≤ measure seed {ω : Space seed | ∀ s ∈ C, t ≤
      |positive (ι := Fin (count k)) (forest T hT root) B (active T hT root B D k dist J)
        (noise D α π η seed ω) a x-
       positive (ι := Fin (count k)) (forest T hT root) B (active T hT root B D k dist J)
        (noise D α π η seed ω) a s|} := by
  let (i : Fin (n+1)) := (seed i).probability
  let (i : Fin (n+1)) : Nonempty (NoiseSpace (seed i).n (seed i).m) :=
    nonempty_of_isProbabilityMeasure (noiseLaw (seed i).m (seed i).mass)
  apply NoiseCube.node_gap D α π η seed a x C _ _ _ t β γ ht hβ hγ hπ hx hamp hbudget
  · intro v
    apply measurable_positive
    intro i b v
    exact ((measurable_pi_apply v).comp (seed i).measurable).comp (measurable_pi_apply i)
  · exact positive_affine (forest T hT root) B (active T hT root B D k dist J)
      (fun i u => noiseG (D i) (seed i).bump u) a
      (TreeCache.fresh_eq_singleton T hT root B D k dist J a) (fun ω => P.pair_distinct ω a)

lemma height_test (X Y : Fin (n+1)) (x y z : V) (hy : y ∈ B Y) (s e l a t : ℕ)
    (he : e ≤ (forest T hT root).depth X) (hst : s ≤ t) (hte : t < e) (hat : a < t)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) dist (heights T hT root D X) J e)
    (hz : z ∈ B ((downPath T hT root X).getVert e))
    (hlen : (forest T hT Y).depth ((downPath T hT root X).getVert e) = l+(e-s))
    (hpath : ∀ b, s ≤ b → b ≤ e →
      (downPath T hT Y ((downPath T hT root X).getVert e)).getVert (l+(b-s)) = (downPath T hT root X).getVert b)
    (τ β γ : ℝ) (hτ : 0 ≤ τ) (hτΔ : τ ≤ 2*P.Δ) (hβ : 0 < β) (hγ : 0 < γ) (hπ : 0 ≤ π)
    (hx : 0 < D ((downPath T hT root X).getVert a) x)
    (hamp : ∀ loc, GoodBump (D ((downPath T hT root X).getVert a)) α η
      ((seed ((downPath T hT root X).getVert a)).bump loc) x →
      ∀ v ∈ B ((downPath T hT root X).getVert t),
        β ≤ |D ((downPath T hT root X).getVert a) x-D ((downPath T hT root X).getVert a) v| ∨
        ∃ j, γ ≤ |(seed ((downPath T hT root X).getVert a)).bump loc j x-
          (seed ((downPath T hT root X).getVert a)).bump loc j v|)
    (hbudget : ((B ((downPath T hT root X).getVert t)).card : ℝ)*(2*τ/β+2*τ/γ) ≤ 1/2) :
    (π/8)*(τ-particleLip k*dist x z) ≤ ‖P.map y-P.map z‖ := by
  let v := (downPath T hT root X).getVert
  let F := fun (ω : Space seed) => positive (ι := Fin (count k)) (forest T hT root) B
    (active T hT root B D k dist J) (noise D α π η seed ω) (v a)
  let E := {ω : Space seed | ∀ b ∈ B (v t), τ ≤ |F ω x-F ω b|}
  have hmeas (b : V) : Measurable (fun ω => F ω b) := by
    apply measurable_positive
    intro i c b
    exact ((measurable_pi_apply b).comp (seed i).measurable).comp (measurable_pi_apply i)
  have hE : MeasurableSet E := by
    simp only [E,Set.ofPred_forall]
    exact MeasurableSet.iInter (fun b => MeasurableSet.iInter (fun _ =>
      measurableSet_le measurable_const ((hmeas x).sub (hmeas b)).abs))
  have hprob : ENNReal.ofReal (π/4) ≤ measure seed E :=
    P.gap_probability (v a) x (B (v t)) τ β γ hτ hβ hγ hπ hx hamp hbudget
  have hlower (ω : Space seed) (hω : ω ∈ E) :
      (τ-particleLip k*dist x z)/2 ≤ raw T hT root B D k J α π η seed cover P.H P.Δ ω y z := by
    rw [← P.datum_dist]
    apply CachedEnsemble.height T hT root B cover run D k dist J
      (states T hT root B D k J α π η seed ω) _ (P.pairs ω) (P.trace ω)
      P.M_pos (P.unique ω) X Y y z hy s e l a t he hst hte hat ha hz hlen hpath false
      (τ-particleLip k*dist x z)
    · intro b
      change |F ω b| ≤ _
      exact (P.height ω (v a) _ b).trans (by linarith [P.Δ_pos])
    · have hh := (abs_le.mp (P.height ω (v a) ((states T hT root B D k J α π η seed ω (v a)).2 (v a)).1 z)).1
      have hn := mul_nonneg (particleLip_pos k).le (dist_nonneg (x := x) (y := z))
      simp only [pairIndex, Bool.false_eq_true, ite_false]
      change τ-particleLip k*dist x z ≤ _
      linarith
    · have hh := (abs_le.mp (P.height ω (v a) ((states T hT root B D k J α π η seed ω (v a)).2 (v a)).1 z)).2
      have hn := mul_nonneg (particleLip_pos k).le (dist_nonneg (x := x) (y := z))
      simp only [pairIndex, Bool.false_eq_true, ite_false]
      change τ-particleLip k*dist x z ≤ _
      linarith
    · exact gap_proxy dist (F ω) x z (B (v t)) (particleLip k) τ
        (P.lipschitz ω (v a) _ x z) hω
  have hh := event_lower_integral (measure seed) _ (P.integrable y z) (fun ω => P.nonneg ω y z)
    E hE (π/4) ((τ-particleLip k*dist x z)/2) (by positivity) hprob hlower
  rw [P.average]
  convert hh using 1 ; ring

lemma launch_test (hzero : ∀ i v, v ∈ B i → D i v = 0)
    (X Y : Fin (n+1)) (y z : V) (hy : y ∈ B Y) (s e l a : ℕ)
    (he : e ≤ (forest T hT root).depth X) (hsa : s ≤ a) (hae : a < e)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) dist (heights T hT root D X) J e)
    (hz : z ∈ B ((downPath T hT root X).getVert e))
    (hlen : (forest T hT Y).depth ((downPath T hT root X).getVert e) = l+(e-s))
    (hpath : ∀ b, s ≤ b → b ≤ e →
      (downPath T hT Y ((downPath T hT root X).getVert e)).getVert (l+(b-s)) = (downPath T hT root X).getVert b) :
    D ((downPath T hT root X).getVert a) z ≤ ‖P.map y-P.map z‖ := by
  let v := (downPath T hT root X).getVert
  have hp (ω : Space seed) : D (v a) z ≤ raw T hT root B D k J α π η seed cover P.H P.Δ ω y z := by
    have ht := CachedEnsemble.launch T hT root B cover run D k dist J
      (states T hT root B D k J α π η seed ω) _ (P.pairs ω) (P.trace ω)
      P.M_pos (P.unique ω) X Y y z hy s e l a he hsa hae ha hz hlen hpath
    have hbag : ∀ b ∈ B (v a),
        (states T hT root B D k J α π η seed ω (v a)).1 ((states T hT root B D k J α π η seed ω (v a)).2 (v a)).1 b =
        (states T hT root B D k J α π η seed ω (v a)).1 ((states T hT root B D k J α π η seed ω (v a)).2 (v a)).2 b := by
      intro b hb
      have hh := ((seed (v a)).bounds (ω (v a))).2.2.2 b
      rw [hzero _ _ hb] at hh
      have hg := P.gap ω (v a) b
      change _ = 2*noiseG (D (v a)) (seed (v a)).bump (ω (v a)) b at hg
      linarith
    specialize ht hbag (fun i r b => (P.height ω i r b).trans (by linarith [P.Δ_pos]))
    change |_ - _|/2 ≤ (P.datum ω).dist y z at ht
    rw [P.gap ω (v a) z,P.datum_dist] at ht
    have hh := ((seed (v a)).bounds (ω (v a))).2.2.2 z
    have ha := le_abs_self (2*noise D α π η seed ω (v a) (v a) z)
    change D (v a) z ≤ noise D α π η seed ω (v a) (v a) z ∧ _ at hh
    linarith
  rw [P.average]
  have hh := integral_mono (integrable_const (D (v a) z)) (P.integrable y z) hp
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

end Model
end
end BoundedTreewidthL1.AnchorExperiment

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles _root_.OAI.BoundedTreewidthL1.RootedTree TreeCache AnchorCache ParticleBatch ExpandedConstruction
attribute [local instance 2000] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section

/-- Every chosen actual finite ordinary seed produces the ensemble; no consistency
or global lower comparison is an assumption. -/
theorem model_exists {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (root : Fin (n+1))
    (B : Fin (n+1) → Finset V) (hne : ∀ i, (B i).Nonempty)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Connected)
    (k : ℕ) (hbag : ∀ i, (B i).card ≤ k) (J α π η : ℝ) :
    let := weightedMetricSpace G ℓ hG hℓ
    let D := fun i => bagDistance G ℓ (B i) (hne i)
    ∀ seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η,
    ∃ P : Model T hT root B D k J α π η seed hcover (fun v => (hrun v).preconnected),
      ∀ i v, D i v ≤ P.Δ := by
  let := weightedMetricSpace G ℓ hG hℓ
  let D := fun i => bagDistance G ℓ (B i) (hne i)
  dsimp only
  intro seed
  let A := active T hT root B D k dist J
  let q := cacheBound k+1
  let R := forest T hT root
  let g := noise D α π η seed
  let S := states T hT root B D k J α π η seed
  let H : ℝ := 1+3*∑ i, ∑ v, D i v
  let Δ : ℝ := 1+∑ i, ∑ v, D i v
  have hD : ∀ i v, 0 ≤ D i v := fun i v =>
    bagDistance_nonneg G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) v
  have hsum : 0 ≤ ∑ i, ∑ v, D i v :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun v _ => hD i v))
  have hH : 0 < H := by dsimp [H]; positivity
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hdSum (i : Fin (n+1)) (v : V) : D i v ≤ ∑ j, ∑ x, D j x := by
    apply (Finset.single_le_sum (fun x (_ : x ∈ (Finset.univ : Finset V)) => hD i x) (Finset.mem_univ v)).trans
    exact Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n+1)))) =>
      Finset.sum_nonneg (fun x _ => hD j x)) (Finset.mem_univ i)
  have hdH (i : Fin (n+1)) (v : V) : (5/2)*D i v ≤ H := by
    dsimp [H]; linarith [hdSum i v,hD i v]
  have hg : ∀ i a v, Measurable (fun ω => g ω i a v) := by
    intro i a v
    exact ((measurable_pi_apply v).comp (seed i).measurable).comp (measurable_pi_apply i)
  have hLip : ∀ ω i a u v, |g ω i a u-g ω i a v| ≤ 3*shortestPathDistance G ℓ u v := by
    intro ω i a u v
    exact ((seed i).bounds (ω i)).2.2.1.dist_le_mul u v
  have hHeight : ∀ ω i a v, |g ω i a v| ≤ H := by
    intro ω i a v
    have hb := ((seed i).bounds (ω i)).2.2.2 v
    change |noiseG (D i) (seed i).bump (ω i) v| ≤ H
    rw [abs_of_nonneg ((hD i v).trans hb.1)]
    exact hb.2.trans (hdH i v)
  have hz : ∀ ω i a v, v ∈ B i → g ω i a v = 0 := by
    intro ω i a v hv
    have hb := ((seed i).bounds (ω i)).2.2.2 v
    have he : D i v = 0 := by
      rw [show D i v = Metric.infDist v (B i : Set V) from
        bagDistance_eq_infDist G hG ℓ hℓ (B i) (hne i) v]
      exact Metric.infDist_zero_of_mem hv
    change D i v ≤ g ω i a v ∧ g ω i a v ≤ (5/2)*D i v at hb
    rw [he] at hb
    exact le_antisymm (by simpa only [mul_zero] using hb.2) hb.1
  have hA : ∀ i, (A i).card ≤ q :=
    graph_active_bound G ℓ hG hℓ T B hne hT root hedge hrun k hbag J
  have hN : Fintype.card (Fin (count k)) = 2*q+k.factorial+2 := by exact Fintype.card_fin _
  have hf (ω : Space seed) := forest_particle_realization (ι := Fin (count k)) R B A k q hbag hA
    hN dist 3 H Δ hH hΔ (g ω) (hLip ω) (hHeight ω) (hz ω)
  obtain ⟨hwn,hwt,hwi,m,Φ,hΦ,hup,hco⟩ := ExpandedAnchor.realization (ι := Fin (count k))
    G hG ℓ hℓ T hT root B hcover hedge (fun v => (hrun v).preconnected) A k q hbag hA hN
    (measure seed) 3 H Δ (by norm_num) hH hΔ g hg hLip hHeight hz
  let P : Model T hT root B D k J α π η seed hcover (fun v => (hrun v).preconnected) := {
    H := H, Δ := Δ, H_pos := hH, Δ_pos := hΔ
    reach := fun ω i => (hf ω).1 i
    trace := fun ω i p hp => by simpa only [states,R,A,g,Fintype.card_fin] using (hf ω).2.1 i p hp
    pairs := fun ω i p hp a ha => (hf ω).2.2.1 i p hp a (by simpa only [Finset.mem_inter] using ha)
    unique := fun ω => state_unique R B A (g ω) k q hN hbag hA
    gap := fun ω i v => by
      apply ((hf ω).2.2.2 i i ?_).2 v
      rw [show fresh R A i = {i} from fresh_eq_singleton T hT root B D k dist J i]
      exact Finset.mem_singleton_self i
    nonneg := fun ω x y => Finset.sum_nonneg (fun c _ => by split_ifs; exact le_rfl; simpa only [Fintype.card_fin] using hwn ω c)
    integrable := fun x y => by
      apply integrable_finsetSum
      intro c _
      split_ifs
      · exact integrable_zero _ _ _
      · simpa only [Fintype.card_fin] using hwi c
    dim := m
    map := Φ
    average := fun x y => by simpa only [raw,A,g,Fintype.card_fin] using hΦ x y
    upper_bound := fun x y => by
      change ‖Φ x-Φ y‖ ≤ upper k*shortestPathDistance G ℓ x y
      convert hup x y using 1 ; simp only [Fintype.card_fin,upper,particleLip] ; ring }
  refine ⟨P,?_⟩
  intro i v
  change D i v ≤ Δ
  dsimp [Δ]; linarith [hdSum i v]
end
end BoundedTreewidthL1.AnchorExperiment

end OAI
