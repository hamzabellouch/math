import OAI.Analysis.KadisonKastler.UnitBallClosure
import OAI.Analysis.FactorGeneration.Bicommutant

namespace OAI

/-! # Nearby separable test algebras

Countably many generators are enlarged alternately by nearby contractions.
The increasing norm closures give the two separable C*-algebras in §9.
All choices and closure estimates are constructed here; there is no
separable-reduction hypothesis.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def cstarHull (s : Set (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (StarAlgebra.adjoin ℂ s).topologicalClosure

def starAlgebraBall (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  {x | x ∈ A ∧ ‖x‖ ≤ 1}

theorem zero_mem_starAlgebraBall (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    0 ∈ starAlgebraBall A := ⟨A.zero_mem, by simp⟩

theorem cstarHull_mono : Monotone (cstarHull (H := H)) :=
  fun _ _ h => StarSubalgebra.topologicalClosure_mono (StarAlgebra.adjoin_mono h)

theorem subset_cstarHull (s : Set (H →L[ℂ] H)) : s ⊆ cstarHull s :=
  (StarAlgebra.subset_adjoin ℂ s).trans (StarSubalgebra.le_topologicalClosure _)

theorem cstarHull_le {s : Set (H →L[ℂ] H)} (M : VonNeumannAlgebra H)
    (hs : s ⊆ M) : cstarHull s ≤ M.toStarSubalgebra :=
  StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le hs) (isClosed_algebra M)

theorem isSeparable_cstarHull {s : Set (H →L[ℂ] H)} (hs : s.Countable) :
    IsSeparable (cstarHull s : Set (H →L[ℂ] H)) :=
  (Generator.separable_countable_star_adjoin hs).closure

omit [CompleteSpace H] in
/-- The bound on distance to a fixed set passes through norm closure. -/
theorem infDist_le_of_mem_closure {s t : Set (H →L[ℂ] H)} {r : ℝ}
    (h : ∀ x ∈ s, Metric.infDist x t ≤ r) {x : H →L[ℂ] H}
    (hx : x ∈ closure s) : Metric.infDist x t ≤ r :=
  closure_minimal h (isClosed_le (Metric.continuous_infDist_pt t) continuous_const) hx

/-- Add a countable family of near approximants to the second seed set. -/
theorem exists_separable_seed_extension (M N : VonNeumannAlgebra H)
    {s t : Set (H →L[ℂ] H)} (hs : s.Countable) (ht : t.Countable)
    (hsM : s ⊆ M) (htN : t ⊆ N) {r : ℝ} (hr : kkDistance M N < r) :
    ∃ t' : Set (H →L[ℂ] H), t'.Countable ∧ t ⊆ t' ∧ t' ⊆ N ∧
      ∀ x ∈ starAlgebraBall (cstarHull s),
        Metric.infDist x (starAlgebraBall (cstarHull t')) ≤ r := by
  obtain ⟨D, hDsub, hDc, hDdense⟩ :=
    ((isSeparable_cstarHull hs).mono
      (show starAlgebraBall (cstarHull s) ⊆ (cstarHull s : Set (H →L[ℂ] H)) from
        fun _ hx => hx.1)).exists_countable_dense_subset
  have happrox : ∀ x : D, ∃ y ∈ unitBall N, ‖(x : H →L[ℂ] H) - y‖ < r := by
    intro x
    have hx := hDsub x.property
    exact exists_unitBall_approx ⟨cstarHull_le M hsM hx.1, hx.2⟩ hr
  choose f hf hdist using happrox
  let t' := t ∪ Set.range f
  have htc : t'.Countable := by
    let : Countable D := hDc.to_subtype
    exact ht.union (Set.countable_range f)
  refine ⟨t', htc, Set.subset_union_left, ?_, ?_⟩
  · rintro y (hy | ⟨x, rfl⟩)
    · exact htN hy
    · exact (hf x).1
  · intro x hx
    apply infDist_le_of_mem_closure (s := D) ?_ (hDdense hx)
    intro y hy
    have hy' : f ⟨y, hy⟩ ∈ starAlgebraBall (cstarHull t') :=
      ⟨subset_cstarHull t' (Or.inr ⟨⟨y, hy⟩, rfl⟩), (hf ⟨y, hy⟩).2⟩
    exact (Metric.infDist_le_dist_of_mem hy').trans
      (by simpa only [dist_eq_norm] using (hdist ⟨y, hy⟩).le)

structure SeparableSeeds (M N : VonNeumannAlgebra H) where
  left : Set (H →L[ℂ] H)
  right : Set (H →L[ℂ] H)
  left_countable : left.Countable
  right_countable : right.Countable
  left_mem : left ⊆ M
  right_mem : right ⊆ N

def SeparableSeeds.Extends {M N : VonNeumannAlgebra H}
    (p q : SeparableSeeds M N) (r : ℝ) : Prop :=
  p.left ⊆ q.left ∧ p.right ⊆ q.right ∧
  (∀ x ∈ starAlgebraBall (cstarHull p.left),
    Metric.infDist x (starAlgebraBall (cstarHull q.right)) ≤ r) ∧
  (∀ x ∈ starAlgebraBall (cstarHull p.right),
    Metric.infDist x (starAlgebraBall (cstarHull q.left)) ≤ r)

theorem SeparableSeeds.exists_extension {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) :
    ∃ q : SeparableSeeds M N, p.Extends q r := by
  obtain ⟨t, htc, hpt, htN, hnear₁⟩ := exists_separable_seed_extension M N
    p.left_countable p.right_countable p.left_mem p.right_mem hr
  obtain ⟨s, hsc, hps, hsM, hnear₂⟩ := exists_separable_seed_extension N M
    p.right_countable p.left_countable p.right_mem p.left_mem
    (by simpa only [kkDistance_comm N M] using hr)
  exact ⟨⟨s, t, hsc, htc, hsM, htN⟩, hps, hpt, hnear₁, hnear₂⟩

def SeparableSeeds.next {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) : SeparableSeeds M N :=
  Classical.choose (p.exists_extension hr)

theorem SeparableSeeds.next_spec {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) :
    p.Extends (p.next hr) r := Classical.choose_spec (p.exists_extension hr)

def SeparableSeeds.stages {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) : ℕ → SeparableSeeds M N
  | 0 => p
  | n + 1 => (p.stages hr n).next hr

theorem SeparableSeeds.stages_left_mono {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) :
    Monotone (fun n => (p.stages hr n).left) :=
  monotone_nat_of_le_succ (fun n => ((p.stages hr n).next_spec hr).1)

theorem SeparableSeeds.stages_right_mono {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) :
    Monotone (fun n => (p.stages hr n).right) :=
  monotone_nat_of_le_succ (fun n => ((p.stages hr n).next_spec hr).2.1)

def increasingCstarClosure (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) :
    StarSubalgebra ℂ (H →L[ℂ] H) := (iSup A).topologicalClosure

theorem le_increasingCstarClosure (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) (n : ℕ) :
    A n ≤ increasingCstarClosure A :=
  (le_iSup A n).trans (StarSubalgebra.le_topologicalClosure _)

theorem isSeparable_increasingCstarClosure
    (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) (hA : Monotone A)
    (hsep : ∀ n, IsSeparable (A n : Set (H →L[ℂ] H))) :
    IsSeparable (increasingCstarClosure A : Set (H →L[ℂ] H)) := by
  apply IsSeparable.closure
  rw [StarSubalgebra.coe_iSup_of_directed hA.directed_le]
  exact IsSeparable.iUnion hsep

theorem infDist_increasingCstarClosure_ball
    (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) (hA : Monotone A)
    (t : Set (H →L[ℂ] H)) {r : ℝ}
    (hnear : ∀ n, ∀ x ∈ starAlgebraBall (A n), Metric.infDist x t ≤ r) :
    ∀ x ∈ starAlgebraBall (increasingCstarClosure A), Metric.infDist x t ≤ r := by
  intro x hx
  apply infDist_le_of_mem_closure (s := starAlgebraBall (iSup A)) ?_ ?_
  · intro y hy
    have hymem : y ∈ ⋃ n, (A n : Set (H →L[ℂ] H)) := by
      rw [← StarSubalgebra.coe_iSup_of_directed hA.directed_le]
      exact hy.1
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hymem
    exact hnear n y ⟨hn, hy.2⟩
  · change x ∈ closure {y | y ∈ (iSup A).toSubalgebra.toSubmodule ∧ ‖y‖ ≤ 1}
    rw [closure_submodule_unitBall]
    exact hx

/-- The alternating countable construction produces nearby closed separable
test algebras containing any prescribed finite operator tests. -/
theorem exists_near_separable_algebra_pair_countable (M N : VonNeumannAlgebra H)
    (E F : Set (H →L[ℂ] H)) (hEc : E.Countable) (hFc : F.Countable)
    (hE : ∀ x ∈ E, x ∈ M) (hF : ∀ x ∈ F, x ∈ N)
    {g : ℝ} (hg : kkDistance M N < g) :
    ∃ A B : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (A : Set (H →L[ℂ] H)) ∧ IsClosed (B : Set (H →L[ℂ] H)) ∧
      IsSeparable (A : Set (H →L[ℂ] H)) ∧ IsSeparable (B : Set (H →L[ℂ] H)) ∧
      A ≤ M.toStarSubalgebra ∧ B ≤ N.toStarSubalgebra ∧
      (∀ x ∈ E, x ∈ A) ∧ (∀ x ∈ F, x ∈ B) ∧
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < g := by
  obtain ⟨r, hr, hrg⟩ := exists_between hg
  let p : SeparableSeeds M N :=
    ⟨E, F, hEc, hFc, hE, hF⟩
  let A (n : ℕ) := cstarHull (p.stages hr n).left
  let B (n : ℕ) := cstarHull (p.stages hr n).right
  have hA : Monotone A := cstarHull_mono.comp (p.stages_left_mono hr)
  have hB : Monotone B := cstarHull_mono.comp (p.stages_right_mono hr)
  have hAM : increasingCstarClosure A ≤ M.toStarSubalgebra :=
    StarSubalgebra.topologicalClosure_minimal
      (iSup_le fun n => cstarHull_le M (p.stages hr n).left_mem) (isClosed_algebra M)
  have hBN : increasingCstarClosure B ≤ N.toStarSubalgebra :=
    StarSubalgebra.topologicalClosure_minimal
      (iSup_le fun n => cstarHull_le N (p.stages hr n).right_mem) (isClosed_algebra N)
  refine ⟨increasingCstarClosure A, increasingCstarClosure B,
    StarSubalgebra.isClosed_topologicalClosure _, StarSubalgebra.isClosed_topologicalClosure _,
    isSeparable_increasingCstarClosure A hA
      (fun n => isSeparable_cstarHull (p.stages hr n).left_countable),
    isSeparable_increasingCstarClosure B hB
      (fun n => isSeparable_cstarHull (p.stages hr n).right_countable),
    hAM, hBN, ?_, ?_, ?_⟩
  · intro x hx
    exact le_increasingCstarClosure A 0 (subset_cstarHull p.left hx)
  · intro x hx
    exact le_increasingCstarClosure B 0 (subset_cstarHull p.right hx)
  · apply lt_of_le_of_lt (Metric.hausdorffDist_le_of_infDist
      ((kkDistance_nonneg M N).trans hr.le) ?_ ?_) hrg
    · apply infDist_increasingCstarClosure_ball A hA
      intro n x hx
      have hnext := ((p.stages hr n).next_spec hr).2.2.1 x hx
      apply le_trans (Metric.infDist_le_infDist_of_subset (t :=
        starAlgebraBall (increasingCstarClosure B)) ?_
        ⟨0, zero_mem_starAlgebraBall _⟩) hnext
      intro y hy
      exact ⟨le_increasingCstarClosure B (n + 1) hy.1, hy.2⟩
    · apply infDist_increasingCstarClosure_ball B hB
      intro n x hx
      have hnext := ((p.stages hr n).next_spec hr).2.2.2 x hx
      apply le_trans (Metric.infDist_le_infDist_of_subset (t :=
        starAlgebraBall (increasingCstarClosure A)) ?_
        ⟨0, zero_mem_starAlgebraBall _⟩) hnext
      intro y hy
      exact ⟨le_increasingCstarClosure A (n + 1) hy.1, hy.2⟩

/-- Finite prescribed tests are a special case of the countable construction. -/
theorem exists_near_separable_algebra_pair (M N : VonNeumannAlgebra H)
    (E F : Finset (H →L[ℂ] H)) (hE : ∀ x ∈ E, x ∈ M) (hF : ∀ x ∈ F, x ∈ N)
    {g : ℝ} (hg : kkDistance M N < g) :
    ∃ A B : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (A : Set (H →L[ℂ] H)) ∧ IsClosed (B : Set (H →L[ℂ] H)) ∧
      IsSeparable (A : Set (H →L[ℂ] H)) ∧ IsSeparable (B : Set (H →L[ℂ] H)) ∧
      A ≤ M.toStarSubalgebra ∧ B ≤ N.toStarSubalgebra ∧
      (∀ x ∈ E, x ∈ A) ∧ (∀ x ∈ F, x ∈ B) ∧
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < g :=
  exists_near_separable_algebra_pair_countable M N E F E.countable_toSet F.countable_toSet hE hF hg

end

end KadisonKastler

end OAI
