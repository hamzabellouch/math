import Mathlib
import OAI.Geometry.HyperbolicGroups.MetricProduct

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators ENNReal
noncomputable section
noncomputable section
open Filter Topology
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Filter Topology

namespace HyperbolicObstruction

/-- A conditional star: branches agree exactly on the named fields.
The finite law placed on it below need not be uniform. -/
def ConditionalStar {F L Ω : Type*} [DecidableEq F] (label : Ω → F → L)
    (I : Finset F) (k : ℕ) :=
  {b : Fin (k + 1) → Ω // ∀ j i, i ∈ I → label (b j) i = label (b 0) i}

namespace ConditionalStar
variable {F L Ω : Type*} [DecidableEq F] {label : Ω → F → L} {I : Finset F} {k : ℕ}
instance [Fintype Ω] [DecidableEq L] : Fintype (ConditionalStar label I k) :=
  inferInstanceAs (Fintype {branches : Fin (k + 1) → Ω //
    ∀ branch field, field ∈ I → label (branches branch) field = label (branches 0) field})

def branch (j : Fin (k + 1)) (b : ConditionalStar label I k) : Ω := b.val j

lemma agree (b : ConditionalStar label I k) (j : Fin (k + 1)) (i : F) (hi : i ∈ I) :
    label (branch j b) i = label (branch 0 b) i := b.property j i hi

end ConditionalStar

/-- Only combinatorial sampling assertions occur here, independent of the action
that may be chosen after the random tables have been exposed. This is not a
replacement for the random-table producer. -/
structure SamplingSequence (F : Type*) [DecidableEq F] (Admissible : Finset F → Prop)
    (L Ω : ℕ → Type*) [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
    [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
    (label : ∀ n, Ω n → F → L n) where
  singleton : ∀ e : F, Tendsto (fun n =>
    ((FiniteLaw.uniform : FiniteLaw (Ω n)).map (fun a => label n a e)).totalVariation
      FiniteLaw.uniform) atTop (𝓝 0)
  star : ∀ (I : Finset F) (e : F), e ∉ I → Admissible (insert e I) → ∀ k : ℕ,
    ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      ∃ κ : FiniteLaw (ConditionalStar (label n) I k),
        (∀ j, (κ.map (ConditionalStar.branch j)).totalVariation FiniteLaw.uniform ≤ η n) ∧
        (κ.map (fun b j => label n (ConditionalStar.branch j b) e)).totalVariation
          (FiniteLaw.uniform : FiniteLaw (Fin (k + 1) → L n)) ≤ η n

/-- Actual normalized orbit points along a symmetric finite generator list. -/
structure EnergyOrbit (L X : Type*) [Fintype L] [MetricSpace X] (M : ℝ) where
  cat : CATZero X
  base : X
  isom : L → X ≃ᵢ X
  inverse : L ≃ L
  symmetric : ∀ i, isom (inverse i) = (isom i).symm
  minimum : ∀ y : X, (∑ i, dist base (isom i base) ^ 2) ≤ ∑ i, dist y (isom i y) ^ 2
  energy : (𝔼 i, dist base (isom i base) ^ 2) = 1
  bound : ∀ i, dist base (isom i base) ≤ M

namespace EnergyOrbit
variable {L X : Type*} [Fintype L] [MetricSpace X] {M : ℝ} (O : EnergyOrbit L X M)

abbrev Cone := TangentCone O.cat O.base
abbrev cone : ConeData O.Cone := TangentCone.coneData O.cat O.base

def vector (i : L) : O.Cone := TangentCone.log O.cat O.base (O.isom i O.base)

lemma normSq_vector (i : L) : O.cone.normSq (O.vector i) = dist O.base (O.isom i O.base) ^ 2 :=
  TangentCone.normSq_log O.cat O.base _

lemma norm_vector (i : L) : dist O.cone.vertex (O.vector i) = dist O.base (O.isom i O.base) := by
  have he := O.normSq_vector i
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp he

lemma barycenter (u : O.Cone) : (𝔼 i, O.cone.pairing u (O.vector i)) ≤ 0 := by
  rw [Fintype.expect_eq_sum_div_card]
  exact div_nonpos_of_nonpos_of_nonneg
    (energy_tangent_barycenter O.cat O.isom O.inverse O.symmetric O.base O.minimum u)
    (by positivity)

lemma energy_vector : (𝔼 i, O.cone.normSq (O.vector i)) = 1 := by
  simp_rw [O.normSq_vector]
  exact O.energy

lemma barycenter_read (σ : L ≃ L) (u : O.Cone) :
    (𝔼 i, O.cone.pairing u (O.vector (σ i))) ≤ 0 := by
  rw [Fintype.expect_eq_sum_div_card, σ.sum_comp (fun i => O.cone.pairing u (O.vector i))]
  simpa only [Fintype.expect_eq_sum_div_card] using O.barycenter u

lemma energy_read (σ : L ≃ L) : (𝔼 i, O.cone.normSq (O.vector (σ i))) = 1 := by
  rw [Fintype.expect_eq_sum_div_card, σ.sum_comp (fun i => O.cone.normSq (O.vector i))]
  simpa only [Fintype.expect_eq_sum_div_card] using O.energy_vector

end EnergyOrbit

namespace SamplingSequence
universe u v w
variable {F : Type u} [DecidableEq F] {Admissible : Finset F → Prop}
  {L Ω : ℕ → Type v} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → F → L n} (S : SamplingSequence F Admissible L Ω label)
  {X : ℕ → Type w} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)

include S

/-- The conditional test applies to arbitrary bounded action-dependent tests,
including tests using inverses of any field labels. -/
theorem conditional {I : Finset F} {e : F} (he : e ∉ I) (hI : Admissible (insert e I))
    (σ : ∀ n, L n ≃ L n) (test : ∀ n, Ω n → (O n).Cone)
    (depends : ∀ n a b, (∀ i ∈ I, label n a i = label n b i) → test n a = test n b)
    {B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (htest : ∀ n a, dist (O n).cone.vertex (test n a) ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (𝔼 a, (O n).cone.pairing (test n a) ((O n).vector (σ n (label n a e)))) < ε := by
  apply conditional_test_eventually
  intro k
  obtain ⟨η, hη, hκ⟩ := S.star I e he hI k
  refine ⟨η, hη, ?_⟩
  filter_upwards [hκ] with n hn
  obtain ⟨κ, hbranch, hleaf⟩ := hn
  have hh := (O n).cone.conditional_test (TangentCone.catZero (O n).cat (O n).base)
    (FiniteLaw.uniform : FiniteLaw (Ω n)) κ (fun i => (O n).vector (σ n i))
    ((O n).barycenter_read (σ n)) ((O n).energy_read (σ n))
    (test n) (fun a => label n a e) k ConditionalStar.branch
    (fun j b => depends n _ _ (fun i hi => ConditionalStar.agree b j i hi)) hM hB
    (fun i => by rw [(O n).norm_vector]; exact (O n).bound _)
    (htest n) hbranch hleaf
  rwa [FiniteLaw.expect_uniform] at hh

/-- Single-field convergence remains usable uniformly after the action has
been chosen: the displacement functions only need the uniform letter bound. -/
theorem edge_energy (e : F) (σ : ∀ n, L n ≃ L n) (hM : 0 ≤ M) :
    Tendsto (fun n => 𝔼 a, dist (O n).base ((O n).isom (σ n (label n a e)) (O n).base) ^ 2)
      atTop (𝓝 1) := by
  let η (n : ℕ) := ((FiniteLaw.uniform : FiniteLaw (Ω n)).map (fun a => label n a e)).totalVariation
    FiniteLaw.uniform
  have he : ∀ n, |(𝔼 a, dist (O n).base ((O n).isom (σ n (label n a e)) (O n).base) ^ 2) - 1| ≤
      2 * M ^ 2 * η n := by
    intro n
    have hb : ∀ i, |dist (O n).base ((O n).isom (σ n i) (O n).base) ^ 2| ≤ M ^ 2 := by
      intro i
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ dist_nonneg hM).mpr ((O n).bound _)
    have hh := (((FiniteLaw.uniform : FiniteLaw (Ω n)).map (fun a => label n a e))).expect_sub_bound
      FiniteLaw.uniform (fun i => dist (O n).base ((O n).isom (σ n i) (O n).base) ^ 2) hb
    simp only [FiniteLaw.expect_map, FiniteLaw.expect_uniform, Fintype.expect_eq_sum_div_card,
      Function.comp_def] at hh
    rw [(σ n).sum_comp (fun i => dist (O n).base ((O n).isom i (O n).base) ^ 2)] at hh
    have hn := (O n).energy
    rw [Fintype.expect_eq_sum_div_card] at hn
    rw [hn] at hh
    simpa only [Fintype.expect_eq_sum_div_card] using hh
  have ht : Tendsto (fun n => 2 * M ^ 2 * η n) atTop (𝓝 0) := by
    simpa using (S.singleton e).const_mul (2 * M ^ 2)
  have hz : Tendsto (fun n => (𝔼 a, dist (O n).base ((O n).isom (σ n (label n a e)) (O n).base) ^ 2) - 1) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ ht
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs] using he n
  have hh := hz.add_const 1
  simpa only [sub_add_cancel, zero_add] using hh

end SamplingSequence
end HyperbolicObstruction


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace EnergyOrbit

/-- Six-letter relative counts provide the bound M=8 for the rescaled genuine
geometric action; no bound on the action is assumed before sampling. -/
theorem exists_of_geometric {L G X : Type*} [Fintype L] [Nonempty L] [Group G]
    [Infinite G] [MetricSpace X] [Nonempty X] [ProperSpace X]
    (hX : CATZero X) (A : GeometricAction G X) (letter : L → G) (inv : L ≃ L)
    (hinv : ∀ i, letter (inv i) = (letter i)⁻¹)
    (hgen : Subgroup.closure (Set.range letter) = ⊤)
    (Row : L → Type*) [∀ i, Fintype (Row i)] (κ : ∀ i, FiniteLaw (Row i))
    (row : ∀ i, Row i → Fin 5 → L)
    (hrow : ∀ i b, (List.ofFn (letter ∘ row i b)).prod = (letter i)⁻¹)
    (hmarg : ∀ i j a, ((κ i).map (fun b => row i b j)).mass a ≤ 2 / Fintype.card L) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ O : EnergyOrbit L (MetricScale.Space r hr X) 8,
      ∀ i, O.isom i = MetricScale.action A.act (letter i) := by
  obtain ⟨r, hr, o, hen, hmin⟩ := IsometricAction.normalized_minimum A letter hgen
  refine ⟨r, hr, ⟨MetricScale.catZero hX, o, fun i => MetricScale.action A.act (letter i),
    inv, ?_, hmin, hen, ?_⟩, fun _ => rfl⟩
  · intro i
    rw [hinv, map_inv]
    rfl
  · intro i
    have hh := IsometricAction.six_letter_displacement_bound
      (MetricScale.action A.act) o letter hen (letter i) (κ i) (row i) (hrow i) (hmarg i)
    nlinarith [dist_nonneg (x := o) (y := MetricScale.action A.act (letter i) o)]

end EnergyOrbit

namespace IsometricAction
variable {G X : Type*} [Group G] [MetricSpace X]

lemma displacement_mul_dist (A : G →* (X ≃ᵢ X)) (o : X) (g k : G) :
    dist o (A (g * k) o) = dist (A g⁻¹ o) (A k o) := by
  have hh := (A g).isometry.dist_eq (A g⁻¹ o) (A k o)
  have hg : A g (A g⁻¹ o) = o := by
    rw [← IsometryEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hg, ← IsometryEquiv.mul_apply, ← map_mul] at hh
  exact hh

end IsometricAction

namespace OrbitWord
variable {F L Ω G X : Type*} [Group G]

def word (label : Ω → F → L) (σ : F → L ≃ L) (letter : L → G) (a : Ω) (w : List F) : G :=
  (w.map (fun e => letter (σ e (label a e)))).prod

lemma nil (label : Ω → F → L) (σ : F → L ≃ L) (letter : L → G) (a : Ω) :
    word label σ letter a [] = 1 := rfl

lemma cons (label : Ω → F → L) (σ : F → L ≃ L) (letter : L → G) (a : Ω) (e : F) (w : List F) :
    word label σ letter a (e :: w) = letter (σ e (label a e)) * word label σ letter a w := rfl

lemma depends (label : Ω → F → L) (σ : F → L ≃ L) (letter : L → G) (a b : Ω) (w : List F)
    (he : ∀ i ∈ w, label a i = label b i) : word label σ letter a w = word label σ letter b w := by
  unfold word
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [he i hi]

lemma bound [MetricSpace X] (A : G →* (X ≃ᵢ X)) (o : X) (label : Ω → F → L)
    (σ : F → L ≃ L) (letter : L → G) {M : ℝ}
    (hb : ∀ i, dist o (A (letter i) o) ≤ M) (a : Ω) (w : List F) :
    dist o (A (word label σ letter a w) o) ≤ w.length * M := by
  induction w with
  | nil => simp [nil]
  | cons e w ih =>
    rw [cons]
    have hh := (IsometricAction.displacement_mul_le A o (letter (σ e (label a e))) _).trans (add_le_add (hb (σ e (label a e))) ih)
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm M] using hh

end OrbitWord

namespace SamplingSequence
universe u v w z
variable {F : Type u} [DecidableEq F] {Admissible : Finset F → Prop}
  {L Ω : ℕ → Type v} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → F → L n} (S : SamplingSequence F Admissible L Ω label)
  {X : ℕ → Type w} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)
  {G : ℕ → Type z} [∀ n, Group (G n)]
  (A : ∀ n, G n →* (X n ≃ᵢ X n)) (letter : ∀ n, L n → G n)
  (hact : ∀ n i, A n (letter n i) = (O n).isom i)
include S hact

/-- Path lower bounds are produced from the sampling assertions and the action,
not postulated as a limiting configuration. The proof uses only finite sums and
one-sided vanishing errors, so the spaces/actions can vary with n. -/
theorem word_lower (down : ∀ I J, I ⊆ J → Admissible J → Admissible I)
    (σ : ∀ n, F → L n ≃ L n) (hM : 0 ≤ M) (w : List F) (hw : w.Nodup)
    (hadm : Admissible w.toFinset) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (w.length : ℝ) - ε ≤
        𝔼 a, dist (O n).base (A n (OrbitWord.word (label n) (σ n) (letter n) a w) (O n).base) ^ 2 := by
  induction w with
  | nil =>
    intro ε hε
    filter_upwards [] with n
    simpa [OrbitWord.nil] using hε.le
  | cons e w ih =>
    have hnot : e ∉ w.toFinset := by simpa using (List.nodup_cons.mp hw).1
    have hadm' : Admissible w.toFinset := down _ _ (by simp) hadm
    have hw' := (List.nodup_cons.mp hw).2
    let test (n : ℕ) (a : Ω n) : (O n).Cone := TangentCone.log (O n).cat (O n).base
      (A n (OrbitWord.word (label n) (σ n) (letter n) a w) (O n).base)
    let σ' (n : ℕ) : L n ≃ L n := (σ n e).trans (O n).inverse
    have htest : ∀ n a, dist (O n).cone.vertex (test n a) ≤ w.length * M := by
      intro n a
      change dist (TangentCone.vertex (O n).cat (O n).base) (test n a) ≤ _
      rw [TangentCone.dist_vertex_log]
      exact OrbitWord.bound (A n) (O n).base (label n) (σ n) (letter n)
        (fun i => by rw [hact]; exact (O n).bound i) a w
    have hc := S.conditional O hnot (by simpa using hadm) σ' test
      (fun n a b hab => by
        dsimp only [test]
        rw [OrbitWord.depends (label n) (σ n) (letter n) a b w
          (fun i hi => hab i (by simpa using hi))])
      hM (mul_nonneg (by positivity) hM) htest
    have hedge := S.edge_energy O e σ' hM
    have hineq (n : ℕ) :
        (𝔼 a, dist (O n).base (A n (OrbitWord.word (label n) (σ n) (letter n) a w) (O n).base) ^ 2) +
        (𝔼 a, dist (O n).base ((O n).isom (σ' n (label n a e)) (O n).base) ^ 2) -
        2 * (𝔼 a, (O n).cone.pairing (test n a) ((O n).vector (σ' n (label n a e)))) ≤
        𝔼 a, dist (O n).base (A n (OrbitWord.word (label n) (σ n) (letter n) a (e :: w)) (O n).base) ^ 2 := by
      rw [← Finset.expect_add_distrib, Finset.mul_expect, ← Finset.expect_sub_distrib]
      apply Finset.expect_le_expect
      intro a _
      have he : (O n).isom (σ' n (label n a e)) = (A n (letter n (σ n e (label n a e)))).symm := by
        simpa only [σ', Equiv.trans_apply, hact] using (O n).symmetric (σ n e (label n a e))
      have hp := TangentCone.pairing_log_ge (O n).cat (O n).base
        (A n (OrbitWord.word (label n) (σ n) (letter n) a w) (O n).base)
        ((O n).isom (σ' n (label n a e)) (O n).base)
      have hd : dist (O n).base (A n (OrbitWord.word (label n) (σ n) (letter n) a (e :: w)) (O n).base) =
          dist (A n (OrbitWord.word (label n) (σ n) (letter n) a w) (O n).base)
            ((O n).isom (σ' n (label n a e)) (O n).base) := by
        rw [OrbitWord.cons, IsometricAction.displacement_mul_dist, dist_comm, he, map_inv]
        rfl
      rw [hd]
      change _ - 2 * (O n).cone.pairing
        (TangentCone.log (O n).cat (O n).base _) (TangentCone.log (O n).cat (O n).base _) ≤ _
      linarith
    intro ε hε
    have h1 := ih hw' hadm' (ε / 3) (by positivity)
    have h2 := hedge.eventually (lt_mem_nhds (show 1 - ε / 3 < (1 : ℝ) by linarith))
    have h3 := hc (ε / 6) (by positivity)
    filter_upwards [h1, h2, h3] with n hn₁ hn₂ hn₃
    have hh := hineq n
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

end SamplingSequence
end HyperbolicObstruction

noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

lemma isometry_segment (h : CATZero X) (e : X ≃ᵢ X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    e (segment h x y t) = segment h (e x) (e y) t :=
  map_segment_of_dist h h e (fun a b => (e.isometry.dist_eq a b).le) x y
    (e.isometry.dist_eq x y) ht

/-- Comparison at fixed fractions is taken before forming the ultralimit. -/
lemma fractional_log_comparison (h : CATZero X) (o x y : X) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    a ^ 2 * dist o x ^ 2 + b ^ 2 * dist o y ^ 2 -
      2 * a * b * (TangentCone.coneData h o).pairing
        (TangentCone.log h o x) (TangentCone.log h o y) ≤
      dist (segment h o x a) (segment h o y b) ^ 2 := by
  have hh := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr
    (TangentCone.dist_log_le h o (segment h o x a) (segment h o y b))
  rw [TangentCone.log_radial h o x ha, TangentCone.log_radial h o y hb,
    (TangentCone.coneData h o).dist_sq,
    (TangentCone.coneData h o).normSq_scale ha.1,
    (TangentCone.coneData h o).normSq_scale hb.1,
    (TangentCone.coneData h o).pairing_scale ha.1 hb.1,
    TangentCone.normSq_log, TangentCone.normSq_log] at hh
  nlinarith only [hh]

end CATZero

namespace SamplingSequence
universe u v w
variable {F : Type u} [DecidableEq F] {Admissible : Finset F → Prop}
  {L Ω : ℕ → Type v} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → F → L n} (S : SamplingSequence F Admissible L Ω label)
  {X : ℕ → Type w} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)
include S

/-- Uniform fractional-distance comparison for any bounded point function of
I, after translations depending on the whole match. -/
theorem fractional_error {I : Finset F} {e : F} (he : e ∉ I)
    (hI : Admissible (insert e I)) (σ : ∀ n, L n ≃ L n)
    (test : ∀ n, Ω n → X n)
    (depends : ∀ n a b, (∀ i ∈ I, label n a i = label n b i) → test n a = test n b)
    {B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (htest : ∀ n a, dist (O n).base (test n a) ≤ B)
    (frame : ∀ n, Ω n → X n ≃ᵢ X n) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      a ^ 2 * (𝔼 m, dist (frame n m (O n).base) (frame n m (test n m)) ^ 2) +
        b ^ 2 * (𝔼 m, dist (frame n m (O n).base)
          (frame n m ((O n).isom (σ n (label n m e)) (O n).base)) ^ 2) - ε ≤
      𝔼 m, dist
        (CATZero.segment (O n).cat (frame n m (O n).base) (frame n m (test n m)) a)
        (CATZero.segment (O n).cat (frame n m (O n).base)
          (frame n m ((O n).isom (σ n (label n m e)) (O n).base)) b) ^ 2 := by
  let logTest (n : ℕ) (m : Ω n) := TangentCone.log (O n).cat (O n).base (test n m)
  have hc := S.conditional O he hI σ logTest
    (fun n m k hh => by simp only [logTest, depends n m k hh]) hM hB
    (fun n m => by
      change dist (TangentCone.vertex _ _) _ ≤ B
      rw [TangentCone.dist_vertex_log]
      exact htest n m)
  intro ε hε
  filter_upwards [hc (ε / 2) (by positivity)] with n hn
  have hi := Finset.expect_le_expect (s := Finset.univ)
    (fun (m : Ω n) _ => CATZero.fractional_log_comparison (O n).cat (O n).base
      (test n m) ((O n).isom (σ n (label n m e)) (O n).base) ha hb)
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect] at hi
  simp only [(frame n _).isometry.dist_eq, ← CATZero.isometry_segment (O n).cat (frame n _) _ _ ha,
    ← CATZero.isometry_segment (O n).cat (frame n _) _ _ hb] 
  have hab : 0 ≤ 2 * a * b := mul_nonneg (mul_nonneg (by norm_num) ha.1) hb.1
  have hab' : 2 * a * b ≤ 2 := by nlinarith [mul_le_mul ha.2 hb.2 hb.1 (by norm_num : (0:ℝ) ≤ 1)]
  have he' := mul_le_mul_of_nonneg_left hn.le hab
  change 2 * a * b * (𝔼 m, (O n).cone.pairing
    (TangentCone.log (O n).cat (O n).base (test n m))
    (TangentCone.log (O n).cat (O n).base ((O n).isom (σ n (label n m e)) (O n).base))) ≤ _ at he'
  nlinarith

end SamplingSequence
end HyperbolicObstruction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

section

end
end

end OAI
