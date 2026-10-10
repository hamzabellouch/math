import Mathlib
import OAI.Geometry.HyperbolicGroups.ConditionalStar

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace OrbitLimit
universe u v
variable {L Ω : ℕ → Type u} [∀ n, Fintype (L n)]
  [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {X : ℕ → Type v} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)

/-- Actual orbit-coordinate arrays with a uniform bound from the minimizing
basepoints, before taking any product or limiting metric. -/
@[ext] structure Array where
  val : ∀ n, Ω n → X n
  bound : ∃ R : ℝ, 0 ≤ R ∧ ∀ n m, dist (O n).base (val n m) ≤ R

abbrev Product (n : ℕ) := MeanProduct.Space (Ω n) (fun _ => X n)
def origin (n : ℕ) : Product (Ω := Ω) (X := X) n :=
  MeanProduct.ofFn _ _ (fun _ => (O n).base)
include O in
theorem productCat (n : ℕ) : CATZero (Product (Ω := Ω) (X := X) n) :=
  MeanProduct.catZero (fun _ => (O n).cat)

variable (U : Ultrafilter ℕ)
def boundedSection (x : Array (Ω := Ω) O) : MetricLimit.Bounded U _ (origin (Ω := Ω) O) :=
  ⟨fun n => MeanProduct.ofFn _ _ (x.val n), by
    obtain ⟨R, hR, hx⟩ := x.bound
    exact ⟨R, fun n => MeanProduct.dist_le_of_forall _ _ hR (hx n)⟩⟩

abbrev Space := MetricLimit.Space (U := U) (X := Product (Ω := Ω) (X := X))
  (o := origin (Ω := Ω) O)
def point (x : Array (Ω := Ω) O) : Space (Ω := Ω) O U := MetricLimit.point (boundedSection O U x)
theorem catZero : CATZero (Space (Ω := Ω) O U) := MetricLimit.catZero (productCat (Ω := Ω) O)

variable {O U}
lemma tendsto_dist_sq (x y : Array (Ω := Ω) O) :
    Tendsto (fun n => 𝔼 m, dist (x.val n m) (y.val n m) ^ 2) U
      (𝓝 (dist (point O U x) (point O U y) ^ 2)) := by
  convert MetricLimit.tendsto_point_dist_sq (boundedSection O U x) (boundedSection O U y) using 1
  · funext n
    exact (MeanProduct.dist_sq ((boundedSection O U x).val n) ((boundedSection O U y).val n)).symm
  · rfl

lemma dist_sq_eq (hU : (U : Filter ℕ) ≤ atTop) (x y : Array (Ω := Ω) O) {a : ℝ}
    (h : Tendsto (fun n => 𝔼 m, dist (x.val n m) (y.val n m) ^ 2) atTop (𝓝 a)) :
    dist (point O U x) (point O U y) ^ 2 = a :=
  tendsto_nhds_unique (tendsto_dist_sq x y) (h.mono_left hU)

lemma dist_sq_lower (hU : (U : Filter ℕ) ≤ atTop) (x y : Array (Ω := Ω) O) {a : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      a - ε ≤ 𝔼 m, dist (x.val n m) (y.val n m) ^ 2) :
    a ≤ dist (point O U x) (point O U y) ^ 2 := by
  apply MetricLimit.lower_of_eventually hU (boundedSection O U x) (boundedSection O U y)
  intro ε hε
  simpa only [boundedSection, MeanProduct.dist_sq, MeanProduct.ofFn_apply] using h ε hε

/-- Coordinate segments stay uniformly bounded. -/
def segment (x y : Array (Ω := Ω) O) (t : ℝ) : Array (Ω := Ω) O :=
  if ht : t ∈ Set.Icc (0 : ℝ) 1 then
    ⟨fun n m => CATZero.segment (O n).cat (x.val n m) (y.val n m) t, by
      obtain ⟨R, hR, hx⟩ := x.bound
      obtain ⟨S, hS, hy⟩ := y.bound
      refine ⟨2 * R + S, by positivity, fun n m => ?_⟩
      have hd : dist (x.val n m) (y.val n m) ≤ R + S := by
        calc
          _ ≤ dist (x.val n m) (O n).base + dist (O n).base (y.val n m) := dist_triangle _ _ _
          _ ≤ R + S := by rw [dist_comm (x.val n m)]; exact add_le_add (hx n m) (hy n m)
      calc
        _ ≤ dist (O n).base (x.val n m) + dist (x.val n m)
          (CATZero.segment (O n).cat (x.val n m) (y.val n m) t) := dist_triangle _ _ _
        _ = dist (O n).base (x.val n m) + t * dist (x.val n m) (y.val n m) := by
          rw [CATZero.segment_left (O n).cat _ _ ht]
        _ ≤ R + dist (x.val n m) (y.val n m) := add_le_add (hx n m)
          (mul_le_of_le_one_left dist_nonneg ht.2)
        _ ≤ 2 * R + S := by linarith⟩
  else x

omit [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)] in
lemma segment_val (x y : Array (Ω := Ω) O) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (m : Ω n) :
    (segment x y t).val n m = CATZero.segment (O n).cat (x.val n m) (y.val n m) t := by
  simp only [segment, dite_eq_left ht]

lemma section_segment (x y : Array (Ω := Ω) O) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    boundedSection O U (segment x y t) =
      MetricLimit.segment (productCat (Ω := Ω) O) (boundedSection O U x) (boundedSection O U y) t := by
  apply MetricLimit.Bounded.ext
  funext n
  rw [MetricLimit.segment_val _ _ _ ht]
  apply MetricScale.Space.ext
  apply PiLp.ext
  intro m
  change (segment x y t).val n m = MeanProduct.apply
    (CATZero.segment (productCat (Ω := Ω) O n) _ _ t) m
  rw [segment_val x y ht, MeanProduct.apply_segment (fun _ => (O n).cat) _ _ ht]
  rfl

lemma point_segment (x y : Array (Ω := Ω) O) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    point O U (segment x y t) = CATZero.segment (catZero O U) (point O U x) (point O U y) t := by
  unfold point
  rw [section_segment x y ht]
  exact MetricLimit.point_segment _ _ _ ht

end OrbitLimit
end HyperbolicObstruction

noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace SamplingSequence
open OrbitLimit
universe u v w z
variable {F : Type u} [DecidableEq F] {Admissible : Finset F → Prop}
  {L Ω : ℕ → Type v} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → F → L n} (S : SamplingSequence F Admissible L Ω label)
  {X : ℕ → Type w} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)
  {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ atTop)
include S hU

/-- Every actual labelled edge has unit limiting squared length, including
edges whose orientation is read backwards. -/
lemma limit_edge (x y : OrbitLimit.Array (Ω := Ω) O) (e : F)
    (σ : ∀ n, L n ≃ L n) (hM : 0 ≤ M)
    (hxy : ∀ n m, dist (x.val n m) (y.val n m) =
      dist (O n).base ((O n).isom (σ n (label n m e)) (O n).base)) :
    dist (point O U x) (point O U y) ^ 2 = 1 := by
  apply dist_sq_eq hU
  simpa only [hxy] using S.edge_energy O e σ hM

/-- The full distinct-field path estimate in the genuine mean-product
ultralimit. -/
lemma limit_path {G : ℕ → Type z} [∀ n, Group (G n)]
    (A : ∀ n, G n →* (X n ≃ᵢ X n)) (letter : ∀ n, L n → G n)
    (hact : ∀ n i, A n (letter n i) = (O n).isom i)
    (down : ∀ I J, I ⊆ J → Admissible J → Admissible I)
    (x y : OrbitLimit.Array (Ω := Ω) O) (σ : ∀ n, F → L n ≃ L n) (hM : 0 ≤ M)
    (w : List F) (hw : w.Nodup) (hadm : Admissible w.toFinset)
    (hxy : ∀ n m, dist (x.val n m) (y.val n m) =
      dist (O n).base (A n (OrbitWord.word (label n) (σ n) (letter n) m w) (O n).base)) :
    (w.length : ℝ) ≤ dist (point O U x) (point O U y) ^ 2 := by
  apply dist_sq_lower hU
  simpa only [hxy] using S.word_lower O A letter hact down σ hM w hw hadm

/-- Fixed-fraction points pass through the product ultralimit before making
any angle assertion. This is the precise exceptional ternary test. -/
lemma limit_fractional {I : Finset F} {e : F} (he : e ∉ I)
    (hI : Admissible (insert e I)) (σ : ∀ n, L n ≃ L n)
    (test : ∀ n, Ω n → X n)
    (depends : ∀ n a b, (∀ i ∈ I, label n a i = label n b i) → test n a = test n b)
    {B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (htest : ∀ n m, dist (O n).base (test n m) ≤ B)
    (frame : ∀ n, Ω n → X n ≃ᵢ X n)
    (o x y : OrbitLimit.Array (Ω := Ω) O)
    (ho : ∀ n m, o.val n m = frame n m (O n).base)
    (hx : ∀ n m, x.val n m = frame n m (test n m))
    (hy : ∀ n m, y.val n m = frame n m ((O n).isom (σ n (label n m e)) (O n).base))
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    a ^ 2 * dist (point O U o) (point O U x) ^ 2 +
      b ^ 2 * dist (point O U o) (point O U y) ^ 2 ≤
      dist (CATZero.segment (catZero O U) (point O U o) (point O U x) a)
        (CATZero.segment (catZero O U) (point O U o) (point O U y) b) ^ 2 := by
  rw [← point_segment o x ha, ← point_segment o y hb]
  apply le_of_forall_pos_le_add
  intro ε hε
  have he' := S.fractional_error O he hI σ test depends hM hB htest frame ha hb ε hε
  have hh : ∀ᶠ n in (U : Filter ℕ),
      a ^ 2 * (𝔼 m, dist (o.val n m) (x.val n m) ^ 2) +
        b ^ 2 * (𝔼 m, dist (o.val n m) (y.val n m) ^ 2) - ε ≤
      𝔼 m, dist ((OrbitLimit.segment o x a).val n m) ((OrbitLimit.segment o y b).val n m) ^ 2 := by
    filter_upwards [hU he'] with n hn
    simpa only [OrbitLimit.segment_val _ _ ha, OrbitLimit.segment_val _ _ hb, ho, hx, hy] using hn
  have ht := le_of_tendsto_of_tendsto
    ((((tendsto_dist_sq o x).const_mul (a ^ 2)).add ((tendsto_dist_sq o y).const_mul (b ^ 2))).sub_const ε)
    (tendsto_dist_sq (OrbitLimit.segment o x a) (OrbitLimit.segment o y b)) hh
  linarith

end SamplingSequence
end HyperbolicObstruction
end
end
end

section

end
end

end OAI
