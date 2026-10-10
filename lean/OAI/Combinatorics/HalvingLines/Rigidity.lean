import OAI.Combinatorics.HalvingLines.Intersections

namespace OAI

namespace PlanarHalving

namespace Zoom

open scoped NNReal Topology
open Filter

structure LineControl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → E → E) (v : E) where
  level : E →L[ℝ] ℝ
  constant : ℝ≥0
  positive : 0 < constant
  strict : ∀ n x, StrictMono (fun t : ℝ => level (f n (x + t • v) - f n x))
  chord : ∀ n x (t u : ℝ), ‖f n (x + t • v) - f n (x + u • v)‖ ≤
    constant * |level (f n (x + t • v) - f n (x + u • v))|

lemma moving_intersection_tendsto
    (f : ℕ → OpenPartialHomeomorph Point Point)
    (hsource : ∀ n, (f n).source = Set.univ)
    (hexhaust : ∀ K : Set Point, IsCompact K → ∀ᶠ n in atTop, K ⊆ (f n).target)
    (x y z : ℕ → Point) (u v U V a b c : Point) (r s : ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (C₁ : LineControl (fun n => f n) u) (C₂ : LineControl (fun n => f n) v)
    (hdir₁ : DirectionalLimit (fun n => f n) u U)
    (hdir₂ : DirectionalLimit (fun n => f n) v V)
    (ha : Tendsto (fun n => f n (x n)) atTop (𝓝 a))
    (hb : Tendsto (fun n => f n (y n)) atTop (𝓝 b))
    (hdet : detPair U V ≠ 0) (hc₁ : c = a + r • U) (hc₂ : c = b + s • V)
    (hunique : ∀ n (t q : ℝ), x n + t • u = y n + q • v → x n + t • u = z n) :
    Tendsto (fun n => f n (z n)) atTop (𝓝 c) := by
  obtain ⟨hU, hA⟩ := moving_line_arcs_tendsto f hsource hexhaust x a u U hu
    C₁.level C₁.constant C₁.positive ha (fun n => C₁.strict n (x n))
    (fun n => C₁.chord n (x n)) hdir₁
  obtain ⟨hV, hB⟩ := moving_line_arcs_tendsto f hsource hexhaust y b v V hv
    C₂.level C₂.constant C₂.positive hb (fun n => C₂.strict n (y n))
    (fun n => C₂.chord n (y n)) hdir₂
  let V' : Point := (C₂.level V)⁻¹ • V
  have hUV' : detPair U V' ≠ 0 := by
    change detPair U ((C₂.level V)⁻¹ • V) ≠ 0
    rw [detPair_smul_right]
    exact mul_ne_zero (inv_ne_zero hV) hdet
  obtain ⟨ψ, hjoint, hψU, hψV⟩ := transverse_covector C₁.level U V' hU hUV'
  let A (n : ℕ) : Set Point := {p | ∃ t : ℝ, p = f n (x n + t • u)}
  let B (n : ℕ) : Set Point := {p | ∃ t : ℝ, p = f n (y n + t • v)}
  refine line_intersection_tendsto C₁.level ψ hjoint A B (fun n => f n (z n))
    (fun n => f n (x n)) a b c ((C₁.level U)⁻¹ • U) V'
    (s * C₂.level V) ha ?_ ?_ ?_ (by rw [hψV]; norm_num) ?_ ?_ ?_
  · rw [hc₂]
    congr 1
    dsimp [V']
    rw [smul_smul, mul_inv_cancel_right₀ hV]
  · simp only [map_smul, hψU, smul_zero]
  · simp only [hc₁, map_add, map_smul, hψU, smul_zero, add_zero]
  · intro n p hpA hpB
    obtain ⟨t, ht⟩ := hpA
    obtain ⟨q, hq⟩ := hpB
    have hxy : x n + t • u = y n + q • v :=
      (f n).injOn (by rw [hsource]; trivial) (by rw [hsource]; trivial) (ht.symm.trans hq)
    rw [ht, hunique n t q hxy]
  · intro R hR
    obtain ⟨γ, hLip, hmem, hlevel, hlim⟩ := hA R hR
    refine ⟨γ, fun n => (hLip n).continuous, hmem, hlevel, ?_⟩
    simpa only [div_eq_mul_inv, mul_smul] using hlim
  · intro R hR
    obtain ⟨γ, hLip, hmem, _, hlim⟩ := hB R hR
    refine ⟨γ, fun n => (hLip n).continuous, hmem, ?_⟩
    simpa only [V', div_eq_mul_inv, mul_smul] using hlim

noncomputable def LineControl.of_monotone
    (f : ℕ → OpenPartialHomeomorph Point Point)
    (hsource : ∀ n, (f n).source = Set.univ)
    (v : Point) (hv : v ≠ 0) (Q : Point ≃L[ℝ] Point)
    (h₁ : ∀ n x, Monotone (fun t : ℝ => (Q (f n (x + t • v))).1))
    (h₂ : ∀ n x, Monotone (fun t : ℝ => (Q (f n (x + t • v))).2)) :
    LineControl (fun n => f n) v where
  level := coneLevel Q
  constant := ‖Q.symm.toContinuousLinearMap‖₊ + 1
  positive := by positivity
  strict n x := by
    have hginj : Function.Injective (fun t : ℝ => f n (x + t • v)) := by
      intro t u he
      apply smul_left_injective ℝ hv
      exact add_left_cancel ((f n).injOn (by rw [hsource]; trivial)
        (by rw [hsource]; trivial) he)
    have hh := coneLevel_strictMono Q _ hginj (h₁ n x) (h₂ n x)
    intro t u htu
    simp only [map_sub]
    exact sub_lt_sub_right (hh htu) _
  chord n x t u := by
    have hh := coneLevel_chord Q (fun t => f n (x + t • v)) (h₁ n x) (h₂ n x) t u
    exact hh.trans (mul_le_mul_of_nonneg_right (by simp) (abs_nonneg _))

lemma parallel_scalars_zero (u v : Point) (hdet : detPair u v ≠ 0)
    (r s : ℝ) (he : r • u = s • v) : r = 0 ∧ s = 0 := by
  have h₁ : r * u.1 = s * v.1 := congrArg Prod.fst he
  have h₂ : r * u.2 = s * v.2 := congrArg Prod.snd he
  have hr : r * detPair u v = 0 := by
    dsimp [detPair]
    linear_combination v.2 * h₁ - v.1 * h₂
  have hs : s * detPair u v = 0 := by
    dsimp [detPair]
    linear_combination u.2 * h₁ - u.1 * h₂
  exact ⟨(mul_eq_zero.mp hr).resolve_right hdet, (mul_eq_zero.mp hs).resolve_right hdet⟩

lemma line_intersection_unique (x y z u v : Point) (hdet : detPair u v ≠ 0)
    (r s : ℝ) (hz₁ : z = x + r • u) (hz₂ : z = y + s • v)
    (t q : ℝ) (he : x + t • u = y + q • v) : x + t • u = z := by
  have hp : (t - r) • u = (q - s) • v := by
    calc
      (t - r) • u = (x + t • u) - (x + r • u) := by rw [sub_smul]; abel
      _ = (y + q • v) - (y + s • v) := by rw [he, ← hz₁, hz₂]
      _ = (q - s) • v := by rw [sub_smul]; abel
  have ht : t = r := sub_eq_zero.mp (parallel_scalars_zero u v hdet _ _ hp).1
  rw [ht, ← hz₁]

inductive Foliation where
  | horizontal
  | vertical
  | diagonal
  deriving DecidableEq

def Foliation.direction : Foliation → Point
  | .horizontal => (1, 0)
  | .vertical => (0, 1)
  | .diagonal => (1, 1)

lemma Foliation.direction_ne_zero (i : Foliation) : i.direction ≠ 0 := by
  cases i <;> norm_num [Foliation.direction]

lemma Foliation.transverse (i j : Foliation) (hij : i ≠ j) :
    detPair i.direction j.direction ≠ 0 := by
  cases i <;> cases j <;> simp_all [Foliation.direction, detPair]

structure FoliatedSequence where
  map : ℕ → OpenPartialHomeomorph Point Point
  source : ∀ n, (map n).source = Set.univ
  exhaust : ∀ K : Set Point, IsCompact K → ∀ᶠ n in atTop, K ⊆ (map n).target
  control : ∀ i : Foliation, LineControl (fun n => map n) i.direction
  direction : ∀ i : Foliation, DirectionalLimit (fun n => map n) i.direction i.direction

def FoliatedSequence.subseq (F : FoliatedSequence) (ρ : ℕ → ℕ) (hρ : StrictMono ρ) :
    FoliatedSequence where
  map n := F.map (ρ n)
  source n := F.source (ρ n)
  exhaust K hK := hρ.tendsto_atTop.eventually (F.exhaust K hK)
  control i := {
    level := (F.control i).level
    constant := (F.control i).constant
    positive := (F.control i).positive
    strict n x := (F.control i).strict (ρ n) x
    chord n x t u := (F.control i).chord (ρ n) x t u }
  direction i σ hσ x y hxy a b ha hb :=
    F.direction i (ρ ∘ σ) (hρ.comp hσ) x y hxy a b ha hb

def FoliatedSequence.Good (F : FoliatedSequence) (σ : ℝ) (x : Point) : Prop :=
  Tendsto (fun n => F.map n x) atTop (𝓝 (σ • x))

lemma FoliatedSequence.Good.subseq {F : FoliatedSequence} {σ : ℝ} {x : Point}
    (h : F.Good σ x) (ρ : ℕ → ℕ) (hρ : StrictMono ρ) : (F.subseq ρ hρ).Good σ x :=
  h.comp hρ.tendsto_atTop

lemma FoliatedSequence.good_intersection (F : FoliatedSequence) (σ : ℝ)
    (i j : Foliation) (hij : i ≠ j) (x y z : Point) (r s : ℝ)
    (hx : F.Good σ x) (hy : F.Good σ y)
    (hz₁ : z = x + r • i.direction) (hz₂ : z = y + s • j.direction) :
    F.Good σ z := by
  exact moving_intersection_tendsto F.map F.source F.exhaust (fun _ => x) (fun _ => y)
    (fun _ => z) i.direction j.direction i.direction j.direction (σ • x) (σ • y)
    (σ • z) (σ * r) (σ * s) i.direction_ne_zero j.direction_ne_zero
    (F.control i) (F.control j) (F.direction i) (F.direction j) hx hy
    (i.transverse j hij)
    (by rw [hz₁, smul_add, smul_smul])
    (by rw [hz₂, smul_add, smul_smul])
    (fun _ => line_intersection_unique x y z i.direction j.direction
      (i.transverse j hij) r s hz₁ hz₂)

lemma FoliatedSequence.good_rect (F : FoliatedSequence) (σ : ℝ)
    (x y : Point) (hx : F.Good σ x) (hy : F.Good σ y) :
    F.Good σ (y.1, x.2) := by
  apply F.good_intersection σ .horizontal .vertical (by decide) x y (y.1, x.2)
    (y.1 - x.1) (x.2 - y.2) hx hy
  · ext <;> dsimp [Foliation.direction] <;> ring
  · ext <;> dsimp [Foliation.direction] <;> ring

lemma FoliatedSequence.good_diagonal_vertical (F : FoliatedSequence) (σ : ℝ)
    (x y : Point) (hx : F.Good σ x) (hy : F.Good σ y) :
    F.Good σ (y.1, x.2 + y.1 - x.1) := by
  apply F.good_intersection σ .diagonal .vertical (by decide) x y
    (y.1, x.2 + y.1 - x.1) (y.1 - x.1) (x.2 + y.1 - x.1 - y.2) hx hy
  · ext <;> dsimp [Foliation.direction] <;> ring
  · ext <;> dsimp [Foliation.direction] <;> ring

lemma FoliatedSequence.good_diagonal_horizontal (F : FoliatedSequence) (σ : ℝ)
    (x y : Point) (hx : F.Good σ x) (hy : F.Good σ y) :
    F.Good σ (x.1 + y.2 - x.2, y.2) := by
  apply F.good_intersection σ .diagonal .horizontal (by decide) x y
    (x.1 + y.2 - x.2, y.2) (y.2 - x.2) (x.1 + y.2 - x.2 - y.1) hx hy
  · ext <;> dsimp [Foliation.direction] <;> ring
  · ext <;> dsimp [Foliation.direction] <;> ring

lemma FoliatedSequence.good_axis_swap (F : FoliatedSequence) (σ a : ℝ)
    (hzero : F.Good σ 0) (ha : F.Good σ (a, 0)) : F.Good σ (0, a) := by
  have hh := F.good_diagonal_vertical σ 0 (a, 0) hzero ha
  have hv := F.good_rect σ (a, a) 0 (by simpa using hh) hzero
  simpa using hv

lemma FoliatedSequence.good_axis_add (F : FoliatedSequence) (σ a b : ℝ)
    (hzero : F.Good σ 0) (ha : F.Good σ (a, 0)) (hb : F.Good σ (b, 0)) :
    F.Good σ (a + b, 0) := by
  have hb' := F.good_axis_swap σ b hzero hb
  have hh := F.good_diagonal_horizontal σ (a, 0) (0, b) ha hb'
  have hv := F.good_rect σ 0 (a + b, b) hzero (by simpa using hh)
  simpa using hv

lemma FoliatedSequence.good_axis_neg (F : FoliatedSequence) (σ a : ℝ)
    (hzero : F.Good σ 0) (ha : F.Good σ (a, 0)) : F.Good σ (-a, 0) := by
  have hh := F.good_diagonal_vertical σ (a, 0) 0 ha hzero
  have hd := F.good_diagonal_horizontal σ 0 (0, -a) hzero (by simpa using hh)
  have hv := F.good_rect σ 0 (-a, -a) hzero (by simpa using hd)
  simpa using hv

lemma FoliatedSequence.good_nat_axis (F : FoliatedSequence) (σ a : ℝ)
    (hzero : F.Good σ 0) (ha : F.Good σ (a, 0)) (m : ℕ) :
    F.Good σ ((m : ℝ) * a, 0) := by
  induction m with
  | zero => simpa only [Nat.cast_zero, zero_mul] using (show F.Good σ (0, 0) from hzero)
  | succ m ih =>
    convert F.good_axis_add σ ((m : ℝ) * a) a hzero ih ha using 1
    push_cast
    ring_nf

lemma FoliatedSequence.good_int_axis (F : FoliatedSequence) (σ a : ℝ)
    (hzero : F.Good σ 0) (ha : F.Good σ (a, 0)) (m : ℤ) :
    F.Good σ ((m : ℝ) * a, 0) := by
  cases m with
  | ofNat n => simpa using F.good_nat_axis σ a hzero ha n
  | negSucc n =>
    convert F.good_axis_neg σ (((n + 1 : ℕ) : ℝ) * a) hzero
      (F.good_nat_axis σ a hzero ha (n + 1)) using 1
    push_cast
    ring_nf

lemma FoliatedSequence.good_lattice (F : FoliatedSequence) (σ a : ℝ)
    (hzero : F.Good σ 0) (ha : F.Good σ (a, 0)) (m n : ℤ) :
    F.Good σ ((m : ℝ) * a, (n : ℝ) * a) := by
  exact F.good_rect σ (0, (n : ℝ) * a) ((m : ℝ) * a, 0)
    (F.good_axis_swap σ ((n : ℝ) * a) hzero (F.good_int_axis σ a hzero ha n))
    (F.good_int_axis σ a hzero ha m)

end Zoom

end PlanarHalving

end OAI
