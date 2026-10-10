import Mathlib

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem358.TriangularRecursion

/-- Conditional scalar sampling functions indexed by the length of the existing prefix. -/
abbrev ConditionalFamily := (n : ℕ) → (Fin n → ℝ) → ℝ → ℝ

/-- Successive conditional sampling, using the last input coordinate at each step. -/
def sample (Q : ConditionalFamily) : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)
  | 0 => fun s => s
  | n + 1 => fun s =>
      Fin.snoc (sample Q n (Fin.init s))
        (Q n (sample Q n (Fin.init s)) (s (Fin.last n)))

@[simp] theorem sample_init (Q : ConditionalFamily) (n : ℕ) (s : Fin (n+1) → ℝ) :
    Fin.init (sample Q (n+1) s) = sample Q n (Fin.init s) := by
  simp [sample]

@[simp] theorem sample_last (Q : ConditionalFamily) (n : ℕ) (s : Fin (n+1) → ℝ) :
    sample Q (n+1) s (Fin.last n) = Q n (sample Q n (Fin.init s)) (s (Fin.last n)) := by
  simp [sample]

@[simp] theorem sample_snoc (Q : ConditionalFamily) (n : ℕ) (s : Fin n → ℝ) (t : ℝ) :
    sample Q (n+1) (Fin.snoc s t) = Fin.snoc (sample Q n s) (Q n (sample Q n s) t) := by
  simp [sample]

/-- Joint measurability of all conditional samplers gives a measurable full sampler. -/
theorem measurable_sample (Q : ConditionalFamily)
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2)) :
    ∀ n, Measurable (sample Q n) := by
  intro n
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
      have hi : Measurable (fun s : Fin (n+1) → ℝ => Fin.init s) := by
        apply Measurable.of_eval
        intro i
        exact measurable_pi_apply i.castSucc
      have hp := ih.comp hi
      apply Measurable.of_eval
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [sample_last, Function.comp_def] using
          (hQ n).comp (hp.prodMk (measurable_pi_apply (Fin.last n)))
      · simpa only [sample, Fin.snoc_castSucc, Function.comp_def] using (measurable_pi_apply j).comp hp

/-- The earlier sampled coordinates remain fixed while the last parameter varies. -/
theorem hasDerivAt_sample_last (Q : ConditionalFamily) (n : ℕ)
    (s : Fin n → ℝ) {t v : ℝ} (hQ : HasDerivAt (Q n (sample Q n s)) v t) :
    HasDerivAt (fun u => sample Q (n+1) (Fin.snoc s u) (Fin.last n)) v t := by
  simpa only [sample_snoc, Fin.snoc_last] using hQ

/-- Conditional prefix-domain invariance propagates to the complete recursive sampler. -/
theorem sample_mem_domains (Q : ConditionalFamily)
    (D : (n : ℕ) → Set (Fin n → ℝ))
    (hzero : ∀ x, x ∈ D 0)
    (hstep : ∀ n x, x ∈ D n → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      Fin.snoc x (Q n x t) ∈ D (n+1)) :
    ∀ n s, (∀ i, s i ∈ Set.Ioo (0 : ℝ) 1) → sample Q n s ∈ D n := by
  intro n
  induction n with
  | zero => intro s hs; exact hzero s
  | succ n ih =>
      intro s hs
      exact hstep n (sample Q n (Fin.init s))
        (ih (Fin.init s) (fun i => hs i.castSucc)) (s (Fin.last n)) (hs (Fin.last n))

/-- Restrict a coordinate tuple to an initial prefix. -/
def take {m n : ℕ} (h : m ≤ n) (s : Fin n → ℝ) : Fin m → ℝ :=
  fun i => s (i.castLE h)

/-- Later random parameters do not affect an earlier sampled prefix. -/
theorem sample_take (Q : ConditionalFamily) {m n : ℕ} (h : m ≤ n) (s : Fin n → ℝ) :
    take h (sample Q n s) = sample Q m (take h s) := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero h
      subst m
      rfl
  | succ n ih =>
      by_cases hmn : m ≤ n
      · change take hmn (Fin.init (sample Q (n+1) s)) =
          sample Q m (take hmn (Fin.init s))
        rw [sample_init]
        exact ih hmn (Fin.init s)
      · have hm : m = n+1 := by omega
        subst m
        rfl

/-- Every sampled coordinate is the corresponding conditional scalar sampler. -/
theorem sample_coordinate (Q : ConditionalFamily) (n : ℕ) (s : Fin n → ℝ) (i : Fin n) :
    sample Q n s i =
      Q i.val (sample Q i.val (take (Nat.le_of_lt i.isLt) s)) (s i) := by
  have hh := congrFun (sample_take Q i.isLt s) (Fin.last i.val)
  have hi : (Fin.last i.val).castLE i.isLt = i := by
    apply Fin.ext
    rfl
  have hpre : Fin.init (take i.isLt s) = take (Nat.le_of_lt i.isLt) s := rfl
  change sample Q n s ((Fin.last i.val).castLE i.isLt) =
    sample Q (i.val+1) (take i.isLt s) (Fin.last i.val) at hh
  rw [sample_last, hpre] at hh
  change sample Q n s ((Fin.last i.val).castLE i.isLt) =
    Q i.val (sample Q i.val (take (Nat.le_of_lt i.isLt) s))
      (s ((Fin.last i.val).castLE i.isLt)) at hh
  simpa only [hi] using hh

/-- Updating a coordinate leaves its earlier prefix unchanged. -/
theorem take_update {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    take (Nat.le_of_lt i.isLt) (Function.update s i t) =
      take (Nat.le_of_lt i.isLt) s := by
  funext k
  apply Function.update_of_ne
  intro hki
  have hv := congrArg Fin.val hki
  have hk := k.isLt
  simp only [Fin.val_castLE] at hv
  omega

/-- The diagonal section of the recursive map is exactly its conditional quantile. -/
theorem sample_update_coordinate (Q : ConditionalFamily) (n : ℕ)
    (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    sample Q n (Function.update s i t) i =
      Q i.val (sample Q i.val (take (Nat.le_of_lt i.isLt) s)) t := by
  rw [sample_coordinate, take_update, Function.update_self]

/-- Every diagonal derivative transfers directly from the corresponding conditional quantile. -/
theorem hasDerivAt_sample_coordinate (Q : ConditionalFamily) (n : ℕ)
    (s : Fin n → ℝ) (i : Fin n) {t v : ℝ}
    (hQ : HasDerivAt (Q i.val (sample Q i.val (take (Nat.le_of_lt i.isLt) s))) v t) :
    HasDerivAt (fun u => sample Q n (Function.update s i u) i) v t := by
  simpa only [sample_update_coordinate] using hQ

/-- The coupled midpoint of two samplers driven by the same parameter tuple. -/
def midpoint (Q R : ConditionalFamily) (n : ℕ) (s : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (sample Q n s i + sample R n s i) / 2

/-- The last-coordinate midpoint fibre, with the original input prefix as parameter. -/
def midpointFiber (Q R : ConditionalFamily) (n : ℕ) (s : Fin n → ℝ) (t : ℝ) : ℝ :=
  (Q n (sample Q n s) t + R n (sample R n s) t) / 2

/-- This is the exact triangular decomposition required by iterated substitution. -/
theorem midpoint_snoc (Q R : ConditionalFamily) (n : ℕ) (s : Fin n → ℝ) (t : ℝ) :
    midpoint Q R (n+1) (Fin.snoc s t) =
      Fin.snoc (midpoint Q R n s) (midpointFiber Q R n s t) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [midpoint, midpointFiber]
  · simp [midpoint, sample_snoc]

/-- Jointly measurable conditional families have jointly measurable sampled midpoints. -/
theorem measurable_midpoint (Q R : ConditionalFamily)
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (hR : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => R n p.1 p.2)) (n : ℕ) :
    Measurable (midpoint Q R n) := by
  apply Measurable.of_eval
  intro i
  exact (((measurable_pi_apply i).comp (measurable_sample Q hQ n)).add
    ((measurable_pi_apply i).comp (measurable_sample R hR n))).div_const 2

/-- Midpoint fibres have the arithmetic mean of the conditional derivatives. -/
theorem hasDerivAt_midpointFiber (Q R : ConditionalFamily) (n : ℕ)
    (s : Fin n → ℝ) {t a b : ℝ}
    (hQ : HasDerivAt (Q n (sample Q n s)) a t)
    (hR : HasDerivAt (R n (sample R n s)) b t) :
    HasDerivAt (midpointFiber Q R n s) ((a+b)/2) t :=
  (hQ.add hR).div_const 2

/-- Every diagonal derivative of the coupled midpoint is the corresponding average. -/
theorem hasDerivAt_midpoint_coordinate (Q R : ConditionalFamily) (n : ℕ)
    (s : Fin n → ℝ) (i : Fin n) {t a b : ℝ}
    (hQ : HasDerivAt (Q i.val (sample Q i.val (take (Nat.le_of_lt i.isLt) s))) a t)
    (hR : HasDerivAt (R i.val (sample R i.val (take (Nat.le_of_lt i.isLt) s))) b t) :
    HasDerivAt (fun u => midpoint Q R n (Function.update s i u) i) ((a+b)/2) t :=
  ((hasDerivAt_sample_coordinate Q n s i hQ).add
    (hasDerivAt_sample_coordinate R n s i hR)).div_const 2

/-- A midpoint fibre is jointly measurable in its original prefix and last parameter. -/
theorem measurable_midpointFiber (Q R : ConditionalFamily)
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2))
    (hR : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => R n p.1 p.2)) (n : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × ℝ => midpointFiber Q R n p.1 p.2) := by
  exact (((hQ n).comp (((measurable_sample Q hQ n).comp measurable_fst).prodMk
    measurable_snd)).add
    ((hR n).comp (((measurable_sample R hR n).comp measurable_fst).prodMk
    measurable_snd))).div_const 2

/-- Strict monotonicity of the conditional quantiles makes the midpoint fibre strictly monotone. -/
theorem strictMonoOn_midpointFiber (Q R : ConditionalFamily) (n : ℕ)
    (s : Fin n → ℝ) {I : Set ℝ}
    (hQ : StrictMonoOn (Q n (sample Q n s)) I)
    (hR : StrictMonoOn (R n (sample R n s)) I) :
    StrictMonoOn (midpointFiber Q R n s) I := by
  intro a ha b hb hab
  have hqa := hQ ha hb hab
  have hra := hR ha hb hab
  unfold midpointFiber
  linarith

end Problem358.TriangularRecursion

end

/-! Finite-prefix density normalization for the canonical triangular sampler.
These are conditional identities, not existence of geometric section data. -/

noncomputable section
open Set
open scoped BigOperators
open Problem358.TriangularRecursion

namespace Problem358.TriangularDensity

abbrev Coordinates (n : ℕ) := Fin n → ℝ

def InUnitCube {n : ℕ} (u : Coordinates n) : Prop := ∀ i, u i ∈ Ioo (0 : ℝ) 1

lemma InUnitCube.init {n : ℕ} {u : Coordinates (n + 1)} (hu : InUnitCube u) :
    InUnitCube (Fin.init u) := fun i => hu i.castSucc

lemma InUnitCube.last {n : ℕ} {u : Coordinates (n + 1)} (hu : InUnitCube u) :
    u (Fin.last n) ∈ Ioo (0 : ℝ) 1 := hu (Fin.last n)

/-- Recursive product of the canonical sampler's longitudinal derivatives. -/
def diagonalProduct (q dq : ConditionalFamily) : (n : ℕ) → Coordinates n → ℝ
  | 0, _ => 1
  | n + 1, u => diagonalProduct q dq n (Fin.init u) *
      dq n (sample q n (Fin.init u)) (u (Fin.last n))

@[simp] theorem diagonalProduct_snoc (q dq : ConditionalFamily) (n : ℕ)
    (s : Coordinates n) (t : ℝ) :
    diagonalProduct q dq (n + 1) (Fin.snoc s t) =
      diagonalProduct q dq n s * dq n (sample q n s) t := by
  simp only [diagonalProduct, Fin.init_snoc, Fin.snoc_last]

/-- The Jacobian product is measurable using only data up to the actual dimension.
Sample measurability can be supplied by the bounded-depth sampler-law API. -/
theorem measurable_diagonalProduct_of_le (q dq : ConditionalFamily) (N : ℕ)
    (hQ : ∀ n, n ≤ N → Measurable (sample q n))
    (hD : ∀ n, n < N → Measurable (fun p : Coordinates n × ℝ => dq n p.1 p.2)) :
    ∀ n, n ≤ N → Measurable (diagonalProduct q dq n) := by
  intro n
  induction n with
  | zero => intro _; exact measurable_const
  | succ n ih =>
      intro hn
      have hnle : n ≤ N := by omega
      have hnlt : n < N := by omega
      have hi : Measurable (fun u : Coordinates (n + 1) => Fin.init u) := by
        apply Measurable.of_eval
        intro i
        exact measurable_pi_apply i.castSucc
      exact ((ih hnle).comp hi).mul ((hD n hnlt).comp
        (((hQ n hnle).comp hi).prodMk (measurable_pi_apply (Fin.last n))))

/-- Measurability of the geometric Jacobian weight for two sampled families. -/
theorem measurable_geometric_diagonalProduct_of_le
    (q r dq dr : ConditionalFamily) (N : ℕ)
    (hQ : ∀ n, n ≤ N → Measurable (sample q n))
    (hR : ∀ n, n ≤ N → Measurable (sample r n))
    (hD : ∀ n, n < N → Measurable (fun p : Coordinates n × ℝ => dq n p.1 p.2))
    (hE : ∀ n, n < N → Measurable (fun p : Coordinates n × ℝ => dr n p.1 p.2))
    (n : ℕ) (hn : n ≤ N) :
    Measurable (fun u => ENNReal.ofReal (Real.sqrt
      (diagonalProduct q dq n u * diagonalProduct r dr n u))) :=
  (((measurable_diagonalProduct_of_le q dq N hQ hD n hn).mul
    (measurable_diagonalProduct_of_le r dr N hR hE n hn)).sqrt).ennreal_ofReal

/-- Finite-cutoff domain induction: no quantile hypotheses above dimension `N`. -/
theorem sample_mem_domains_of_le (q : ConditionalFamily) (D : (n : ℕ) → Set (Coordinates n))
    (N : ℕ) (hzero : (fun i => Fin.elim0 i) ∈ D 0)
    (hstep : ∀ n, n < N → ∀ x, x ∈ D n → ∀ t ∈ Ioo (0 : ℝ) 1,
      Fin.snoc x (q n x t) ∈ D (n + 1)) :
    ∀ n, n ≤ N → ∀ u, InUnitCube u → sample q n u ∈ D n := by
  intro n
  induction n with
  | zero =>
      intro hn u hu
      have hu0 : u = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
      simpa only [sample, hu0] using hzero
  | succ n ih =>
      intro hn u hu
      exact hstep n (by omega) (sample q n (Fin.init u))
        (ih (by omega) _ hu.init) _ hu.last

/-- Finite-cutoff telescoping for a genuinely finite collection of sections. -/
theorem diagonalProduct_eq_density_ratio_of_le
    (q dq : ConditionalFamily) (D : (n : ℕ) → Set (Coordinates n))
    (p : (n : ℕ) → Coordinates n → ℝ) (N : ℕ)
    (hzero : (fun i => Fin.elim0 i) ∈ D 0)
    (hstep : ∀ n, n < N → ∀ x, x ∈ D n → ∀ t ∈ Ioo (0 : ℝ) 1,
      Fin.snoc x (q n x t) ∈ D (n + 1))
    (hnonzero : ∀ n, n ≤ N → ∀ x, x ∈ D n → p n x ≠ 0)
    (hratio : ∀ n, n < N → ∀ x, x ∈ D n → ∀ t ∈ Ioo (0 : ℝ) 1,
      dq n x t = p n x / p (n + 1) (Fin.snoc x (q n x t))) :
    ∀ n, n ≤ N → ∀ u, InUnitCube u →
      diagonalProduct q dq n u = p 0 (fun i => Fin.elim0 i) / p n (sample q n u) := by
  intro n
  induction n with
  | zero =>
      intro hn u hu
      have hu0 : u = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
      subst u
      simp only [diagonalProduct, sample]
      exact (div_self (hnonzero 0 (Nat.zero_le N) _ hzero)).symm
  | succ n ih =>
      intro hn u hu
      have hn' : n ≤ N := by omega
      have hprefix := sample_mem_domains_of_le q D N hzero hstep n hn' (Fin.init u) hu.init
      rw [diagonalProduct, ih hn' _ hu.init, hratio n (by omega) _ hprefix _ hu.last]
      change _ = _ / p (n + 1) (Fin.snoc (sample q n (Fin.init u))
        (q n (sample q n (Fin.init u)) (u (Fin.last n))))
      field_simp [hnonzero n hn' _ hprefix]

/-- The individual longitudinal derivative in each full-coordinate direction. -/
def diagonal (q dq : ConditionalFamily) (n : ℕ) (u : Coordinates n) (i : Fin n) : ℝ :=
  dq i.val (sample q i.val (take (Nat.le_of_lt i.isLt) u)) (u i)

/-- The recursively accumulated Jacobian is the product used by the finite
arithmetic/geometric-mean bound. -/
theorem diagonalProduct_eq_prod (q dq : ConditionalFamily) :
    ∀ n u, diagonalProduct q dq n u = ∏ i : Fin n, diagonal q dq n u i := by
  intro n
  induction n with
  | zero => intro u; simp [diagonalProduct]
  | succ n ih =>
      intro u
      rw [diagonalProduct, ih, Fin.prod_univ_castSucc]
      rfl

/-- At a terminal section whose density is one, the diagonal derivative product
is the original body's volume, independent of all sampling parameters. -/
theorem diagonalProduct_eq_initial_density
    (q dq : ConditionalFamily) (D : (n : ℕ) → Set (Coordinates n))
    (p : (n : ℕ) → Coordinates n → ℝ) (N : ℕ)
    (hzero : (fun i => Fin.elim0 i) ∈ D 0)
    (hstep : ∀ n, n < N → ∀ x, x ∈ D n → ∀ t ∈ Ioo (0 : ℝ) 1,
      Fin.snoc x (q n x t) ∈ D (n + 1))
    (hnonzero : ∀ n, n ≤ N → ∀ x, x ∈ D n → p n x ≠ 0)
    (hratio : ∀ n, n < N → ∀ x, x ∈ D n → ∀ t ∈ Ioo (0 : ℝ) 1,
      dq n x t = p n x / p (n + 1) (Fin.snoc x (q n x t)))
    (hterminal : ∀ x ∈ D N, p N x = 1)
    (u : Coordinates N) (hu : InUnitCube u) :
    diagonalProduct q dq N u = p 0 (fun i => Fin.elim0 i) := by
  rw [diagonalProduct_eq_density_ratio_of_le q dq D p N hzero hstep hnonzero hratio N
    (le_refl N) u hu, hterminal _ (sample_mem_domains_of_le q D N hzero hstep N
      (le_refl N) u hu), div_one]

end Problem358.TriangularDensity

end

/-! Positivity and almost-everywhere parameter support for finite triangular samplers. -/

noncomputable section
open MeasureTheory Set
open Problem358.TriangularRecursion

namespace Problem358.TriangularDensity

/-- The finite product of interval-restricted Lebesgue measures is concentrated
on the open unit cube, including the zero-dimensional case. -/
theorem ae_inUnitCube (n : ℕ) :
    ∀ᵐ u ∂(Measure.pi fun _ : Fin n =>
      (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), InUnitCube u := by
  apply Filter.eventually_all.mpr
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_Ioo)

/-- Positive longitudinal derivatives along valid sampled prefixes give a
positive diagonal product. No assumptions above the finite cutoff are needed. -/
theorem diagonalProduct_pos_of_le (q dq : ConditionalFamily) (N : ℕ)
    (hpos : ∀ n, n < N → ∀ u, InUnitCube u → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dq n (sample q n u) t) :
    ∀ n, n ≤ N → ∀ u, InUnitCube u → 0 < diagonalProduct q dq n u := by
  intro n
  induction n with
  | zero =>
      intro hn u hu
      exact zero_lt_one
  | succ n ih =>
      intro hn u hu
      exact mul_pos (ih (by omega) (Fin.init u) hu.init)
        (hpos n (by omega) (Fin.init u) hu.init _ hu.last)

/-- The domain-invariance form discharges sampled-prefix positivity directly
from the conditional density data used to construct a sampler. -/
theorem diagonalProduct_pos_of_domains
    (q dq : ConditionalFamily) (D : (n : ℕ) → Set (Coordinates n)) (N : ℕ)
    (hzero : (fun i => Fin.elim0 i) ∈ D 0)
    (hstep : ∀ n, n < N → ∀ x, x ∈ D n → ∀ t ∈ Ioo (0 : ℝ) 1,
      Fin.snoc x (q n x t) ∈ D (n + 1))
    (hpos : ∀ n, n < N → ∀ x, x ∈ D n → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dq n x t) :
    ∀ n, n ≤ N → ∀ u, InUnitCube u → 0 < diagonalProduct q dq n u := by
  apply diagonalProduct_pos_of_le q dq N
  intro n hn u hu t ht
  exact hpos n hn _
    (sample_mem_domains_of_le q D N hzero hstep n (Nat.le_of_lt hn) u hu) t ht

end Problem358.TriangularDensity

end

end OAI
