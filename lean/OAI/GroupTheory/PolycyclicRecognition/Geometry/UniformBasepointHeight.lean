import OAI.GroupTheory.PolycyclicRecognition.Algebra.BasepointLabelStabilization

namespace OAI

/-! # A uniform sublinear height error from stabilized basepoint labels -/

namespace PolycyclicRecognition
open Filter
open scoped Topology

/-- Scale stabilization and the proved basepoint comparison select one
linear label per map, uniformly at all centers. The error is sublinear
uniformly in the map and in the two centers. -/
theorem uniform_sublinear_height_of_stable_labels
    {P G L W : Type*} [Group G] [PseudoMetricSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (label : P → G → ℝ → L) (A : L → W →L[ℝ] W)
    (J : P → G → W) (π : G → W)
    {r₀ t η : ℝ} (ht : 0 < t) (hη : 0 < η)
    (hstable : ∀ p x r, r₀ ≤ r → label p x r = label p x r₀)
    (hcompare : ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → (∀ n, 1 ≤ t * scale n) →
      ∀ (p : ℕ → P) (x y : ℕ → G), (∀ n, dist (x n) (y n) ≤ η * scale n) →
      (∀ᶠ n in atTop, label (p n) (x n) (scale n) = label (p n) (y n) (t * scale n)) ∧
      Tendsto (fun n => (scale n)⁻¹ • (J (p n) (y n) - J (p n) (x n) -
        A (label (p n) (y n) (t * scale n)) (π ((x n)⁻¹ * y n)))) atTop (𝓝 0)) :
    ∃ a : P → L,
      (∀ p x r, r₀ ≤ r → label p x r = a p) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ p x y r,
        R ≤ r → dist x y ≤ η * r →
          ‖J p y - J p x - A (a p) (π (x⁻¹ * y))‖ ≤ ε * r) := by
  have hc := stable_label_independent_of_center label ht hη hstable
    (fun scale hg hs h1 ht1 p x y hd =>
      (hcompare scale hg hs h1 ht1 (fun _ => p) (fun _ => x) (fun _ => y) hd).1)
  let a := fun p => label p 1 r₀
  have ha p x r (hr : r₀ ≤ r) : label p x r = a p :=
    (hstable p x r hr).trans (hc p x 1)
  refine ⟨a, ha, ?_⟩
  apply uniform_local_norm_bound_of_sequences
    (fun p x y => J p y - J p x - A (a p) (π (x⁻¹ * y))) ht
  intro scale hg hs h1 ht1 p x y hd
  have hh := (hcompare scale hg hs h1 ht1 p x y hd).2
  apply hh.congr'
  filter_upwards [(hg.const_mul_atTop ht).eventually_ge_atTop r₀] with n hn
  rw [ha (p n) (y n) _ hn]

/-- A uniform error bound on expanding metric balls has the usual global
sublinear form, including an additive constant for the bounded initial range. -/
theorem uniform_sublinear_of_local_radius_bound
    {P X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W]
    (error : P → X → X → W) {η : ℝ} (hη : 0 < η)
    (hlocal : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ p x y r,
      R ≤ r → dist x y ≤ η * r → ‖error p x y‖ ≤ ε * r) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ p x y,
      ‖error p x y‖ ≤ ε * dist x y + C := by
  intro ε hε
  obtain ⟨R, hR, hb⟩ := hlocal (ε * η) (mul_pos hε hη)
  refine ⟨ε * η * R, mul_nonneg (mul_pos hε hη).le (zero_le_one.trans hR), ?_⟩
  intro p x y
  have hr : R ≤ R + dist x y / η := le_add_of_nonneg_right (div_nonneg dist_nonneg hη.le)
  have hd : dist x y ≤ η * (R + dist x y / η) := by
    have he : η * (dist x y / η) = dist x y := by field_simp
    rw [mul_add, he]
    exact le_add_of_nonneg_left (mul_nonneg hη.le (zero_le_one.trans hR))
  have he : ε * η * (R + dist x y / η) = ε * dist x y + ε * η * R := by
    field_simp
    ring
  exact (hb p x y _ hr hd).trans_eq he

/-- The global two-center estimate gives exactly the centered height
estimate used to construct the boundary maps, with one constant for all
centers and all maps. -/
theorem centered_uniform_height_of_two_point_estimate
    {P G W : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (π : G →* Multiplicative W) (f : P → G → G) (A : P → W →L[ℝ] W)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(π (f p y)).toAdd - (π (f p x)).toAdd - A p ((π (x⁻¹ * y)).toAdd)‖ ≤
        ε * dist x y + B) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x g,
      ‖(π ((f p x)⁻¹ * f p (x * g))).toAdd - A p ((π g).toAdd)‖ ≤
        ε * dist 1 g + B := by
  intro ε hε
  obtain ⟨B, hB, hb⟩ := hsub ε hε
  refine ⟨B, hB, ?_⟩
  intro p x g
  have hh := hb p x (x * g)
  have hd : dist x (x * g) = dist 1 g := by
    simpa only [mul_one] using dist_mul_left x (1 : G) g
  simpa only [map_mul, map_inv, toAdd_mul, toAdd_inv, inv_mul_cancel_left,
    neg_add_eq_sub, hd] using hh

end PolycyclicRecognition

end OAI
