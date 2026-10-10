import OAI.Geometry.EinsteinFour.AngularGradient

namespace OAI

/-! Sixth spherical moments for the directional derivative of normal curvature.
All moments are the explicit Folland specialization from `SphericalMoments`. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

/-- Contracting one fourth moment with a matrix. -/
theorem fourth_single_contraction (D : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    (∑ k, ∑ l, D k l * momentFour a b k l) =
      (delta a b * (∑ k, D k k) + D a b + D b a) / 24 := by
  have hm (k l : Fin 4) : D k l * momentFour a b k l =
      (D k l * delta a b * delta k l + D k l * delta a k * delta b l +
        D k l * delta a l * delta b k) / 24 := by
    unfold momentFour
    ring
  simp_rw [hm, ← Finset.sum_div, Finset.sum_add_distrib]
  congr 1
  simp [delta, mul_ite, ite_mul, Finset.mul_sum]

theorem delta_symm (a b : Fin 4) : delta a b = delta b a := by
  simp [delta, eq_comm]

theorem momentFour_cycle (a b c d : Fin 4) :
    momentFour a b c d = momentFour a d b c := by
  unfold momentFour
  rw [delta_symm d c, delta_symm d b]
  ring

/-- Group the fifteen pairings by the partner of the first index. -/
theorem sixth_sum_recursion (C D : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    (∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentSix a b i j k l) =
      (delta a b * (∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentFour i j k l) +
        (∑ j, C a j * (∑ k, ∑ l, D k l * momentFour b j k l)) +
        (∑ i, C i a * (∑ k, ∑ l, D k l * momentFour b i k l)) +
        (∑ l, D a l * (∑ i, ∑ j, C i j * momentFour b l i j)) +
        (∑ k, D k a * (∑ i, ∑ j, C i j * momentFour b k i j))) / 8 := by
  have hm (i j k l : Fin 4) : C i j * D k l * momentSix a b i j k l =
      (delta a b * (C i j * D k l * momentFour i j k l) +
       C i j * D k l * delta a i * momentFour b j k l +
       C i j * D k l * delta a j * momentFour b i k l +
       C i j * D k l * delta a k * momentFour b l i j +
       C i j * D k l * delta a l * momentFour b k i j) / 8 := by
    unfold momentSix
    rw [momentFour_cycle b i j l, momentFour_cycle b i j k]
    ring
  have h0 : (∑ i, ∑ j, ∑ k, ∑ l,
      delta a b * (C i j * D k l * momentFour i j k l)) =
      delta a b * (∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentFour i j k l) := by
    simp only [Finset.mul_sum]
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l,
      C i j * D k l * delta a i * momentFour b j k l) =
      ∑ j, C a j * (∑ k, ∑ l, D k l * momentFour b j k l) := by
    simp [delta, mul_ite, ite_mul, Finset.sum_ite_irrel, Finset.mul_sum, mul_assoc]
  have h2 : (∑ i, ∑ j, ∑ k, ∑ l,
      C i j * D k l * delta a j * momentFour b i k l) =
      ∑ i, C i a * (∑ k, ∑ l, D k l * momentFour b i k l) := by
    simp [delta, mul_ite, ite_mul, Finset.sum_ite_irrel, Finset.mul_sum, mul_assoc]
  have hr (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
      (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
    calc
      _ = ∑ i, ∑ k, ∑ j, f i j k := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  have h3 : (∑ i, ∑ j, ∑ k, ∑ l,
      C i j * D k l * delta a k * momentFour b l i j) =
      ∑ l, D a l * (∑ i, ∑ j, C i j * momentFour b l i j) := by
    simp only [delta, mul_ite, ite_mul, mul_zero, mul_one, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [hr]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h4 : (∑ i, ∑ j, ∑ k, ∑ l,
      C i j * D k l * delta a l * momentFour b k i j) =
      ∑ k, D k a * (∑ i, ∑ j, C i j * momentFour b k i j) := by
    simp only [delta, mul_ite, ite_mul, mul_zero, mul_one, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hr]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hm, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [h0, h1, h2, h3, h4]

theorem fourth_single_contraction_traceFree (D : Fin 4 → Fin 4 → ℝ)
    (hD : ∑ k, D k k = 0) (hDs : ∀ i j, D i j = D j i) (a b : Fin 4) :
    (∑ k, ∑ l, D k l * momentFour a b k l) = D a b / 12 := by
  rw [fourth_single_contraction, hD, hDs b a]
  ring

/-- A fourth-degree harmonic has no second-degree spherical moment. -/
theorem sixth_sum_traceFree (C D : Fin 4 → Fin 4 → ℝ)
    (hC : ∑ k, C k k = 0) (hD : ∑ k, D k k = 0)
    (hCs : ∀ i j, C i j = C j i) (hDs : ∀ i j, D i j = D j i)
    (a b : Fin 4) :
    (∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentSix a b i j k l) =
      delta a b * (∑ i, ∑ j, C i j * D i j) / 96 +
        ((∑ k, C a k * D k b) + (∑ k, D a k * C k b)) / 48 := by
  rw [sixth_sum_recursion, fourth_sum_formula, hC, hD]
  simp_rw [fourth_single_contraction_traceFree D hD hDs,
    fourth_single_contraction_traceFree C hC hCs]
  have hp : (∑ i, ∑ j, C i j * D j i) = ∑ i, ∑ j, C i j * D i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hDs j i]
  rw [hp]
  have h1 : (∑ j, C a j * (D b j / 12)) = (∑ j, C a j * D j b) / 12 := by
    simp_rw [hDs b, ← mul_div_assoc, ← Finset.sum_div]
  have h2 : (∑ i, C i a * (D b i / 12)) = (∑ i, C a i * D i b) / 12 := by
    simp_rw [← hCs a, hDs b, ← mul_div_assoc, ← Finset.sum_div]
  have h3 : (∑ l, D a l * (C b l / 12)) = (∑ l, D a l * C l b) / 12 := by
    simp_rw [hCs b, ← mul_div_assoc, ← Finset.sum_div]
  have h4 : (∑ k, D k a * (C b k / 12)) = (∑ k, D a k * C k b) / 12 := by
    simp_rw [← hDs a, hCs b, ← mul_div_assoc, ← Finset.sum_div]
  rw [h1, h2, h3, h4]
  ring

/-- The raw weighted quadratic product is exactly a sixth-moment contraction. -/
theorem integral_weighted_quadratic_mul (h : FollandMoments)
    (C D : Mat4) (a b : Fin 4) :
    (∫ q, q.val a * q.val b * (quadratic C q * quadratic D q) ∂sphereMeasure) =
      ∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentSix a b i j k l := by
  have he : (fun q : Directions =>
      q.val a * q.val b * (quadratic C q * quadratic D q)) =
      fun q => ∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l *
        (q.val a * q.val b * q.val i * q.val j * q.val k * q.val l) := by
    funext q
    have hp : quadratic C q * quadratic D q =
        ∑ i, ∑ j, ∑ k, ∑ l,
          C i j * D k l * (q.val i * q.val j * q.val k * q.val l) := by
      unfold quadratic
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [hp]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul, h.sixth]

/-- The useful matrix form of the sixth moment. -/
theorem integral_weighted_quadratic_mul_traceFree (h : FollandMoments)
    (C D : Mat4) (hC : C.trace = 0) (hD : D.trace = 0)
    (hCs : Cᵀ = C) (hDs : Dᵀ = D) (a b : Fin 4) :
    (∫ q, q.val a * q.val b * (quadratic C q * quadratic D q) ∂sphereMeasure) =
      delta a b * (∑ i, ∑ j, C i j * D i j) / 96 +
        (C * D + D * C) a b / 48 := by
  rw [integral_weighted_quadratic_mul h]
  have hc : ∑ k, C k k = 0 := hC
  have hd : ∑ k, D k k = 0 := hD
  have hcs (i j : Fin 4) : C i j = C j i :=
    (congrFun (congrFun hCs i) j).symm
  have hds (i j : Fin 4) : D i j = D j i :=
    (congrFun (congrFun hDs i) j).symm
  simpa only [Matrix.add_apply, Matrix.mul_apply] using!
    sixth_sum_traceFree C D hc hd hcs hds a b

end

end PositiveEinsteinFour.Angular

end OAI
