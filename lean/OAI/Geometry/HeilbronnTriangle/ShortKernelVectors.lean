import OAI.Geometry.HeilbronnTriangle.ShortestIntegralVector

namespace OAI


namespace Problem355.ShortKernelVectors

theorem pair_independent_of_coordinates {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℝ ι) (i j : ι)
    (hu : u i ≠ 0) (hv : v i = 0) (hvj : v j ≠ 0) :
    LinearIndependent ℝ ![u, v] := by
  apply linearIndependent_fin2.mpr
  change v ≠ 0 ∧ ∀ a : ℝ, a • v ≠ u
  constructor
  · intro h
    apply hvj
    simp only [h, PiLp.zero_apply]
  · intro a h
    have hi := congrArg (fun x : EuclideanSpace ℝ ι => x i) h
    simp only [PiLp.smul_apply, smul_eq_mul, hv, mul_zero] at hi
    exact hu hi.symm

theorem short_kernel_pair_zero (x : Fin 3 → ℤ) (hx : x 0 ≠ 0) :
    ∃ u v : Fin 3 → ℤ,
      dotProduct x u = 0 ∧ dotProduct x v = 0 ∧
      LinearIndependent ℝ ![IntegralMinima.toEuclidean u, IntegralMinima.toEuclidean v] ∧
      ‖IntegralMinima.toEuclidean u‖ ≤ ‖IntegralMinima.toEuclidean x‖ ∧
      ‖IntegralMinima.toEuclidean v‖ ≤ ‖IntegralMinima.toEuclidean x‖ := by
  let u : Fin 3 → ℤ := ![-x 1, x 0, 0]
  let v : Fin 3 → ℤ := ![-x 2, 0, x 0]
  have hxR : (x 0 : ℝ) ≠ 0 := by exact_mod_cast hx
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_⟩
  · simp [u, dotProduct, Fin.sum_univ_three]
    ring
  · simp [v, dotProduct, Fin.sum_univ_three]
    ring
  · apply pair_independent_of_coordinates (IntegralMinima.toEuclidean u) (IntegralMinima.toEuclidean v) 1 2
    · simpa [IntegralMinima.toEuclidean, u] using hxR
    · simp [IntegralMinima.toEuclidean, v]
    · simpa [IntegralMinima.toEuclidean, v] using hxR
  · have hsq : ‖IntegralMinima.toEuclidean u‖ ^ 2 ≤ ‖IntegralMinima.toEuclidean x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, IntegralMinima.toEuclidean,
        Fin.sum_univ_three, u]; nlinarith [sq_nonneg (x 2 : ℝ)]
    nlinarith [norm_nonneg (IntegralMinima.toEuclidean u), norm_nonneg (IntegralMinima.toEuclidean x)]
  · have hsq : ‖IntegralMinima.toEuclidean v‖ ^ 2 ≤ ‖IntegralMinima.toEuclidean x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, IntegralMinima.toEuclidean,
        Fin.sum_univ_three, v]; nlinarith [sq_nonneg (x 1 : ℝ)]
    nlinarith [norm_nonneg (IntegralMinima.toEuclidean v), norm_nonneg (IntegralMinima.toEuclidean x)]

theorem short_kernel_pair_one (x : Fin 3 → ℤ) (hx : x 1 ≠ 0) :
    ∃ u v : Fin 3 → ℤ,
      dotProduct x u = 0 ∧ dotProduct x v = 0 ∧
      LinearIndependent ℝ ![IntegralMinima.toEuclidean u, IntegralMinima.toEuclidean v] ∧
      ‖IntegralMinima.toEuclidean u‖ ≤ ‖IntegralMinima.toEuclidean x‖ ∧
      ‖IntegralMinima.toEuclidean v‖ ≤ ‖IntegralMinima.toEuclidean x‖ := by
  let u : Fin 3 → ℤ := ![x 1, -x 0, 0]
  let v : Fin 3 → ℤ := ![0, -x 2, x 1]
  have hxR : (x 1 : ℝ) ≠ 0 := by exact_mod_cast hx
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_⟩
  · simp [u, dotProduct, Fin.sum_univ_three]
    ring
  · simp [v, dotProduct, Fin.sum_univ_three]
    ring
  · apply pair_independent_of_coordinates (IntegralMinima.toEuclidean u) (IntegralMinima.toEuclidean v) 0 2
    · simpa [IntegralMinima.toEuclidean, u] using hxR
    · simp [IntegralMinima.toEuclidean, v]
    · simpa [IntegralMinima.toEuclidean, v] using hxR
  · have hsq : ‖IntegralMinima.toEuclidean u‖ ^ 2 ≤ ‖IntegralMinima.toEuclidean x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, IntegralMinima.toEuclidean,
        Fin.sum_univ_three, u]; nlinarith [sq_nonneg (x 2 : ℝ)]
    nlinarith [norm_nonneg (IntegralMinima.toEuclidean u), norm_nonneg (IntegralMinima.toEuclidean x)]
  · have hsq : ‖IntegralMinima.toEuclidean v‖ ^ 2 ≤ ‖IntegralMinima.toEuclidean x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, IntegralMinima.toEuclidean,
        Fin.sum_univ_three, v]; nlinarith [sq_nonneg (x 0 : ℝ)]
    nlinarith [norm_nonneg (IntegralMinima.toEuclidean v), norm_nonneg (IntegralMinima.toEuclidean x)]

theorem short_kernel_pair_two (x : Fin 3 → ℤ) (hx : x 2 ≠ 0) :
    ∃ u v : Fin 3 → ℤ,
      dotProduct x u = 0 ∧ dotProduct x v = 0 ∧
      LinearIndependent ℝ ![IntegralMinima.toEuclidean u, IntegralMinima.toEuclidean v] ∧
      ‖IntegralMinima.toEuclidean u‖ ≤ ‖IntegralMinima.toEuclidean x‖ ∧
      ‖IntegralMinima.toEuclidean v‖ ≤ ‖IntegralMinima.toEuclidean x‖ := by
  let u : Fin 3 → ℤ := ![x 2, 0, -x 0]
  let v : Fin 3 → ℤ := ![0, x 2, -x 1]
  have hxR : (x 2 : ℝ) ≠ 0 := by exact_mod_cast hx
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_⟩
  · simp [u, dotProduct, Fin.sum_univ_three]
    ring
  · simp [v, dotProduct, Fin.sum_univ_three]
    ring
  · apply pair_independent_of_coordinates (IntegralMinima.toEuclidean u) (IntegralMinima.toEuclidean v) 0 1
    · simpa [IntegralMinima.toEuclidean, u] using hxR
    · simp [IntegralMinima.toEuclidean, v]
    · simpa [IntegralMinima.toEuclidean, v] using hxR
  · have hsq : ‖IntegralMinima.toEuclidean u‖ ^ 2 ≤ ‖IntegralMinima.toEuclidean x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, IntegralMinima.toEuclidean,
        Fin.sum_univ_three, u]; nlinarith [sq_nonneg (x 1 : ℝ)]
    nlinarith [norm_nonneg (IntegralMinima.toEuclidean u), norm_nonneg (IntegralMinima.toEuclidean x)]
  · have hsq : ‖IntegralMinima.toEuclidean v‖ ^ 2 ≤ ‖IntegralMinima.toEuclidean x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, IntegralMinima.toEuclidean,
        Fin.sum_univ_three, v]; nlinarith [sq_nonneg (x 0 : ℝ)]
    nlinarith [norm_nonneg (IntegralMinima.toEuclidean v), norm_nonneg (IntegralMinima.toEuclidean x)]

theorem exists_short_kernel_pair (x : Fin 3 → ℤ) (hx : x ≠ 0) :
    ∃ u v : Fin 3 → ℤ,
      dotProduct x u = 0 ∧ dotProduct x v = 0 ∧
      LinearIndependent ℝ ![IntegralMinima.toEuclidean u, IntegralMinima.toEuclidean v] ∧
      ‖IntegralMinima.toEuclidean u‖ ≤ ‖IntegralMinima.toEuclidean x‖ ∧
      ‖IntegralMinima.toEuclidean v‖ ≤ ‖IntegralMinima.toEuclidean x‖ := by
  by_cases h0 : x 0 ≠ 0
  · exact short_kernel_pair_zero x h0
  by_cases h1 : x 1 ≠ 0
  · exact short_kernel_pair_one x h1
  have h2 : x 2 ≠ 0 := by
    intro h2
    apply hx
    funext i
    fin_cases i <;> simp_all
  exact short_kernel_pair_two x h2

end Problem355.ShortKernelVectors

end OAI
