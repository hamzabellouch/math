import OAI.Analysis.NumericalRange.ResolventPositivity

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_241 u_242 u_243

open scoped BigOperators Matrix.Norms.L2Operator
section

theorem continuous_polynomialValue {m d : ℕ}
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    Continuous (polynomialValue B) := by
  apply continuous_finsetSum
  intro k _
  exact (continuous_pow k.val).smul continuous_const

theorem numericalRange_image {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRange A =
      (fun x : EuclideanSpace ℂ (Fin n) =>
        inner ℂ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x)) ''
      Metric.sphere 0 1 := by
  ext z
  simp [numericalRange, Set.mem_image]

theorem numericalRange_compact {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    IsCompact (numericalRange A) := by
  rw [numericalRange_image]
  apply (isCompact_sphere (0 : EuclideanSpace ℂ (Fin n)) 1).image
  exact continuous_id.inner (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).continuous

theorem numericalRange_nonempty {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) : (numericalRange A).Nonempty := by
  let i : Fin n := ⟨0, hn⟩
  let x : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  refine ⟨inner ℂ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x), x, ?_, rfl⟩
  simp [x]

theorem rangeMaximum_attained {n m d : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    ∃ z ∈ numericalRange A, rangeMaximum A B = ‖polynomialValue B z‖ := by
  obtain ⟨z, hz, hmax⟩ := (numericalRange_compact A).exists_isMaxOn
    (numericalRange_nonempty hn A) (continuous_polynomialValue B).norm.continuousOn
  refine ⟨z, hz, ?_⟩
  apply le_antisymm
  · apply csSup_le
    · exact (numericalRange_nonempty hn A).image _
    · rintro v ⟨w, hw, rfl⟩
      exact hmax hw
  · apply le_csSup
    · exact ((numericalRange_compact A).image (continuous_polynomialValue B).norm).bddAbove
    · exact ⟨z, hz, rfl⟩


open Set Metric
open scoped RealInnerProductSpace

lemma linear_sphere_image_eq_ball_image
    {E : Type u_241} {F : Type u_242} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F)
    (hker : ∃ v : E, L v = 0 ∧ v ≠ 0) :
    L '' sphere (0 : E) 1 = L '' closedBall (0 : E) 1 := by
  apply Subset.antisymm
  · exact image_mono sphere_subset_closedBall
  · rintro z ⟨x, hx, rfl⟩
    obtain ⟨v, hv, hv0⟩ := hker
    let w := (‖v‖⁻¹ : ℝ) • v
    have hwn : ‖w‖ = 1 := by simp [w, norm_smul, norm_ne_zero_iff.mpr hv0]
    have hwL : L w = 0 := by simp [w, hv]
    have hxn : ‖x‖ ≤ 1 := by simpa using hx
    have htwo : 1 ≤ ‖x + (2 : ℝ) • w‖ := by
      have h := norm_sub_le (x + (2 : ℝ) • w) x
      have heq : x + (2 : ℝ) • w - x = (2 : ℝ) • w := by abel
      rw [heq, norm_smul, hwn] at h
      norm_num at h
      linarith
    have hc : Continuous (fun t : ℝ => ‖x + t • w‖) :=
      (continuous_const.add (continuous_id.smul continuous_const)).norm
    obtain ⟨t, ht, htn⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2)
      hc.continuousOn (show (1 : ℝ) ∈ Icc ‖x + (0 : ℝ) • w‖ ‖x + (2 : ℝ) • w‖ by
        simpa using And.intro hxn htwo)
    refine ⟨x + t • w, ?_, ?_⟩
    · simpa using htn
    · simp [hwL]

lemma realThree_complex_kernel (L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℂ) :
    ∃ v, L v = 0 ∧ v ≠ 0 := by
  by_contra h
  have hker : ∀ v, L v = 0 → v = 0 := by simpa only [not_exists, not_and, not_not] using h
  have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hker)
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  norm_num at hdim

abbrev BlochSpace := EuclideanSpace ℝ (Fin 3)

def blochLinear (a b c : ℂ) : BlochSpace →ₗ[ℝ] ℂ where
  toFun u := (u 0 : ℂ) * a + (u 1 : ℂ) * b + (u 2 : ℂ) * c
  map_add' u v := by simp only [PiLp.add_apply, Complex.ofReal_add]; ring
  map_smul' t u := by
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
      Complex.real_smul]
    ring

lemma convex_bloch_image (d a b c : ℂ) :
    Convex ℝ ((fun u : BlochSpace => d + blochLinear a b c u) '' sphere 0 1) := by
  have heq := linear_sphere_image_eq_ball_image (blochLinear a b c)
    (realThree_complex_kernel _)
  have himage : (fun u : BlochSpace => d + blochLinear a b c u) '' sphere 0 1 =
      (fun z : ℂ => d + z) '' (blochLinear a b c '' closedBall 0 1) := by
    rw [← heq, image_image]
  rw [himage]
  exact ((convex_closedBall (0 : BlochSpace) 1).linear_image _).translate d

end

section
open scoped ComplexConjugate
open Set Metric

def spinorBloch (a b : ℂ) : BlochSpace :=
  WithLp.toLp 2 ![Complex.normSq a - Complex.normSq b,
    2 * (conj a * b).re, 2 * (conj a * b).im]

lemma spinorBloch_norm_sq (a b : ℂ) :
    ‖spinorBloch a b‖ ^ 2 = (Complex.normSq a + Complex.normSq b) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [spinorBloch, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

lemma spinorBloch_sphere {a b : ℂ} (h : Complex.normSq a + Complex.normSq b = 1) :
    spinorBloch a b ∈ sphere 0 1 := by
  have hn := spinorBloch_norm_sq a b
  rw [h] at hn
  simp only [mem_sphere, dist_zero_right]
  nlinarith [norm_nonneg (spinorBloch a b)]

lemma exists_spinor_of_sphere {u v w : ℝ} (h : u ^ 2 + v ^ 2 + w ^ 2 = 1) :
    ∃ a b : ℂ, Complex.normSq a + Complex.normSq b = 1 ∧
      Complex.normSq a - Complex.normSq b = u ∧
      2 * (conj a * b).re = v ∧ 2 * (conj a * b).im = w := by
  have hu : -1 ≤ u := by nlinarith [sq_nonneg v, sq_nonneg w]
  by_cases hpole : u = -1
  · have hv : v = 0 := by nlinarith [sq_nonneg w]
    have hw : w = 0 := by nlinarith [sq_nonneg v]
    exact ⟨0, 1, by simp [hpole, hv, hw]⟩
  · have hult : -1 < u := lt_of_le_of_ne hu (Ne.symm hpole)
    have hup : 0 < (1 + u) / 2 := by linarith
    let s : ℝ := Real.sqrt ((1 + u) / 2)
    have hspos : 0 < s := Real.sqrt_pos.mpr hup
    have hs : s ^ 2 = (1 + u) / 2 := Real.sq_sqrt hup.le
    let a : ℂ := s
    let b : ℂ := ((v : ℂ) + (w : ℂ) * Complex.I) / (2 * a)
    have ha0 : a ≠ 0 := by
      dsimp [a]
      exact_mod_cast hspos.ne'
    have hna : Complex.normSq a = (1 + u) / 2 := by
      simpa [a, Complex.normSq_apply, pow_two] using hs
    have hab : 2 * (conj a * b) = (v : ℂ) + (w : ℂ) * Complex.I := by
      have hac : conj a = a := by simp [a]
      dsimp [b]
      rw [hac]
      field_simp
    have hnab : 4 * Complex.normSq a * Complex.normSq b = v ^ 2 + w ^ 2 := by
      have hn := congrArg Complex.normSq hab
      rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj] at hn
      have htwo : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
      rw [htwo] at hn
      simpa [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two, mul_assoc] using hn
    have hmul : (Complex.normSq a) * (Complex.normSq a + Complex.normSq b - 1) = 0 := by
      nlinarith
    have hsum : Complex.normSq a + Complex.normSq b = 1 := by
      have hzero := (mul_eq_zero.mp hmul).resolve_left (by rw [hna]; exact hup.ne')
      linarith
    refine ⟨a, b, hsum, ?_, ?_, ?_⟩
    · linarith
    · have hh := congrArg Complex.re hab
      simpa using hh
    · have hh := congrArg Complex.im hab
      simpa using hh

lemma exists_spinor_bloch {u : BlochSpace} (hu : u ∈ sphere 0 1) :
    ∃ a b : ℂ, Complex.normSq a + Complex.normSq b = 1 ∧ spinorBloch a b = u := by
  have hn : ‖u‖ = 1 := by simpa using hu
  have hsq : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    have hh := EuclideanSpace.real_norm_sq_eq u
    rw [hn, Fin.sum_univ_three] at hh
    simpa using hh.symm
  obtain ⟨a,b,hs,h0,h1,h2⟩ := exists_spinor_of_sphere hsq
  refine ⟨a,b,hs, ?_⟩
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

def spinorQuadratic (A B C D a b : ℂ) : ℂ :=
  (Complex.normSq a : ℂ) * A + conj a * b * B + conj b * a * C + (Complex.normSq b : ℂ) * D

lemma spinorQuadratic_bloch (A B C D a b : ℂ)
    (h : Complex.normSq a + Complex.normSq b = 1) :
    spinorQuadratic A B C D a b =
      (A + D) / 2 + blochLinear ((A-D)/2) ((B+C)/2)
        (Complex.I * (B-C)/2) (spinorBloch a b) := by
  have hsum : ((Complex.normSq a : ℂ) + (Complex.normSq b : ℂ)) = 1 := by exact_mod_cast h
  have hrewrite : (A + D) / 2 =
      ((Complex.normSq a : ℂ) + (Complex.normSq b : ℂ)) * (A + D) / 2 := by rw [hsum, one_mul]
  rw [hrewrite]
  apply Complex.ext <;>
    simp [spinorQuadratic, blochLinear, spinorBloch, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im] <;> ring

def spinorRange (A B C D : ℂ) : Set ℂ :=
  {z | ∃ a b : ℂ, Complex.normSq a + Complex.normSq b = 1 ∧ spinorQuadratic A B C D a b = z}

lemma spinorRange_eq (A B C D : ℂ) :
    spinorRange A B C D =
      (fun u : BlochSpace => (A+D)/2 + blochLinear ((A-D)/2) ((B+C)/2)
        (Complex.I * (B-C)/2) u) '' sphere 0 1 := by
  ext z
  constructor
  · rintro ⟨a,b,h,rfl⟩
    exact ⟨spinorBloch a b, spinorBloch_sphere h, (spinorQuadratic_bloch A B C D a b h).symm⟩
  · rintro ⟨u,hu,rfl⟩
    obtain ⟨a,b,hs,rfl⟩ := exists_spinor_bloch hu
    exact ⟨a,b,hs,spinorQuadratic_bloch A B C D a b hs⟩

lemma convex_spinorRange (A B C D : ℂ) : Convex ℝ (spinorRange A B C D) := by
  rw [spinorRange_eq]
  exact convex_bloch_image _ _ _ _

end

open scoped ComplexConjugate InnerProductSpace
section Compression
variable {E : Type u_243} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma orthonormal_pair_norm (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℂ e f = 0) (a b : ℂ) :
    ‖a • e + b • f‖ ^ 2 = Complex.normSq a + Complex.normSq b := by
  have hab : inner ℂ (a • e) (b • f) = 0 := by
    rw [inner_smul_left, inner_smul_right, hef]; simp
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • e) (b • f) hab
  simpa [norm_smul, he, hf, Complex.normSq_eq_norm_sq, pow_two] using hn

lemma quadratic_compression (T : E →L[ℂ] E) (e f : E) (a b : ℂ) :
    inner ℂ (a • e + b • f) (T (a • e + b • f)) =
      spinorQuadratic (inner ℂ e (T e)) (inner ℂ e (T f))
        (inner ℂ f (T e)) (inner ℂ f (T f)) a b := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, spinorQuadratic]
  rw [← Complex.mul_conj a, ← Complex.mul_conj b]
  ring

def operatorNumericalRange (T : E →L[ℂ] E) : Set ℂ :=
  {z | ∃ x : E, ‖x‖ = 1 ∧ inner ℂ x (T x) = z}

lemma compression_spinor_subset (T : E →L[ℂ] E) (e f : E)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℂ e f = 0) :
    spinorRange (inner ℂ e (T e)) (inner ℂ e (T f))
      (inner ℂ f (T e)) (inner ℂ f (T f)) ⊆ operatorNumericalRange T := by
  rintro z ⟨a,b,hab,rfl⟩
  refine ⟨a • e + b • f, ?_, quadratic_compression T e f a b⟩
  have hn := orthonormal_pair_norm e f he hf hef a b
  rw [hab] at hn
  nlinarith [norm_nonneg (a • e + b • f)]

theorem convex_operatorNumericalRange (T : E →L[ℂ] E) :
    Convex ℝ (operatorNumericalRange T) := by
  intro z hz w hw s t hs ht hst
  obtain ⟨e,he,rfl⟩ := hz
  obtain ⟨y,hy,rfl⟩ := hw
  let α := inner ℂ e y
  let v := y - α • e
  have hev : inner ℂ e v = 0 := by
    dsimp [v, α]
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, he]
    simp
  by_cases hv : v = 0
  · have hye : y = α • e := sub_eq_zero.mp hv
    have hα : ‖α‖ = 1 := by simpa [hye, norm_smul, he] using hy
    have hα2 : Complex.normSq α = 1 := by rw [Complex.normSq_eq_norm_sq, hα]; norm_num
    have hval : inner ℂ y (T y) = inner ℂ e (T e) := by
      rw [hye, map_smul, inner_smul_left, inner_smul_right]
      calc
        conj α * (α * inner ℂ e (T e)) = (α * conj α) * inner ℂ e (T e) := by ring
        _ = _ := by rw [Complex.mul_conj, hα2]; simp
    rw [hval, ← add_smul, hst, one_smul]
    exact ⟨e, he, rfl⟩
  · let f : E := ((‖v‖⁻¹ : ℝ) : ℂ) • v
    have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hf : ‖f‖ = 1 := by
      simp [f, norm_smul, hnv]
    have hef : inner ℂ e f = 0 := by
      change inner ℂ e (((‖v‖⁻¹ : ℝ) : ℂ) • v) = 0
      rw [inner_smul_right, hev, mul_zero]
    let β : ℂ := ‖v‖
    have hβ : β • f = v := by
      simp [β, f, smul_smul, hnv]
    have hyrep : y = α • e + β • f := by
      rw [hβ]
      dsimp [v]
      abel
    have hunit : Complex.normSq α + Complex.normSq β = 1 := by
      have hn := orthonormal_pair_norm e f he hf hef α β
      rw [← hyrep, hy] at hn
      simpa using hn.symm
    have hzS : inner ℂ e (T e) ∈ spinorRange (inner ℂ e (T e)) (inner ℂ e (T f))
        (inner ℂ f (T e)) (inner ℂ f (T f)) := by
      exact ⟨1,0,by simp,by simp [spinorQuadratic]⟩
    have hwS : inner ℂ y (T y) ∈ spinorRange (inner ℂ e (T e)) (inner ℂ e (T f))
        (inner ℂ f (T e)) (inner ℂ f (T f)) := by
      refine ⟨α,β,hunit,?_⟩
      rw [← quadratic_compression, ← hyrep]
    exact compression_spinor_subset T e f he hf hef
      (convex_spinorRange _ _ _ _ hzS hwS hs ht hst)

end Compression

theorem numericalRange_convex {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Convex ℝ (numericalRange A) :=
  convex_operatorNumericalRange (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A)


end CompleteCrouzeix

end

end OAI
