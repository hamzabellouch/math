import OAI.Probability.InvariantIsing.Cavity.CavityFiniteGaussian

namespace OAI

/-! Almost-sure nonsingularity of the fixed-width iid Gaussian block. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

namespace InvariantIsing

private lemma gaussian_pi_extract_law {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (f : J → I) (hf : Function.Injective f) :
    (Measure.pi (fun _ : I => gaussianReal 0 1)).map
      (fun x j => x (f j)) = Measure.pi (fun _ : J => gaussianReal 0 1) := by
  have hi : iIndepFun (fun i : I => fun x : I → ℝ => x i)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have he := (hi.precomp hf).map_fun_eq_pi_map (fun j =>
    (measurable_pi_apply (f j)).aemeasurable)
  simpa only [(measurePreserving_eval (fun _ : I => gaussianReal 0 1) _).map_eq] using he

/-- Replacing one coordinate by a fresh standard Gaussian preserves the
finite iid Gaussian law. The unused old coordinate causes no problem. -/
private lemma gaussian_pi_update_law {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    ((Measure.pi (fun _ : I => gaussianReal 0 1)).prod (gaussianReal 0 1)).map
      (fun p : (I → ℝ) × ℝ => Function.update p.1 i p.2) =
        Measure.pi (fun _ : I => gaussianReal 0 1) := by
  have hm : Measurable (fun p : (I → ℝ) × ℝ => Function.update p.1 i p.2) :=
    measurable_update'
  symm
  apply Measure.pi_eq
  intro s hs
  have hpre : (fun p : (I → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro hp
      refine ⟨?_, ?_⟩
      · intro j
        by_cases hji : j = i
        · subst j; simp
        · simpa only [Function.update_of_ne hji] using hp j
      · simpa only [Function.update_self] using hp i
    · rintro ⟨hp, hi⟩ j
      by_cases hji : j = i
      · subst j; simpa only [Function.update_self] using hi
      · simpa only [Function.update_of_ne hji] using hp j
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    Measure.pi_pi]
  have he : (fun j => (gaussianReal 0 1) (Function.update s i Set.univ j)) =
      Function.update (fun j => (gaussianReal 0 1) (s j)) i 1 := by
    funext j
    by_cases hji : j = i
    · subst j; simp
    · simp only [Function.update_of_ne hji]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i), one_mul]
  simpa only [Finset.sdiff_singleton_eq_erase] using
    (Finset.prod_erase_mul (s := Finset.univ)
      (f := fun j => (gaussianReal 0 1) (s j)) (Finset.mem_univ i))

private lemma determinant_update_corner_affine (n : ℕ)
    (x : Fin (n + 1) × Fin (n + 1) → ℝ) :
    ∃ c : ℝ, ∀ t : ℝ,
      Matrix.det (fun i j => Function.update x (0, 0) t (i, j)) =
        t * Matrix.det (fun i j : Fin n => x (i.succ, j.succ)) + c := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => x (i, j)
  refine ⟨∑ j : Fin n, (-1 : ℝ) ^ (j.succ : ℕ) * A 0 j.succ *
    Matrix.det (A.submatrix Fin.succ j.succ.succAbove), ?_⟩
  intro t
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => Function.update x (0, 0) t (i, j)
  have hb (j : Fin (n + 1)) : B.submatrix Fin.succ j.succAbove =
      A.submatrix Fin.succ j.succAbove := by
    ext a b
    change Function.update x (0, 0) t (a.succ, j.succAbove b) = x (a.succ, j.succAbove b)
    exact Function.update_of_ne
      (show (a.succ, j.succAbove b) ≠ (0, 0) from
        fun h => Fin.succ_ne_zero a (congrArg Prod.fst h)) t x
  change B.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp_rw [hb]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  have h00 : B 0 0 = t := by simp [B]
  have h0j (j : Fin n) : B 0 j.succ = A 0 j.succ := by simp [B, A]
  rw [h00]
  simp_rw [h0j]
  rfl

private lemma gaussian_affine_ne_zero (a c : ℝ) (ha : a ≠ 0) :
    ∀ᵐ t ∂gaussianReal 0 1, t * a + c ≠ 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hn : ∀ᵐ t ∂gaussianReal 0 1, t ≠ -c / a := by
    exact compl_mem_ae_iff.mpr (measure_singleton (-c / a))
  filter_upwards [hn] with t ht
  intro he
  apply ht
  apply (eq_div_iff ha).mpr
  linarith

/-- A square matrix with independent standard Gaussian entries is
nonsingular almost surely, including the empty-matrix convention. -/
theorem cavityGaussianSquare_det_ne_zero (n : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1),
      Matrix.det (fun i j => x (i, j)) ≠ 0 := by
  induction n with
  | zero =>
    apply ae_of_all
    intro x
    have h : Matrix.det (show Matrix (Fin 0) (Fin 0) ℝ from fun i j => x (i, j)) = 1 :=
      Matrix.det_isEmpty
    exact h.trans_ne one_ne_zero
  | succ n ih =>
    let μ := Measure.pi (fun _ : Fin (n + 1) × Fin (n + 1) => gaussianReal 0 1)
    let corner : Fin (n + 1) × Fin (n + 1) := (0, 0)
    let f : Fin n × Fin n → Fin (n + 1) × Fin (n + 1) := fun p => (p.1.succ, p.2.succ)
    have hf : Function.Injective f := by
      intro p q h
      exact Prod.ext (Fin.succ_inj.mp (congrArg Prod.fst h))
        (Fin.succ_inj.mp (congrArg Prod.snd h))
    have hminor : ∀ᵐ x ∂μ, Matrix.det (fun i j : Fin n => x (i.succ, j.succ)) ≠ 0 := by
      have hh : ∀ᵐ y ∂μ.map (fun x j => x (f j)),
          Matrix.det (fun i j : Fin n => y (i, j)) ≠ 0 := by
        rw [gaussian_pi_extract_law f hf]
        exact ih
      exact ae_of_ae_map
        (show AEMeasurable (fun x j => x (f j)) μ from (by fun_prop : Measurable _).aemeasurable) hh
    have hpair : ∀ᵐ p ∂μ.prod (gaussianReal 0 1),
        Matrix.det (fun i j => Function.update p.1 corner p.2 (i, j)) ≠ 0 := by
      have hm : Measurable (fun p : (Fin (n + 1) × Fin (n + 1) → ℝ) × ℝ =>
          Matrix.det (fun i j => Function.update p.1 corner p.2 (i, j))) := by
        unfold corner
        fun_prop
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm measurable_const).compl).mpr
      filter_upwards [hminor] with x hx
      obtain ⟨c, hc⟩ := determinant_update_corner_affine n x
      filter_upwards [gaussian_affine_ne_zero _ c hx] with t ht
      simpa only [corner, hc] using ht
    rw [← gaussian_pi_update_law corner]
    apply (ae_map_iff (by fun_prop)
      (measurableSet_eq_fun (by fun_prop) measurable_const).compl).mpr
    exact hpair

/-- The concrete first `q` iid Gaussian rows used by the frame construction
are full rank almost surely. -/
theorem cavityGaussianRows_square_det_ne_zero (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Matrix.det (fun i j : Fin q => x i j) ≠ 0 := by
  have hh : ∀ᵐ y ∂(cavityGaussianRows q).map
      (fun x : ℕ → Fin q → ℝ => fun p : Fin q × Fin q => x p.1 p.2),
      Matrix.det (fun i j : Fin q => y (i, j)) ≠ 0 := by
    rw [(cavityGaussianRows_finite_array_law q q).map_eq]
    exact cavityGaussianSquare_det_ne_zero q
  exact ae_of_ae_map (cavityGaussianRows_finite_array_law q q).aemeasurable hh

end InvariantIsing

end

end OAI
