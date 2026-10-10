import OAI.NumberTheory.JointDickman.Counting.SamplingMoments

namespace OAI

/-!
# Quantitative finite sampling transfer

The finite family consists of sampled column sequences and one sign per
sampled occurrence. Its cardinal is `(2 * N)^m`, including repeated columns.
The common bad event is paid once. Moment and tail obligations are explicit
mathematical hypotheses, not additional published inputs.
-/

open Finset
open scoped BigOperators
open JointDickman.PublishedInputs

namespace JointDickman

section ProbabilityTransfer

variable {Ω : Type*} [Fintype Ω]

theorem finiteProbability_nonneg (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (E : Ω → Prop) :
    0 ≤ finiteProbability w E := by
  classical
  exact sum_nonneg fun x _ => by by_cases h : E x <;> simp [h, hw x]

theorem finiteExpectation_nonneg (w f : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ finiteExpectation w f :=
  sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)

theorem finiteExpectation_indicator_cs (w A : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (B : Ω → Prop) [DecidablePred B] :
    finiteExpectation w (fun x => if B x then A x else 0) ≤
      Real.sqrt (finiteExpectation w (fun x => A x ^ 2) * finiteProbability w B) := by
  classical
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset Ω)
    (f := fun x => w x * A x ^ 2) (g := fun x => if B x then w x else 0)
    (r := fun x => w x * (if B x then A x else 0))
    (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    (fun x _ => by by_cases hb : B x <;> simp [hb, hw x])
    (fun x _ => by
      by_cases hb : B x
      · simp only [hb, ite_true]
        ring_nf
        exact le_rfl
      · simp [hb])
  have hprob : (∑ x, if B x then w x else 0) = finiteProbability w B := by
    unfold finiteProbability
    apply sum_congr rfl
    intro x _
    by_cases hx : B x <;> simp [hx]
  rw [hprob] at h
  exact Real.le_sqrt_of_sq_le h

theorem finiteProbability_bad_family {J : Type*} [Fintype J]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (G : Ω → Prop) (E : J → Ω → Prop) :
    finiteProbability w (fun x => ¬ G x ∨ ∃ j, E j x) ≤
      finiteProbability w (fun x => ¬ G x) +
        ∑ j, finiteProbability w (fun x => G x ∧ E j x) := by
  classical
  have hs : finiteProbability w (fun x => ¬ G x ∨ ∃ j, E j x) =
      finiteProbability w (fun x => ¬ G x) +
        finiteProbability w (fun x => ∃ j, G x ∧ E j x) := by
    unfold finiteProbability
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    by_cases hg : G x <;> simp [hg]
  rw [hs]
  have hu := finiteProbability_union_le w hw (fun j x => G x ∧ E j x)
  linarith

/-- Finite Cauchy–Schwarz turns a tail estimate into an expectation estimate. -/
theorem finiteExpectation_transfer {J : Type*} [Fintype J]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hwone : (∑ x, w x) = 1)
    (X A : Ω → ℝ) (Z : J → Ω → ℝ) (G : Ω → Prop)
    (e u V t : ℝ) (hthreshold : 0 ≤ u + e) (hV : 0 ≤ V)
    (hdom : ∀ x, X x ≤ A x)
    (hgood : ∀ x, G x → ∃ j, X x ≤ Z j x + e)
    (htail : ∀ j, finiteProbability w (fun x => G x ∧ u < Z j x) ≤ t)
    (hmoment : finiteExpectation w (fun x => A x ^ 2) ≤ V) :
    finiteExpectation w X ≤ u + e +
      Real.sqrt (V * (finiteProbability w (fun x => ¬ G x) + (Fintype.card J : ℝ) * t)) := by
  classical
  let B : Ω → Prop := fun x => ¬ G x ∨ ∃ j, u < Z j x
  have hB : finiteProbability w B ≤
      finiteProbability w (fun x => ¬ G x) + (Fintype.card J : ℝ) * t := by
    have hu := finiteProbability_bad_family w hw G (fun j x => u < Z j x)
    have hs := sum_le_sum (s := (univ : Finset J)) (fun j _ => htail j)
    simp only [sum_const, card_univ, nsmul_eq_mul] at hs
    exact hu.trans (by linarith)
  have hpoint (x : Ω) : X x ≤ u + e + (if B x then A x else 0) := by
    by_cases hb : B x
    · simp only [hb, ite_true]
      linarith [hdom x]
    · have hg : G x := by
        by_contra hng
        exact hb (Or.inl hng)
      obtain ⟨j, hj⟩ := hgood x hg
      have hz : Z j x ≤ u := by
        by_contra hzu
        exact hb (Or.inr ⟨j, lt_of_not_ge hzu⟩)
      simp only [hb, ite_false, add_zero]
      linarith
  have hE := finiteExpectation_mono w hw hpoint
  rw [finiteExpectation_add, finiteExpectation_const w hwone] at hE
  have hcs := finiteExpectation_indicator_cs w A hw B
  have hmul : finiteExpectation w (fun x => A x ^ 2) * finiteProbability w B ≤
      V * (finiteProbability w (fun x => ¬ G x) + (Fintype.card J : ℝ) * t) :=
    mul_le_mul hmoment hB (finiteProbability_nonneg w hw B) hV
  have hsqrt := Real.sqrt_le_sqrt hmul
  linarith

end ProbabilityTransfer

section CutFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unnormalized finite real sign-cut maximum. -/
noncomputable def kernelCutMaximum (K : ι → ι → ℝ) : ℝ :=
  (univ : Finset ((ι → Bool) × (ι → Bool))).sup' univ_nonempty
    (fun st => |realBilinear K (fun i => cutSign (st.1 i)) (fun j => cutSign (st.2 j))|)

theorem kernelCutMaximum_le (K : ι → ι → ℝ) (C : ℝ)
    (hC : ∀ s t : ι → Bool,
      |realBilinear K (fun i => cutSign (s i)) (fun j => cutSign (t j))| ≤ C) :
    kernelCutMaximum K ≤ C := by
  apply Finset.sup'_le
  intro st _
  exact hC st.1 st.2

theorem kernelCutMaximum_nonneg (K : ι → ι → ℝ) : 0 ≤ kernelCutMaximum K := by
  exact (abs_nonneg _).trans (Finset.le_sup'
    (fun st : (ι → Bool) × (ι → Bool) =>
      |realBilinear K (fun i => cutSign (st.1 i)) (fun j => cutSign (st.2 j))|)
    (mem_univ ((fun _ => false), (fun _ => false))))

theorem kernelCutMaximum_le_absolute_mass (K : ι → ι → ℝ) :
    kernelCutMaximum K ≤ ∑ i, ∑ j, |K i j| := by
  apply kernelCutMaximum_le
  intro s t
  unfold realBilinear
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  simp [abs_mul, abs_cutSign]

/-- A sampled column sequence with a sign attached to each occurrence. -/
abbrev ColumnSample (m : ℕ) := (Fin m → ι) × (Fin m → Bool)

omit [DecidableEq ι] in
theorem card_columnSample (m : ℕ) :
    Fintype.card (ColumnSample (ι := ι) m) = (2 * Fintype.card ι) ^ m := by
  simp only [ColumnSample, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  rw [← Nat.mul_pow, Nat.mul_comm]

noncomputable def columnSampleResponse {m : ℕ} (K : ι → ι → ℝ)
    (s : ColumnSample (ι := ι) m) (i : ι) : ℝ :=
  responseSign (∑ a, K i (s.1 a) * cutSign (s.2 a))

noncomputable def columnSampleResidual {m : ℕ} (K : ι → ι → ℝ)
    (s : ColumnSample (ι := ι) m) : ℝ :=
  residualColumnBound K (univ.image s.1) (columnSampleResponse K s)

theorem kernelCutMaximum_sample_bound [Nonempty ι] (K : ι → ι → ℝ)
    (hsym : ∀ i j, K i j = K j i) (d Q : ℝ)
    (hrow : ∀ i, (∑ j, |K i j|) ≤ d) (hsquare : (∑ i, ∑ j, K i j ^ 2) ≤ Q)
    (m : ℕ) (hm : 0 < m) :
    ∃ s : ColumnSample (ι := ι) m, kernelCutMaximum K ≤ columnSampleResidual K s +
      (2 * Real.sqrt ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) / m * Q)) + 2 * m * d) := by
  obtain ⟨δ, σ, _, hσ⟩ := exists_small_column_skeleton K hsym d hrow m hm
  refine ⟨(σ, fun a => δ (σ a)), ?_⟩
  have hc := kernelCutMaximum_le K _ hσ
  have hmult : (Fintype.card ι : ℝ) *
      ((Fintype.card ι : ℝ) / m * ∑ i, ∑ j, K i j ^ 2) ≤
        (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) / m * Q) := by
    gcongr
  have hsqrt := Real.sqrt_le_sqrt hmult
  change kernelCutMaximum K ≤
    residualColumnBound K (univ.image σ) (sampledResponse K (fun j => cutSign (δ j)) σ) + _
  linarith

/-- The manuscript's normalization divides the sign maximum by `N`. -/
noncomputable def kernelCutNorm (K : ι → ι → ℝ) : ℝ :=
  kernelCutMaximum K / Fintype.card ι

noncomputable def kernelAbsoluteMass (K : ι → ι → ℝ) : ℝ :=
  (∑ i, ∑ j, |K i j|) / Fintype.card ι

noncomputable def columnSampleNorm {m : ℕ} (K : ι → ι → ℝ)
    (s : ColumnSample (ι := ι) m) : ℝ := columnSampleResidual K s / Fintype.card ι

noncomputable def samplingError (d Q : ℝ) (m : ℕ) : ℝ :=
  (2 * Real.sqrt ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) / m * Q)) +
    2 * m * d) / Fintype.card ι

theorem kernelCutNorm_le_absolute_mass (K : ι → ι → ℝ) :
    kernelCutNorm K ≤ kernelAbsoluteMass K :=
  div_le_div_of_nonneg_right (kernelCutMaximum_le_absolute_mass K) (Nat.cast_nonneg _)

theorem kernelCutNorm_sample_bound [Nonempty ι] (K : ι → ι → ℝ)
    (hsym : ∀ i j, K i j = K j i) (d Q : ℝ)
    (hrow : ∀ i, (∑ j, |K i j|) ≤ d) (hsquare : (∑ i, ∑ j, K i j ^ 2) ≤ Q)
    (m : ℕ) (hm : 0 < m) :
    ∃ s : ColumnSample (ι := ι) m,
      kernelCutNorm K ≤ columnSampleNorm K s + samplingError (ι := ι) d Q m := by
  obtain ⟨s, hs⟩ := kernelCutMaximum_sample_bound K hsym d Q hrow hsquare m hm
  refine ⟨s, ?_⟩
  have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)
  simpa only [kernelCutNorm, columnSampleNorm, samplingError, add_div] using hh

end CutFamily

section RandomMatrix

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Quantitative transfer from the finite family to the fully adaptive cut.
The common bad-event mass appears only once in the final error. -/
theorem randomMatrix_sampling_transfer
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hwone : (∑ x, w x) = 1)
    (K : Ω → ι → ι → ℝ) (G : Ω → Prop) (d Q u V t : ℝ)
    (m : ℕ) (hm : 0 < m) (hV : 0 ≤ V)
    (hthreshold : 0 ≤ u + samplingError (ι := ι) d Q m)
    (hsym : ∀ x, G x → ∀ i j, K x i j = K x j i)
    (hrow : ∀ x, G x → ∀ i, (∑ j, |K x i j|) ≤ d)
    (hsquare : ∀ x, G x → (∑ i, ∑ j, K x i j ^ 2) ≤ Q)
    (htail : ∀ s : ColumnSample (ι := ι) m,
      finiteProbability w (fun x => G x ∧ u < columnSampleNorm (K x) s) ≤ t)
    (hmoment : finiteExpectation w (fun x => kernelAbsoluteMass (K x) ^ 2) ≤ V) :
    finiteExpectation w (fun x => kernelCutNorm (K x)) ≤
      u + samplingError (ι := ι) d Q m +
        Real.sqrt (V * (finiteProbability w (fun x => ¬ G x) +
          (((2 * Fintype.card ι) ^ m : ℕ) : ℝ) * t)) := by
  have hh := finiteExpectation_transfer w hw hwone
    (fun x => kernelCutNorm (K x)) (fun x => kernelAbsoluteMass (K x))
    (fun s x => columnSampleNorm (K x) s) G
    (samplingError (ι := ι) d Q m) u V t hthreshold hV
    (fun x => kernelCutNorm_le_absolute_mass (K x))
    (fun x hx => kernelCutNorm_sample_bound (K x) (hsym x hx) d Q (hrow x hx) (hsquare x hx) m hm)
    htail hmoment
  simpa only [card_columnSample] using hh

end RandomMatrix

section KernelMoments

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem finiteExpectation_div (w f : Ω → ℝ) (c : ℝ) :
    finiteExpectation w (fun x => f x / c) = finiteExpectation w f / c := by
  simp only [div_eq_mul_inv, finiteExpectation_mul_const]

omit [DecidableEq ι] in
theorem kernelAbsoluteMass_sq_le_average_rows (K : ι → ι → ℝ) :
    kernelAbsoluteMass K ^ 2 ≤
      (∑ i, (∑ j, |K i j|) ^ 2) / Fintype.card ι := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ι)
    (fun _ => (1 : ℝ)) (fun i => ∑ j, |K i j|)
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at hcs
  unfold kernelAbsoluteMass
  calc
    _ = (∑ i, ∑ j, |K i j|) ^ 2 / (Fintype.card ι : ℝ) ^ 2 := div_pow _ _ _
    _ ≤ ((Fintype.card ι : ℝ) * ∑ i, (∑ j, |K i j|) ^ 2) /
        (Fintype.card ι : ℝ) ^ 2 := div_le_div_of_nonneg_right hcs (sq_nonneg _)
    _ = _ := by field_simp

omit [DecidableEq ι] in
theorem kernelAbsoluteMass_second_moment
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (K : Ω → ι → ι → ℝ) (V : ℝ)
    (hrow : ∀ i, finiteExpectation w (fun x => (∑ j, |K x i j|) ^ 2) ≤ V) :
    finiteExpectation w (fun x => kernelAbsoluteMass (K x) ^ 2) ≤ V := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ finiteExpectation w
        (fun x => (∑ i, (∑ j, |K x i j|) ^ 2) / Fintype.card ι) :=
      finiteExpectation_mono w hw (fun x => kernelAbsoluteMass_sq_le_average_rows (K x))
    _ = (∑ i, finiteExpectation w (fun x => (∑ j, |K x i j|) ^ 2)) /
        Fintype.card ι := by rw [finiteExpectation_div, finiteExpectation_sum]
    _ ≤ (∑ _i : ι, V) / Fintype.card ι :=
      div_le_div_of_nonneg_right (sum_le_sum (fun i _ => hrow i)) hN.le
    _ = V := by simp [hN.ne']

end KernelMoments

section SiteKernel

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype A]

/-- Realizing a finite site kernel on one independent configuration. -/
def realizedSiteKernel (E : ι → ι → A → A → ℝ) (x : ι → A) (i j : ι) : ℝ :=
  E i j (x i) (x j)

/-- The uniform-integrability moment required in the sampling transfer is
derived from the row-moment theorem. -/
theorem realizedSiteKernel_second_moment
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E H : ι → ι → A → A → ℝ)
    (hdom : ∀ i j a b, |E i j a b| ≤ H i j a b)
    (hdiag : ∀ i a, H i i a a = 0) (C q : ℝ)
    (hmean : ∀ i a, |siteRowMean p H i a| ≤ C)
    (hsquare : ∀ i, (∑ j, finiteExpectation (siteProductMass p)
      (fun x => H i j (x i) (x j) ^ 2)) ≤ q) :
    finiteExpectation (siteProductMass p)
      (fun x => kernelAbsoluteMass (realizedSiteKernel E x) ^ 2) ≤ C ^ 2 + q := by
  apply kernelAbsoluteMass_second_moment _ (siteProductMass_nonneg p hp)
  intro i
  have hrow : finiteExpectation (siteProductMass p) (fun x => siteRowSum H i x ^ 2) ≤
      C ^ 2 + q := by
    have hh := siteRow_sq_le p hp hpone H hdiag i C (hmean i)
    rw [siteRowSquareMass_eq_sum_entries p hpone H hdiag i] at hh
    linarith [hsquare i]
  refine (finiteExpectation_mono (siteProductMass p) (siteProductMass_nonneg p hp) ?_).trans hrow
  intro x
  have hsum : (∑ j, |realizedSiteKernel E x i j|) ≤ siteRowSum H i x :=
    sum_le_sum fun j _ => hdom i j (x i) (x j)
  exact sq_le_sq₀ (sum_nonneg fun _ _ => abs_nonneg _)
    ((sum_nonneg fun _ _ => abs_nonneg _).trans hsum) |>.mpr hsum

/-- The finite quantitative transfer for actual independent site kernels.
Only the finite family tail bound remains an explicit sampling obligation. -/
theorem siteKernel_sampling_transfer
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E H : ι → ι → A → A → ℝ) (G : (ι → A) → Prop)
    (hdom : ∀ i j a b, |E i j a b| ≤ H i j a b)
    (hdiag : ∀ i a, H i i a a = 0) (hsym : ∀ i j a b, E i j a b = E j i b a)
    (C q d Q u t : ℝ) (m : ℕ) (hm : 0 < m) (hq : 0 ≤ q)
    (hmean : ∀ i a, |siteRowMean p H i a| ≤ C)
    (hsquare : ∀ i, (∑ j, finiteExpectation (siteProductMass p)
      (fun x => H i j (x i) (x j) ^ 2)) ≤ q)
    (hthreshold : 0 ≤ u + samplingError (ι := ι) d Q m)
    (hrowG : ∀ x, G x → ∀ i, (∑ j, |E i j (x i) (x j)|) ≤ d)
    (hsquareG : ∀ x, G x → (∑ i, ∑ j, E i j (x i) (x j) ^ 2) ≤ Q)
    (htail : ∀ s : ColumnSample (ι := ι) m,
      finiteProbability (siteProductMass p)
        (fun x => G x ∧ u < columnSampleNorm (realizedSiteKernel E x) s) ≤ t) :
    finiteExpectation (siteProductMass p) (fun x => kernelCutNorm (realizedSiteKernel E x)) ≤
      u + samplingError (ι := ι) d Q m +
        Real.sqrt ((C ^ 2 + q) * (finiteProbability (siteProductMass p) (fun x => ¬ G x) +
          (((2 * Fintype.card ι) ^ m : ℕ) : ℝ) * t)) := by
  apply randomMatrix_sampling_transfer _ (siteProductMass_nonneg p hp) (siteProductMass_sum p hpone)
    (realizedSiteKernel E) G d Q u (C ^ 2 + q) t m hm (add_nonneg (sq_nonneg C) hq) hthreshold
  · intro x _ i j
    exact hsym i j (x i) (x j)
  · exact hrowG
  · exact hsquareG
  · exact htail
  · exact realizedSiteKernel_second_moment p hp hpone E H hdom hdiag C q hmean hsquare

end SiteKernel

end JointDickman

end OAI
