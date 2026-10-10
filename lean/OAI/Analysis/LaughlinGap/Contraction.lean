import Mathlib
import OAI.Analysis.LaughlinGap.PairEnergy

namespace OAI

/-! Contraction. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators InnerProduct Topology

section BlockOperator
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

abbrev ColumnSpace (ι E : Type*) [Fintype ι] [NormedAddCommGroup E] := PiLp 2 (fun _ : ι => E)

noncomputable def columnProjection (b : ι) : ColumnSpace ι E →L[ℂ] E :=
  (PiLp.projₗ 2 (fun _ : ι => E) b).toContinuousLinearMap

noncomputable def columnInclusion (b : ι) : E →L[ℂ] ColumnSpace ι E :=
  (((WithLp.linearEquiv 2 ℂ (ι → E)).symm.toLinearMap).comp
    (LinearMap.single ℂ (fun _ : ι => E) b)).toContinuousLinearMap

omit [DecidableEq ι] in
@[simp] lemma columnProjection_apply (b : ι) (x : ColumnSpace ι E) :
    columnProjection b x = x b := rfl

@[simp] lemma columnInclusion_apply (b c : ι) (x : E) :
    columnInclusion b x c = if c = b then x else 0 := by
  change (Pi.single b x : ι → E) c = _
  rw [Pi.single_apply]

noncomputable def blockOperator (M : Matrix ι ι ℂ) (T : E →L[ℂ] E) :
    ColumnSpace ι E →L[ℂ] ColumnSpace ι E :=
  ∑ b, ∑ c, M b c • (columnInclusion b).comp (T.comp (columnProjection c))

@[simp] lemma blockOperator_apply (M : Matrix ι ι ℂ) (T : E →L[ℂ] E)
    (x : ColumnSpace ι E) (b : ι) : blockOperator M T x b = ∑ c, M b c • T (x c) := by
  classical
  simp [blockOperator, columnInclusion_apply, smul_ite]

lemma blockOperator_inner (M : Matrix ι ι ℂ) (T : E →L[ℂ] E)
    (x y : ColumnSpace ι E) :
    inner ℂ x (blockOperator M T y) = ∑ b, ∑ c, M b c * inner ℂ (x b) (T (y c)) := by
  simp only [PiLp.inner_apply, blockOperator_apply, inner_sum, inner_smul_right]

theorem blockOperator_tendsto {M : ℕ → Matrix ι ι ℂ} {M₀ : Matrix ι ι ℂ}
    {T : ℕ → E →L[ℂ] E} {T₀ : E →L[ℂ] E}
    (hM : ∀ b c, Filter.Tendsto (fun Q => M Q b c) Filter.atTop (𝓝 (M₀ b c)))
    (hT : Filter.Tendsto T Filter.atTop (𝓝 T₀)) :
    Filter.Tendsto (fun Q => blockOperator (M Q) (T Q)) Filter.atTop (𝓝 (blockOperator M₀ T₀)) := by
  apply tendsto_finsetSum
  intro b _
  apply tendsto_finsetSum
  intro c _
  apply (hM b c).smul
  have hf : Continuous (fun T : E →L[ℂ] E =>
      (columnInclusion b).comp (T.comp (columnProjection c))) := by fun_prop
  exact hf.continuousAt.tendsto.comp hT

theorem matrixLift_inner_eq_block (A : ι → Module.End ℂ E) (M : Matrix ι ι ℂ) (x : E) :
    inner ℂ x (matrixLift A M x) =
      inner ℂ (WithLp.toLp 2 (fun b => A b x))
        (blockOperator M (1 : E →L[ℂ] E) (WithLp.toLp 2 (fun b => A b x))) := by
  rw [blockOperator_inner]
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, inner_sum, inner_smul_right,
    LinearMap.adjoint_inner_right, one_apply_eq_self]

theorem conjugated_matrix_transfer
    (A : ι → Module.End ℂ E) (Δ : ℕ → E → E)
    (eStar : E → ℝ) (eQ : ℕ → E → ℝ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hA : ∀ x, (∑ b, ‖A b x‖ ^ 2) ≤ C₀ * eStar x)
    (hΔ : ∀ᶠ Q in Filter.atTop, ∀ x, eStar (Δ Q x) ≤ eQ Q x)
    (U : ℕ → E →L[ℂ] E) (M : ℕ → Matrix ι ι ℂ) (M₀ : Matrix ι ι ℂ)
    (hU : Filter.Tendsto U Filter.atTop (𝓝 1))
    (hM : ∀ b c, Filter.Tendsto (fun Q => M Q b c) Filter.atTop (𝓝 (M₀ b c)))
    (h₀ : (matrixLift A M₀).IsPositive) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Filter.Tendsto ρ Filter.atTop (𝓝 0) ∧
      ∀ᶠ Q in Filter.atTop, ∀ x,
        -(ρ Q) * eQ Q x ≤
          (∑ b, ∑ c, M Q b c * inner ℂ (U Q (A b (Δ Q x)))
            (U Q (A c (Δ Q x)))).re := by
  let S := blockOperator M₀ (1 : E →L[ℂ] E)
  let T := fun Q => blockOperator (M Q) ((U Q).adjoint * U Q)
  have hAdj : Filter.Tendsto (fun Q => (U Q).adjoint) Filter.atTop (𝓝 1) := by
    simpa only [Function.comp_def, ContinuousLinearMap.adjoint_one] using
      ContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp hU
  have hT : Filter.Tendsto T Filter.atTop (𝓝 S) := by
    exact blockOperator_tendsto hM (by simpa using hAdj.mul hU)
  refine ⟨fun Q => C₀ * ‖T Q - S‖, fun Q => mul_nonneg hC₀ (norm_nonneg _),
    relative_column_error_tendsto hT, ?_⟩
  filter_upwards [hΔ] with Q hΔQ
  intro x
  have hp := relative_column_perturbation_bound (fun b x => A b x) (Δ Q) eStar (eQ Q)
    hC₀ hA hΔQ (T Q) S (fun x => ?_) x
  · simpa only [T, blockOperator_inner, PiLp.toLp_apply, mul_apply_eq_comp,
      ContinuousLinearMap.adjoint_inner_right, RCLike.re_eq_complex_re] using hp
  · rw [← matrixLift_inner_eq_block]
    exact h₀.re_inner_nonneg_right x

omit [DecidableEq ι] in

theorem matrixLift_conjugated_inner (A : ι → Module.End ℂ E) (M : Matrix ι ι ℂ)
    (U D : Module.End ℂ E) (x : E) :
    inner ℂ x (matrixLift (fun b => U * A b * D) M x) =
      ∑ b, ∑ c, M b c * inner ℂ (U (A b (D x))) (U (A c (D x))) := by
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, inner_sum, inner_smul_right,
    LinearMap.adjoint_inner_right]

omit [Fintype ι] [DecidableEq ι] in

theorem matrix_compression_tendsto {κ : Type*} [Fintype κ]
    {W : ℕ → Matrix ι κ ℂ} {W₀ : Matrix ι κ ℂ}
    {C : ℕ → Matrix κ κ ℂ} {C₀ : Matrix κ κ ℂ}
    (hW : ∀ b r, Filter.Tendsto (fun Q => W Q b r) Filter.atTop (𝓝 (W₀ b r)))
    (hC : ∀ r s, Filter.Tendsto (fun Q => C Q r s) Filter.atTop (𝓝 (C₀ r s)))
    (b c : ι) :
    Filter.Tendsto (fun Q => (W Q * C Q * (W Q).conjTranspose) b c)
      Filter.atTop (𝓝 ((W₀ * C₀ * W₀.conjTranspose) b c)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply tendsto_finsetSum
  intro r _
  apply Filter.Tendsto.mul
  · apply tendsto_finsetSum
    intro s _
    exact (hW b s).mul (hC s r)
  · exact (hW c r).star

end BlockOperator
end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators Topology InnerProduct

theorem extendLocal_relative_energy_bound {n m : ℕ} {ι : Type*} [Fintype ι]
    (S : Module.End ℂ (Hilbert n)) (B : ι → Module.End ℂ (Hilbert n)) (c : ℝ)
    (h : ∀ x, c * (∑ b, ‖B b x‖ ^ 2) ≤ (inner ℂ x (S x)).re) (x : Hilbert (n+m)) :
    c * (∑ b, ‖extendLocal (B b) x‖ ^ 2) ≤ (inner ℂ x (extendLocal S x)).re := by
  rw [inner_eq_sum_slice]
  simp_rw [norm_sq_eq_sum_slice, slice_extendLocal]
  rw [Complex.re_sum, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum (fun R _ => h (slice R x))

theorem local_relative_matrix_transfer {n L : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Fin L) (j k : ι → Fin n)
    (M : ℕ → Matrix ι ι ℂ) (M₀ : Matrix ι ι ℂ)
    (hM : ∀ b c, Filter.Tendsto (fun Q => M Q b c) Filter.atTop (𝓝 (M₀ b c)))
    (h₀ : (matrixLift (fun b => annihilation (k b) * annihilation (j b) *
      localPairStar n (p b).val) M₀).IsPositive) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Filter.Tendsto ρ Filter.atTop (𝓝 0) ∧
      ∀ᶠ Q in Filter.atTop, ∀ m (x : Hilbert (n+m)),
        -(ρ Q) * (∑ a : Fin L, ‖extendLocal (localPair n Q a.val) x‖ ^ 2) ≤
          (inner ℂ x (extendLocal (matrixLift
            (fun b => (localDeltaInv n Q).toLinearMap *
              (annihilation (k b) * annihilation (j b) * localPairStar n (p b).val) *
                (localDelta n Q).toLinearMap) (M Q)) x)).re := by
  let A : ι → Module.End ℂ (Hilbert n) :=
    fun b => annihilation (k b) * annihilation (j b) * localPairStar n (p b).val
  have hA (x : Hilbert n) :
      ∑ b, ‖A b x‖ ^ 2 ≤ (Fintype.card ι : ℝ) * localPairEnergyStar n L x := by
    apply annihilator_collection_bound p (fun a : Fin L => localPairStar n a.val)
      (fun b y => annihilation (k b) (annihilation (j b) y))
    · intro a
      simpa only [Finset.card_univ] using Finset.card_le_card
        (Finset.filter_subset (fun b => p b = a) Finset.univ)
    · intro b y
      exact double_annihilation_norm_le (j b) (k b) y
  have hΔ : ∀ᶠ Q in Filter.atTop, ∀ x,
      localPairEnergyStar n L (localDelta n Q x) ≤ localPairEnergy n L Q x := by
    filter_upwards [Filter.eventually_ge_atTop (L+2)] with Q hQ
    intro x
    exact localPairEnergy_transfer (by omega) (by omega) x
  obtain ⟨ρ, hρ, ht, hq⟩ := conjugated_matrix_transfer A (fun Q x => localDelta n Q x)
    (localPairEnergyStar n L) (fun Q => localPairEnergy n L Q)
    (C₀ := (Fintype.card ι : ℝ)) (Nat.cast_nonneg _) hA hΔ
    (localDeltaInv n) M M₀ (localDeltaInv_tendsto n) hM h₀
  refine ⟨ρ, hρ, ht, ?_⟩
  filter_upwards [hq] with Q hqQ
  intro m x
  apply extendLocal_relative_energy_bound _ (fun a : Fin L => localPair n Q a.val) (-ρ Q) ?_ x
  intro y
  rw [matrixLift_conjugated_inner]
  exact hqQ y

theorem localFour_factor_tendsto (p j k : ℕ) :
    Filter.Tendsto (fun Q => pairRescalingFactor Q p /
      (orbitalDiagonalFactor Q j * orbitalDiagonalFactor Q k)) Filter.atTop (𝓝 1) := by
  simpa only [Pi.div_def, Pi.mul_def, one_mul, div_one] using (pairRescalingFactor_tendsto p).div
    ((orbitalDiagonalFactor_tendsto j).mul (orbitalDiagonalFactor_tendsto k)) (by norm_num)

theorem local_four_family_transfer {n L : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (p : ι → Fin L) (j k : ι → Fin n)
    (s : ℕ → κ → ι → ℝ) (s₀ : κ → ι → ℝ)
    (C : ℕ → Matrix κ κ ℂ) (C₀ : Matrix κ κ ℂ)
    (hs : ∀ r b, Filter.Tendsto (fun Q => s Q r b) Filter.atTop (𝓝 (s₀ r b)))
    (hC : ∀ r t, Filter.Tendsto (fun Q => C Q r t) Filter.atTop (𝓝 (C₀ r t)))
    (h₀ : (matrixLift (fun r => ∑ b, (s₀ r b : ℂ) •
      (annihilation (k b) * annihilation (j b) * localPairStar n (p b).val)) C₀).IsPositive) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Filter.Tendsto ρ Filter.atTop (𝓝 0) ∧
      ∀ᶠ Q in Filter.atTop, ∀ m (x : Hilbert (n+m)),
        -(ρ Q) * (∑ a : Fin L, ‖extendLocal (localPair n Q a.val) x‖ ^ 2) ≤
          (inner ℂ x (extendLocal (matrixLift
            (fun r => ∑ b, (s Q r b : ℂ) •
              (annihilation (k b) * annihilation (j b) * localPair n Q (p b).val)) (C Q)) x)).re := by
  let A : ι → Module.End ℂ (Hilbert n) :=
    fun b => annihilation (k b) * annihilation (j b) * localPairStar n (p b).val
  let w : ℕ → Matrix ι κ ℂ := fun Q b r =>
    ((s Q r b * (pairRescalingFactor Q (p b).val /
      (orbitalDiagonalFactor Q (j b).val * orbitalDiagonalFactor Q (k b).val)) : ℝ) : ℂ)
  let w₀ : Matrix ι κ ℂ := fun b r => (s₀ r b : ℂ)
  have hw : ∀ b r, Filter.Tendsto (fun Q => w Q b r) Filter.atTop (𝓝 (w₀ b r)) := by
    intro b r
    have h := (hs r b).mul (localFour_factor_tendsto (p b).val (j b).val (k b).val)
    simpa only [Function.comp_def, mul_one, w, w₀] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp h
  have hM₀ : (matrixLift A (w₀ * C₀ * w₀.conjTranspose)).IsPositive := by
    rw [matrixLift_columns]
    simpa only [contractCombination, w₀, Complex.star_def, Complex.conj_ofReal] using h₀
  obtain ⟨ρ, hρ, ht, hq⟩ := local_relative_matrix_transfer p j k
    (fun Q => w Q * C Q * (w Q).conjTranspose) (w₀ * C₀ * w₀.conjTranspose)
    (matrix_compression_tendsto hw hC) hM₀
  refine ⟨ρ, hρ, ht, ?_⟩
  filter_upwards [hq, Filter.eventually_ge_atTop (n+L+2)] with Q hqQ hQ
  intro m x
  have hf (r : κ) :
      contractCombination (fun b => (localDeltaInv n Q).toLinearMap * A b *
        (localDelta n Q).toLinearMap) (fun b => w Q b r) =
      ∑ b, (s Q r b : ℂ) • (annihilation (k b) * annihilation (j b) * localPair n Q (p b).val) := by
    unfold contractCombination
    apply Finset.sum_congr rfl
    intro b _
    have hqb : (p b).val ≤ 2*Q-2 := by have := (p b).is_lt; omega
    rw [localFour_conjugation (by omega : 0 < Q) (by omega : n ≤ Q+1) hqb]
    simp [w, A, smul_smul]
  have heq : matrixLift
      (fun r => ∑ b, (s Q r b : ℂ) •
        (annihilation (k b) * annihilation (j b) * localPair n Q (p b).val)) (C Q) =
      matrixLift (fun b => (localDeltaInv n Q).toLinearMap * A b *
        (localDelta n Q).toLinearMap) (w Q * C Q * (w Q).conjTranspose) := by
    rw [matrixLift_columns]
    simp only [hf]
  rw [heq]
  exact hqQ m x

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct Topology ComplexOrder

@[simp] lemma word_nil {n : ℕ} : word ([] : List (Fin n)) = 1 := rfl
@[simp] lemma word_cons {n : ℕ} (j : Fin n) (js : List (Fin n)) :
    word (j :: js) = word js * annihilation j := rfl

lemma annihilation_anticommute {n : ℕ} (i j : Fin n) :
    annihilation i * annihilation j = -(annihilation j * annihilation i) := by
  by_cases h : i = j
  · subst j
    have hz : annihilation i * annihilation i = 0 := transition_square i false
    simp only [hz, neg_zero]
  · exact transition_anticommute_of_ne h false false

lemma word_perm_scalar {n : ℕ} {js ks : List (Fin n)} (h : js.Perm ks) :
    ∃ c : ℂ, word js = c • word ks := by
  induction h with
  | nil => exact ⟨1, by simp⟩
  | cons j h ih =>
    obtain ⟨c,hc⟩ := ih
    exact ⟨c, by simp only [word_cons, hc, smul_mul_assoc]⟩
  | swap i j js =>
    refine ⟨-1, ?_⟩
    rw [word_cons, word_cons, word_cons, word_cons]
    rw [mul_assoc, annihilation_anticommute i j, mul_neg, ← mul_assoc]
    simp only [neg_smul, one_smul]
  | trans h h' ih ih' =>
    obtain ⟨c,hc⟩ := ih
    obtain ⟨d,hd⟩ := ih'
    exact ⟨c*d, by rw [hc, hd, smul_smul]⟩

lemma word_eq_zero_of_not_nodup {n : ℕ} (js : List (Fin n)) (h : ¬ js.Nodup) :
    word js = 0 := by
  induction js with
  | nil => simp at h
  | cons j js ih =>
    by_cases hj : js.Nodup
    · have hm : j ∈ js := by simpa only [List.nodup_cons, hj, and_true, not_not] using h
      obtain ⟨c,hc⟩ := word_perm_scalar (List.perm_cons_erase hm)
      rw [word_cons, hc, word_cons, smul_mul_assoc, mul_assoc]
      have hz : annihilation j * annihilation j = 0 := transition_square j false
      rw [hz, mul_zero, smul_zero]
    · rw [word_cons, ih hj, zero_mul]

theorem word_normal_form {n : ℕ} (js : List (Fin n)) :
    ∃ c : ℂ, word js = c • word (js.toFinset.sort (· ≤ ·)) := by
  by_cases hn : js.Nodup
  · apply word_perm_scalar
    exact ((js.toFinset.sort_perm_toList (· ≤ ·)).trans (List.toFinset_toList hn)).symm
  · exact ⟨0, by rw [word_eq_zero_of_not_nodup js hn, zero_smul]⟩

@[simp] lemma inner_vacuum_left {n : ℕ} (x : Hilbert n) :
    inner ℂ (vacuum n) x = x ∅ := by
  simp [vacuum, EuclideanSpace.inner_single_left]

theorem basisContraction_adjoint_vacuum {n k : ℕ} (A : BasisLabel n k) :
    (basisContraction A).adjoint (vacuum n) = EuclideanSpace.single A.val 1 := by
  apply ext_inner_right ℂ
  intro x
  rw [LinearMap.adjoint_inner_left, inner_vacuum_left, basisContraction_apply_empty]
  simp [EuclideanSpace.inner_single_left]

noncomputable def allBasisContraction {n : ℕ} (A : Finset (Fin n)) : Module.End ℂ (Hilbert n) :=
  word (A.sort (· ≤ ·))

noncomputable def fullContraction {n : ℕ} (v : Hilbert n) : Module.End ℂ (Hilbert n) :=
  contractCombination allBasisContraction v

@[simp] theorem fullContraction_single {n : ℕ} (A : Finset (Fin n)) (c : ℂ) :
    fullContraction (EuclideanSpace.single A c) = star c • allBasisContraction A := by
  classical
  simp [fullContraction, contractCombination, PiLp.single_apply, apply_ite, ite_smul]

@[simp] theorem fullContraction_add {n : ℕ} (v w : Hilbert n) :
    fullContraction (v+w) = fullContraction v + fullContraction w := by
  simp [fullContraction, contractCombination, add_smul, Finset.sum_add_distrib]

@[simp] theorem fullContraction_smul {n : ℕ} (c : ℂ) (v : Hilbert n) :
    fullContraction (c • v) = star c • fullContraction v := by
  simp [fullContraction, contractCombination, smul_smul, Finset.smul_sum]

@[simp] theorem fullContraction_zero {n : ℕ} : fullContraction (0 : Hilbert n) = 0 := by
  simp [fullContraction, contractCombination]

noncomputable def reconstruct {n : ℕ} :
    Module.End ℂ (Hilbert n) →ₗ[ℂ] Module.End ℂ (Hilbert n) where
  toFun B := fullContraction (B.adjoint (vacuum n))
  map_add' B B' := by simp
  map_smul' c B := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, fullContraction_smul,
      Complex.star_def, Complex.conj_conj, RingHom.id_apply]

@[simp] lemma reconstruct_allBasisContraction {n : ℕ} (A : Finset (Fin n)) :
    reconstruct (allBasisContraction A) = allBasisContraction A := by
  change fullContraction ((basisContraction (⟨A,rfl⟩ : BasisLabel n A.card)).adjoint (vacuum n)) = _
  rw [basisContraction_adjoint_vacuum, fullContraction_single]
  simp

theorem reconstruct_word {n : ℕ} (js : List (Fin n)) : reconstruct (word js) = word js := by
  obtain ⟨c,hc⟩ := word_normal_form js
  rw [hc]
  change reconstruct (c • allBasisContraction js.toFinset) = c • allBasisContraction js.toFinset
  rw [map_smul, reconstruct_allBasisContraction]

theorem reconstruct_four_pair {n : ℕ} (v : Fin n → Fin n → ℂ) (j k : Fin n) :
    reconstruct (annihilation k * annihilation j * pairAnnihilator v) =
      annihilation k * annihilation j * pairAnnihilator v := by
  simp only [pairAnnihilator, Finset.mul_sum, mul_ite, mul_zero, mul_smul_comm,
    map_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : x < y
  · rw [ite_eq_left h, map_smul]
    congr 1
    have he : annihilation k * annihilation j * (annihilation y * annihilation x) =
        word [x,y,j,k] := by simp only [word_cons, word_nil, one_mul, mul_assoc]
    rw [he, reconstruct_word]
  · rw [ite_eq_right h, map_zero]

noncomputable def createdGram {n : ℕ} {ι : Type*} (B : ι → Module.End ℂ (Hilbert n)) :
    Matrix ι ι ℂ := fun r s => inner ℂ ((B r).adjoint (vacuum n)) ((B s).adjoint (vacuum n))

theorem annihilator_gram_positive {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → Module.End ℂ (Hilbert n)) (hB : ∀ r, reconstruct (B r) = B r)
    (C : Matrix ι ι ℂ) (hC : C.IsHermitian)
    (hG : (createdGram B * C * createdGram B).PosSemidef) :
    (matrixLift B C).IsPositive := by
  let W : Matrix (Finset (Fin n)) ι ℂ := fun A r => (B r).adjoint (vacuum n) A
  have heq : W.conjTranspose * W = createdGram B := by
    ext r s
    change (∑ A : Finset (Fin n), star (W A r) * W A s) = _
    simp only [W, createdGram, PiLp.inner_apply, RCLike.inner_apply]
    exact Finset.sum_congr rfl (fun A _ => mul_comm _ _)
  have hp := matrixLift_gram_positive allBasisContraction W C hC (by rwa [heq])
  have hf (r : ι) : contractCombination allBasisContraction (fun A => W A r) = B r := hB r
  simpa only [hf] using hp

theorem local_four_family_transfer_of_gram {n L : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p : ι → Fin L) (j k : ι → Fin n)
    (s : ℕ → κ → ι → ℝ) (s₀ : κ → ι → ℝ)
    (C : ℕ → Matrix κ κ ℂ) (C₀ : Matrix κ κ ℂ)
    (hs : ∀ r b, Filter.Tendsto (fun Q => s Q r b) Filter.atTop (𝓝 (s₀ r b)))
    (hC : ∀ r t, Filter.Tendsto (fun Q => C Q r t) Filter.atTop (𝓝 (C₀ r t)))
    (hC₀ : C₀.IsHermitian)
    (hG : let B := fun r => ∑ b, (s₀ r b : ℂ) •
        (annihilation (k b) * annihilation (j b) * localPairStar n (p b).val)
      (createdGram B * C₀ * createdGram B).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Filter.Tendsto ρ Filter.atTop (𝓝 0) ∧
      ∀ᶠ Q in Filter.atTop, ∀ m (x : Hilbert (n+m)),
        -(ρ Q) * (∑ a : Fin L, ‖extendLocal (localPair n Q a.val) x‖ ^ 2) ≤
          (inner ℂ x (extendLocal (matrixLift
            (fun r => ∑ b, (s Q r b : ℂ) •
              (annihilation (k b) * annihilation (j b) * localPair n Q (p b).val)) (C Q)) x)).re := by
  apply local_four_family_transfer p j k s s₀ C C₀ hs hC
  apply annihilator_gram_positive _ _ C₀ hC₀ hG
  intro r
  simp only [map_sum, map_smul, localPairStar, reconstruct_four_pair]

end LaughlinGap.Occupation

namespace LaughlinGap
open scoped BigOperators

theorem monic_eval_pos_of_nonnegative_coefficients (P : Polynomial ℝ) (hP : P.Monic)
    (hc : ∀ k, 0 ≤ P.coeff k) {x : ℝ} (hx : 0 < x) : 0 < P.eval x := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (hc k) (pow_nonneg hx.le k)
  · refine ⟨P.natDegree, Polynomial.natDegree_mem_support_of_nonzero hP.ne_zero, ?_⟩
    rw [hP.coeff_natDegree, one_mul]
    exact pow_pos hx _

theorem symmetric_posSemidef_of_charpoly_coefficients {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (hc : ∀ k, 0 ≤ (-M).charpoly.coeff k) : M.PosSemidef := by
  rw [hM.posSemidef_iff_eigenvalues_nonneg]
  intro i
  by_contra hn
  have hneg : hM.eigenvalues i < 0 := lt_of_not_ge hn
  have hm : -hM.eigenvalues i ∈ spectrum ℝ (-M) := by
    rw [← spectrum.neg_eq]
    simpa only [Set.mem_neg, neg_neg] using hM.eigenvalues_mem_spectrum_real i
  have hz := (Matrix.mem_spectrum_iff_isRoot_charpoly).mp hm
  have hp := monic_eval_pos_of_nonnegative_coefficients (-M).charpoly
    (-M).charpoly_monic hc (neg_pos.mpr hneg)
  exact (ne_of_gt hp) hz

theorem rational_charpoly_certificate_sound {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ) (hM : M.IsHermitian)
    (hc : ∀ k ≤ Fintype.card ι, 0 ≤ (-M).charpoly.coeff k) :
    (M.map (algebraMap ℚ ℝ)).PosSemidef := by
  apply symmetric_posSemidef_of_charpoly_coefficients
  · exact hM.map _ (fun x => by simp)
  · intro k
    have heq : -(M.map (algebraMap ℚ ℝ)) = (-M).map (algebraMap ℚ ℝ) := by
      ext i j
      simp
    rw [heq, Matrix.charpoly_map, Polynomial.coeff_map]
    have hh : 0 ≤ (-M).charpoly.coeff k := by
      by_cases hk : k ≤ Fintype.card ι
      · exact hc k hk
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using lt_of_not_ge hk)]
    change (0 : ℝ) ≤ ((-M).charpoly.coeff k : ℝ)
    exact_mod_cast hh

end LaughlinGap

namespace LaughlinGap
open scoped Topology

theorem comparison_coefficient_tendsto {ρ : ℕ → ℝ}
    (hρ : Filter.Tendsto ρ Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun Q => 1 - (93527408868499 / 10^14 : ℝ) -
      threeBodyTail Q - 1222*(3/10^6) - ρ Q) Filter.atTop (𝓝 gammaStar) := by
  have h := ((threeBodyTail_tendsto.const_sub
    (1 - (93527408868499 / 10^14 : ℝ))).sub_const (1222*(3/10^6))).sub hρ
  simpa only [sub_zero, final_margin_arithmetic] using h

theorem comparison_coefficient_eventually_lt {ρ : ℕ → ℝ}
    (hρ : Filter.Tendsto ρ Filter.atTop (𝓝 0)) {γ : ℝ} (hγ : γ < gammaStar) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, γ < 1 - (93527408868499 / 10^14 : ℝ) -
      threeBodyTail Q - 1222*(3/10^6) - ρ Q := by
  exact Filter.eventually_atTop.mp ((comparison_coefficient_tendsto hρ).eventually
    (Ioi_mem_nhds hγ))

theorem comparison_coefficient_eventually_one_div_twenty_five {ρ : ℕ → ℝ}
    (hρ : Filter.Tendsto ρ Filter.atTop (𝓝 0)) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, (1/25 : ℝ) < 1 - (93527408868499 / 10^14 : ℝ) -
      threeBodyTail Q - 1222*(3/10^6) - ρ Q :=
  comparison_coefficient_eventually_lt hρ one_div_twenty_five_lt_gammaStar

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

abbrev PairLabel (n : ℕ) := {a : Fin n × Fin n // a.1 < a.2}

noncomputable def basicPair {n : ℕ} (a : PairLabel n) : Module.End ℂ (Hilbert n) :=
  annihilation a.val.2 * annihilation a.val.1

noncomputable def pairContraction {n : ℕ} (v : PairLabel n → ℂ) : Module.End ℂ (Hilbert n) :=
  ∑ a, star (v a) • basicPair a

noncomputable def oneContraction {n : ℕ} (a b : PairLabel n) : Module.End ℂ (Hilbert n) :=
  -(if a.val.1 = b.val.1 then creation b.val.2 * annihilation a.val.2 else 0) +
    (if a.val.2 = b.val.1 then creation b.val.2 * annihilation a.val.1 else 0) +
    (if a.val.1 = b.val.2 then creation b.val.1 * annihilation a.val.2 else 0) -
    (if a.val.2 = b.val.2 then creation b.val.1 * annihilation a.val.1 else 0)

lemma basicPair_middle {n : ℕ} (a b : PairLabel n) :
    basicPair a * (basicPair b).adjoint =
      (if a = b then 1 else 0) + oneContraction a b + (basicPair b).adjoint * basicPair a := by
  have hcross : ¬(a.val.2 = b.val.1 ∧ a.val.1 = b.val.2) := by
    rintro ⟨ha,hb⟩
    have h := a.property
    rw [ha,hb] at h
    exact lt_asymm h b.property
  have hdiag : (a.val.1 = b.val.1 ∧ a.val.2 = b.val.2) ↔ a = b := by
    constructor
    · rintro ⟨h₁,h₂⟩
      apply Subtype.ext
      exact Prod.ext h₁ h₂
    · rintro rfl; exact ⟨rfl,rfl⟩
  simp only [basicPair, adjoint_mul, annihilation_adjoint]
  rw [← mul_assoc, pair_normal_order, ite_eq_right hcross]
  simp only [hdiag]
  unfold oneContraction
  noncomm_ring

lemma annihilation_commute_basicPair {n : ℕ} (i : Fin n) (a : PairLabel n) :
    annihilation i * basicPair a = basicPair a * annihilation i := by
  unfold basicPair
  rw [← mul_assoc, annihilation_anticommute i a.val.2, neg_mul, mul_assoc,
    annihilation_anticommute i a.val.1, mul_neg, neg_neg, ← mul_assoc]

lemma basicPair_commute {n : ℕ} (a b : PairLabel n) :
    basicPair a * basicPair b = basicPair b * basicPair a := by
  change annihilation a.val.2 * annihilation a.val.1 * basicPair b = _
  rw [mul_assoc, annihilation_commute_basicPair, ← mul_assoc,
    annihilation_commute_basicPair, mul_assoc]
  rfl

lemma pairContraction_commute {n : ℕ} (v w : PairLabel n → ℂ) :
    pairContraction v * pairContraction w = pairContraction w * pairContraction v := by
  simp only [pairContraction, Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [basicPair_commute, mul_comm]

noncomputable def pairOneContraction {n : ℕ} (v w : PairLabel n → ℂ) :
    Module.End ℂ (Hilbert n) :=
  ∑ a, ∑ b, (star (v a) * w b) • oneContraction a b

theorem pairContraction_middle {n : ℕ} (v w : PairLabel n → ℂ) :
    pairContraction v * (pairContraction w).adjoint =
      (∑ a, star (v a) * w a) • 1 + pairOneContraction v w +
        (pairContraction w).adjoint * pairContraction v := by
  classical
  simp only [pairContraction, map_sum, map_smulₛₗ, Complex.star_def, Complex.conj_conj, Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [basicPair_middle, smul_add, Finset.sum_add_distrib]
  have hdiag : (∑ a : PairLabel n, ∑ b : PairLabel n,
      (star (v a) * w b) • (if a = b then (1 : Module.End ℂ (Hilbert n)) else 0)) =
      (∑ a, star (v a) * w a) • 1 := by
    simp [smul_ite, ← Finset.sum_smul]
  simp only [mul_comm (w _) ((starRingEnd ℂ) (v _))]
  simp only [Complex.star_def] at hdiag
  rw [hdiag]
  congr 1
  rw [Finset.sum_comm]

noncomputable def pairHamiltonian {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) : Module.End ℂ (Hilbert n) :=
  ∑ p, (pairContraction (v p)).adjoint * pairContraction (v p)

noncomputable def pairThreeTerm {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) : Module.End ℂ (Hilbert n) :=
  ∑ p, ∑ r, (pairContraction (v p)).adjoint * pairOneContraction (v p) (v r) *
    pairContraction (v r)

noncomputable def pairFourTerm {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) : Module.End ℂ (Hilbert n) :=
  ∑ p, ∑ r, (pairContraction (v r) * pairContraction (v p)).adjoint *
    (pairContraction (v r) * pairContraction (v p))

theorem pairHamiltonian_square {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → PairLabel n → ℂ)
    (hv : ∀ p r, (∑ a, star (v p a) * v r a) = if p = r then 1 else 0) :
    pairHamiltonian v * pairHamiltonian v =
      pairHamiltonian v + pairThreeTerm v + pairFourTerm v := by
  classical
  have hp (p r : ι) :
      ((pairContraction (v p)).adjoint * pairContraction (v p)) *
        ((pairContraction (v r)).adjoint * pairContraction (v r)) =
      (if p = r then (pairContraction (v p)).adjoint * pairContraction (v r) else 0) +
      (pairContraction (v p)).adjoint * pairOneContraction (v p) (v r) * pairContraction (v r) +
      (pairContraction (v r) * pairContraction (v p)).adjoint *
        (pairContraction (v r) * pairContraction (v p)) := by
    rw [mul_assoc, ← mul_assoc (pairContraction (v p)), pairContraction_middle, hv]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, adjoint_mul]
    have he : (pairContraction (v p)).adjoint *
        ((pairContraction (v r)).adjoint * pairContraction (v p) * pairContraction (v r)) =
        (pairContraction (v p)).adjoint * (pairContraction (v r)).adjoint *
          (pairContraction (v r) * pairContraction (v p)) := by
      rw [mul_assoc, pairContraction_commute (v p) (v r), ← mul_assoc]
    rw [he]
    by_cases h : p = r <;> simp [h, mul_assoc]
  unfold pairHamiltonian
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, hp, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

end LaughlinGap.Occupation

end

end OAI
