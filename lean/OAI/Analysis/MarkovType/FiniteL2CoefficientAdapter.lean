import OAI.Analysis.MarkovType.SequenceL2JConvex
import OAI.Analysis.MarkovType.CoefficientLowerPower
import OAI.Analysis.MarkovType.FiniteL2
import OAI.Analysis.MarkovType.FiniteMartingaleConditional
import OAI.Analysis.MarkovType.FiniteMartingalePairing
import OAI.Analysis.MarkovType.FinitePowerMeanBound

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators ENNReal

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

def finiteL2ToSequence {m : ℕ} (μ : FiniteLaw (Fin m)) :
    (Fin m → E) →ₗ[ℝ] SequenceL2 E where
  toFun f := ∑ i : Fin m,
    lp.single (2 : ℝ≥0∞) i.val (Real.sqrt (μ.mass i) • f i)
  map_add' f g := by
    simp only [Pi.add_apply, smul_add, lp.single_add, Finset.sum_add_distrib]
  map_smul' c f := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change lp.single (E := fun _ : ℕ => E) (2 : ℝ≥0∞) i.val
      (Real.sqrt (μ.mass i) • (c • f i)) = _
    rw [smul_comm (Real.sqrt (μ.mass i)) c, lp.single_smul, RingHom.id_apply]

theorem finiteL2ToSequence_norm_sq {m : ℕ} (μ : FiniteLaw (Fin m)) (f : Fin m → E) :
    ‖finiteL2ToSequence μ f‖ ^ 2 = μ.expect (fun i => ‖f i‖ ^ (2 : ℕ)) := by
  classical
  let e : Fin m ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let g : ℕ → E := fun k => if hk : k < m then
    Real.sqrt (μ.mass ⟨k, hk⟩) • f ⟨k, hk⟩ else 0
  let s : Finset ℕ := Finset.univ.map e
  have hg (i : Fin m) : g (e i) = Real.sqrt (μ.mass i) • f i := by
    simp [g, e, i.is_lt]
  have hleft : (∑ k ∈ s, lp.single (2 : ℝ≥0∞) k (g k)) =
      finiteL2ToSequence μ f := by
    rw [Finset.sum_map]
    simp only [hg]
    rfl
  have hright : (∑ k ∈ s, ‖g k‖ ^ (2 : ℕ)) =
      μ.expect (fun i => ‖f i‖ ^ (2 : ℕ)) := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    rw [hg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (μ.mass_nonneg i)]
  have h := lp.norm_sum_single (p := (2 : ℝ≥0∞))
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) g s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [hleft, hright] at h
  exact h

@[simp] theorem finiteL2ToSequence_norm {m : ℕ} (μ : FiniteLaw (Fin m))
    (f : Fin m → E) : ‖finiteL2ToSequence μ f‖ = finiteL2Norm μ f := by
  apply (sq_eq_sq₀ (norm_nonneg _) (finiteL2Norm_nonneg μ f)).mp
  rw [finiteL2ToSequence_norm_sq, finiteL2Norm_sq]

theorem finiteL2ToSequence_eq_zero_on_mass_pos {m : ℕ} (μ : FiniteLaw (Fin m))
    (f : Fin m → E) (hf : finiteL2ToSequence μ f = 0)
    (i : Fin m) (hi : 0 < μ.mass i) : f i = 0 := by
  apply eq_zero_of_finiteL2Norm_eq_zero μ f _ i hi
  rw [← finiteL2ToSequence_norm, hf, norm_zero]

section FiniteProcess

variable {Ω : Type*} [sectionFintypeΩ : Fintype Ω]

omit sectionNormedSpaceℝE in
private theorem finiteL2Norm_eq_of_positive_mass [NormedSpace ℝ E] (μ : FiniteLaw Ω)
    (f g : Ω → E) (h : ∀ ω, 0 < μ.mass ω → f ω = g ω) :
    finiteL2Norm μ f = finiteL2Norm μ g := by
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro ω _
  change μ.mass ω * ‖f ω‖ ^ (2 : ℕ) = μ.mass ω * ‖g ω‖ ^ (2 : ℕ)
  by_cases hz : μ.mass ω = 0
  · simp only [hz, zero_mul]
  · rw [h ω (lt_of_le_of_ne (μ.mass_nonneg ω) (Ne.symm hz))]

theorem FinitePartitionFiltration.IsMartingaleUpTo.finiteL2Norm_le_terminal
    {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
    {M : ℕ → Ω → E} {N j : ℕ} (hM : F.IsMartingaleUpTo μ M N) (hj : j ≤ N) :
    finiteL2Norm μ (M j) ≤ finiteL2Norm μ (M N) := by
  have heq : finiteL2Norm μ (M j) =
      finiteL2Norm μ (F.conditionalProcess μ (M N) j) := by
    apply finiteL2Norm_eq_of_positive_mass
    intro ω hω
    exact (hM.conditional_terminal_of_mass_pos hj ω hω).symm
  rw [heq]
  exact F.finiteL2Norm_conditionalProcess_le μ (M N) j

def finiteCoefficientProcess {N : ℕ} (M : ℕ → Ω → E) (a : Fin (N + 1) → ℝ)
    (t : ℕ) (ω : Ω) : E :=
  ∑ i : Fin (N + 1), if i.val ≤ t then a i • finiteDifference M i.val ω else 0

omit sectionFintypeΩ in
theorem finiteCoefficientProcess_terminal [Fintype Ω] {N : ℕ} (M : ℕ → Ω → E)
    (a : Fin (N + 1) → ℝ) (ω : Ω) :
    finiteCoefficientProcess M a N ω = ∑ i, a i • finiteDifference M i.val ω := by
  apply Finset.sum_congr rfl
  intro i _
  exact ite_eq_left (Nat.le_of_lt_succ i.is_lt)

omit sectionFintypeΩ in
theorem finiteCoefficientProcess_difference [Fintype Ω] {N j : ℕ} (M : ℕ → Ω → E)
    (a : Fin (N + 1) → ℝ) (hj : 0 < j) (hjN : j ≤ N) (ω : Ω) :
    finiteDifference (finiteCoefficientProcess M a) j ω =
      a ⟨j, Nat.lt_succ_of_le hjN⟩ • finiteDifference M j ω := by
  let l : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hjN⟩
  rw [finiteDifference, ite_eq_right (Nat.ne_of_gt hj)]
  change (∑ i : Fin (N + 1), if i.val ≤ j then a i • finiteDifference M i.val ω else 0) -
    (∑ i : Fin (N + 1), if i.val ≤ j - 1 then a i • finiteDifference M i.val ω else 0) = _
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i : Fin (N + 1), if i = l then a l • finiteDifference M j ω else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = l
      · subst i
        have hjprev : ¬ j ≤ j - 1 := by omega
        simp [l, hjprev]
      · have hiv : i.val ≠ j := fun h => hi (Fin.ext h)
        have hiff : i.val ≤ j ↔ i.val ≤ j - 1 := by omega
        simp only [hiff, sub_self, ite_eq_right hi]
    _ = _ := by simp [l]

theorem finiteCoefficientProcess_isMartingale {N : ℕ}
    {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω} {M : ℕ → Ω → E}
    (hM : F.IsMartingaleUpTo μ M N) (a : Fin (N + 1) → ℝ) :
    F.IsMartingaleUpTo μ (finiteCoefficientProcess M a) N := by
  constructor
  · intro j hj ω η hωη
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val ≤ j
    · simp only [ite_eq_left hi]
      rw [hM.difference_adapted (Nat.le_of_lt_succ i.is_lt) (F.refines hi hωη)]
    · simp only [ite_eq_right hi]
  · intro j hj hjN
    have hdiff : finiteDifference (finiteCoefficientProcess M a) j =
        fun ω => a ⟨j, Nat.lt_succ_of_le hjN⟩ • finiteDifference M j ω :=
      funext (finiteCoefficientProcess_difference M a hj hjN)
    rw [hdiff]
    exact (hM.2 j hj hjN).predictable_smul (fun _ => a ⟨j, Nat.lt_succ_of_le hjN⟩)
      (fun {_ _} _ => rfl)

end FiniteProcess

theorem finiteDifference_coefficientMonotone {m N : ℕ}
    {μ : FiniteLaw (Fin m)} {F : FinitePartitionFiltration (Fin m)}
    {M : ℕ → Fin m → E} (hM : F.IsMartingaleUpTo μ M N) :
    CoefficientMonotone (fun i : Fin (N + 1) =>
      finiteL2ToSequence μ (finiteDifference M i.val)) := by
  intro a k hk
  rw [one_mul]
  have hsum (c : Fin (N + 1) → ℝ) :
      finiteL2ToSequence μ (fun ω => ∑ i, c i • finiteDifference M i.val ω) =
        ∑ i, c i • finiteL2ToSequence μ (finiteDifference M i.val) := by
    have heq : (fun ω => ∑ i : Fin (N + 1), c i • finiteDifference M i.val ω) =
        ∑ i : Fin (N + 1), c i • finiteDifference M i.val := by
      funext ω
      simp only [Finset.sum_apply, Pi.smul_apply]
    rw [heq, map_sum]
    simp only [map_smul]
  have hpref := hsum (fun i => if i.val < k then a i else 0)
  simp only [ite_smul, zero_smul] at hpref
  rw [← hpref, ← hsum a, finiteL2ToSequence_norm, finiteL2ToSequence_norm]
  by_cases hk0 : k = 0
  · subst k
    simpa only [Nat.not_lt_zero, ite_false, Finset.sum_const_zero, finiteL2Norm_zero] using
      finiteL2Norm_nonneg μ (fun ω => ∑ i, a i • finiteDifference M i.val ω)
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hprefProcess :
      (fun ω => ∑ i : Fin (N + 1), if i.val < k then
        a i • finiteDifference M i.val ω else 0) =
        finiteCoefficientProcess M a (k - 1) := by
    funext ω
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.val < k ↔ i.val ≤ k - 1 := by omega
    simp only [hi]
  have hfullProcess : (fun ω => ∑ i, a i • finiteDifference M i.val ω) =
      finiteCoefficientProcess M a N :=
    (funext (finiteCoefficientProcess_terminal M a)).symm
  rw [hprefProcess, hfullProcess]
  exact (finiteCoefficientProcess_isMartingale hM a).finiteL2Norm_le_terminal (by omega)

theorem sum_finiteL2ToSequence_differences {m : ℕ} (μ : FiniteLaw (Fin m))
    (M : ℕ → Fin m → E) (N : ℕ) :
    (∑ i : Fin (N + 1), finiteL2ToSequence μ (finiteDifference M i.val)) =
      finiteL2ToSequence μ (M N) := by
  rw [← map_sum]
  apply congrArg (finiteL2ToSequence μ)
  funext ω
  rw [Finset.sum_apply]
  exact (Finset.sum_range (n := N + 1)
    (fun k : ℕ => finiteDifference M k ω)).symm.trans
      (sum_finiteDifference_eq M N ω)

theorem finiteLowerL2_of_sequence_obstruction
    (h : FiniteTriangularObstruction (SequenceL2 E)) :
    ∃ s : ℝ, 2 ≤ s ∧ ∃ χ : ℝ, 1 ≤ χ ∧ FiniteLowerL2 E s χ := by
  obtain ⟨q, hq, D, hD, hpower⟩ :=
    h.coefficient_lower_power (K := 2) (by norm_num)
  have hqreal : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  let χ : ℝ := max 1 (D ^ (1 / (q : ℝ)))
  have hχ : D ^ (1 / (q : ℝ)) ≤ χ := le_max_right _ _
  refine ⟨(q : ℝ), hqreal, χ, le_max_left _ _, ?_⟩
  intro m μ F M N hM
  let x : Fin (N + 1) → SequenceL2 E := fun i =>
    finiteL2ToSequence μ (finiteDifference M i.val)
  have hx : CoefficientBasic 2 x :=
    (finiteDifference_coefficientMonotone hM).mono (by norm_num)
  have hpow := hpower (N + 1) x hx
  have htotal : (∑ i, x i) = finiteL2ToSequence μ (M N) :=
    sum_finiteL2ToSequence_differences μ M N
  rw [htotal, finiteL2ToSequence_norm] at hpow
  simp only [x, finiteL2ToSequence_norm] at hpow
  have hsum := sum_le_of_sum_pow_le hq hD (finiteL2Norm_nonneg μ (M N))
    (fun i : Fin (N + 1) => finiteL2Norm μ (finiteDifference M i.val))
    (fun i => finiteL2Norm_nonneg μ _) hpow
  have hfinal : (∑ i : Fin (N + 1), finiteL2Norm μ (finiteDifference M i.val)) ≤
      χ * ((N + 1 : ℕ) : ℝ) ^ (1 - 1 / (q : ℝ)) * finiteL2Norm μ (M N) :=
    hsum.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hχ (Real.rpow_nonneg (Nat.cast_nonneg (N + 1)) _))
      (finiteL2Norm_nonneg μ (M N)))
  rw [Finset.sum_range]
  simpa only [Nat.cast_add, Nat.cast_one] using hfinal

end MarkovSuperreflexivity

end

end OAI
