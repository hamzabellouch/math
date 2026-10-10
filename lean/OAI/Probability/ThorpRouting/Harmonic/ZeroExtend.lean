import Mathlib
import OAI.Probability.ThorpRouting.Harmonic.TypedSet

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.SparseContact

section
open scoped BigOperators Classical

lemma sum_injections {L α M : Type*} [Fintype L] [Fintype α] [AddCommMonoid M]
    (F : (L → α) → M) (hF : ∀ y, ¬Function.Injective y → F y = 0) :
    (∑ y : L → α, F y) = ∑ y : L ↪ α, F y := by
  classical
  rw [← Finset.sum_image Function.Embedding.coe_injective.injOn]
  apply Eq.symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  apply hF y
  intro h
  exact hy (Finset.mem_image.mpr ⟨⟨y,h⟩, Finset.mem_univ _, rfl⟩)

noncomputable def zeroExtend {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) : EuclideanSpace ℂ (L → α) := by
  classical
  exact WithLp.toLp 2 (fun y => if h : Function.Injective y then f ⟨y,h⟩ else 0)

@[simp] lemma zeroExtend_inj {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) (y : L ↪ α) : zeroExtend f y = f y := by
  classical
  simp only [zeroExtend, WithLp.ofLp_toLp, dite_eq_left y.injective]
  congr 1

lemma zeroExtend_noninj {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) (y : L → α) (hy : ¬Function.Injective y) : zeroExtend f y = 0 := by
  classical
  simp only [zeroExtend, WithLp.ofLp_toLp, dite_eq_right hy]

lemma sum_zeroExtend_mul {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) (g : (L → α) → ℂ) :
    (∑ y : L → α, g y * zeroExtend f y) = ∑ y : L ↪ α, g y * f y := by
  rw [sum_injections _ (fun y hy => by rw [zeroExtend_noninj f y hy, mul_zero])]
  simp only [zeroExtend_inj]

lemma norm_zeroExtend {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) : ‖zeroExtend f‖ = ‖f‖ := by
  have hs : ‖zeroExtend f‖^2 = ‖f‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      sum_injections _ (fun y hy => by rw [zeroExtend_noninj f y hy]; simp)]
    simp only [zeroExtend_inj]
  nlinarith [norm_nonneg (zeroExtend f), norm_nonneg f]

lemma partial_proper_zero {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (hA : A ≠ Finset.univ) (f : EuclideanSpace ℂ (L ↪ Card d)) (hf : IsHarmonic f) :
    rectOperator (fun (x : L ↪ Card d) (y : L → Card d) => partialKernel d A x y) (zeroExtend f) = 0 := by
  classical
  ext x
  rw [rectOperator_apply, sum_zeroExtend_mul]
  change (∑ y : L ↪ Card d, (partialKernel d A x y : ℂ) * f y) = 0
  simp only [partialKernel, endpointProb, finiteMean, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_sum, Complex.ofReal_natCast]
  simp_rw [div_eq_mul_inv, mul_assoc, ← Finset.mul_sum]
  rw [mul_eq_zero]
  right
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ω _
  calc
    _ = ∑ y : L ↪ Card d, (↑(Fintype.card (SwitchIndex d → Bool)) : ℂ)⁻¹ *
        (if ∀ i ∈ A, y i = butterflyPerm d (decodeButterfly d ω) (x i) then f y else 0) :=
      by
        apply Finset.sum_congr rfl
        intro y _
        have hh : (∀ i ∈ A, butterflyPerm d (decodeButterfly d ω) (x i) = y i) ↔
            (∀ i ∈ A, y i = butterflyPerm d (decodeButterfly d ω) (x i)) :=
          forall₂_congr fun _ _ => eq_comm
        by_cases h : ∀ i ∈ A, butterflyPerm d (decodeButterfly d ω) (x i) = y i
        · simp only [ite_eq_left h, ite_eq_left (hh.mp h), Complex.ofReal_one, one_mul]
        · simp only [ite_eq_right h, ite_eq_right (mt hh.mpr h), Complex.ofReal_zero, zero_mul, mul_zero]
    _ = 0 := by
      rw [← Finset.mul_sum]
      apply mul_eq_zero_of_right
      convert hf A hA (fun i => butterflyPerm d (decodeButterfly d ω) (x i)) using 1
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> rfl

lemma partial_full_action {L : Type*} [Fintype L] (d : ℕ)
    (f : EuclideanSpace ℂ (L ↪ Card d)) :
    rectOperator (fun (x : L ↪ Card d) (y : L → Card d) => partialKernel d Finset.univ x y) (zeroExtend f) =
      DensityTransfer.applyKernel (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
        (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f := by
  classical
  ext x
  rw [rectOperator_apply, sum_zeroExtend_mul]
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  simp only [partialKernel, Finset.card_univ, div_self (by positivity : ((2:ℝ)^d)^(Fintype.card L) ≠ 0),
    one_mul, endpointProb, UnitaryFinite.actionKernel]
  apply finiteMean_congr
  intro ω
  congr 1
  simp only [Finset.mem_univ, forall_const, Function.Embedding.ext_iff]
  rfl

lemma alternating_retained_eq {L : Type*} [Fintype L] (d : ℕ)
    (x : L ↪ Card d) (y : L → Card d) :
    (∑ A : Finset L, (-1:ℝ)^A.card * retainedKernel d A x y) =
      ∑ A : Finset L, (-1:ℝ)^A.card * partialKernel d A x y := by
  classical
  by_cases h : ContactEvent d x y
  · simp only [retainedKernel, ite_eq_left h]
  · simp only [retainedKernel, ite_eq_right h, mul_zero, Finset.sum_const_zero]
    exact (alternating_kernel_cancel d x y h).symm

lemma alternating_harmonic_action {L : Type*} [Fintype L] (d : ℕ)
    (f : EuclideanSpace ℂ (L ↪ Card d)) (hf : IsHarmonic f) :
    (∑ A : Finset L, ((-1:ℂ)^A.card) • rectOperator (retainedKernel d A) (zeroExtend f)) =
      ((-1:ℂ)^(Fintype.card L)) • DensityTransfer.applyKernel
        (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
          (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f := by
  classical
  calc
    _ = ∑ A : Finset L, ((-1:ℂ)^A.card) •
        rectOperator (fun (x : L ↪ Card d) y => partialKernel d A x y) (zeroExtend f) := by
      ext x
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, rectOperator_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Finset L)))]
      apply Finset.sum_congr rfl
      intro y _
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      congr 1
      have he := congrArg (fun t : ℝ => (t:ℂ)) (alternating_retained_eq d x y)
      simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
        Complex.ofReal_one] using he
    _ = ((-1:ℂ)^(Fintype.card L)) •
        rectOperator (fun (x : L ↪ Card d) y => partialKernel d Finset.univ x y) (zeroExtend f) := by
      rw [Finset.sum_eq_single (Finset.univ : Finset L)]
      · simp only [Finset.card_univ]
      · intro A _ hA
        rw [partial_proper_zero d A hA f hf, smul_zero]
      · simp
    _ = _ := by rw [partial_full_action]

lemma harmonic_action_bound {L : Type*} [Fintype L] (d : ℕ)
    (f : EuclideanSpace ℂ (L ↪ Card d)) (hf : IsHarmonic f)
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    ‖DensityTransfer.applyKernel (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
      (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f‖ ≤
      (2:ℝ)^(Fintype.card L) *
        Real.sqrt ((2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
          Real.exp (Real.exp 1*(Fintype.card L))) * ‖f‖ := by
  classical
  let B := (2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
          Real.exp (Real.exp 1*(Fintype.card L))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnorm (A : Finset L) : ‖rectOperator (retainedKernel d A)‖ ≤ Real.sqrt B := by
    have hh := retained_norm_sq d A hδ hδ1
    have hs := Real.sq_sqrt hB
    have hn := Real.sqrt_nonneg B
    nlinarith
  calc
    _ = ‖((-1:ℂ)^(Fintype.card L)) • DensityTransfer.applyKernel
        (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
          (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f‖ := by
      simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ = ‖∑ A : Finset L, ((-1:ℂ)^A.card) • rectOperator (retainedKernel d A) (zeroExtend f)‖ := by
      rw [alternating_harmonic_action d f hf]
    _ ≤ ∑ A : Finset L, ‖((-1:ℂ)^A.card) • rectOperator (retainedKernel d A) (zeroExtend f)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ A : Finset L, Real.sqrt B * ‖f‖ := by
      apply Finset.sum_le_sum
      intro A _
      simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      calc _ ≤ ‖rectOperator (retainedKernel d A)‖ * ‖zeroExtend f‖ :=
              ContinuousLinearMap.le_opNorm _ _
           _ ≤ Real.sqrt B * ‖zeroExtend f‖ := mul_le_mul_of_nonneg_right (hnorm A) (norm_nonneg _)
           _ = _ := by rw [norm_zeroExtend]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]; ring

lemma harmonic_action_zero_one {L : Type*} [Fintype L] (d : ℕ)
    (hL : Fintype.card L = 1) (f : EuclideanSpace ℂ (L ↪ Card d)) (hf : IsHarmonic f) :
    DensityTransfer.applyKernel (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
      (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f = 0 := by
  classical
  obtain ⟨i,hi⟩ := Fintype.card_eq_one_iff.mp hL
  have hz (A : Finset L) : rectOperator (retainedKernel d A) = 0 := by
    ext v x
    have hh (y : L → Card d) : ¬ContactEvent d x y := by
      intro h
      obtain ⟨j,hj,_⟩ := h i
      exact hj (hi j).symm
    simp only [rectOperator_apply, retainedKernel, ite_eq_right (hh _), Complex.ofReal_zero,
      zero_mul, Finset.sum_const_zero, zero_apply, PiLp.zero_apply]
  have he := alternating_harmonic_action d f hf
  simp only [hz, zero_apply, smul_zero, Finset.sum_const_zero, hL, pow_one,
    neg_smul, one_smul] at he
  exact neg_eq_zero.mp he.symm

end
open scoped BigOperators

def MainStatement : Prop :=
  ∃ Cstar C : ℝ, 0 < Cstar ∧ 0 < C ∧
    ∀ (d : ℕ), 1 ≤ d → ∀ (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ),
      let k := μ.card - μ.rowLen 0
      1 ≤ k → k < 2^d → ∀ reverse : Bool,
        ‖sweepOperator d μ e reverse‖^2 ≤
          min 1 ((Cstar * d * k / (2:ℝ)^d) ^ ((k:ℝ)/2)) ∧
        (k = 1 → sweepOperator d μ e reverse = 0) ∧
        ‖sweepOperator d μ e reverse‖^2 ≤
          C^k * (1+(d:ℝ))^(C*k) * ((k:ℝ)/(2:ℝ)^d)^((k:ℝ)/2)

end Thorp.SparseContact

namespace Thorp.SparseContact
open scoped BigOperators Classical

lemma exists_exact_fixed_unit {α L : Type*} [Fintype α] [Fintype L]
    (μ : YoungDiagram) (e : α ≃ Specht.Cell μ) (x₀ : L ↪ α)
    (hL : Fintype.card L = μ.card - μ.rowLen 0) :
    ∃ w : Specht.hilbertSpace μ,
      UnitaryFinite.IsFixed UnitaryFinite.tupleAction x₀ (Specht.relabelledUnitary μ e) w ∧ ‖w‖ = 1 := by
  let K := UnitaryFinite.fixedSpace (V := Specht.hilbertSpace μ) UnitaryFinite.tupleAction x₀ (Specht.relabelledUnitary μ e)
  have hd : 0 < Module.finrank ℂ (Specht.hilbertSpace μ) := by
    rw [Specht.finrank_hilbertSpace]
    exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr (Specht.space_ne_bot μ))
  have hdim := Specht.relabelled_tuple_dimension μ e x₀
  rw [hL, Nat.choose_self, mul_one] at hdim
  have hm : 0 < Module.finrank ℂ K := by
    by_contra h
    have hz : Module.finrank ℂ K = 0 := by omega
    change _ ≤ Module.finrank ℂ K * _ at hdim
    rw [hz, zero_mul] at hdim
    omega
  let B := stdOrthonormalBasis ℂ K
  let i : Fin (Module.finrank ℂ K) := ⟨0,hm⟩
  exact ⟨(B i).val, (B i).prop, B.orthonormal.norm_eq_one i⟩

lemma sweep_forward_norm {d : ℕ} (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    ‖sweepOperator d μ e rev‖ = ‖sweepOperator d μ e false‖ := by
  cases rev
  · rfl
  · simp only [sweepOperator, Bool.false_eq_true, ite_false, ite_true]
    rw [UnitaryFinite.sampleOperator_inv _ (Specht.relabelledUnitary_unitary μ e),
      ContinuousLinearMap.adjoint.norm_map]

lemma sweep_norm_le_one (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    ‖sweepOperator d μ e rev‖ ≤ 1 :=
  UnitaryFinite.sampleOperator_norm_le _ (Specht.relabelledUnitary_unitary μ e) _

section Generic
variable {L V : Type*} [Fintype L] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

lemma sample_sweep_bound (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    [Representation.IsIrreducible ρ] (hρ : UnitaryFinite.IsUnitary ρ)
    (x₀ : L ↪ Card d) (w : V) (hw : UnitaryFinite.IsFixed UnitaryFinite.tupleAction x₀ ρ w)
    (hn : ‖w‖ = 1)
    (hh : ∀ v, IsHarmonic (UnitaryFinite.normalizedCoefficient UnitaryFinite.tupleAction x₀
      (UnitaryFinite.tupleAction_transitive x₀) ρ w v))
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    ‖UnitaryFinite.sampleOperator ρ (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))‖ ≤
      (2:ℝ)^(Fintype.card L) *
        Real.sqrt ((2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
          Real.exp (Real.exp 1*(Fintype.card L))) := by
  rw [← ContinuousLinearMap.adjoint.norm_map (UnitaryFinite.sampleOperator ρ
    (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))),
    ← UnitaryFinite.sampleOperator_inv ρ hρ]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [UnitaryFinite.sampleOperator_inv_apply]
  have ha := harmonic_action_bound d _ (hh v) hδ hδ1
  rw [UnitaryFinite.coefficient_random UnitaryFinite.tupleAction x₀
    (UnitaryFinite.tupleAction_transitive x₀) ρ hρ _ w hw,
    UnitaryFinite.normalizedCoefficient_norm _ _ _ ρ hρ w hw hn,
    UnitaryFinite.normalizedCoefficient_norm _ _ _ ρ hρ w hw hn] at ha
  exact ha

lemma sample_sweep_zero_one (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    [Representation.IsIrreducible ρ] (hρ : UnitaryFinite.IsUnitary ρ)
    (x₀ : L ↪ Card d) (w : V) (hw : UnitaryFinite.IsFixed UnitaryFinite.tupleAction x₀ ρ w)
    (hn : ‖w‖ = 1)
    (hh : ∀ v, IsHarmonic (UnitaryFinite.normalizedCoefficient UnitaryFinite.tupleAction x₀
      (UnitaryFinite.tupleAction_transitive x₀) ρ w v))
    (hL : Fintype.card L = 1) :
    UnitaryFinite.sampleOperator ρ (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω)) = 0 := by
  apply ContinuousLinearMap.adjoint.injective
  rw [map_zero, ← UnitaryFinite.sampleOperator_inv ρ hρ]
  apply ContinuousLinearMap.ext
  intro v
  rw [UnitaryFinite.sampleOperator_inv_apply]
  have ha := harmonic_action_zero_one d hL _ (hh v)
  have he := congrArg norm ha
  rw [UnitaryFinite.coefficient_random UnitaryFinite.tupleAction x₀
    (UnitaryFinite.tupleAction_transitive x₀) ρ hρ _ w hw,
    UnitaryFinite.normalizedCoefficient_norm _ _ _ ρ hρ w hw hn, norm_zero] at he
  exact norm_eq_zero.mp he
end Generic

lemma sweep_norm_bound (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (hδ : 0 < 2*(d:ℝ)*(μ.card - μ.rowLen 0 : ℕ)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(μ.card - μ.rowLen 0 : ℕ)/(2:ℝ)^d ≤ 1) (rev : Bool) :
    ‖sweepOperator d μ e rev‖ ≤ (2:ℝ)^(μ.card - μ.rowLen 0) *
      Real.sqrt ((2*(d:ℝ)*(μ.card - μ.rowLen 0 : ℕ)/(2:ℝ)^d)^(((μ.card - μ.rowLen 0 : ℕ):ℝ)/2) *
        Real.exp (Real.exp 1*(μ.card - μ.rowLen 0 : ℕ))) := by
  classical
  let x₀ : Specht.Tail μ ↪ Card d := (Function.Embedding.subtype _).trans e.symm.toEmbedding
  obtain ⟨w,hw,hn⟩ := exists_exact_fixed_unit μ e x₀ (Specht.tail_card μ)
  let := Specht.relabelledUnitary_irreducible μ e
  rw [sweep_forward_norm μ e rev]
  have hh (v : Specht.hilbertSpace μ) : IsHarmonic (UnitaryFinite.normalizedCoefficient
      (V := Specht.hilbertSpace μ) UnitaryFinite.tupleAction x₀
      (UnitaryFinite.tupleAction_transitive x₀) (Specht.relabelledUnitary μ e) w v) :=
    normalizedCoefficient_harmonic μ e (Specht.tail_card μ) x₀ w hw v
  have he := sample_sweep_bound (V := Specht.hilbertSpace μ) (L := Specht.Tail μ) d (Specht.relabelledUnitary μ e)
  have he := he (Specht.relabelledUnitary_unitary μ e) x₀ w hw hn hh
  have he := he (by simpa only [Specht.tail_card] using hδ) (by simpa only [Specht.tail_card] using hδ1)
  simpa only [sweepOperator, Bool.false_eq_true, ite_false, Specht.tail_card] using he

lemma sweep_zero_one (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (hk : μ.card - μ.rowLen 0 = 1) (rev : Bool) : sweepOperator d μ e rev = 0 := by
  classical
  let x₀ : Specht.Tail μ ↪ Card d := (Function.Embedding.subtype _).trans e.symm.toEmbedding
  obtain ⟨w,hw,hn⟩ := exists_exact_fixed_unit μ e x₀ (Specht.tail_card μ)
  let := Specht.relabelledUnitary_irreducible μ e
  have hh (v : Specht.hilbertSpace μ) : IsHarmonic (UnitaryFinite.normalizedCoefficient
      (V := Specht.hilbertSpace μ) UnitaryFinite.tupleAction x₀
      (UnitaryFinite.tupleAction_transitive x₀) (Specht.relabelledUnitary μ e) w v) :=
    normalizedCoefficient_harmonic μ e (Specht.tail_card μ) x₀ w hw v
  have he := sample_sweep_zero_one (V := Specht.hilbertSpace μ) (L := Specht.Tail μ) d (Specht.relabelledUnitary μ e)
  have he := he (Specht.relabelledUnitary_unitary μ e) x₀ w hw hn hh
  have he := he ((Specht.tail_card μ).trans hk)
  have hz : sweepOperator d μ e false = 0 := by
    simpa only [sweepOperator, Bool.false_eq_true, ite_false] using he
  apply (norm_eq_zero (a := sweepOperator d μ e rev)).mp
  rw [sweep_forward_norm μ e rev, hz]
  exact @norm_zero (Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ) _

end Thorp.SparseContact

namespace Thorp.SparseContact

noncomputable def contactConstant : ℝ := 32 * Real.exp (2 * Real.exp 1)

lemma contactConstant_gt_one : 1 < contactConstant := by
  have h : 1 ≤ Real.exp (2 * Real.exp 1) := Real.one_le_exp (by positivity)
  unfold contactConstant
  linarith

lemma contactConstant_gt_two : 2 < contactConstant := by
  have h : 1 ≤ Real.exp (2 * Real.exp 1) := Real.one_le_exp (by positivity)
  unfold contactConstant
  linarith

lemma inflated_contact_bound {δ : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    ((2:ℝ)^k * Real.sqrt (δ^((k:ℝ)/2) * Real.exp (Real.exp 1*k)))^2 =
      ((contactConstant/2)*δ)^((k:ℝ)/2) := by
  have hC : 0 ≤ contactConstant/2 := by have := contactConstant_gt_one; positivity
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.mul_rpow hC hδ]
  have hc : contactConstant/2 = Real.exp (2*(Real.log 4+Real.exp 1)) := by
    unfold contactConstant
    rw [show 2*(Real.log 4+Real.exp 1) = Real.log 4*2+2*Real.exp 1 by ring,
      Real.exp_add, Real.exp_mul (Real.log 4) 2, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
    ring
  rw [hc, ←Real.exp_mul]
  have hpow : ((2:ℝ)^k)^2 = Real.exp (Real.log 4 * k) := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num only [pow_two]
    rw [Real.exp_mul (Real.log 4) k, Real.exp_log (by norm_num : (0:ℝ)<4), Real.rpow_natCast]
  rw [hpow]
  calc
    _ = (Real.exp (Real.log 4*k)*Real.exp (Real.exp 1*k))*δ^((k:ℝ)/2) := by ring
    _ = _ := by rw [←Real.exp_add]; congr 2; ring

lemma contact_crude_arithmetic {C d q : ℝ} (hC : 1 ≤ C) (hd : 1 ≤ d) (hq : 0 ≤ q) (k : ℕ) :
    (C*d*q)^((k:ℝ)/2) ≤ C^k*(1+d)^(C*k)*q^((k:ℝ)/2) := by
  rw [Real.mul_rpow (by positivity) hq, Real.mul_rpow (by positivity) (by positivity)]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hC (by linarith [Nat.cast_nonneg (α := ℝ) k])
  · calc
      d^((k:ℝ)/2) ≤ (1+d)^((k:ℝ)/2) := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ ≤ (1+d)^(C*k) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  · positivity
  · positivity


lemma sweep_sharp_bound (d : ℕ) (hd : 1 ≤ d) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (hk : 1 ≤ μ.card - μ.rowLen 0) (rev : Bool) :
    ‖sweepOperator d μ e rev‖^2 ≤ min 1
      ((contactConstant*d*(μ.card - μ.rowLen 0 : ℕ)/(2:ℝ)^d)^(((μ.card - μ.rowLen 0 : ℕ):ℝ)/2)) := by
  let k := μ.card - μ.rowLen 0
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hδ : 0 < 2*(d:ℝ)*k/(2:ℝ)^d := by positivity
  have hOne : ‖sweepOperator d μ e rev‖^2 ≤ 1 := by
    have h := sweep_norm_le_one d μ e rev
    have h0 := norm_nonneg (sweepOperator d μ e rev)
    nlinarith
  refine le_min hOne ?_
  have he : contactConstant * d * (k:ℝ)/(2:ℝ)^d =
      (contactConstant/2)*(2*(d:ℝ)*k/(2:ℝ)^d) := by ring
  change _ ≤ (contactConstant * d * (k:ℝ)/(2:ℝ)^d)^((k:ℝ)/2)
  rw [he]
  by_cases hs : 2*(d:ℝ)*k/(2:ℝ)^d ≤ 1
  · have h := sweep_norm_bound d μ e hδ hs rev
    have hb : 0 ≤ (2:ℝ)^k * Real.sqrt
        ((2*(d:ℝ)*k/(2:ℝ)^d)^((k:ℝ)/2)*Real.exp (Real.exp 1*k)) := by positivity
    calc
      _ ≤ ((2:ℝ)^k * Real.sqrt
          ((2*(d:ℝ)*k/(2:ℝ)^d)^((k:ℝ)/2)*Real.exp (Real.exp 1*k)))^2 :=
        (sq_le_sq₀ (norm_nonneg (sweepOperator d μ e rev)) hb).mpr h
      _ = _ := inflated_contact_bound hδ.le k
  · apply hOne.trans
    apply Real.one_le_rpow
    · have hc : 1 ≤ contactConstant/2 := by have := contactConstant_gt_two; linarith
      exact one_le_mul_of_one_le_of_one_le hc (le_of_lt (lt_of_not_ge hs))
    · positivity

theorem uniform_sparse_contact : MainStatement := by
  refine ⟨contactConstant, contactConstant, (lt_trans (by norm_num) contactConstant_gt_one),
    (lt_trans (by norm_num) contactConstant_gt_one), ?_⟩
  intro d hd μ e k hk _ rev
  have hs := sweep_sharp_bound d hd μ e hk rev
  refine ⟨hs, ?_, ?_⟩
  · intro hk1
    exact sweep_zero_one d μ e hk1 rev
  · apply (hs.trans (min_le_right _ _)).trans
    change (contactConstant * d * (k:ℝ)/(2:ℝ)^d)^((k:ℝ)/2) ≤ _
    rw [mul_div_assoc]
    exact contact_crude_arithmetic contactConstant_gt_one.le
      (by exact_mod_cast hd) (by positivity) k

end Thorp.SparseContact

namespace Thorp.DimensionEstimates
open scoped BigOperators

lemma log_factorial_upper_binary (n : ℕ) (hn : 0<n) :
    Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log n-Real.log 2*((n:ℝ)-1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hb : (2:ℝ) ≤ (1+(n:ℝ)⁻¹)^n := by
      have h := one_add_mul_le_pow (by have := inv_nonneg.mpr hn0.le; linarith : (-2:ℝ)≤(n:ℝ)⁻¹) n
      norm_num [mul_inv_cancel₀ hn0.ne'] at h ⊢
      exact h
    have hl := Real.log_le_log (by norm_num : (0:ℝ)<2) hb
    rw [Real.log_pow] at hl
    have hs : Real.log (1+(n:ℝ)⁻¹)=Real.log ((n:ℝ)+1)-Real.log n := by
      rw [←Real.log_div (by positivity) hn0.ne']
      congr 1
      field_simp
    rw [hs] at hl
    rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_add,Nat.cast_one]
    nlinarith

lemma log_factorial_lower (n : ℕ) (hn : 0<n) :
    (n:ℝ)*Real.log n-n+1 ≤ Real.log (n.factorial:ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hl := Real.log_le_sub_one_of_pos (show 0<((n:ℝ)+1)/n by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at hl
    have hh := mul_le_mul_of_nonneg_left hl hn0.le
    have he : (n:ℝ)*(((n:ℝ)+1)/n-1)=1 := by field_simp; ring
    rw [he] at hh
    rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_add,Nat.cast_one]
    nlinarith

lemma log_factorial_upper (n : ℕ) (hn : 0<n) :
    Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log n-n+Real.log n+1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hl := Real.one_sub_inv_le_log_of_pos (show 0<((n:ℝ)+1)/n by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at hl
    have hh := mul_le_mul_of_nonneg_left hl (show 0≤(n:ℝ)+1 by positivity)
    have he : ((n:ℝ)+1)*(1-(((n:ℝ)+1)/n)⁻¹)=1 := by field_simp; ring
    rw [he] at hh
    rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_add,Nat.cast_one]
    nlinarith

variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
open scoped Classical

noncomputable def fiberWeight (f : X → I) (i : I) : ℝ := Fintype.card {x // f x=i}

omit [Fintype I] in
lemma fiberWeight_nonneg (f : X → I) (i : I) : 0≤fiberWeight f i := Nat.cast_nonneg _

omit [Fintype I] in
lemma fiberWeight_pos (f : X → I) (x : X) : 0<fiberWeight f (f x) := by
  let : Nonempty {y // f y=f x} := ⟨⟨x,rfl⟩⟩
  exact Nat.cast_pos.mpr Fintype.card_pos

lemma fiber_sum (f : X → I) (u : I → ℝ) :
    ∑ x, u (f x)=∑ i, fiberWeight f i*u i := by
  rw [←Equiv.sum_comp (Equiv.sigmaFiberEquiv f)]
  simp only [Equiv.sigmaFiberEquiv_apply,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ x : {x // f x=i}, u (f x)) = ∑ _x : {x // f x=i}, u i :=
      Finset.sum_congr rfl (fun x _ => congrArg u x.property)
    _ = _ := by simp [fiberWeight]

lemma sum_fiberWeight (f : X → I) : ∑ i, fiberWeight f i=Fintype.card X := by
  have h := fiber_sum f (fun _ => 1)
  simpa using h.symm

theorem incidence_entropy (f : X → I) (g : X → J)
    (hinj : Function.Injective (fun x => (f x,g x))) :
    (∑ i, fiberWeight f i*Real.log (fiberWeight f i))+
      (∑ j, fiberWeight g j*Real.log (fiberWeight g j)) ≤
        (Fintype.card X:ℝ)*Real.log (Fintype.card X) := by
  by_cases hX : Nonempty X
  · let : Nonempty X := hX
    have hN : (0:ℝ)<Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
    have hprod : ∑ x, fiberWeight f (f x)*fiberWeight g (g x) ≤ (Fintype.card X:ℝ)^2 := by
      calc
        _ ≤ ∑ p : I × J, fiberWeight f p.1*fiberWeight g p.2 := by
          calc
            _ = ∑ p ∈ Finset.univ.image (fun x => (f x,g x)), fiberWeight f p.1*fiberWeight g p.2 := by
              rw [Finset.sum_image (fun x _ y _ h => hinj h)]
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun p _ _ => mul_nonneg (fiberWeight_nonneg f p.1) (fiberWeight_nonneg g p.2))
        _ = _ := by
          rw [Fintype.sum_prod_type]
          simp_rw [←Finset.mul_sum]
          rw [←Finset.sum_mul,sum_fiberWeight,sum_fiberWeight,pow_two]
    have hdiv : (∑ x, fiberWeight f (f x)*fiberWeight g (g x))/(Fintype.card X:ℝ) ≤ Fintype.card X := by
      apply (div_le_iff₀ hN).mpr
      simpa only [pow_two] using hprod
    have hl (x : X) := Real.log_le_sub_one_of_pos
      (show 0<fiberWeight f (f x)*fiberWeight g (g x)/(Fintype.card X:ℝ) from
        div_pos (mul_pos (fiberWeight_pos f x) (fiberWeight_pos g x)) hN)
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hl x)
    simp_rw [Real.log_div (mul_pos (fiberWeight_pos f _) (fiberWeight_pos g _)).ne' hN.ne',
      Real.log_mul (fiberWeight_pos f _).ne' (fiberWeight_pos g _).ne'] at hs
    rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,
      fiber_sum f (fun i => Real.log (fiberWeight f i)),
      fiber_sum g (fun j => Real.log (fiberWeight g j)),
      Finset.sum_sub_distrib,←Finset.sum_div] at hs
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hs
    linarith
  · let : IsEmpty X := not_nonempty_iff.mp hX
    have hf (i : I) : fiberWeight f i=0 := by simp [fiberWeight]
    have hg (j : J) : fiberWeight g j=0 := by simp [fiberWeight]
    simp [hf,hg]

end Thorp.DimensionEstimates

namespace Thorp.DimensionEstimates
open scoped BigOperators Classical

lemma log_factorial_upper_binary_all (n : ℕ) :
    Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log n-Real.log 2*((n:ℝ)-1) := by
  by_cases hn : n=0
  · subst n
    simpa using (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  · exact log_factorial_upper_binary n (Nat.pos_of_ne_zero hn)

lemma log_fiber_factorials {X I : Type*} [Fintype X] [Fintype I] (f : X → I) :
    Real.log ((∏ i, (Fintype.card {x // f x=i}).factorial : ℕ):ℝ) ≤
      ∑ i, fiberWeight f i*Real.log (fiberWeight f i) -
        Real.log 2*((Fintype.card X:ℝ)-Fintype.card I) := by
  rw [Nat.cast_prod,Real.log_prod (fun _ _ => by positivity)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    log_factorial_upper_binary_all (Fintype.card {x // f x=i}))
  change ∑ i, Real.log ((Fintype.card {x // f x=i}).factorial:ℝ) ≤
    ∑ i, (fiberWeight f i*Real.log (fiberWeight f i)-Real.log 2*(fiberWeight f i-1)) at h
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_sub_distrib,sum_fiberWeight] at h
  simpa using h

theorem dimension_log_from_incidence {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    [Nonempty X] (f : X → I) (g : X → J)
    (hinj : Function.Injective (fun x => (f x,g x))) (D : ℕ)
    (hD : (Fintype.card X).factorial ≤ D *
      (∏ i, (Fintype.card {x // f x=i}).factorial) *
      (∏ j, (Fintype.card {x // g x=j}).factorial)) :
    ((2*Real.log 2-1)*(Fintype.card X:ℝ)-
      Real.log 2*((Fintype.card I:ℝ)+Fintype.card J)+1) ≤ Real.log D := by
  have hd : 0<D := by
    by_contra h
    have : D=0 := by omega
    simp [this] at hD
    exact (Nat.factorial_pos _).ne' hD
  have hf := log_fiber_factorials f
  have hg := log_fiber_factorials g
  have hi := incidence_entropy f g hinj
  have hlo := log_factorial_lower (Fintype.card X) Fintype.card_pos
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<(Fintype.card X).factorial)
    (show ((Fintype.card X).factorial:ℝ) ≤ D *
      (∏ i, (Fintype.card {x // f x=i}).factorial) *
      (∏ j, (Fintype.card {x // g x=j}).factorial) by exact_mod_cast hD)
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at hlog
  nlinarith


lemma scaled_binEntropy (N j : ℝ) (hN : 0<N) (hj : 0<j) (hjN : j<N) :
    N*Real.binEntropy (j/N)=N*Real.log N-j*Real.log j-(N-j)*Real.log (N-j) := by
  have hsub : 0<N-j := sub_pos.mpr hjN
  have he : 1-j/N=(N-j)/N := by field_simp
  unfold Real.binEntropy
  rw [he,Real.log_inv,Real.log_inv,Real.log_div hj.ne' hN.ne',
    Real.log_div hsub.ne' hN.ne']
  field_simp
  ring

lemma log_choose_lower_entropy (N j : ℕ) (hj : 0<j) (hjN : j<N) :
    (N:ℝ)*Real.binEntropy ((j:ℝ)/N)-2*Real.log N-1 ≤ Real.log (N.choose j:ℝ) := by
  have hN : 0<N := lt_trans hj hjN
  have ht : 0<N-j := Nat.sub_pos_of_lt hjN
  have hj0 : (0:ℝ)<j := by exact_mod_cast hj
  have hN0 : (0:ℝ)<N := by exact_mod_cast hN
  have hjN0 : (j:ℝ)<N := by exact_mod_cast hjN
  have hchoose : (0:ℝ)<N.choose j := by exact_mod_cast Nat.choose_pos hjN.le
  have hfac := congrArg (fun n : ℕ => Real.log (n:ℝ)) (Nat.choose_mul_factorial_mul_factorial hjN.le)
  simp only [Nat.cast_mul] at hfac
  rw [Real.log_mul (mul_pos hchoose (by positivity)).ne' (by positivity),
    Real.log_mul hchoose.ne' (by positivity)] at hfac
  have hlo := log_factorial_lower N hN
  have hji := log_factorial_upper j hj
  have hti := log_factorial_upper (N-j) ht
  have hjlog := Real.log_le_log hj0 hjN0.le
  have htlog := Real.log_le_log (by exact_mod_cast ht : (0:ℝ)<(N-j:ℕ))
    (by exact_mod_cast Nat.sub_le N j : ((N-j:ℕ):ℝ)≤N)
  rw [Nat.cast_sub hjN.le] at hti htlog
  rw [scaled_binEntropy N j hN0 hj0 hjN0]
  linarith

lemma binEntropy_three_quarters :
    Real.binEntropy (3/4:ℝ)=2*Real.log 2-(3/4:ℝ)*Real.log 3 := by
  have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  unfold Real.binEntropy
  norm_num only [show (1-(3/4:ℝ))=1/4 by norm_num]
  rw [Real.log_div (by norm_num) (by norm_num),h4]
  ring

noncomputable def entropyGap : ℝ := Real.log (32/27:ℝ)/3

lemma entropyGap_pos : 0<entropyGap := by
  unfold entropyGap
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

lemma entropyGap_eq : entropyGap=(5*Real.log 2-3*Real.log 3)/3 := by
  unfold entropyGap
  rw [Real.log_div (by norm_num) (by norm_num),show (32:ℝ)=2^5 by norm_num,
    show (27:ℝ)=3^3 by norm_num,Real.log_pow,Real.log_pow]
  norm_num

lemma binEntropy_tail_lower (q : ℝ) (hq : 0≤q) (hq' : q≤3/4) :
    q*Real.log 2+entropyGap*q ≤ Real.binEntropy q := by
  have hc := Real.strictConcave_binEntropy.concaveOn.2
    (show (0:ℝ)∈Set.Icc 0 1 by constructor <;> norm_num)
    (show (3/4:ℝ)∈Set.Icc 0 1 by constructor <;> norm_num)
    (show 0≤1-4*q/3 by linarith) (show 0≤4*q/3 by positivity)
    (show (1-4*q/3)+(4*q/3)=1 by ring)
  simp only [Real.binEntropy_zero,binEntropy_three_quarters,smul_eq_mul,mul_zero,zero_add] at hc
  have he : 4*q/3*(3/4:ℝ)=q := by ring
  rw [he] at hc
  rw [entropyGap_eq]
  linarith

lemma log_dimension_from_binomial (N j D : ℕ) (hj : 0<j) (hjN : j<N)
    (hfrac : (j:ℝ)≤(3/4:ℝ)*N) (hD : N.choose j≤D*2^j) :
    entropyGap*(j:ℝ)-2*Real.log N-1 ≤ Real.log D := by
  have hpos : 0<N.choose j := Nat.choose_pos hjN.le
  have hd : 0<D := by nlinarith [Nat.zero_le (2^j)]
  have hN : (0:ℝ)<N := by exact_mod_cast lt_trans hj hjN
  have hm := Real.log_le_log (by exact_mod_cast hpos : (0:ℝ)<N.choose j)
    (show (N.choose j:ℝ)≤D*2^j by exact_mod_cast hD)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hm
  have he := binEntropy_tail_lower ((j:ℝ)/N) (by positivity)
    ((div_le_iff₀ hN).mpr hfrac)
  have hel := mul_le_mul_of_nonneg_left he hN.le
  have hbin := log_choose_lower_entropy N j hj hjN
  have heq : (N:ℝ)*((j:ℝ)/N*Real.log 2+entropyGap*((j:ℝ)/N))=
      (j:ℝ)*Real.log 2+entropyGap*j := by field_simp
  rw [heq] at hel
  linarith

lemma balanced_dimension_coefficient_pos : 0<(3/2:ℝ)*Real.log 2-1 := by
  linarith [Real.log_two_gt_d9]


lemma log_choose_upper (N j : ℕ) (hN : 0<N) (hj : j≤N) :
    Real.log (N.choose j:ℝ) ≤ (j:ℝ)*Real.log N-Real.log (j.factorial:ℝ) := by
  have hh := Real.log_le_log (by exact_mod_cast Nat.choose_pos hj : (0:ℝ)<N.choose j)
    (Nat.choose_le_pow_div j N : (N.choose j:ℝ)≤(N:ℝ)^j/(j.factorial:ℝ))
  rw [Real.log_div (by positivity : (N:ℝ)^j≠0) (by positivity : (j.factorial:ℝ)≠0),Real.log_pow] at hh
  exact hh

lemma log_choose_lower (N j : ℕ) (hj : j≤N) :
    (j:ℝ)*Real.log (N+1-j:ℕ)-Real.log (j.factorial:ℝ) ≤ Real.log (N.choose j:ℝ) := by
  have hp : 0<N+1-j := by omega
  have hh := Real.log_le_log (by positivity : (0:ℝ)<((N+1-j:ℕ):ℝ)^j/(j.factorial:ℝ))
    (Nat.pow_le_choose j N : (((N+1-j:ℕ):ℝ)^j)/(j.factorial:ℝ)≤N.choose j)
  rw [Real.log_div (by positivity : (((N+1-j:ℕ):ℝ)^j)≠0) (by positivity : (j.factorial:ℝ)≠0),Real.log_pow] at hh
  exact hh

lemma footprint_log_bound (N k j D m : ℕ) (hN : 0<N) (hk : j≤k) (hj : j≤N)
    (hD : 0<D) (hfoot : D * k.choose j ≤ m * N.choose j) :
    Real.log D-(j:ℝ)*(Real.log N-Real.log (k+1-j:ℕ)) ≤ Real.log m := by
  have hkpos := Nat.choose_pos hk
  have hprod : 0<D*k.choose j := Nat.mul_pos hD hkpos
  have hm : 0 < m := by
    by_contra h
    have he : m=0 := by omega
    simp only [he,zero_mul] at hfoot
    omega
  have hh := Real.log_le_log (by exact_mod_cast hprod : (0:ℝ)<D*k.choose j)
    (show (D:ℝ)*k.choose j≤ m*N.choose j by exact_mod_cast hfoot)
  rw [Real.log_mul (by positivity) (by exact_mod_cast hkpos.ne'),
    Real.log_mul (by positivity) (by exact_mod_cast (Nat.choose_pos hj).ne')] at hh
  have hlo := log_choose_lower k j hk
  have hup := log_choose_upper N j hN hj
  nlinarith

lemma log_factorial_le_mul_log (j : ℕ) (_hj : 0<j) :
    Real.log (j.factorial:ℝ)≤(j:ℝ)*Real.log j := by
  have h := Real.log_le_log (by positivity : (0:ℝ)<j.factorial)
    (show (j.factorial:ℝ)≤(j:ℝ)^j by exact_mod_cast Nat.factorial_le_pow j)
  simpa only [Real.log_pow] using h

lemma near_row_log_dimension (N j D : ℕ) (hj : 0<j) (hsmall : 2*j≤N)
    (hD : N.choose j≤D*2^j) :
    (j:ℝ)*(Real.log ((N:ℝ)/j)-2*Real.log 2) ≤ Real.log D := by
  have hjN : j≤N := by omega
  have hN : 0<N := by omega
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hn : 0<N+1-j := by omega
  have hnreal : (N:ℝ)/2≤(N+1-j:ℕ) := by
    rw [Nat.cast_sub (by omega : j≤N+1),Nat.cast_add,Nat.cast_one]
    have hc : 2*(j:ℝ)≤N := by exact_mod_cast hsmall
    linarith
  have hDpos : 0<D := by
    have hc := Nat.choose_pos hjN
    by_contra h
    have he : D=0 := by omega
    simp only [he,zero_mul] at hD
    omega
  have hm := Real.log_le_log (by exact_mod_cast Nat.choose_pos hjN : (0:ℝ)<N.choose j)
    (show (N.choose j:ℝ)≤D*2^j by exact_mod_cast hD)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hm
  have hl := Real.log_le_log (by positivity : (0:ℝ)<(N:ℝ)/2) hnreal
  rw [Real.log_div hNp.ne' (by norm_num)] at hl
  have hh := log_choose_lower N j hjN
  have hf := log_factorial_le_mul_log j hj
  rw [Real.log_div hNp.ne' hjp.ne']
  nlinarith

open Filter

noncomputable def nearPower : ℝ := 1/2048
noncomputable def nearFraction : ℝ := 1/4096
noncomputable def tailPower : ℝ := 1535/1048576

noncomputable def chosenTuple (N j : ℕ) : ℕ :=
  ⌈(j:ℝ)*((N:ℝ)/j)^nearPower⌉₊

lemma chosenTuple_bounds (N j : ℕ) (hj : 0<j) (hx : 1≤(N:ℝ)/j)
    (hhalf : ((N:ℝ)/j)^(nearPower-1)≤1/2) :
    j≤chosenTuple N j ∧ chosenTuple N j≤N ∧
      (chosenTuple N j:ℝ)≤2*j*((N:ℝ)/j)^nearPower := by
  let x : ℝ := (N:ℝ)/j
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hj1 : (1:ℝ)≤j := by exact_mod_cast hj
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hpow : 1≤x^nearPower := Real.one_le_rpow hx (by norm_num [nearPower])
  have hceil : (j:ℝ)*x^nearPower≤chosenTuple N j := Nat.le_ceil _
  have hceil' : (chosenTuple N j:ℝ)<(j:ℝ)*x^nearPower+1 := Nat.ceil_lt_add_one (by positivity)
  have he : (j:ℝ)*x=N := by dsimp [x]; field_simp
  have hh : x^nearPower≤x/2 := by
    rw [Real.rpow_sub hxp,Real.rpow_one] at hhalf
    nlinarith [(div_le_iff₀ hxp).mp hhalf]
  constructor
  · exact_mod_cast (le_mul_of_one_le_right hjp.le hpow).trans hceil
  constructor
  · apply Nat.ceil_le.mpr
    change (j:ℝ)*x^nearPower≤N
    nlinarith
  · change (chosenTuple N j:ℝ)≤2*(j:ℝ)*x^nearPower
    nlinarith

lemma chosenTuple_tail_lower (N j : ℕ) (hj : 0<j)
    (hx : 2≤((N:ℝ)/j)^nearPower) :
    (j:ℝ)*((N:ℝ)/j)^nearPower/2 ≤ (chosenTuple N j+1-j:ℕ) := by
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hc : (j:ℝ)*((N:ℝ)/j)^nearPower≤chosenTuple N j := Nat.le_ceil _
  have hjk : j≤chosenTuple N j := by exact_mod_cast (by nlinarith : (j:ℝ)≤chosenTuple N j)
  rw [Nat.cast_sub (by omega : j≤chosenTuple N j+1),Nat.cast_add,Nat.cast_one]
  nlinarith

lemma chosenTuple_log_footprint (N j D m : ℕ) (hj : 0<j)
    (hN : 2*j≤N) (hD : N.choose j≤D*2^j)
    (hx : 2≤((N:ℝ)/j)^nearPower)
    (hlog : 8*Real.log 2/nearPower≤Real.log ((N:ℝ)/j))
    (hfoot : D * (chosenTuple N j).choose j ≤ m * N.choose j) :
    nearFraction*Real.log D≤Real.log m := by
  let x : ℝ := (N:ℝ)/j
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hxp : 0<x := by dsimp [x]; positivity
  have hdpos : 0<D := by
    have hc := Nat.choose_pos (show j≤N by omega)
    by_contra h
    have hz : D=0 := by omega
    simp only [hz,zero_mul] at hD
    omega
  have htail := chosenTuple_tail_lower N j hj hx
  have hjk : j≤chosenTuple N j := by
    have hc : (j:ℝ)*x^nearPower≤chosenTuple N j := Nat.le_ceil _
    exact_mod_cast (by nlinarith : (j:ℝ)≤chosenTuple N j)
  have hh := footprint_log_bound N (chosenTuple N j) j D m (by omega) hjk (by omega) hdpos hfoot
  have htlog := Real.log_le_log (by positivity : (0:ℝ)<(j:ℝ)*x^nearPower/2) htail
  rw [Real.log_div (by positivity) (by norm_num),Real.log_mul hjp.ne' (by positivity),Real.log_rpow hxp] at htlog
  have hxlog : Real.log x=Real.log N-Real.log j := Real.log_div hNp.ne' hjp.ne'
  have hdim := near_row_log_dimension N j D hj hN hD
  change (j:ℝ)*(Real.log x-2*Real.log 2)≤Real.log D at hdim
  have hh' : Real.log D-(j:ℝ)*((1-nearPower)*Real.log x+Real.log 2)≤Real.log m := by
    have hm := mul_le_mul_of_nonneg_left htlog hjp.le
    rw [hxlog] at hm
    nlinarith
  have hlg : (3-nearPower)*Real.log 2≤nearFraction*Real.log x := by
    dsimp [nearPower,nearFraction] at hlog ⊢
    have := Real.log_pos (by norm_num : (1:ℝ)<2)
    linarith
  have hlg' := mul_le_mul_of_nonneg_left hlg hjp.le
  dsimp [nearPower,nearFraction] at hh' hlg' ⊢
  nlinarith

lemma near_row_log_uniform (N j D : ℕ) (hj : 0<j) (hN : 2*j≤N)
    (hD : N.choose j≤D*2^j) (hlog : 4*Real.log 2+2≤Real.log ((N:ℝ)/j)) :
    (1/2:ℝ)*Real.log N≤Real.log D ∧ (j:ℝ)≤Real.log D := by
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hj1 : (1:ℝ)≤j := by exact_mod_cast hj
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hd := near_row_log_dimension N j D hj hN hD
  have hjlog := Real.log_le_sub_one_of_pos hjp
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hi : 1≤Real.log ((N:ℝ)/j) := by linarith
  have he : Real.log N=Real.log j+Real.log ((N:ℝ)/j) := by rw [Real.log_div hNp.ne' hjp.ne']; ring
  constructor
  · rw [he]
    nlinarith
  · nlinarith

end Thorp.DimensionEstimates

end ThorpNine.Harmonic

end OAI
