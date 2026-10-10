import OAI.Analysis.SegmentLenses.Obstructions

namespace OAI

/-!
# Duality and reflexivity for Hilbertian sums
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

open scoped ENNReal


def Reflexive (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)

section L2Duality
variable {I : Type*} [decidableEqI : DecidableEq I] (E : I → Type*) [∀ i, NormedAddCommGroup (E i)] [iNormedSpaceEi : ∀ i, NormedSpace ℝ (E i)]

abbrev L2Sum := lp E 2

def l2Restriction (F : StrongDual ℝ (L2Sum E)) (i : I) : StrongDual ℝ (E i) :=
  F.comp (lp.singleContinuousLinearMap ℝ E 2 i)

@[simp] theorem l2Restriction_apply (F : StrongDual ℝ (L2Sum E)) (i : I) (x : E i) :
    l2Restriction E F i x = F (lp.single 2 i x) := rfl

theorem l2_norm_sum_single_sq (s : Finset I) (x : ∀ i, E i) :
    ‖∑ i ∈ s, lp.single 2 i (x i)‖ ^ 2 = ∑ i ∈ s, ‖x i‖ ^ 2 := by
  have _ := iNormedSpaceEi
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_sum_single (p := 2) (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x s



theorem l2Restriction_square_sum (F : StrongDual ℝ (L2Sum E)) (s : Finset I) :
    ∑ i ∈ s, ‖l2Restriction E F i‖ ^ 2 ≤ ‖F‖ ^ 2 := by
  classical
  let M : I → ℝ := fun i => ‖l2Restriction E F i‖
  let S := ∑ i ∈ s, M i ^ 2
  let A := ∑ i ∈ s, M i
  have hM : ∀ i, 0 ≤ M i := fun i => norm_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hM i)
  have hmain : S ≤ ‖F‖ * Real.sqrt S := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := ε / (A + 1)
    have hδ : 0 < δ := div_pos hε (by linarith)
    have hex : ∀ i, ∃ x : E i, ‖x‖ < 1 ∧ M i - δ < ‖l2Restriction E F i x‖ := by
      intro i
      exact (l2Restriction E F i).exists_lt_apply_of_lt_opNorm (by dsimp only [M]; linarith)
    choose x hxn hxe using hex
    let y : ∀ i, E i := fun i => if 0 ≤ l2Restriction E F i (x i) then x i else -x i
    have hyn : ∀ i, ‖y i‖ ≤ 1 := by
      intro i
      dsimp only [y]
      split_ifs <;> simpa only [norm_neg] using (hxn i).le
    have hye : ∀ i, l2Restriction E F i (y i) = ‖l2Restriction E F i (x i)‖ := by
      intro i
      dsimp only [y]
      split_ifs with hi
      · exact (abs_of_nonneg hi).symm
      · rw [map_neg, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hi)]
    let z : L2Sum E := ∑ i ∈ s, lp.single 2 i (M i • y i)
    have hzn : ‖z‖ ≤ Real.sqrt S := by
      apply Real.le_sqrt_of_sq_le
      rw [l2_norm_sum_single_sq]
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hM i)]
      have hb : M i * ‖y i‖ ≤ M i := by nlinarith [hM i, hyn i]
      nlinarith [mul_nonneg (hM i) (norm_nonneg (y i))]
    have hze : F z = ∑ i ∈ s, M i * ‖l2Restriction E F i (x i)‖ := by
      simp only [z, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      change l2Restriction E F i (M i • y i) = _
      rw [map_smul, smul_eq_mul, hye]
    have hlow : S - δ * A ≤ F z := by
      rw [hze]
      change (∑ i ∈ s, M i ^ 2) - δ * (∑ i ∈ s, M i) ≤ _
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have h := mul_le_mul_of_nonneg_left (hxe i).le (hM i)
      nlinarith
    have hhigh : F z ≤ ‖F‖ * Real.sqrt S := by
      exact (le_abs_self _).trans ((F.le_opNorm z).trans
        (mul_le_mul_of_nonneg_left hzn (norm_nonneg _)))
    have hδε : δ * A < ε := by
      dsimp only [δ]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by linarith : 0 < A + 1)).mpr
      nlinarith
    linarith
  change S ≤ ‖F‖ ^ 2
  have hs := Real.sq_sqrt hS
  nlinarith [Real.sqrt_nonneg S, norm_nonneg F]


def l2DualRestrictions (F : StrongDual ℝ (L2Sum E)) : L2Sum (fun i => StrongDual ℝ (E i)) :=
  ⟨l2Restriction E F, memℓp_gen' (C := ‖F‖ ^ 2) (fun s => by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using l2Restriction_square_sum E F s)⟩


def l2DualPair : L2Sum (fun i => StrongDual ℝ (E i)) →L[ℝ] StrongDual ℝ (L2Sum E) :=
  lp.dualPairing 2 2 (fun i => ContinuousLinearMap.id ℝ (StrongDual ℝ (E i)))
    (K := 1) (fun _ => ContinuousLinearMap.norm_id_le)

@[simp] theorem l2DualPair_apply (f : L2Sum (fun i => StrongDual ℝ (E i))) (x : L2Sum E) :
    l2DualPair E f x = ∑' i, f i (x i) := by
  have _ := decidableEqI
  exact rfl

theorem l2DualPair_norm_le : ‖l2DualPair E‖ ≤ 1 := by
  have _ := decidableEqI
  exact
    lp.norm_dualPairing _ _

@[simp] theorem l2DualPair_single (f : L2Sum (fun i => StrongDual ℝ (E i))) (i : I) (x : E i) :
    l2DualPair E f (lp.single 2 i x) = f i x := by
  classical
  rw [l2DualPair_apply]
  rw [tsum_eq_single i]
  · rw [lp.single_apply_self]
  · intro j hji
    rw [lp.single_apply_ne 2 i x hji, map_zero]

@[simp] theorem l2DualPair_restrictions (F : StrongDual ℝ (L2Sum E)) :
    l2DualPair E (l2DualRestrictions E F) = F := by
  apply ContinuousLinearMap.ext
  intro x
  have h1 := (l2DualPair E (l2DualRestrictions E F)).hasSum (lp.hasSum_single (by norm_num) x)
  have h2 := F.hasSum (lp.hasSum_single (by norm_num) x)
  simp only [l2DualPair_single, l2DualRestrictions, l2Restriction_apply] at h1
  exact h1.unique h2

@[simp] theorem l2DualRestrictions_pair (f : L2Sum (fun i => StrongDual ℝ (E i))) :
    l2DualRestrictions E (l2DualPair E f) = f := by
  apply Subtype.ext
  funext i
  apply ContinuousLinearMap.ext
  intro x
  exact l2DualPair_single E f i x

theorem l2DualPair_surjective : Function.Surjective (l2DualPair E) := fun F =>
  ⟨l2DualRestrictions E F, l2DualPair_restrictions E F⟩

theorem l2DualRestrictions_norm_le (F : StrongDual ℝ (L2Sum E)) :
    ‖l2DualRestrictions E F‖ ≤ ‖F‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg _)
  intro s
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, l2DualRestrictions] using l2Restriction_square_sum E F s

theorem l2DualPair_norm_map (f : L2Sum (fun i => StrongDual ℝ (E i))) :
    ‖l2DualPair E f‖ = ‖f‖ := by
  apply le_antisymm
  · exact (l2DualPair E).le_of_opNorm_le (l2DualPair_norm_le E) f |>.trans_eq (one_mul _)
  · simpa only [l2DualRestrictions_pair] using l2DualRestrictions_norm_le E (l2DualPair E f)


def l2DualEquiv : L2Sum (fun i => StrongDual ℝ (E i)) ≃ₗᵢ[ℝ] StrongDual ℝ (L2Sum E) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (l2DualPair E).toLinearMap, norm_map' := l2DualPair_norm_map E }
    (l2DualPair_surjective E)


theorem l2Sum_reflexive (hE : ∀ i, Reflexive (E i)) : Reflexive (L2Sum E) := by
  intro Φ
  let G := Φ.comp (l2DualPair E)
  let z := l2DualRestrictions (fun i => StrongDual ℝ (E i)) G
  have hex : ∀ i, ∃ x : E i, NormedSpace.inclusionInDoubleDual ℝ (E i) x = z i :=
    fun i => hE i (z i)
  choose x hx using hex
  have hnorm : ∀ i, ‖x i‖ = ‖z i‖ := by
    intro i
    have h := (NormedSpace.inclusionInDoubleDualLi ℝ (E := E i)).norm_map (x i)
    change ‖NormedSpace.inclusionInDoubleDual ℝ (E i) (x i)‖ = _ at h
    rw [hx] at h
    exact h.symm
  let u : L2Sum E := ⟨x, memℓp_gen (by
    simpa only [hnorm] using (lp.memℓp z).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
  refine ⟨u, ?_⟩
  apply ContinuousLinearMap.ext
  intro F
  obtain ⟨f, rfl⟩ := l2DualPair_surjective E F
  change l2DualPair E f u = Φ (l2DualPair E f)
  have hG := l2DualPair_restrictions (fun i => StrongDual ℝ (E i)) G
  have hh := congrArg (fun L => L f) hG
  change (∑' i, z i (f i)) = Φ (l2DualPair E f) at hh
  rw [← hh, l2DualPair_apply]
  apply tsum_congr
  intro i
  have h := congrArg (fun φ => φ (f i)) (hx i)
  exact h

end L2Duality

section ReflexivityTransport
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem Reflexive.of_equiv (hE : Reflexive E) (e : E ≃L[ℝ] D) : Reflexive D := by
  intro Φ
  let F := Φ.comp (e.symm.toContinuousLinearMap.precomp ℝ)
  obtain ⟨x, hx⟩ := hE F
  refine ⟨e x, ?_⟩
  apply ContinuousLinearMap.ext
  intro g
  have h := congrArg (fun L => L (g.comp e.toContinuousLinearMap)) hx
  change g (e x) = Φ ((g.comp e.toContinuousLinearMap).comp e.symm.toContinuousLinearMap) at h
  have he : (g.comp e.toContinuousLinearMap).comp e.symm.toContinuousLinearMap = g := by
    ext y
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply]
  rw [he] at h
  exact h

theorem Reflexive.dual (hE : Reflexive E) : Reflexive (StrongDual ℝ E) := by
  intro Φ
  let x := Φ.comp (NormedSpace.inclusionInDoubleDual ℝ E)
  refine ⟨x, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  obtain ⟨p, rfl⟩ := hE f
  rfl

end ReflexivityTransport


theorem hilbert_reflexive (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] : Reflexive E := by
  intro Φ
  let j := InnerProductSpace.toDual ℝ E
  let g := Φ.comp j.toContinuousLinearEquiv.toContinuousLinearMap
  let y := j.symm g
  refine ⟨y, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  obtain ⟨v, rfl⟩ := j.surjective f
  change inner ℝ v y = Φ (j v)
  rw [real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply




end SegmentLenses

end

end OAI
