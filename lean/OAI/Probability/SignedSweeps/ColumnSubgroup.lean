import OAI.Probability.SignedSweeps.ColumnAnnihilation
import OAI.Probability.SignedSweeps.PartitionGeometry

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

def oneCardRepresentation (n : ℕ) :
    Representation ℂ (SymmetricGroup n) (Fin n → ℂ) where
  toFun g := {
    toFun := fun f x => f (g⁻¹ x)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_one' := by ext f x; rfl
  map_mul' := by intros; ext f x; rfl

@[simp]
lemma oneCardRepresentation_apply {n : ℕ} (g : SymmetricGroup n) (f : Fin n → ℂ) (x : Fin n) :
    oneCardRepresentation n g f x = f (g⁻¹ x) := rfl

def binaryFlip (d : ℕ) (i : Fin d) : Equiv.Perm (BinaryPositions d) where
  toFun x := Function.update x i (x i).rev
  invFun x := Function.update x i (x i).rev
  left_inv x := by simp
  right_inv x := by simp

def flipPermutation (d : ℕ) (i : Fin d) : SymmetricGroup (2 ^ d) :=
  (positionsEquiv d).permCongr (binaryFlip d i)

@[simp]
lemma binaryFlip_apply (d : ℕ) (i : Fin d) (x : BinaryPositions d) :
    binaryFlip d i x = Function.update x i (x i).rev := rfl

@[simp]
lemma flipPermutation_inv (d : ℕ) (i : Fin d) :
    (flipPermutation d i)⁻¹ = flipPermutation d i := by
  apply Equiv.ext
  intro x
  rfl

@[simp]
lemma flipPermutation_twice (d : ℕ) (i : Fin d) (x : Fin (2 ^ d)) :
    flipPermutation d i (flipPermutation d i x) = x := by
  have h := (flipPermutation d i).symm_apply_apply x
  change (flipPermutation d i)⁻¹ ((flipPermutation d i) x) = x at h
  rwa [flipPermutation_inv] at h

lemma flipPermutation_mem (d : ℕ) (i : Fin d) :
    flipPermutation d i ∈ coordinateSubgroup d i := by
  intro x
  funext j
  simp [flipPermutation, Equiv.permCongr_apply, Function.update_of_ne j.2]

lemma flipPermutation_commute (d : ℕ) (i j : Fin d) :
    Commute (flipPermutation d i) (flipPermutation d j) := by
  change _ * _ = _ * _
  apply Equiv.ext
  intro x
  apply (positionsEquiv d).symm.injective
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, flipPermutation,
    Equiv.permCongr_apply, Equiv.symm_apply_apply]
  by_cases h : i = j
  · rw [h]
  · simp only [binaryFlip_apply, Function.update_of_ne h, Function.update_of_ne (Ne.symm h)]
    exact Function.update_comm (Ne.symm h) _ _ _

lemma binary_eq_or_flip {d : ℕ} (i : Fin d) (x y : BinaryPositions d)
    (h : ∀ j, j ≠ i → y j = x j) : y = x ∨ y = binaryFlip d i x := by
  by_cases hi : y i = x i
  · left
    funext j
    exact if hji : j = i then hji ▸ hi else h j hji
  · right
    have hf : y i = (x i).rev := by
      generalize hxi : x i = a at hi ⊢
      generalize hyi : y i = b at hi ⊢
      fin_cases a <;> fin_cases b <;> simp_all
    funext j
    by_cases hji : j = i
    · simpa [hji] using hf
    · simpa [Function.update_of_ne hji] using h j hji

lemma coordinate_or_flip {d : ℕ} (i : Fin d) {g : SymmetricGroup (2 ^ d)}
    (hg : g ∈ coordinateSubgroup d i) (x : Fin (2 ^ d)) :
    g x = x ∨ g x = flipPermutation d i x := by
  have hb := binary_eq_or_flip i ((positionsEquiv d).symm x) ((positionsEquiv d).symm (g x))
    (fun j hj => congrFun (hg x) ⟨j, hj⟩)
  rcases hb with hb | hb
  · exact Or.inl ((positionsEquiv d).symm.injective hb)
  · right
    apply (positionsEquiv d).symm.injective
    simpa only [flipPermutation, Equiv.permCongr_apply, Equiv.symm_apply_apply] using hb

lemma oneCard_average_eq {d : ℕ} (i : Fin d) :
    groupAverage ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype) =
      (1 / 2 : ℂ) • (1 + oneCardRepresentation (2 ^ d) (flipPermutation d i)) := by
  classical
  let ρ := (oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype
  let T : (Fin (2 ^ d) → ℂ) →ₗ[ℂ] (Fin (2 ^ d) → ℂ) :=
    (1 / 2 : ℂ) • (1 + oneCardRepresentation (2 ^ d) (flipPermutation d i))
  have hTf (g : coordinateSubgroup d i) (f : Fin (2 ^ d) → ℂ) : ρ g (T f) = T f := by
    ext x
    change (1 / 2 : ℂ) * (f (g.1⁻¹ x) + f ((flipPermutation d i)⁻¹ (g.1⁻¹ x))) =
      (1 / 2 : ℂ) * (f x + f ((flipPermutation d i)⁻¹ x))
    rw [flipPermutation_inv]
    rcases coordinate_or_flip i ((coordinateSubgroup d i).inv_mem g.property) x with hx | hx
    · rw [hx]
    · rw [hx, flipPermutation_twice, add_comm]
  apply LinearMap.ext
  intro f
  funext x
  have hfixed := groupAverage_fixed ρ (T f) (fun g => hTf g f)
  have ha : groupAverage ρ (T f) = groupAverage ρ f := by
    show groupAverage ρ ((1 / 2 : ℂ) • (f + ρ ⟨flipPermutation d i, flipPermutation_mem d i⟩ f)) = _
    rw [map_smul, map_add, groupAverage_apply_action]
    module
  exact congrFun (ha.symm.trans hfixed) x

lemma oneCard_averages_commute {d : ℕ} (i j : Fin d) :
    Commute (groupAverage ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype))
      (groupAverage ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d j).subtype)) := by
  rw [oneCard_average_eq, oneCard_average_eq]
  apply Commute.smul_right
  apply Commute.smul_left
  apply Commute.add_left (Commute.one_left _)
  apply Commute.add_right (Commute.one_right _)
  exact (flipPermutation_commute d i j).map (oneCardRepresentation (2 ^ d))

lemma prod_absorbs_commuting_idempotent {M : Type*} [Monoid M] (L : List M) (P : M)
    (hm : P ∈ L) (hc : ∀ A ∈ L, Commute P A) (hP : IsIdempotentElem P) :
    P * L.prod = L.prod := by
  induction L with
  | nil => simp at hm
  | cons A L ih =>
    simp only [List.prod_cons]
    rcases List.mem_cons.mp hm with h | h
    · rw [← h, ← mul_assoc, hP]
    · calc
        P * (A * L.prod) = A * (P * L.prod) := by rw [← mul_assoc, hc A (by simp), mul_assoc]
        _ = A * L.prod := by rw [ih h (fun B hB => hc B (by simp [hB]))]

def oneCardSweep (d : ℕ) : (Fin (2 ^ d) → ℂ) →ₗ[ℂ] (Fin (2 ^ d) → ℂ) :=
  ((List.ofFn (fun i : Fin d =>
    groupAverage ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype))).reverse).prod

lemma oneCardSweep_invariant {d : ℕ} (f : Fin (2 ^ d) → ℂ) (g : SymmetricGroup (2 ^ d)) :
    oneCardRepresentation (2 ^ d) g (oneCardSweep d f) = oneCardSweep d f := by
  have hfixed (i : Fin d) :
      groupAverage ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype) *
        oneCardSweep d = oneCardSweep d := by
    unfold oneCardSweep
    apply prod_absorbs_commuting_idempotent _ _ (by
      simp only [List.mem_reverse, List.mem_ofFn]
      exact ⟨i, rfl⟩)
    · intro A hA
      simp only [List.mem_reverse, List.mem_ofFn] at hA
      obtain ⟨j, rfl⟩ := hA
      exact oneCard_averages_commute i j
    · exact groupAverage_idempotent _
  have ht := coordinateSubgroups_generate d
    (vectorStabilizer (oneCardRepresentation (2 ^ d)) (oneCardSweep d f)) (fun i h hh => by
      change oneCardRepresentation (2 ^ d) h (oneCardSweep d f) = oneCardSweep d f
      have hi := congrArg (fun T : _ →ₗ[ℂ] _ => T f) (hfixed i)
      rw [← hi]
      exact groupAverage_invariant
        ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype) ⟨h, hh⟩ (oneCardSweep d f))
  exact (show g ∈ vectorStabilizer (oneCardRepresentation (2 ^ d)) (oneCardSweep d f) from ht ▸ Subgroup.mem_top _)

lemma oneCard_sum_invariant {n : ℕ} (g : SymmetricGroup n) (f : Fin n → ℂ) :
    ∑ b, oneCardRepresentation n g f b = ∑ b, f b := by
  exact Equiv.sum_comp g⁻¹ f

lemma oneCard_average_sum {n : ℕ} (H : Subgroup (SymmetricGroup n)) (f : Fin n → ℂ) :
    ∑ b, groupAverage ((oneCardRepresentation n).comp H.subtype) f b = ∑ b, f b := by
  have hc : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply,
    Finset.sum_apply, MonoidHom.comp_apply, Subgroup.subtype_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [oneCard_sum_invariant, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

lemma oneCardSweep_sum {d : ℕ} (f : Fin (2 ^ d) → ℂ) :
    ∑ b, oneCardSweep d f b = ∑ b, f b := by
  have hp : ∀ L : List (Fin d), ∀ f : Fin (2 ^ d) → ℂ,
      ∑ b, ((L.map (fun i => groupAverage
        ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype))).prod f) b =
        ∑ b, f b := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih =>
      intro f
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [oneCard_average_sum, ih]
  simpa [oneCardSweep, List.ofFn_eq_map] using hp (List.finRange d).reverse f

lemma oneCardSweep_uniform {d : ℕ} (f : Fin (2 ^ d) → ℂ) (x : Fin (2 ^ d)) :
    oneCardSweep d f x = (∑ b, f b) / (2 ^ d : ℕ) := by
  have hc (y : Fin (2 ^ d)) : oneCardSweep d f y = oneCardSweep d f x := by
    have h := congrFun (oneCardSweep_invariant f (Equiv.swap x y)) x
    simpa using h
  have hs := oneCardSweep_sum f
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn : (((2 ^ d) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero d (by norm_num : (2 : ℕ) ≠ 0))
  apply (eq_div_iff hn).mpr
  rwa [mul_comm]

def oneCardLift {n : ℕ} (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] RegularSpace n where
  toFun f := WithLp.toLp 2 (fun g => f (g a))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma oneCardLift_intertwines {n : ℕ} (a : Fin n) (f : Fin n → ℂ) (g : SymmetricGroup n) :
    oneCardLift a (oneCardRepresentation n g f) = regularRepresentation n g (oneCardLift a f) := by
  ext h
  rfl

lemma oneCardLift_groupAverage {n : ℕ} (a : Fin n) (f : Fin n → ℂ) (H : Subgroup (SymmetricGroup n)) :
    oneCardLift a (groupAverage ((oneCardRepresentation n).comp H.subtype) f) =
      groupAverage ((regularRepresentation n).comp H.subtype) (oneCardLift a f) := by
  classical
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    MonoidHom.comp_apply, Subgroup.subtype_apply, oneCardLift_intertwines]

lemma spechtInclusion_layer {d : ℕ} (lam : Partition (2 ^ d)) (i : Fin d) (x : Specht lam) :
    spechtInclusion lam (layerOperator lam i x) =
      groupAverage ((regularRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype)
        (spechtInclusion lam x) := by
  classical
  simp only [layerOperator, groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rfl

lemma specht_function_of_one_card {n : ℕ} (lam : Partition n) (hk : n - lam.1.rowLen 0 = 1)
    (x : Specht lam) : ∃ a : Fin n, ∃ f : Fin n → ℂ, spechtInclusion lam x = oneCardLift a f := by
  classical
  have hc : Fintype.card (OffFirstRow lam) = 1 := (card_offFirstRow lam).trans hk
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hc
  let f := fun b : Fin n => spechtInclusion lam x (Equiv.swap a.1 b)
  refine ⟨a.1, f, ?_⟩
  ext g
  let h := Equiv.swap a.1 (g a.1)
  have he (b : OffFirstRow lam) : h b.1 = g b.1 := by
    rw [ha b]
    exact Equiv.swap_apply_left _ _
  let t : rowSubgroup lam := ⟨h⁻¹ * g, restrict_offFirstRow_eq lam h g he⟩
  change spechtInclusion lam x g = spechtInclusion lam x h
  simpa [t] using specht_right_row lam x t h

lemma oneCardLift_sweep {d : ℕ} (lam : Partition (2 ^ d)) (x : Specht lam)
    {a : Fin (2 ^ d)} {f : Fin (2 ^ d) → ℂ} (hx : spechtInclusion lam x = oneCardLift a f) :
    spechtInclusion lam (sweepOperator lam x) = oneCardLift a (oneCardSweep d f) := by
  have hh : ∀ (L : List (Fin d)) (x : Specht lam) (f : Fin (2 ^ d) → ℂ),
      spechtInclusion lam x = oneCardLift a f →
      spechtInclusion lam ((L.map (layerOperator lam)).prod x) =
      oneCardLift a ((L.map (fun i => groupAverage
        ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype))).prod f) := by
    intro L
    induction L with
    | nil => intros; simpa
    | cons i L ih =>
      intro x f hx
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [spechtInclusion_layer, ih x f hx, ← oneCardLift_groupAverage]
  simpa [sweepOperator, oneCardSweep, List.ofFn_eq_map] using hh (List.ofFn (fun i : Fin d => i)).reverse x f hx

lemma sweepOperator_eq_zero_of_level_one {d : ℕ} (lam : Partition (2 ^ d))
    (hk : 2 ^ d - lam.1.rowLen 0 = 1) : sweepOperator lam = 0 := by
  have hl : 1 < lam.1.colLen 0 := by
    by_contra h
    have hc : Fintype.card (OffFirstRow lam) = 1 := (card_offFirstRow lam).trans hk
    obtain ⟨a, _⟩ := Fintype.card_eq_one_iff.mp hc
    exact a.property (rowOf_eq_zero lam (by omega) a.1)
  ext x
  apply specht_invariant_eq_zero lam hl
  intro g
  obtain ⟨a, f, hx⟩ := specht_function_of_one_card lam hk x
  apply (show Function.Injective (spechtInclusion lam) from Subtype.val_injective)
  change regularRepresentation _ g (spechtInclusion lam (sweepOperator lam x)) = _
  rw [oneCardLift_sweep lam x hx, ← oneCardLift_intertwines, oneCardSweep_invariant]

lemma weightedMoment_eq_zero_of_level_one {d : ℕ} (lam : Partition (2 ^ d))
    (hk : 2 ^ d - lam.1.rowLen 0 = 1) {r : ℕ} (hr : 1 ≤ r) :
    weightedMoment lam r = 0 := by
  simp [weightedMoment, sweepSquare, positiveSquare,
    sweepOperator_eq_zero_of_level_one lam hk, zero_pow (by omega : r ≠ 0)]

lemma signed_moment_bound_of_level_one {d : ℕ} (lam : Partition (2 ^ d))
    (hk : 2 ^ d - lam.1.rowLen 0 = 1) {r : ℕ} (hr : 1 ≤ r)
    (η κ : ℝ) {u v : ℕ} (α : Partition u) (β : Partition v) (l : ℕ) :
    logMoment (weightedMoment lam r) ≤
      ((coefficient η d * signedEntropy α β + remainderBudget κ d l : ℝ) : EReal) := by
  rw [weightedMoment_eq_zero_of_level_one lam hk hr, logMoment_zero]
  exact bot_le

end SignedSweeps
end

end OAI
