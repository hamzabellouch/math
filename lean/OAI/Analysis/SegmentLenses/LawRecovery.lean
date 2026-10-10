import OAI.Analysis.SegmentLenses.AtomicBalls

namespace OAI

/-!
# Exact finite-law recovery and coefficient representations
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses



namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]


def expect (μ : FiniteLaw Ω) {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : Ω → E) : E :=
  ∑ ω, μ.weight ω • f ω

@[simp] theorem expect_const (μ : FiniteLaw Ω) {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (c : E) : μ.expect (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_smul, μ.total, one_smul]

@[simp] theorem expect_add (μ : FiniteLaw Ω) {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f g : Ω → E) : μ.expect (fun ω => f ω + g ω) = μ.expect f + μ.expect g := by
  simp only [expect, smul_add, Finset.sum_add_distrib]

@[simp] theorem expect_sub (μ : FiniteLaw Ω) {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f g : Ω → E) : μ.expect (fun ω => f ω - g ω) = μ.expect f - μ.expect g := by
  simp only [expect, smul_sub, Finset.sum_sub_distrib]

@[simp] theorem expect_smul (μ : FiniteLaw Ω) {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a : ℝ) (f : Ω → E) : μ.expect (fun ω => a • f ω) = a • μ.expect f := by
  simp only [expect, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  exact smul_comm _ _ _

@[simp] theorem expect_map (μ : FiniteLaw Ω) {E F : Type*} [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F] (T : E →ₗ[ℝ] F) (f : Ω → E) :
    μ.expect (fun ω => T (f ω)) = T (μ.expect f) := by
  simp only [expect, map_sum, map_smul]

@[simp] theorem expect_scalar (μ : FiniteLaw Ω) (f : Ω → ℝ) : μ.expect f = μ.mean f := rfl

@[simp] theorem mean_sum (μ : FiniteLaw Ω) {ι : Type*} [Fintype ι] (f : Ω → ι → ℝ) :
    μ.mean (fun ω => ∑ i, f ω i) = ∑ i, μ.mean (fun ω => f ω i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem norm_expect_le (μ : FiniteLaw Ω) {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Ω → E) : ‖μ.expect f‖ ≤ μ.mean (fun ω => ‖f ω‖) := by
  calc
    ‖μ.expect f‖ ≤ ∑ ω, ‖μ.weight ω • f ω‖ := norm_sum_le _ _
    _ = μ.mean (fun ω => ‖f ω‖) := by
      simp only [mean, norm_smul, Real.norm_eq_abs, abs_of_nonneg (μ.nonneg _)]

theorem mean_sqrt_le (μ : FiniteLaw Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    μ.mean (fun ω => Real.sqrt (f ω)) ≤ Real.sqrt (μ.mean f) := by
  have h := μ.sq_mean_le (fun ω => Real.sqrt (f ω))
  simp only [Real.sq_sqrt (hf _)] at h
  have hs := Real.sq_sqrt (μ.mean_nonneg hf)
  nlinarith [Real.sqrt_nonneg (μ.mean f)]


def product {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') :
    FiniteLaw (Ω × Ω') where
  weight ω := μ.weight ω.1 * ν.weight ω.2
  nonneg ω := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, μ.total, ν.total]

theorem product_mean {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω) (ν : FiniteLaw Ω')
    (f : Ω × Ω' → ℝ) :
    (μ.product ν).mean f = μ.mean (fun ω => ν.mean (fun ω' => f (ω, ω'))) := by
  simp only [mean, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem product_mul {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω) (ν : FiniteLaw Ω')
    (f : Ω → ℝ) (g : Ω' → ℝ) :
    (μ.product ν).mean (fun ω => f ω.1 * g ω.2) = μ.mean f * ν.mean g := by
  rw [product_mean]
  simp only [mean_mul]
  simp only [mean, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω hω
  ring


def pooled {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') :
    FiniteLaw (Ω ⊕ Ω') where
  weight := Sum.elim (fun ω => μ.weight ω / 2) (fun ω => ν.weight ω / 2)
  nonneg := fun ω => by cases ω <;> apply div_nonneg <;> first | exact μ.nonneg _ | exact ν.nonneg _ | norm_num
  total := by norm_num [Fintype.sum_sum_type, ← Finset.sum_div, μ.total, ν.total]

theorem pooled_expect {Ω' E : Type*} [Fintype Ω'] [AddCommMonoid E] [Module ℝ E]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') (f : Ω → E) (g : Ω' → E) :
    (μ.pooled ν).expect (Sum.elim f g) = (1/2 : ℝ) • μ.expect f + (1/2 : ℝ) • ν.expect g := by
  simp only [expect, pooled, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.smul_sum, smul_smul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro ω hω <;> congr 1 <;> ring

end FiniteLaw

section LawRecovery
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]


def representation (F : SegmentFamily V) (c : FamilyCoefficients F) : Representation V := ⟨F, c⟩

@[simp] theorem representation_value (F : SegmentFamily V) (c : FamilyCoefficients F) :
    (representation F c).value = familyValue F c := by
  have _ := decidableEqV
  exact rfl

@[simp] theorem representation_energy (F : SegmentFamily V) (c : FamilyCoefficients F) :
    (representation F c).energy = ‖c‖ ^ 2 := by
  have _ := decidableEqV
  change (∑ S : F.sets, c S ^ 2) = ‖c‖ ^ 2
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]


def coefficientLaw (K : Finset V) (c : LocalCoefficients K) (hc : coefficientBudget K c ≤ 1) :
    FiniteLaw (Option (LocalFamily K)) where
  weight ω := ω.elim (1 - coefficientBudget K c) (fun F => ‖c F‖)
  nonneg ω := by cases ω with
    | none => exact sub_nonneg.mpr hc
    | some F => exact norm_nonneg _
  total := by simp [Fintype.sum_option, coefficientBudget]

def coefficientAtoms (K : Finset V) (c : LocalCoefficients K) :
    Option (LocalFamily K) → Representation V :=
  fun ω => ω.elim (representation default 0)
    (fun F => representation F.val (‖c F‖⁻¹ • c F))

theorem coefficientAtoms_energy (K : Finset V) (c : LocalCoefficients K)
    (ω : Option (LocalFamily K)) : (coefficientAtoms K c ω).energy ≤ 1 := by
  cases ω with
  | none => simp [coefficientAtoms]
  | some F =>
      change (representation F.val (‖c F‖⁻¹ • c F)).energy ≤ 1
      rw [representation_energy]
      nlinarith [norm_normalized_le (c F), norm_nonneg (‖c F‖⁻¹ • c F)]

theorem coefficientLaw_mean (K : Finset V) (c : LocalCoefficients K)
    (hc : coefficientBudget K c ≤ 1) :
    (coefficientLaw K c hc).expect (fun ω => (coefficientAtoms K c ω).value) = localValue K c := by
  simp only [FiniteLaw.expect, coefficientLaw, Fintype.sum_option, coefficientAtoms,
    Option.elim_none, Option.elim_some, representation_value, map_zero, smul_zero, zero_add]
  change (∑ F, ‖c F‖ • familyValue F.val (‖c F‖⁻¹ • c F)) = ∑ F, familyValue F.val (c F)
  apply Finset.sum_congr rfl
  intro F hF
  rw [← map_smul, smul_smul]
  by_cases hz : ‖c F‖ = 0
  · have hc0 : c F = 0 := norm_eq_zero.mp hz
    simp [hc0]
  · rw [mul_inv_cancel₀ hz, one_smul]

end LawRecovery

namespace FiniteLaw
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]



theorem absolute_mass_identity (μ : FiniteLaw Ω) (b : Ω → Γ → ℝ) :
    (∑ g, μ.mean (fun ω => |b ω g|) ^ 2) -
      (∑ g, μ.mean (fun ω => b ω g) ^ 2) =
    (μ.product μ).mean (fun ω => ∑ g, (|b ω.1 g * b ω.2 g| - b ω.1 g * b ω.2 g)) := by
  have ha : ∀ g, (μ.product μ).mean (fun ω => |b ω.1 g| * |b ω.2 g|) =
      μ.mean (fun ω => |b ω g|) ^ 2 := fun g => by
    rw [μ.product_mul μ (fun ω => |b ω g|) (fun ω => |b ω g|), sq]
  have hb : ∀ g, (μ.product μ).mean (fun ω => b ω.1 g * b ω.2 g) =
      μ.mean (fun ω => b ω g) ^ 2 := fun g => by
    rw [μ.product_mul μ (fun ω => b ω g) (fun ω => b ω g), sq]
  simp only [mean_sum, mean_sub, abs_mul, ha, hb, Finset.sum_sub_distrib]

theorem absolute_mass_bound (μ : FiniteLaw Ω) (b : Ω → Γ → ℝ) (L : Ω → ℝ)
    (h : ∀ ω ω', (∑ g, (|b ω g * b ω' g| - b ω g * b ω' g)) ≤ L ω + L ω') :
    (∑ g, μ.mean (fun ω => |b ω g|) ^ 2) ≤
      (∑ g, μ.mean (fun ω => b ω g) ^ 2) + 2 * μ.mean L := by
  have hm := (μ.product μ).mean_mono (fun ω => h ω.1 ω.2)
  rw [← absolute_mass_identity] at hm
  have he : (μ.product μ).mean (fun ω => L ω.1 + L ω.2) = 2 * μ.mean L := by
    rw [product_mean]
    simp only [mean_add, mean_const]
    ring
  rw [he] at hm
  linarith



theorem signed_mass_bound (μ : FiniteLaw Ω) (b W : Ω → Γ → ℝ) (V : Ω → ℝ)
    (hzero : ∀ g, μ.mean (fun ω => b ω g + W ω g) = 0)
    (hW : ∀ ω, (∑ g, W ω g ^ 2) ≤ V ω) :
    (∑ g, μ.mean (fun ω => b ω g) ^ 2) ≤ μ.mean V := by
  calc
    (∑ g, μ.mean (fun ω => b ω g) ^ 2) = ∑ g, μ.mean (fun ω => W ω g) ^ 2 := by
      apply Finset.sum_congr rfl
      intro g hg
      have h := hzero g
      rw [mean_add] at h
      have he : μ.mean (fun ω => b ω g) = - μ.mean (fun ω => W ω g) := by linarith only [h]
      rw [he, neg_sq]
    _ ≤ ∑ g, μ.mean (fun ω => W ω g ^ 2) :=
      Finset.sum_le_sum (fun g _ => μ.sq_mean_le (fun ω => W ω g))
    _ = μ.mean (fun ω => ∑ g, W ω g ^ 2) := (μ.mean_sum _).symm
    _ ≤ μ.mean V := μ.mean_mono hW



theorem joint_mass_bound (μ : FiniteLaw Ω) (b W : Ω → Γ → ℝ) (V L : Ω → ℝ)
    (hzero : ∀ g, μ.mean (fun ω => b ω g + W ω g) = 0)
    (hW : ∀ ω, (∑ g, W ω g ^ 2) ≤ V ω)
    (hc : ∀ ω ω', (∑ g, (|b ω g * b ω' g| - b ω g * b ω' g)) ≤ L ω + L ω') :
    (∑ g, μ.mean (fun ω => |b ω g|) ^ 2) ≤ μ.mean V + 2 * μ.mean L :=
  (μ.absolute_mass_bound b L hc).trans (add_le_add (μ.signed_mass_bound b W V hzero hW) le_rfl)

end FiniteLaw

section RepresentationGates
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

@[simp] theorem segmentFunctional_unitVector (S : Finset V) (g : V) :
    segmentFunctional S (unitVector g) = if g ∈ S then 1 else 0 := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  simp [segmentFunctional, coordinate_unitVector, eq_comm]

@[simp] theorem Representation.apply_unitVector (A : Representation V) (g : V) :
    A.value (unitVector g) = ∑ S : A.family.sets, if g ∈ S.val then A.coeff S else 0 := by
  simp [Representation.value, segmentFunctional_unitVector, mul_ite]

theorem Representation.apply_of_mem (A : Representation V) (S : A.family.sets)
    {g : V} (hg : g ∈ S.val) : A.value (unitVector g) = A.coeff S := by
  rw [A.apply_unitVector, Finset.sum_eq_single S]
  · simp [hg]
  · intro T hT hne
    have hn : g ∉ T.val := fun ht => Finset.disjoint_left.mp
      (A.family.disjoint T.property S.property (fun he => hne (Subtype.ext he))) ht hg
    simp [hn]
  · simp

theorem Representation.apply_nonzero (A : Representation V) {g : V}
    (hg : A.value (unitVector g) ≠ 0) : ∃ S : A.family.sets, g ∈ S.val := by
  rw [A.apply_unitVector] at hg
  by_contra h
  apply hg
  apply Finset.sum_eq_zero
  intro S hS
  have hn : g ∉ S.val := fun hS => h ⟨S, hS⟩
  simp [hn]



theorem Representation.gate_energy_le (A : Representation V) {H : Finset V}
    (G : Finset V) (hG : ∀ g ∈ G, Gate H g) :
    (∑ g : G, A.value (unitVector g.val) ^ 2) ≤ A.energy := by
  classical
  let active : G → Prop := fun g => A.value (unitVector g.val) ≠ 0
  let Γ := {g : G // active g}
  have hS : ∀ g : Γ, ∃ S : A.family.sets, g.val.val ∈ S.val :=
    fun g => A.apply_nonzero g.property
  let select : Γ → A.family.sets := fun g => Classical.choose (hS g)
  have hmem : ∀ g : Γ, g.val.val ∈ (select g).val := fun g => Classical.choose_spec (hS g)
  have hinj : Function.Injective select := by
    intro g g' he
    apply Subtype.ext
    apply Subtype.ext
    have hm' := hmem g'
    rw [← he] at hm'
    exact A.family.gate_unique (select g) (hG _ g.val.property) (hG _ g'.val.property)
      (hmem g) hm'
  have hsum : (∑ g : G, A.value (unitVector g.val) ^ 2) =
      ∑ g : Γ, A.coeff (select g) ^ 2 := by
    have he : (∑ g : G, A.value (unitVector g.val) ^ 2) =
        ∑ g : G, if active g then A.value (unitVector g.val) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      by_cases hne : active g
      · simp [hne]
      · have hz : A.value (unitVector g.val) = 0 := not_ne_iff.mp hne
        simp [hne, hz]
    rw [he, ← Finset.sum_filter,
      Finset.sum_subtype (p := active) _ (fun g => by simp)]
    apply Finset.sum_congr rfl
    intro g hg
    rw [A.apply_of_mem (select g) (hmem g)]
  rw [hsum]
  calc
    (∑ g : Γ, A.coeff (select g) ^ 2) =
      ∑ S ∈ Finset.univ.image select, A.coeff S ^ 2 := (Finset.sum_image (s := Finset.univ) (g := select)
        (f := fun S => A.coeff S ^ 2) hinj.injOn).symm
    _ ≤ ∑ S, A.coeff S ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)

end RepresentationGates


end SegmentLenses

end

end OAI
