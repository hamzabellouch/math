import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Logic.Equiv.Prod
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalEdgesLemmas
import OAI.Computability.UniqueGames.Gadgets.AdaptivePathsLemmas
import OAI.Computability.UniqueGames.Reduction.BinaryLinear
import OAI.Computability.UniqueGames.Reduction.FinalParametersLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Gadget.LinearEvaluation

universe u v

variable {V : Type u} {P : Type v}
variable [AddCommGroup V] [Module (ZMod 2) V]
variable [AddCommGroup P] [Module (ZMod 2) P]

def fiberEquivKernel (f : V →ₗ[ZMod 2] P) (a : P) (v : V) (hv : f v = a) :
    {x : V // f x = a} ≃ f.ker where
  toFun x := ⟨x.val - v, by simp [x.property, hv]⟩
  invFun k := ⟨k.val + v, by simp [hv]⟩
  left_inv x := by ext; simp
  right_inv k := by ext; simp

theorem fiber_card_eq_kernel_of_surjective (f : V →ₗ[ZMod 2] P)
    (hf : Function.Surjective f) (a : P) :
    Nat.card {x : V // f x = a} = Nat.card f.ker := by
  obtain ⟨v, hv⟩ := hf a
  exact Nat.card_congr (fiberEquivKernel f a v hv)

variable [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) P]

omit [FiniteDimensional (ZMod 2) P] in

theorem fiber_card_mul_pow_of_surjective (f : V →ₗ[ZMod 2] P)
    (hf : Function.Surjective f) (a : P) :
    Nat.card {x : V // f x = a} * 2 ^ Module.finrank (ZMod 2) P = Nat.card V := by
  rw [fiber_card_eq_kernel_of_surjective f hf]
  have hr : Module.finrank (ZMod 2) f.range = Module.finrank (ZMod 2) P := by
    rw [LinearMap.range_eq_top.mpr hf, finrank_top]
  rw [← hr]
  exact LinearKernelCount.kernel_card_mul_pow_rank f

theorem fiber_card_mul_card_of_surjective (f : V →ₗ[ZMod 2] P)
    (hf : Function.Surjective f) (a : P) :
    Nat.card {x : V // f x = a} * Nat.card P = Nat.card V := by
  rw [LinearKernelCount.card_binary_space (V := P)]
  exact fiber_card_mul_pow_of_surjective f hf a

omit [FiniteDimensional (ZMod 2) P] in

theorem cancellation_card_mul_pow_of_surjective (f : V →ₗ[ZMod 2] P)
    (hf : Function.Surjective f) (a : P) :
    Nat.card {x : V // a + f x = 0} * 2 ^ Module.finrank (ZMod 2) P = Nat.card V := by
  have hevent : {x : V // a + f x = 0} ≃ {x : V // f x = -a} :=
    Equiv.subtypeEquivRight fun _ => add_eq_zero_iff_eq_neg'
  rw [Nat.card_congr hevent]
  exact fiber_card_mul_pow_of_surjective f hf (-a)

theorem cancellation_count_of_surjective_card_le_eight (f : V →ₗ[ZMod 2] P)
    (hf : Function.Surjective f) (a : P) (hcard : Nat.card P ≤ 8) :
    Nat.card V ≤ 8 * Nat.card {x : V // a + f x = 0} := by
  have heq := cancellation_card_mul_pow_of_surjective f hf a
  rw [← LinearKernelCount.card_binary_space (V := P)] at heq
  calc
    Nat.card V = Nat.card {x : V // a + f x = 0} * Nat.card P := heq.symm
    _ ≤ Nat.card {x : V // a + f x = 0} * 8 := Nat.mul_le_mul_left _ hcard
    _ = _ := Nat.mul_comm _ _

theorem cancellation_count_at_least_one_eighth_of_surjective (f : V →ₗ[ZMod 2] P)
    (hf : Function.Surjective f) (a : P) (hP : Module.finrank (ZMod 2) P ≤ 3) :
    Nat.card V ≤ 8 * Nat.card {x : V // a + f x = 0} := by
  apply cancellation_count_of_surjective_card_le_eight f hf a
  rw [LinearKernelCount.card_binary_space (V := P)]
  exact (Nat.pow_le_pow_right (by decide) hP : 2 ^ Module.finrank (ZMod 2) P ≤ 2 ^ 3)

def evaluation (x : V) : (V →ₗ[ZMod 2] P) →ₗ[ZMod 2] P := LinearMap.applyₗ x

omit [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) P] in
@[simp] theorem evaluation_apply (x : V) (f : V →ₗ[ZMod 2] P) :
    evaluation x f = f x := rfl

omit [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) P] in

theorem evaluation_surjective (x : V) (hx : x ≠ 0) :
    Function.Surjective (evaluation x : (V →ₗ[ZMod 2] P) →ₗ[ZMod 2] P) := by
  intro a
  have hxbot : x ∉ (⊥ : Submodule (ZMod 2) V) := by simpa using hx
  obtain ⟨f, _, hf⟩ := LinearMap.exists_extend_of_notMem
    (0 : (⊥ : Submodule (ZMod 2) V) →ₗ[ZMod 2] P) hxbot a
  exact ⟨f, hf⟩

theorem evaluation_fiber_card_mul_pow (x : V) (hx : x ≠ 0) (a : P) :
    Nat.card {f : V →ₗ[ZMod 2] P // f x = a} *
      2 ^ Module.finrank (ZMod 2) P = Nat.card (V →ₗ[ZMod 2] P) := by
  exact fiber_card_mul_pow_of_surjective (evaluation x) (evaluation_surjective x hx) a

theorem cancellation_count_at_least_one_eighth (x : V) (hx : x ≠ 0) (a : P)
    (hP : Module.finrank (ZMod 2) P ≤ 3) :
    Nat.card (V →ₗ[ZMod 2] P) ≤ 8 * Nat.card {f : V →ₗ[ZMod 2] P // a + f x = 0} := by
  exact cancellation_count_at_least_one_eighth_of_surjective
    (evaluation x) (evaluation_surjective x hx) a hP

noncomputable def uniformProbability (event : V → Prop) : ℚ :=
  (Nat.card {x : V // event x} : ℚ) / (Nat.card V : ℚ)

omit [FiniteDimensional (ZMod 2) P] in

theorem cancellation_probability_of_surjective (f : V →ₗ[ZMod 2] P)
    (hf : Function.Surjective f) (a : P) :
    uniformProbability (fun x => a + f x = 0) =
      1 / (2 : ℚ) ^ Module.finrank (ZMod 2) P := by
  have hV : (Nat.card V : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (LinearKernelCount.card_source_pos (V := V)))
  have hpow : (2 : ℚ) ^ Module.finrank (ZMod 2) P ≠ 0 := pow_ne_zero _ (by decide)
  apply (div_eq_div_iff hV hpow).mpr
  have heq := cancellation_card_mul_pow_of_surjective f hf a
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, one_mul] using
    congrArg (fun k : Nat => (k : ℚ)) heq

omit [FiniteDimensional (ZMod 2) P] in

theorem cancellation_probability_at_least_one_eighth_of_surjective
    (f : V →ₗ[ZMod 2] P) (hf : Function.Surjective f) (a : P)
    (hP : Module.finrank (ZMod 2) P ≤ 3) :
    (1 : ℚ) / 8 ≤ uniformProbability (fun x => a + f x = 0) := by
  rw [cancellation_probability_of_surjective f hf a]
  apply one_div_le_one_div_of_le (pow_pos (by decide) _)
  have hnat : 2 ^ Module.finrank (ZMod 2) P ≤ 8 :=
    (Nat.pow_le_pow_right (by decide) hP : 2 ^ Module.finrank (ZMod 2) P ≤ 2 ^ 3)
  exact_mod_cast hnat

omit [FiniteDimensional (ZMod 2) P] in

theorem cancellation_probability_target_dim_zero
    (f : V →ₗ[ZMod 2] P) (hf : Function.Surjective f) (a : P)
    (hP : Module.finrank (ZMod 2) P = 0) :
    uniformProbability (fun x => a + f x = 0) = 1 := by
  rw [cancellation_probability_of_surjective f hf a, hP]
  simp

theorem evaluation_cancellation_probability (x : V) (hx : x ≠ 0) (a : P) :
    uniformProbability (fun f : V →ₗ[ZMod 2] P => a + f x = 0) =
      1 / (2 : ℚ) ^ Module.finrank (ZMod 2) P :=
  cancellation_probability_of_surjective (evaluation x) (evaluation_surjective x hx) a

theorem evaluation_cancellation_probability_at_least_one_eighth
    (x : V) (hx : x ≠ 0) (a : P) (hP : Module.finrank (ZMod 2) P ≤ 3) :
    (1 : ℚ) / 8 ≤ uniformProbability (fun f : V →ₗ[ZMod 2] P => a + f x = 0) :=
  cancellation_probability_at_least_one_eighth_of_surjective
    (evaluation x) (evaluation_surjective x hx) a hP

theorem cancellation_finset_count_of_surjective [Fintype V] [DecidableEq P]
    (f : V →ₗ[ZMod 2] P) (hf : Function.Surjective f) (a : P)
    (hP : Module.finrank (ZMod 2) P ≤ 3) :
    Fintype.card V ≤ 8 * (Finset.univ.filter (fun x : V => a + f x = 0)).card := by
  have h := cancellation_count_at_least_one_eighth_of_surjective f hf a hP
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

theorem evaluation_cancellation_finset_count [Fintype (V →ₗ[ZMod 2] P)] [DecidableEq P]
    (x : V) (hx : x ≠ 0) (a : P) (hP : Module.finrank (ZMod 2) P ≤ 3) :
    Fintype.card (V →ₗ[ZMod 2] P) ≤
      8 * (Finset.univ.filter (fun f : V →ₗ[ZMod 2] P => a + f x = 0)).card := by
  have h := cancellation_count_at_least_one_eighth x hx a hP
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

theorem correction_space_card_pos : 0 < Nat.card (V →ₗ[ZMod 2] P) :=
  LinearKernelCount.card_source_pos

omit [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) P] in

theorem evaluation_fibers_equal_card (x : V) (hx : x ≠ 0) (a b : P) :
    Nat.card {f : V →ₗ[ZMod 2] P // f x = a} =
      Nat.card {f : V →ₗ[ZMod 2] P // f x = b} := by
  exact (fiber_card_eq_kernel_of_surjective (evaluation x) (evaluation_surjective x hx) a).trans
    (fiber_card_eq_kernel_of_surjective (evaluation x) (evaluation_surjective x hx) b).symm

end UniqueGamesTheorem.Gadget.LinearEvaluation

end

section

namespace PerfectCompleteness.DirectionQuotient

abbrev F2 := UniqueGamesTheorem.Integration.BinaryLinear.F2

variable {V B : Type*} [AddCommGroup V] [Module F2 V]

def line (a : V) : Submodule F2 V := Submodule.span F2 {a}

abbrev Space (a : V) := V ⧸ line a

def proj (a : V) : V →ₗ[F2] Space a := (line a).mkQ

theorem proj_surjective (a : V) : Function.Surjective (proj a) :=
  (line a).mkQ_surjective

theorem mem_line_iff (a x : V) : x ∈ line a ↔ x = 0 ∨ x = a := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
    rcases UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases c with hzero | hone
    · left
      simpa only [hzero, zero_smul] using hc.symm
    · right
      simpa only [hone, one_smul] using hc.symm
  · rintro (rfl | rfl)
    · exact (line a).zero_mem
    · exact Submodule.mem_span_singleton_self _

theorem proj_eq_zero_iff (a x : V) : proj a x = 0 ↔ x = 0 ∨ x = a :=
  (Submodule.Quotient.mk_eq_zero (line a)).trans (mem_line_iff a x)

theorem proj_eq_iff (a x y : V) :
    proj a x = proj a y ↔ x - y = 0 ∨ x - y = a :=
  (Submodule.Quotient.eq (line a)).trans (mem_line_iff a (x - y))

theorem card_line (a : V) (ha : a ≠ 0) : Nat.card (line a) = 2 := by
  calc
    Nat.card (line a) = Nat.card F2 :=
      Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton F2 V a ha).symm.toEquiv
    _ = 2 := Nat.card_zmod 2

theorem card_proj_fiber (a : V) (ha : a ≠ 0) (z : Space a) :
    Nat.card {v : V // proj a v = z} = 2 := by
  rw [UniqueGamesTheorem.Gadget.LinearEvaluation.fiber_card_eq_kernel_of_surjective
    (proj a) (proj_surjective a) z]
  change Nat.card (LinearMap.ker (line a).mkQ) = 2
  rw [Submodule.ker_mkQ]
  exact card_line a ha

def projectWithSide (a : V) (x : V × B) : Space a × B :=
  (proj a x.1, x.2)

theorem projectWithSide_surjective (a : V) :
    Function.Surjective (projectWithSide (B := B) a) := by
  intro z
  obtain ⟨v, hv⟩ := proj_surjective a z.1
  exact ⟨(v, z.2), Prod.ext hv rfl⟩

def withSideFiberEquiv (a : V) (z : Space a × B) :
    {x : V × B // projectWithSide a x = z} ≃ {v : V // proj a v = z.1} where
  toFun x := ⟨x.val.1, congrArg Prod.fst x.property⟩
  invFun v := ⟨(v.val, z.2), Prod.ext v.property rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl (congrArg Prod.snd x.property).symm
  right_inv v := by
    apply Subtype.ext
    rfl

theorem card_projectWithSide_fiber (a : V) (ha : a ≠ 0) (z : Space a × B) :
    Nat.card {x : V × B // projectWithSide a x = z} = 2 :=
  (Nat.card_congr (withSideFiberEquiv a z)).trans (card_proj_fiber a ha z.1)

open MixedSupport CanonicalKeys

theorem coarsen_at_most_two [Finite V] {n : Nat}
    (slots : Fin n → Slot) (f : Assignment slots → V) (a : V) (ha : a ≠ 0)
    (Q : Label slots (proj a ∘ f)) :
    Nat.card {P : Label slots f // CanonicalEdges.coarsen slots f (proj a) P = Q} ≤ 2 := by
  apply CanonicalEdges.coarsen_at_most_two slots f (proj a)
  intro z
  exact (card_proj_fiber a ha z).le

theorem coarsenWithSide_at_most_two [Finite V] [Finite B] {n : Nat}
    (slots : Fin n → Slot) (f : Assignment slots → V × B) (a : V) (ha : a ≠ 0)
    (Q : Label slots (projectWithSide a ∘ f)) :
    Nat.card {P : Label slots f //
      CanonicalEdges.coarsen slots f (projectWithSide a) P = Q} ≤ 2 := by
  apply CanonicalEdges.coarsen_at_most_two slots f (projectWithSide a)
  intro z
  exact (card_projectWithSide_fiber a ha z).le

end PerfectCompleteness.DirectionQuotient

end

section

namespace PerfectCompleteness.BlockQuotient

open DirectionQuotient

variable {I B : Type*} {V : I → Type*} [DecidableEq I]

abbrev JointOutput (V : I → Type*) (B : Type*) := (∀ i, V i) × B

abbrev OtherBlocks (V : I → Type*) (selected : I) := ∀ i : {i // i ≠ selected}, V i.val

def splitOutput (V : I → Type*) (B : Type*) (selected : I) :
    JointOutput V B ≃ V selected × (OtherBlocks V selected × B) :=
  ((Equiv.piSplitAt selected V).prodCongr (Equiv.refl B)).trans (Equiv.prodAssoc _ _ _)

@[simp] theorem splitOutput_selected (selected : I) (x : JointOutput V B) :
    (splitOutput V B selected x).1 = x.1 selected := rfl

@[simp] theorem splitOutput_other (selected : I) (x : JointOutput V B)
    (i : {i // i ≠ selected}) :
    (splitOutput V B selected x).2.1 i = x.1 i.val := rfl

@[simp] theorem splitOutput_side (selected : I) (x : JointOutput V B) :
    (splitOutput V B selected x).2.2 = x.2 := rfl

variable [∀ i, AddCommGroup (V i)] [∀ i, Module F2 (V i)]

def projectBlock (selected : I) (a : V selected) (x : JointOutput V B) :
    Space a × (OtherBlocks V selected × B) :=
  projectWithSide a (splitOutput V B selected x)

@[simp] theorem projectBlock_selected (selected : I) (a : V selected)
    (x : JointOutput V B) : (projectBlock selected a x).1 = proj a (x.1 selected) := rfl

@[simp] theorem projectBlock_other (selected : I) (a : V selected)
    (x : JointOutput V B) (i : {i // i ≠ selected}) :
    (projectBlock selected a x).2.1 i = x.1 i.val := rfl

@[simp] theorem projectBlock_side (selected : I) (a : V selected)
    (x : JointOutput V B) : (projectBlock selected a x).2.2 = x.2 := rfl

theorem projectBlock_surjective (selected : I) (a : V selected) :
    Function.Surjective (projectBlock (B := B) selected a) :=
  (projectWithSide_surjective a).comp (splitOutput V B selected).surjective

def blockFiberEquiv (selected : I) (a : V selected)
    (z : Space a × (OtherBlocks V selected × B)) :
    {x : JointOutput V B // projectBlock selected a x = z} ≃
      {y : V selected × (OtherBlocks V selected × B) // projectWithSide a y = z} where
  toFun x := ⟨splitOutput V B selected x.val, x.property⟩
  invFun y := ⟨(splitOutput V B selected).symm y.val, by
    change projectWithSide a (splitOutput V B selected ((splitOutput V B selected).symm y.val)) = z
    rw [(splitOutput V B selected).apply_symm_apply]
    exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (splitOutput V B selected).symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    exact (splitOutput V B selected).apply_symm_apply y.val

theorem card_projectBlock_fiber (selected : I) (a : V selected) (ha : a ≠ 0)
    (z : Space a × (OtherBlocks V selected × B)) :
    Nat.card {x : JointOutput V B // projectBlock selected a x = z} = 2 :=
  (Nat.card_congr (blockFiberEquiv selected a z)).trans
    (card_projectWithSide_fiber a ha z)

open MixedSupport CanonicalKeys

theorem coarsenBlock_at_most_two [Finite I] [∀ i, Finite (V i)] [Finite B] {n : Nat}
    (slots : Fin n → Slot) (f : Assignment slots → JointOutput V B)
    (selected : I) (a : V selected) (ha : a ≠ 0)
    (Q : Label slots (projectBlock selected a ∘ f)) :
    Nat.card {P : Label slots f //
      CanonicalEdges.coarsen slots f (projectBlock selected a) P = Q} ≤ 2 := by
  apply CanonicalEdges.coarsen_at_most_two slots f (projectBlock selected a)
  intro z
  exact (card_projectBlock_fiber selected a ha z).le

end PerfectCompleteness.BlockQuotient

end

section

namespace UniqueGamesTheorem.Integration.CutoffBudget

open scoped BigOperators

noncomputable def cutoffSum (r : Nat) (ρ : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (r + 1),
    if d = 0 then ρ else (2 : ℝ) ^ (30 * d * d) * ρ ^ ((1 : ℝ) / 4)

theorem cutoffSum_le (r : Nat) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    cutoffSum r ρ ≤
      (r + 1 : ℝ) * (2 : ℝ) ^ (30 * r * r) * ρ ^ ((1 : ℝ) / 4) := by
  have hroot : 0 ≤ ρ ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hρ.le _
  have hrho : ρ ≤ ρ ^ ((1 : ℝ) / 4) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hρ hρ1
        (by norm_num : (1 : ℝ) / 4 ≤ 1))
  have hone : (1 : ℝ) ≤ 2 ^ (30 * r * r) := one_le_pow₀ (by norm_num)
  calc
    cutoffSum r ρ ≤ ∑ _d ∈ Finset.range (r + 1),
        (2 : ℝ) ^ (30 * r * r) * ρ ^ ((1 : ℝ) / 4) := by
      unfold cutoffSum
      apply Finset.sum_le_sum
      intro d hd
      have hdr : d ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
      split_ifs
      · exact hrho.trans (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hone hroot)
      · apply mul_le_mul_of_nonneg_right _ hroot
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 30 hdr) hdr
    _ = _ := by simp [mul_assoc]

theorem rho_real_bounds {r s : Nat} (hs : r + 1 < s) :
    0 < (FinalParameters.rho r s : ℝ) ∧ (FinalParameters.rho r s : ℝ) < 1 := by
  constructor
  · exact_mod_cast FinalParameters.rho_pos r s
  · have hq : FinalParameters.rho r s < 1 := by
      unfold FinalParameters.rho
      exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    exact_mod_cast hq

theorem cutoffSum_le_budget {r s : Nat} {δ : ℚ} (hs : r + 1 < s)
    (hbudget : (FinalParameters.levelConstant r : ℝ) *
      (FinalParameters.rho r s : ℝ) ^ ((1 : ℝ) / 4) ≤ (δ : ℝ) / 8) :
    cutoffSum r (FinalParameters.rho r s : ℝ) ≤ (δ : ℝ) / 8 := by
  have hρ := rho_real_bounds hs
  apply (cutoffSum_le r hρ.1 hρ.2.le).trans
  simpa [FinalParameters.levelConstant, pow_two, mul_assoc] using hbudget

theorem exists_symbol_dimension_cutoff (r : Nat) {δ : ℚ} (hδ : 0 < δ) :
    ∃ s : Nat, r + 1 < s ∧
      cutoffSum r (FinalParameters.rho r s : ℝ) ≤ (δ : ℝ) / 8 := by
  obtain ⟨s, hs, hbudget⟩ := RealBounds.exists_symbol_dimension_real r hδ
  exact ⟨s, hs, cutoffSum_le_budget hs hbudget⟩

end UniqueGamesTheorem.Integration.CutoffBudget

end

end OAI
