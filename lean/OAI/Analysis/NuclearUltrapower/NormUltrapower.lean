import OAI.Analysis.NuclearUltrapower.Model
import OAI.Analysis.NuclearUltrapower.TensorGap
import OAI.Analysis.NuclearUltrapower.VariableUltraproduct

namespace OAI

section

universe u

noncomputable section
open Filter
open scoped Topology

namespace NuclearUltrapower
variable {A : Type*} [CStarAlgebra A]

/-- Both-sided approximate-unitarity is essential: no stable-finiteness or
Dedekind-finiteness is assumed for the ambient C*-algebra. -/
theorem isUnit_of_star_products {a : A} (hl : IsUnit (star a * a))
    (hr : IsUnit (a * star a)) : IsUnit a := by
  let l := Ring.inverse (star a * a) * star a
  let r := star a * Ring.inverse (a * star a)
  have hla : l * a = 1 := by
    dsimp [l]
    rw [mul_assoc, Ring.inverse_mul_cancel _ hl]
  have har : a * r = 1 := by
    dsimp [r]
    rw [← mul_assoc, Ring.mul_inverse_cancel _ hr]
  have he : l = r := by
    calc l = l * (a * r) := by rw [har, mul_one]
         _ = (l * a) * r := (mul_assoc _ _ _).symm
         _ = r := by rw [hla, one_mul]
  exact ⟨⟨a, r, har, he ▸ hla⟩, rfl⟩

local instance polarSpectralOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance polarSpectralOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- The polar retraction on the open set of invertible elements. -/
def polarUnitary (a : A) (ha : IsUnit a) : unitary A := by
  let q := CFC.sqrt (star a * a)
  have hq : IsUnit q := (CFC.isUnit_sqrt_iff _ (star_mul_self_nonneg a)).mpr
    (ha.star.mul ha)
  have hqi : IsUnit (Ring.inverse q) := by
    rw [← hq.unit_spec, Ring.inverse_unit]
    exact Units.isUnit _
  refine ⟨a * Ring.inverse q, ((ha.mul hqi).mem_unitary_iff_star_mul_self).mpr ?_⟩
  have hqstar : star q = q := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have hi : star (Ring.inverse q) = Ring.inverse q := by
    rw [← Ring.inverse_star, hqstar]
  rw [star_mul, hi]
  calc
    (Ring.inverse q * star a) * (a * Ring.inverse q) =
      Ring.inverse q * (star a * a) * Ring.inverse q := by simp only [mul_assoc]
    _ = Ring.inverse q * (q * q) * Ring.inverse q := by
      rw [show q * q = star a * a from CFC.sqrt_mul_sqrt_self _]
    _ = 1 := by
      rw [← mul_assoc (Ring.inverse q) q q, Ring.inverse_mul_cancel _ hq,
        one_mul, Ring.mul_inverse_cancel _ hq]

@[simp] theorem polarUnitary_value (a : A) (ha : IsUnit a) :
    (polarUnitary a ha : A) = a * Ring.inverse (CFC.sqrt (star a * a)) := rfl

/-- A unitary-valued extension of polar retraction. Away from invertibles it
is set equal to 1. -/
def unitaryReplacement (a : A) : unitary A := by
  classical
  exact if h : IsUnit a then polarUnitary a h else 1

/-- Asymptotically unitary bounded families admit genuine unitary replacements
with norm-null difference along any filter. -/
theorem unitaryReplacement_tendsto {ι : Type*} {l : Filter ι} (a : ι → A)
    (hb : IsBoundedUnder (· ≤ ·) l (fun i => ‖a i‖))
    (hl : Tendsto (fun i => star (a i) * a i) l (𝓝 1))
    (hr : Tendsto (fun i => a i * star (a i)) l (𝓝 1)) :
    Tendsto (fun i => (unitaryReplacement (a i) : A) - a i) l (𝓝 0) := by
  have hles : ∀ᶠ i in l, IsUnit (star (a i) * a i) :=
    hl.eventually (Units.isOpen.mem_nhds isUnit_one)
  have hres : ∀ᶠ i in l, IsUnit (a i * star (a i)) :=
    hr.eventually (Units.isOpen.mem_nhds isUnit_one)
  have hunit : ∀ᶠ i in l, IsUnit (a i) :=
    (hles.and hres).mono (fun _ h => isUnit_of_star_products h.1 h.2)
  have hsqrt : Tendsto (fun i => CFC.sqrt (star (a i) * a i)) l (𝓝 (1 : A)) := by
    have h := (CFC.continuousOn_sqrt (A := A) 1 (by change (0 : A) ≤ 1; exact zero_le_one)).tendsto
    have hc := h.comp (tendsto_nhdsWithin_iff.mpr ⟨hl,
      Filter.Eventually.of_forall (fun i => star_mul_self_nonneg (a i))⟩)
    simpa only [Function.comp_def, CFC.sqrt_one] using hc
  have hinv : Tendsto (fun i => Ring.inverse (CFC.sqrt (star (a i) * a i))) l (𝓝 (1 : A)) := by
    have h := (NormedRing.inverse_continuousAt (1 : Aˣ)).tendsto.comp hsqrt
    simpa only [Function.comp_def, Units.val_one, Ring.inverse_one] using h
  have hz : Tendsto (fun i => Ring.inverse (CFC.sqrt (star (a i) * a i)) - 1) l (𝓝 (0 : A)) := by
    simpa using hinv.sub_const 1
  have hp := Filter.isBoundedUnder_le_mul_tendsto_zero hb hz
  apply hp.congr'
  filter_upwards [hunit] with i hi
  simp [unitaryReplacement, hi, mul_sub]

end NuclearUltrapower

namespace NuclearUltrapower
section UltrapowerDefinition
variable (B : Type u) [CStarAlgebra B] (ω : Ultrafilter ℕ)

theorem ultraRel_iff_norm (x y : BoundedSeq B) :
    ultraRel B ω x y ↔
      Tendsto (fun n => ‖x n - y n‖) (ω : Filter ℕ) (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero

theorem seq_bounded (x : BoundedSeq B) :
    IsBoundedUnder (· ≤ ·) (ω : Filter ℕ) (norm ∘ x) :=
  Filter.isBoundedUnder_of ⟨‖x‖, fun n => x.norm_coe_le_norm n⟩

theorem ultraRel_star {x y : BoundedSeq B} (h : ultraRel B ω x y) :
    ultraRel B ω (star x) (star y) := by
  simpa only [ultraRel, star_sub, star_zero, BoundedContinuousFunction.star_apply] using h.star

/-- The canonical quotient map, preserving the unit and the complex star algebra. -/
def normUltrapowerMk : BoundedSeq B →⋆ₐ[ℂ] NormUltrapower B ω where
  __ := (ultraCon B ω).mkₐ ℂ
  map_star' _ := rfl

end UltrapowerDefinition
end NuclearUltrapower

namespace NuclearUltrapower
variable {B : Type*} [CStarAlgebra B] [Nontrivial B] (ω : Ultrafilter ℕ)

/-- Every unitary sequence is bounded by one. -/
def boundedUnitarySeq (u : ℕ → unitary B) : BoundedSeq B :=
  BoundedContinuousFunction.mkOfDiscrete (fun n => (u n : B)) 2 (by
    intro n m
    calc dist (u n : B) (u m : B) ≤ ‖(u n : B)‖ + ‖(u m : B)‖ := dist_le_norm_add_norm _ _
         _ = 2 := by rw [CStarRing.norm_coe_unitary, CStarRing.norm_coe_unitary]; norm_num)

@[simp] theorem boundedUnitarySeq_apply (u : ℕ → unitary B) (n : ℕ) :
    boundedUnitarySeq u n = (u n : B) := rfl

omit [Nontrivial B] in
theorem normUltrapowerMk_eq_iff (x y : BoundedSeq B) :
    normUltrapowerMk B ω x = normUltrapowerMk B ω y ↔ ultraRel B ω x y :=
  Quotient.eq

omit [Nontrivial B] in
/-- The defining quotient map is surjective, with no assumed model of the quotient. -/
theorem normUltrapowerMk_surjective : Function.Surjective (normUltrapowerMk B ω) :=
  Quotient.mk_surjective

/-- 24--36, with both left and right
unitarity used. The result requires neither stable finiteness nor separability. -/
theorem unitary_lift (u : unitary (NormUltrapower B ω)) :
    ∃ x : ℕ → unitary B, normUltrapowerMk B ω (boundedUnitarySeq x) = (u : NormUltrapower B ω) := by
  obtain ⟨y, hy⟩ := normUltrapowerMk_surjective (B := B) ω u
  have hlq : normUltrapowerMk B ω (star y * y) = normUltrapowerMk B ω 1 := by
    rw [map_mul, map_star, hy, Unitary.star_mul_self_of_mem u.property, map_one]
  have hrq : normUltrapowerMk B ω (y * star y) = normUltrapowerMk B ω 1 := by
    rw [map_mul, map_star, hy, Unitary.mul_star_self_of_mem u.property, map_one]
  have hl : Tendsto (fun n => star (y n) * y n) (ω : Filter ℕ) (𝓝 1) := by
    have hh := (normUltrapowerMk_eq_iff ω _ _).mp hlq
    exact tendsto_sub_nhds_zero_iff.mp hh
  have hr : Tendsto (fun n => y n * star (y n)) (ω : Filter ℕ) (𝓝 1) := by
    have hh := (normUltrapowerMk_eq_iff ω _ _).mp hrq
    exact tendsto_sub_nhds_zero_iff.mp hh
  refine ⟨fun n => unitaryReplacement (y n), ?_⟩
  rw [← hy, normUltrapowerMk_eq_iff]
  exact unitaryReplacement_tendsto y (seq_bounded B ω y) hl hr

/-- Coordinatewise lifts preserve each fixed multiplicative relation in the
norm ultralimit. No simultaneous coordinate relations or countable intersection
of large sets are asserted. -/
theorem unitary_lift_defects {Γ : Type*} [Group Γ]
    (ρ : Γ →* unitary (NormUltrapower B ω)) (x : Γ → ℕ → unitary B)
    (hx : ∀ g, normUltrapowerMk B ω (boundedUnitarySeq (x g)) = (ρ g : NormUltrapower B ω))
    (g h : Γ) :
    Tendsto (fun n => (x g n : B) * (x h n : B) - (x (g * h) n : B))
      (ω : Filter ℕ) (𝓝 0) := by
  have he : normUltrapowerMk B ω (boundedUnitarySeq (x g) * boundedUnitarySeq (x h)) =
      normUltrapowerMk B ω (boundedUnitarySeq (x (g * h))) := by
    rw [map_mul, hx, hx, hx, map_mul, Submonoid.coe_mul]
  exact (normUltrapowerMk_eq_iff ω _ _).mp he

/-- Choice of unitary lifts, normalized at the group identity. -/
theorem exists_unitary_lifts {Γ : Type*} [Group Γ]
    (ρ : Γ →* unitary (NormUltrapower B ω)) :
    ∃ x : Γ → ℕ → unitary B, (∀ n, x 1 n = 1) ∧
      (∀ g, normUltrapowerMk B ω (boundedUnitarySeq (x g)) = (ρ g : NormUltrapower B ω)) ∧
      ∀ g h, Tendsto (fun n => (x g n : B) * (x h n : B) - (x (g * h) n : B))
        (ω : Filter ℕ) (𝓝 0) := by
  classical
  choose y hy using (fun g => unitary_lift ω (ρ g))
  let x : Γ → ℕ → unitary B := fun g => if g = 1 then fun _ => 1 else y g
  have hx : ∀ g, normUltrapowerMk B ω (boundedUnitarySeq (x g)) = (ρ g : NormUltrapower B ω) := by
    intro g
    by_cases hg : g = 1
    · subst g
      have he : boundedUnitarySeq (x 1) = (1 : BoundedSeq B) := by ext n; simp [x]
      rw [he, map_one, map_one, Submonoid.coe_one]
    · simpa [x, hg] using hy g
  exact ⟨x, fun n => by simp [x], hx, fun g h => unitary_lift_defects ω ρ x hx g h⟩

end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology ENNReal
namespace NuclearUltrapower
universe u
variable (B : Type u) [CStarAlgebra B] [Nontrivial B] (ω : Ultrafilter ℕ)

/-- The two standard bounded-sequence presentations agree coordinatewise. -/
def boundedSeqToLp : BoundedSeq B →⋆ₐ[ℂ] VariableUltra.Seq (fun _ : ℕ => B) where
  toFun x := ⟨(fun n => x n), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨n,rfl⟩
    exact x.norm_coe_le_norm n⟩⟩
  map_zero' := by ext n; rfl
  map_add' _ _ := by ext n; rfl
  map_one' := by ext n; rfl
  map_mul' _ _ := by ext n; rfl
  map_star' _ := by ext n; rfl
  commutes' _ := by ext n; rfl

@[simp] theorem boundedSeqToLp_apply (x : BoundedSeq B) (n : ℕ) :
    boundedSeqToLp B x n = x n := rfl

/-- Endow the norm-null ring quotient with its canonical C*-model,
without replacing the norm-null ideal by any algebraic relation. -/
def normUltraToCStar : NormUltrapower B ω →⋆ₐ[ℂ] VariableUltra.Algebra (fun _ : ℕ => B) ω where
  toFun := Quotient.map (boundedSeqToLp B) (by
    intro x y h
    exact (ultraRel_iff_norm B ω x y).mp h)
  map_zero' := rfl
  map_add' x y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y => rfl
  map_one' := rfl
  map_mul' x y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y => rfl
  map_star' x := by
    induction x using Quotient.inductionOn with | h x => rfl
  commutes' _ := rfl

@[simp] theorem normUltraToCStar_mk (x : BoundedSeq B) :
    normUltraToCStar B ω (normUltrapowerMk B ω x) =
      VariableUltra.mk (fun _ : ℕ => B) ω (boundedSeqToLp B x) := rfl

theorem normUltraToCStar_injective : Function.Injective (normUltraToCStar B ω) := by
  intro x y h
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((ultraRel_iff_norm B ω x y).mpr (Quotient.exact h))

@[simp] theorem boundedSeqToLp_unitary (u : ℕ → unitary B) :
    boundedSeqToLp B (boundedUnitarySeq u) = VariableUltra.unitarySequence (fun _ : ℕ => B) u := by
  ext n
  rfl

end NuclearUltrapower
end
end

end OAI
