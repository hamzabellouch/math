import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.FiniteDrop

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]


open Filter Topology BoundedContinuousFunction

universe uQuot

namespace KirchbergRordam
namespace NormUltrapower

variable {A : Type*} [CStarAlgebra A]


theorem exists_norm_limit (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
  obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
    (Ultrafilter.map (fun n => ‖x n‖) ω) (by
      change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
      exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
  exact ⟨r, hr, h⟩


theorem normLimit_nonneg (ω : Ultrafilter ℕ) (x : BoundedSeq A) : 0 ≤ normLimit ω x :=
  (exists_norm_limit ω x).choose_spec.1.1

theorem normLimit_le (ω : Ultrafilter ℕ) (x : BoundedSeq A) : normLimit ω x ≤ ‖x‖ :=
  (exists_norm_limit ω x).choose_spec.1.2

theorem tendsto_norm (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 (normLimit ω x)) :=
  (exists_norm_limit ω x).choose_spec.2

@[simp]
theorem normLimit_zero (ω : Ultrafilter ℕ) : normLimit ω (0 : BoundedSeq A) = 0 := by
  apply tendsto_nhds_unique (tendsto_norm ω 0)
  simp

@[simp]
theorem normLimit_neg (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    normLimit ω (-x) = normLimit ω x := by
  apply tendsto_nhds_unique (tendsto_norm ω (-x))
  simpa using tendsto_norm ω x

theorem normLimit_add_le (ω : Ultrafilter ℕ) (x y : BoundedSeq A) :
    normLimit ω (x + y) ≤ normLimit ω x + normLimit ω y := by
  exact le_of_tendsto_of_tendsto (tendsto_norm ω (x+y))
    ((tendsto_norm ω x).add (tendsto_norm ω y))
    (Eventually.of_forall fun n => norm_add_le (x n) (y n))

theorem normLimit_mul_le (ω : Ultrafilter ℕ) (x y : BoundedSeq A) :
    normLimit ω (x * y) ≤ normLimit ω x * normLimit ω y := by
  exact le_of_tendsto_of_tendsto (tendsto_norm ω (x*y))
    ((tendsto_norm ω x).mul (tendsto_norm ω y))
    (Eventually.of_forall fun n => norm_mul_le (x n) (y n))

@[simp]
theorem normLimit_star (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    normLimit ω (star x) = normLimit ω x := by
  apply tendsto_nhds_unique (tendsto_norm ω (star x))
  simpa using tendsto_norm ω x

theorem normLimit_star_mul (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    normLimit ω (star x * x) = normLimit ω x * normLimit ω x := by
  apply tendsto_nhds_unique (tendsto_norm ω (star x * x))
  simpa only [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.star_apply,
    CStarRing.norm_star_mul_self] using (tendsto_norm ω x).mul (tendsto_norm ω x)

theorem normLimit_sub_le (ω : Ultrafilter ℕ) (x y : BoundedSeq A) :
    normLimit ω x - normLimit ω y ≤ normLimit ω (x-y) := by
  have h := normLimit_add_le ω (x-y) y
  rw [sub_add_cancel] at h
  linarith

theorem normLimit_lipschitz (ω : Ultrafilter ℕ) :
    LipschitzWith 1 (normLimit ω : BoundedSeq A → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_le, dist_eq_norm]
  constructor
  · have h := (normLimit_sub_le ω y x).trans (normLimit_le ω (y-x))
    rw [norm_sub_rev] at h
    linarith
  · exact (normLimit_sub_le ω x y).trans (normLimit_le ω (x-y))


@[simp]
theorem mem_nullIdeal (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    x ∈ nullIdeal ω ↔ Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 0) := by
  change normLimit ω x = 0 ↔ _
  constructor
  · intro h
    simpa only [h] using tendsto_norm ω x
  · exact fun h => tendsto_nhds_unique (tendsto_norm ω x) h


@[simp]
theorem star_mk (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    star (Ideal.Quotient.mk (nullIdeal ω) x) = Ideal.Quotient.mk (nullIdeal ω) (star x) := rfl


theorem normLimit_eq_of_sub_mem (ω : Ultrafilter ℕ) {x y : BoundedSeq A}
    (h : x-y ∈ nullIdeal ω) : normLimit ω x = normLimit ω y := by
  change normLimit ω (x-y) = 0 at h
  apply le_antisymm
  · have h' := normLimit_sub_le ω x y
    linarith
  · have h' := normLimit_sub_le ω y x
    rw [← neg_sub x y, normLimit_neg, h] at h'
    linarith


theorem normLimit_le_quotient (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    normLimit ω x ≤ ‖Ideal.Quotient.mk (nullIdeal ω) x‖ := by
  apply QuotientAddGroup.le_norm_iff.mpr
  intro y hy
  have h : y-x ∈ nullIdeal ω := (Ideal.Quotient.eq).mp hy
  rw [← normLimit_eq_of_sub_mem ω h]
  exact normLimit_le ω y


theorem cutRepresentative_norm_le (x : BoundedSeq A) (c : ℝ) (hc : 0 ≤ c) :
    ‖cutRepresentative x c hc‖ ≤ c := by
  apply (BoundedContinuousFunction.norm_le hc).mpr
  intro n
  change ‖if ‖x n‖ < c then x n else 0‖ ≤ c
  split_ifs with h
  · exact h.le
  · simpa only [norm_zero] using hc

theorem cutRepresentative_mk_eq (ω : Ultrafilter ℕ) (x : BoundedSeq A)
    (c : ℝ) (hc : 0 ≤ c) (hlim : normLimit ω x < c) :
    Ideal.Quotient.mk (nullIdeal ω) x =
      Ideal.Quotient.mk (nullIdeal ω) (cutRepresentative x c hc) := by
  rw [Ideal.Quotient.eq, mem_nullIdeal]
  have he : ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ < c :=
    (tendsto_norm ω x).eventually (eventually_lt_nhds hlim)
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0) := tendsto_const_nhds
  apply hz.congr'
  filter_upwards [he] with n hn
  change (0 : ℝ) = ‖x n - (if ‖x n‖ < c then x n else 0)‖
  rw [ite_eq_left hn, sub_self, norm_zero]


theorem quotient_norm_le_normLimit (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    ‖Ideal.Quotient.mk (nullIdeal ω) x‖ ≤ normLimit ω x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpos : 0 ≤ normLimit ω x + ε := add_nonneg (normLimit_nonneg ω x) hε.le
  rw [cutRepresentative_mk_eq ω x (normLimit ω x + ε) hpos (lt_add_of_pos_right _ hε)]
  have hb := Submodule.Quotient.norm_mk_le (nullIdeal ω)
    (cutRepresentative x (normLimit ω x + ε) hpos)
  exact hb.trans (cutRepresentative_norm_le x (normLimit ω x + ε) hpos)


theorem norm_mk_eq (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    ‖Ideal.Quotient.mk (nullIdeal ω) x‖ = normLimit ω x :=
  le_antisymm (quotient_norm_le_normLimit ω x) (normLimit_le_quotient ω x)


theorem normLimit_const (ω : Ultrafilter ℕ) (a : A) :
    normLimit ω (constantSeq a) = ‖a‖ :=
  tendsto_nhds_unique (tendsto_norm ω (constantSeq a)) tendsto_const_nhds

@[simp]
theorem norm_diagonal (ω : Ultrafilter ℕ) (a : A) : ‖diagonal ω a‖ = ‖a‖ := by
  change ‖Ideal.Quotient.mk (nullIdeal ω) (constantSeq a)‖ = ‖a‖
  rw [norm_mk_eq, normLimit_const]

theorem diagonal_isometry (ω : Ultrafilter ℕ) : Isometry (diagonal (A := A) ω) := by
  apply Isometry.of_dist_eq
  intro a b
  rw [dist_eq_norm, ← map_sub, norm_diagonal, dist_eq_norm]

instance quotientNontrivial (ω : Ultrafilter ℕ) [Nontrivial A] : Nontrivial (Algebra A ω) :=
  (diagonal_isometry ω).injective.nontrivial


instance centralNontrivial (ω : Ultrafilter ℕ) [Nontrivial A] :
    Nontrivial (CentralAlgebra A ω) := inferInstance

theorem mem_central_iff (ω : Ultrafilter ℕ) (z : Algebra A ω) :
    z ∈ centralSubalgebra ω ↔ ∀ a : A, diagonal ω a * z = z * diagonal ω a := by
  change z ∈ StarSubalgebra.centralizer ℂ (Set.range (diagonal ω)) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a
    exact (h (diagonal ω a) ⟨a, rfl⟩).1
  · intro h x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨h a, by simpa only [map_star] using h (star a)⟩


theorem mk_mem_central_iff (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    quotientMap ω x ∈ centralSubalgebra ω ↔
      ∀ a : A, Tendsto (fun n => ‖x n * a - a * x n‖) (ω : Filter ℕ) (𝓝 0) := by
  rw [mem_central_iff]
  constructor
  · intro h a
    have he : Ideal.Quotient.mk (nullIdeal ω) (x * constantSeq a) =
        Ideal.Quotient.mk (nullIdeal ω) (constantSeq a * x) := (h a).symm
    exact (mem_nullIdeal ω _).mp (Ideal.Quotient.eq.mp he)
  · intro h a
    have he : x * constantSeq a - constantSeq a * x ∈ nullIdeal ω :=
      (mem_nullIdeal ω _).mpr (h a)
    exact (Ideal.Quotient.eq.mpr he).symm

end NormUltrapower
end KirchbergRordam
end

end OAI
