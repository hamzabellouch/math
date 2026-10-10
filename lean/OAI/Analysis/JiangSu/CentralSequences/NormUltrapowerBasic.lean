import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI


noncomputable section
open scoped ENNReal Topology
open Filter Metric

namespace NormUltra
variable (A : ℕ → Type*) [∀ n, NonUnitalCStarAlgebra (A n)]
abbrev BoundedFamilies := lp A ∞
namespace BoundedFamilies
variable {A} {U : Ultrafilter ℕ}
lemma norm_coordinate_le (x : BoundedFamilies A) (n : ℕ) : ‖x n‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by simp) x n

def vanishing (U : Ultrafilter ℕ) : Submodule ℂ (BoundedFamilies A) where
  carrier := {x | Tendsto (fun n => ‖x n‖) (U : Filter ℕ) (𝓝 0)}
  zero_mem' := by simp
  add_mem' hx hy := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_add_le _ _)
    simpa using hx.add hy
  smul_mem' c x hx := by
    change Tendsto (fun n => ‖c • x n‖) (U : Filter ℕ) (𝓝 0)
    simpa only [norm_smul, mul_zero] using (tendsto_const_nhds (x := ‖c‖)).mul hx

@[simp] lemma mem_vanishing (x : BoundedFamilies A) : x ∈ vanishing (A := A) U ↔
    Tendsto (fun n => ‖x n‖) (U : Filter ℕ) (𝓝 0) := Iff.rfl

lemma mul_mem_vanishing_left (x : BoundedFamilies A) {y : BoundedFamilies A}
    (hy : y ∈ vanishing (A := A) U) : x*y ∈ vanishing (A := A) U := by
  rw [mem_vanishing]
  have h : Tendsto (fun n => ‖x‖*‖y n‖) (U : Filter ℕ) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ‖x‖)).mul hy
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h
  exact (norm_mul_le (x n) (y n)).trans
    (mul_le_mul_of_nonneg_right (norm_coordinate_le x n) (norm_nonneg _))

lemma mul_mem_vanishing_right {x : BoundedFamilies A} (hx : x ∈ vanishing (A := A) U)
    (y : BoundedFamilies A) : x*y ∈ vanishing (A := A) U := by
  rw [mem_vanishing]
  have h : Tendsto (fun n => ‖x n‖*‖y‖) (U : Filter ℕ) (𝓝 0) := by
    simpa using hx.mul (tendsto_const_nhds (x := ‖y‖))
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h
  exact (norm_mul_le (x n) (y n)).trans
    (mul_le_mul_of_nonneg_left (norm_coordinate_le y n) (norm_nonneg _))

lemma star_mem_vanishing {x : BoundedFamilies A} (hx : x ∈ vanishing (A := A) U) : star x ∈ vanishing (A := A) U := by
  change Tendsto (fun n => ‖star (x n)‖) (U : Filter ℕ) (𝓝 0)
  simpa only [norm_star] using (mem_vanishing x).mp hx

instance vanishing_closed : IsClosed (vanishing (A := A) U : Set (BoundedFamilies A)) := by
  apply isClosed_of_closure_subset
  intro x hx
  change Tendsto (fun n => ‖x n‖) (U : Filter ℕ) (𝓝 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε/2) (by linarith)
  have hN := Metric.tendsto_nhds.mp hy (ε/2) (by linarith)
  filter_upwards [hN] with n hn
  have hdiff : ‖x n-y n‖ < ε/2 := by
    have h := norm_coordinate_le (x-y) n
    exact h.trans_lt (by simpa only [dist_eq_norm] using hxy)
  have htail : ‖y n‖ < ε/2 := by simpa using hn
  rw [dist_zero_right, norm_norm]
  exact (norm_le_norm_sub_add (x n) (y n)).trans_lt
    (by simpa only [add_halves] using add_lt_add hdiff htail)

def vanishingCon (U : Ultrafilter ℕ) : RingCon (BoundedFamilies A) where
  toSetoid := (vanishing (A := A) U).quotientRel
  add' := by
    intro x y u v hxy huv
    rw [Submodule.quotientRel_def] at hxy huv ⊢
    convert (vanishing (A := A) U).add_mem hxy huv using 1
    abel
  mul' := by
    intro x y u v hxy huv
    rw [Submodule.quotientRel_def] at hxy huv ⊢
    have h := (vanishing (A := A) U).add_mem (mul_mem_vanishing_right hxy u)
      (mul_mem_vanishing_left y huv)
    convert h using 1
    noncomm_ring
end BoundedFamilies
end NormUltra

namespace NormUltra
variable (A : ℕ → Type*) [∀ n, NonUnitalCStarAlgebra (A n)]

def QuotientAlgebra (U : Ultrafilter ℕ) := (BoundedFamilies.vanishingCon (A := A) U).Quotient
namespace QuotientAlgebra
open BoundedFamilies

variable {A} {U : Ultrafilter ℕ}
instance : NonUnitalRing (QuotientAlgebra A U) :=
  inferInstanceAs (NonUnitalRing (vanishingCon (A := A) U).Quotient)
instance : NormedAddCommGroup (QuotientAlgebra A U) :=
  inferInstanceAs (NormedAddCommGroup (BoundedFamilies A ⧸ vanishing (A := A) U))
instance : Module ℂ (QuotientAlgebra A U) :=
  inferInstanceAs (Module ℂ (BoundedFamilies A ⧸ vanishing (A := A) U))
instance : NormedSpace ℂ (QuotientAlgebra A U) :=
  inferInstanceAs (NormedSpace ℂ (BoundedFamilies A ⧸ vanishing (A := A) U))
instance : CompleteSpace (QuotientAlgebra A U) :=
  inferInstanceAs (CompleteSpace (BoundedFamilies A ⧸ vanishing (A := A) U))

def mk (U : Ultrafilter ℕ) (x : BoundedFamilies A) : QuotientAlgebra A U := Submodule.Quotient.mk x
@[simp] lemma mk_add (x y : BoundedFamilies A) : mk U (x+y) = mk U x+mk U y := rfl
@[simp] lemma mk_mul (x y : BoundedFamilies A) : mk U (x*y) = mk U x*mk U y := rfl
@[simp] lemma mk_sub (x y : BoundedFamilies A) : mk U (x-y) = mk U x-mk U y := rfl
@[simp] lemma mk_smul (c : ℂ) (x : BoundedFamilies A) : mk U (c • x) = c • mk U x := rfl
@[simp] lemma mk_zero : mk U (0 : BoundedFamilies A) = 0 := rfl
lemma mk_surjective : Function.Surjective (mk (A := A) U) := Quotient.mk_surjective
lemma mk_eq_mk_iff (x y : BoundedFamilies A) : mk U x = mk U y ↔ x-y ∈ vanishing (A := A) U :=
  Submodule.Quotient.eq _
lemma norm_mk_le (x : BoundedFamilies A) : ‖mk U x‖ ≤ ‖x‖ := Submodule.Quotient.norm_mk_le _ _
lemma exists_norm_mk_lt (x : QuotientAlgebra A U) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : BoundedFamilies A, mk U a = x ∧ ‖a‖ < ‖x‖+ε := Submodule.Quotient.norm_mk_lt x hε

instance : NonUnitalNormedRing (QuotientAlgebra A U) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have h := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at h
    obtain ⟨ε₁, ε₂, ⟨h₁,h₂⟩, h⟩ := h
    obtain ⟨a, rfl, ha⟩ := exists_norm_mk_lt x h₁
    obtain ⟨b, rfl, hb⟩ := exists_norm_mk_lt y h₂
    simp only [Real.dist_eq, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [norm_mk_le (U := U) a]⟩
      ⟨by linarith, by linarith [norm_mk_le (U := U) b]⟩
    exact ((norm_mk_le (U := U) (a*b)).trans (norm_mul_le a b)).trans (sub_lt_iff_lt_add'.mp h.1).le

instance : Star (QuotientAlgebra A U) := ⟨Quotient.map' star (by
  intro x y h
  change (vanishing (A := A) U).quotientRel x y at h
  change (vanishing (A := A) U).quotientRel (star x) (star y)
  rw [Submodule.quotientRel_def] at h ⊢
  simpa only [star_sub] using star_mem_vanishing h)⟩
@[simp] lemma mk_star (x : BoundedFamilies A) : mk U (star x) = star (mk U x) := rfl
instance : StarRing (QuotientAlgebra A U) where
  star_involutive := by
    intro x
    obtain ⟨x,rfl⟩ := mk_surjective x
    exact congrArg (mk U) (star_star x)
  star_mul := by
    intro x y
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    exact congrArg (mk U) (star_mul x y)
  star_add := by
    intro x y
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    exact congrArg (mk U) (star_add x y)
instance : StarModule ℂ (QuotientAlgebra A U) where
  star_smul := by
    intro c x
    obtain ⟨x,rfl⟩ := mk_surjective x
    exact congrArg (mk U) (star_smul c x)
instance : IsScalarTower ℂ (QuotientAlgebra A U) (QuotientAlgebra A U) where
  smul_assoc := by
    intro c x y
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    exact congrArg (mk U) (smul_mul_assoc c x y)
instance : SMulCommClass ℂ (QuotientAlgebra A U) (QuotientAlgebra A U) where
  smul_comm := by
    intro c x y
    obtain ⟨x,rfl⟩ := mk_surjective x
    obtain ⟨y,rfl⟩ := mk_surjective y
    exact congrArg (mk U) (smul_comm c x y)
end QuotientAlgebra
end NormUltra

end


noncomputable section
open scoped ENNReal Topology
open Filter

namespace NormUltra
variable {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)] {U : Ultrafilter ℕ}
namespace BoundedFamilies
lemma norm_bounded (U : Ultrafilter ℕ) (x : BoundedFamilies A) :
    IsBoundedUnder (· ≤ ·) (U : Filter ℕ) (fun n => ‖x n‖) :=
  isBoundedUnder_of ⟨‖x‖, norm_coordinate_le x⟩
lemma norm_cobounded (U : Ultrafilter ℕ) (x : BoundedFamilies A) :
    IsCoboundedUnder (· ≤ ·) (U : Filter ℕ) (fun n => ‖x n‖) :=
  (isBoundedUnder_of ⟨0, fun n => norm_nonneg (x n)⟩ :
    IsBoundedUnder (· ≥ ·) (U : Filter ℕ) (fun n => ‖x n‖)).isCoboundedUnder_le
lemma limsup_norm_nonneg (U : Ultrafilter ℕ) (x : BoundedFamilies A) :
    0 ≤ limsup (fun n => ‖x n‖) (U : Filter ℕ) :=
  le_limsup_of_frequently_le (Eventually.of_forall (fun n => norm_nonneg (x n))).frequently (norm_bounded U x)

lemma limsup_norm_le_of_vanishing_sub (x y : BoundedFamilies A)
    (h : x-y ∈ vanishing (A := A) U) : limsup (fun n => ‖x n‖) (U : Filter ℕ) ≤ ‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le (norm_cobounded U x)
  have he : ∀ᶠ n in (U : Filter ℕ), ‖x n-y n‖ < ε := by
    have h0' : Tendsto (fun n => ‖x n-y n‖) (U : Filter ℕ) (𝓝 0) := h
    exact (tendsto_order.mp h0').2 ε hε
  filter_upwards [he] with n hn
  have ht := norm_le_norm_sub_add (x n) (y n)
  have hy := norm_coordinate_le y n
  linarith

def mask (x : BoundedFamilies A) (S : Set ℕ) : BoundedFamilies A := by
  classical
  exact ⟨fun n => if n ∈ S then x n else 0, memℓp_infty ⟨‖x‖, by
    rintro _ ⟨n,rfl⟩
    change ‖if n ∈ S then x n else 0‖ ≤ ‖x‖
    split_ifs
    · exact norm_coordinate_le x n
    · simpa only [norm_zero] using norm_nonneg x⟩⟩
lemma mask_sub_mem (x : BoundedFamilies A) (S : Set ℕ) (hS : S ∈ U) :
    mask x S-x ∈ vanishing (A := A) U := by
  change Tendsto (fun n => ‖(mask x S) n-x n‖) (U : Filter ℕ) (𝓝 0)
  apply (tendsto_congr' (show (fun n => ‖(mask x S) n-x n‖) =ᶠ[(U : Filter ℕ)] fun _ => (0 : ℝ) from ?_)).mpr
    tendsto_const_nhds
  filter_upwards [hS] with n hn
  simp [mask, hn]
lemma norm_mask_le (x : BoundedFamilies A) (S : Set ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n ∈ S, ‖x n‖ ≤ C) : ‖mask x S‖ ≤ C := by
  classical
  apply lp.norm_le_of_forall_le hC
  intro n
  change ‖if n ∈ S then x n else 0‖ ≤ C
  split_ifs with hn
  · exact h n hn
  · simpa using hC
end BoundedFamilies
namespace QuotientAlgebra
open BoundedFamilies

theorem norm_mk_eq_limsup (x : BoundedFamilies A) :
    ‖mk U x‖ = limsup (fun n => ‖x n‖) (U : Filter ℕ) := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hE := eventually_lt_of_limsup_lt
      (lt_add_of_pos_right (limsup (fun n => ‖x n‖) (U : Filter ℕ)) hε) (norm_bounded U x)
    let S := {n | ‖x n‖ < limsup (fun n => ‖x n‖) (U : Filter ℕ)+ε}
    have hS : S ∈ U := hE
    have heq : mk U (mask x S) = mk U x := (mk_eq_mk_iff _ _).mpr (mask_sub_mem x S hS)
    rw [←heq]
    exact (norm_mk_le (U := U) _).trans (norm_mask_le x S _ (by linarith [limsup_norm_nonneg U x])
      (fun n hn => hn.le))
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨y,hy,hn⟩ := exists_norm_mk_lt (mk U x) hε
    have hxy : x-y ∈ vanishing (A := A) U := (mk_eq_mk_iff _ _).mp hy.symm
    exact (limsup_norm_le_of_vanishing_sub x y hxy).trans hn.le

lemma norm_star_mul_self_eq (x : QuotientAlgebra A U) : ‖star x*x‖ = ‖x‖*‖x‖ := by
  obtain ⟨x,rfl⟩ := mk_surjective x
  rw [←mk_star,←mk_mul,norm_mk_eq_limsup,norm_mk_eq_limsup]
  let f : ℝ → ℝ := fun t => max t 0 * max t 0
  have hf : Monotone f := by
    intro a b hab
    exact mul_self_le_mul_self (le_max_right _ _) (max_le_max hab le_rfl)
  have hc : Continuous f := (continuous_id.max continuous_const).mul (continuous_id.max continuous_const)
  have h := hf.map_limsup_of_continuousAt (fun n => ‖x n‖) hc.continuousAt
    (norm_bounded U x) (norm_cobounded U x)
  have he : f ∘ (fun n => ‖x n‖) = fun n => ‖star (x n)*x n‖ := by
    funext n
    simp only [Function.comp_apply, f, max_eq_left (norm_nonneg (x n)), CStarRing.norm_star_mul_self]
  rw [he] at h
  dsimp [f] at h
  rw [max_eq_left (limsup_norm_nonneg U x)] at h
  exact h.symm

instance : CStarRing (QuotientAlgebra A U) where
  norm_mul_self_le x := (norm_star_mul_self_eq x).symm.le
instance : NonUnitalCStarAlgebra (QuotientAlgebra A U) where

def mkHom : BoundedFamilies A →⋆ₙₐ[ℂ] QuotientAlgebra A U where
  toFun := mk U
  map_zero' := rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  map_star' := fun _ => rfl
end QuotientAlgebra
end NormUltra

end

end OAI
