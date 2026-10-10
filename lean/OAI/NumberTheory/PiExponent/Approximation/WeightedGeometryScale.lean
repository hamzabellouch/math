import OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting
import OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.WeightedGeometryScale

theorem exists_power_scale {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i) :
    ∃ R : ℕ, 0 < R ∧ ∃ e : Fin n → ℕ,
      (∀ i, 0 < e i) ∧ ∀ i, w i * (e i : ℚ) = R := by
  obtain ⟨R,hR,e,he,heq⟩ := positive_rational_weights_common_denominator
    (fun i => (w i)⁻¹) (fun i => inv_pos.mpr (hw i))
  refine ⟨R,hR,e,he,fun i => ?_⟩
  have hi : (w i)⁻¹ = (e i : ℚ) / (R : ℚ) := by
    apply Rat.cast_injective (α := ℝ)
    simpa only [Rat.cast_inv, Rat.cast_div, Rat.cast_natCast] using heq i
  have hR' : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hwi : w i ≠ 0 := (hw i).ne'
  have hi' := (eq_div_iff hR').mp hi
  rw [← hi']
  field_simp

theorem exists_common_scale {n : ℕ} (w v : Fin n → ℚ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) :
    ∃ R : ℕ, 0 < R ∧ ∃ e t : Fin n → ℕ,
      (∀ i, 0 < e i) ∧ (∀ i, 0 < t i) ∧
      (∀ i, w i * (e i : ℚ) = R) ∧
      (∀ i, v i * (t i : ℚ) = R) := by
  obtain ⟨A,hA,e,he,heq⟩ := exists_power_scale w hw
  obtain ⟨B,hB,t,ht,htq⟩ := exists_power_scale v hv
  refine ⟨A*B,Nat.mul_pos hA hB,fun i => e i * B,fun i => t i * A,
    fun i => Nat.mul_pos (he i) hB,fun i => Nat.mul_pos (ht i) hA,?_,?_⟩
  · intro i
    push_cast
    rw [← mul_assoc, heq]
  · intro i
    push_cast
    rw [← mul_assoc, htq, mul_comm]

def monomials {n : ℕ} (w : Fin n → ℚ) (R : ℚ) : Finset (Fin n →₀ ℕ) :=
  (realWeightedSimplex (fun i => (w i : ℝ)) (R : ℝ)).image Finsupp.equivFunOnFinite.symm

@[simp] theorem mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (a : Fin n →₀ ℕ) :
    a ∈ monomials w R ↔ (∑ i, w i * (a i : ℚ)) ≤ R := by
  classical
  rw [monomials, Finset.mem_image]
  constructor
  · rintro ⟨b,hb,rfl⟩
    have h := (mem_realWeightedSimplex (fun i => by exact_mod_cast hw i)).mp hb
    exact_mod_cast h
  · intro ha
    refine ⟨fun i => a i,?_,Finsupp.equivFunOnFinite_symm_coe a⟩
    apply (mem_realWeightedSimplex (fun i => by exact_mod_cast hw i)).mpr
    exact_mod_cast ha

theorem zero_mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (hR : 0 ≤ R) : (0 : Fin n →₀ ℕ) ∈ monomials w R := by
  rw [mem_monomials w hw]
  simpa using hR

theorem pure_mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (e : Fin n → ℕ) (he : ∀ i, w i * (e i : ℚ) = R) (i : Fin n) :
    Finsupp.single i (e i) ∈ monomials w R := by
  classical
  rw [mem_monomials w hw]
  simpa [Finsupp.single_apply] using (he i).le

theorem coordinate_mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (e : Fin n → ℕ) (hepos : ∀ i, 0 < e i)
    (he : ∀ i, w i * (e i : ℚ) = R) (i : Fin n) :
    Finsupp.single i 1 ∈ monomials w R := by
  classical
  rw [mem_monomials w hw]
  have hi : (1 : ℚ) ≤ e i := by exact_mod_cast hepos i
  have h := mul_le_mul_of_nonneg_left hi (hw i).le
  simpa [Finsupp.single_apply, he] using h

theorem exists_log_cutoff {m : ℕ} (v : Fin (m+1) → ℚ) (hv0 : 0 < v 0) :
    ∃ T : Fin m → ℕ, ∀ i, v i.succ < (T i : ℚ) * v 0 := by
  have h (i : Fin m) : ∃ T : ℕ, v i.succ < (T : ℚ) * v 0 := by
    obtain ⟨T,hT⟩ := exists_nat_gt (v i.succ / v 0)
    exact ⟨T,(div_lt_iff₀ hv0).mp hT⟩
  exact Classical.axiom_of_choice h

structure Scale {n : ℕ} (w v : Fin n → ℚ) where
  radius : ℕ
  radius_pos : 0 < radius
  degreePowers : Fin n → ℕ
  jetPowers : Fin n → ℕ
  degreePowers_pos : ∀ i, 0 < degreePowers i
  jetPowers_pos : ∀ i, 0 < jetPowers i
  degreePowers_eq : ∀ i, w i * (degreePowers i : ℚ) = radius
  jetPowers_eq : ∀ i, v i * (jetPowers i : ℚ) = radius

def chooseScale {n : ℕ} (w v : Fin n → ℚ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) : Scale w v := by
  apply Classical.choice
  obtain ⟨R,hR,e,t,he,ht,heq,htq⟩ := exists_common_scale w v hw hv
  exact ⟨⟨R,hR,e,t,he,ht,heq,htq⟩⟩

namespace Scale
variable {n : ℕ} {w v : Fin n → ℚ} (s : Scale w v)

abbrev Index := ↥(monomials w s.radius)

def exponents (i : s.Index) : Fin n →₀ ℕ := i.val

def constantIndex (hw : ∀ i, 0 < w i) : s.Index :=
  ⟨0,zero_mem_monomials w hw s.radius (by exact_mod_cast s.radius_pos.le)⟩

def coordinateIndex (hw : ∀ i, 0 < w i) (i : Fin n) : s.Index :=
  ⟨Finsupp.single i 1,coordinate_mem_monomials w hw s.radius s.degreePowers
    s.degreePowers_pos s.degreePowers_eq i⟩

def pureIndex (hw : ∀ i, 0 < w i) (i : Fin n) : s.Index :=
  ⟨Finsupp.single i (s.degreePowers i),pure_mem_monomials w hw s.radius
    s.degreePowers s.degreePowers_eq i⟩

@[simp] theorem exponents_constant (hw : ∀ i, 0 < w i) :
    s.exponents (s.constantIndex hw) = 0 := rfl

@[simp] theorem exponents_coordinate (hw : ∀ i, 0 < w i) (i : Fin n) :
    s.exponents (s.coordinateIndex hw i) = Finsupp.single i 1 := rfl

@[simp] theorem exponents_pure (hw : ∀ i, 0 < w i) (i : Fin n) :
    s.exponents (s.pureIndex hw i) = Finsupp.single i (s.degreePowers i) := rfl

theorem budget (hw : ∀ i, 0 < w i) (i : s.Index) :
    (∑ j, w j * (s.exponents i j : ℚ)) ≤ s.radius :=
  (mem_monomials w hw s.radius i.val).mp i.property

end Scale

end PiExponent.WeightedGeometryScale

end

end OAI
