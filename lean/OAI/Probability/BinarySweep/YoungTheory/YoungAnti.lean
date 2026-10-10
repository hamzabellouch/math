import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungTabloid

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

def signC : G μ →* ℂ :=
  ((Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)).comp Equiv.Perm.sign

lemma signC_eq (g : G μ) : signC μ g = ((Equiv.Perm.sign g : ℤ) : ℂ) := rfl

lemma signC_sq (g : G μ) : signC μ g * signC μ g = 1 := by
  rw [signC_eq, ← Int.cast_mul]
  norm_cast
  exact congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign g))

lemma signC_ne_zero (g : G μ) : signC μ g ≠ 0 := by
  intro h
  have hh := signC_sq μ g
  simp [h] at hh

lemma signC_inv (g : G μ) : signC μ g⁻¹ = signC μ g := by
  apply (mul_left_cancel₀ (signC_ne_zero μ g))
  rw [← map_mul, mul_inv_cancel, map_one, signC_sq]

lemma signC_swap {x y : Cell μ} (h : x ≠ y) : signC μ (Equiv.swap x y) = -1 := by
  simp [signC_eq, Equiv.Perm.sign_swap h]

abbrev C := colStabilizer μ
instance : Fintype (C μ) := Fintype.ofFinite _

def columnAnti : Module.End ℂ (Tabloid μ → ℂ) :=
  ∑ c : C μ, signC μ c.val • tabloidRepresentation μ c.val

lemma columnAnti_apply (v : Tabloid μ → ℂ) :
    columnAnti μ v = ∑ c : C μ, signC μ c.val • tabloidRepresentation μ c.val v := by
  simp [columnAnti, LinearMap.sum_apply]

lemma columnAnti_rep (c : C μ) (v : Tabloid μ → ℂ) :
    columnAnti μ (tabloidRepresentation μ c.val v) = signC μ c.val • columnAnti μ v := by
  rw [columnAnti_apply, columnAnti_apply, Finset.smul_sum]
  have h := Equiv.sum_comp (Equiv.mulRight c)
    (fun d : C μ => signC μ c.val • (signC μ d.val • tabloidRepresentation μ d.val v))
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  change signC μ d.val • tabloidRepresentation μ d.val (tabloidRepresentation μ c.val v) =
    signC μ c.val • (signC μ (d * c).val • tabloidRepresentation μ (d * c).val v)
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
  rw [show signC μ c.val * (signC μ d.val * signC μ c.val) = signC μ d.val from by
    calc
      _ = signC μ d.val * (signC μ c.val * signC μ c.val) := by ring
      _ = signC μ d.val := by rw [signC_sq, mul_one]]

def polytabloid : Tabloid μ → ℂ :=
  columnAnti μ (tabloidBasis μ (tabloidOfPerm μ 1))

lemma columnAnti_basis_column (c : C μ) :
    columnAnti μ (tabloidBasis μ (tabloidOfPerm μ c.val)) = signC μ c.val • polytabloid μ := by
  rw [← mul_one c.val, ← smul_tabloidOfPerm, ← rep_basis, columnAnti_rep]
  rfl

lemma col_fixes_base_iff (c : C μ) :
    c.val • tabloidOfPerm μ 1 = tabloidOfPerm μ 1 ↔ c = 1 := by
  rw [smul_tabloidOfPerm, mul_one, tabloidOfPerm_eq_iff]
  constructor
  · intro hc
    have hr : c.val ∈ rowStabilizer μ := by
      have h := (rowStabilizer μ).inv_mem hc
      simpa using h
    have hi : c.val ∈ rowStabilizer μ ⊓ colStabilizer μ := ⟨hr, c.property⟩
    rw [row_col_intersection] at hi
    exact Subtype.ext hi
  · intro hc
    subst c
    simp

lemma polytabloid_base : polytabloid μ (tabloidOfPerm μ 1) = 1 := by
  rw [polytabloid, columnAnti_apply]
  simp_rw [rep_basis, smul_tabloidOfPerm, mul_one]
  simp only [Finset.sum_apply, Pi.smul_apply, tabloidBasis, Pi.single_apply]
  have he (c : C μ) : tabloidOfPerm μ 1 = tabloidOfPerm μ c.val ↔ c = 1 := by
    simpa [smul_tabloidOfPerm, eq_comm] using (col_fixes_base_iff μ c)
  simp only [he]
  simp

lemma polytabloid_ne_zero : polytabloid μ ≠ 0 := by
  intro h
  have hh := congrFun h (tabloidOfPerm μ 1)
  rw [polytabloid_base] at hh
  exact one_ne_zero hh

lemma swap_mem_fiber {X Y : Type*} [DecidableEq X] (f : X → Y) {x y : X}
    (h : f x = f y) : Equiv.swap x y ∈ fiberStabilizer f := by
  intro z
  exact Equiv.apply_swap_eq_self h z

lemma swap_fixes_tabloid (t : Tabloid μ) {x y : Cell μ} (h : t.val x = t.val y) :
    (Equiv.swap x y : G μ) • t = t := by
  apply Subtype.ext
  funext z
  change t.val ((Equiv.swap x y)⁻¹ z) = t.val z
  simpa only [Equiv.swap_inv] using Equiv.apply_swap_eq_self h z

lemma columnAnti_basis_collision (π : G μ) {x y : Cell μ}
    (hne : x ≠ y) (hc : col x = col y) (hr : row (π⁻¹ x) = row (π⁻¹ y)) :
    columnAnti μ (tabloidBasis μ (tabloidOfPerm μ π)) = 0 := by
  let c : C μ := ⟨Equiv.swap x y, swap_mem_fiber _ hc⟩
  have hf : c.val • tabloidOfPerm μ π = tabloidOfPerm μ π :=
    swap_fixes_tabloid μ _ hr
  have h := columnAnti_rep μ c (tabloidBasis μ (tabloidOfPerm μ π))
  rw [rep_basis, hf] at h
  have hs : signC μ c.val = -1 := signC_swap μ hne
  rw [hs, neg_one_smul] at h
  ext t
  have ht := congrFun h t
  simp only [Pi.neg_apply] at ht
  change columnAnti μ (tabloidBasis μ (tabloidOfPerm μ π)) t = 0
  linear_combination (1 / 2 : ℂ) * ht

lemma columnAnti_basis_span (t : Tabloid μ) :
    ∃ a : ℂ, columnAnti μ (tabloidBasis μ t) = a • polytabloid μ := by
  obtain ⟨π, rfl⟩ := tabloidOfPerm_surjective μ t
  rcases row_col_alternative μ π⁻¹ with ⟨x, y, hne, hc, hr⟩ | ⟨r, hr, c, hc, he⟩
  · exact ⟨0, by rw [columnAnti_basis_collision μ π hne hc hr, zero_smul]⟩
  · have hp : π = c⁻¹ * r⁻¹ := by simpa using congrArg Inv.inv he
    rw [hp, tabloidOfPerm_row_mul μ c⁻¹ ⟨r⁻¹, (rowStabilizer μ).inv_mem hr⟩]
    exact ⟨signC μ c⁻¹, columnAnti_basis_column μ ⟨c⁻¹, (colStabilizer μ).inv_mem hc⟩⟩

lemma sum_tabloidBasis (v : Tabloid μ → ℂ) :
    ∑ t : Tabloid μ, v t • tabloidBasis μ t = v := by
  ext t
  simp [tabloidBasis, Pi.single_apply, Finset.sum_apply]

theorem columnAnti_rank_one (v : Tabloid μ → ℂ) :
    columnAnti μ v = (columnAnti μ v (tabloidOfPerm μ 1)) • polytabloid μ := by
  have hv : ∃ a : ℂ, columnAnti μ v = a • polytabloid μ := by
    choose a ha using columnAnti_basis_span μ
    refine ⟨∑ t, v t * a t, ?_⟩
    conv_lhs => rw [← sum_tabloidBasis μ v]
    rw [map_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro t ht
    rw [map_smul, ha, smul_smul]
  obtain ⟨a, ha⟩ := hv
  have he := congrFun ha (tabloidOfPerm μ 1)
  simp only [Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one] at he
  rw [he, ha]

lemma columnAnti_square (v : Tabloid μ → ℂ) :
    columnAnti μ (columnAnti μ v) = (Fintype.card (C μ) : ℂ) • columnAnti μ v := by
  rw [columnAnti_apply μ v]
  rw [map_sum]
  simp_rw [map_smul, columnAnti_rep, smul_smul, signC_sq, one_smul]
  rw [← columnAnti_apply]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

lemma columnAnti_polytabloid :
    columnAnti μ (polytabloid μ) = (Fintype.card (C μ) : ℂ) • polytabloid μ :=
  columnAnti_square μ _

end BinaryCoordinateSweeps.Young

end

end OAI
