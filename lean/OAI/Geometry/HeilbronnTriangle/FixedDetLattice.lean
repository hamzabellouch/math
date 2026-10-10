import OAI.Geometry.HeilbronnTriangle.FixedDetReduction
import OAI.Geometry.HeilbronnTriangle.SuccessiveEstimates

namespace OAI


noncomputable section

namespace Problem355.FixedDetLattice

open Module Submodule MeasureTheory
open scoped BigOperators

abbrev E := EuclideanSpace ℝ (Fin 3)

def basisMatrix (b : Basis (Fin 3) ℝ E) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => b i j

lemma orthonormal_det_eq (b : Basis (Fin 3) ℝ E) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det b = (basisMatrix b).det := by
  rw [Basis.det_apply]
  have hmat : (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix b =
      (basisMatrix b).transpose := by
    ext i j
    rfl
  rw [hmat, Matrix.det_transpose]

lemma covolume_span_basis_eq_det (b : Basis (Fin 3) ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |(basisMatrix b).det| := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis,
    LatticeLowerProduct.volumeReal_fundamentalDomain_orthonormal,
    mul_one, orthonormal_det_eq]

lemma basisMatrix_det_ne_zero (b : Basis (Fin 3) ℝ E) : (basisMatrix b).det ≠ 0 := by
  apply abs_pos.mp
  rw [← covolume_span_basis_eq_det]
  exact ZLattice.covolume_pos (Submodule.span ℤ (Set.range b)) volume

lemma basisMatrix_coord_bound (b : Basis (Fin 3) ℝ E) (i j : Fin 3) :
    |basisMatrix b i j| ≤ ‖b i‖ := by
  simpa only [basisMatrix, Real.norm_eq_abs] using PiLp.norm_apply_le (b i) j

lemma relIndex_clears_rows (L : Submodule ℤ E) (b : Basis (Fin 3) ℝ E)
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ i, (WithLp.toLp 2 (A i) : E) ∈ L) :
    ∀ i, (Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup • A i ∈
      Submodule.span ℤ (Set.range (basisMatrix b)) := by
  intro i
  have h := (Submodule.span ℤ (Set.range b)).toAddSubgroup.nsmul_relIndex_mem
    (K := L.toAddSubgroup) (g := (WithLp.toLp 2 (A i) : E)) (hA i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
  apply (Submodule.mem_span_range_iff_exists_fun ℤ).mpr
  refine ⟨c, ?_⟩
  ext j
  have hh := congrArg (fun x : E => x j) hc
  simpa [basisMatrix] using hh

theorem fixed_det_count_of_successive_basis
    (a : ℝ) (ha : 0 ≤ a) (hanis : FixedDetReduction.AnisotropicEstimate a)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hunit : ∀ x ∈ L, x ≠ 0 → 1 ≤ ‖x‖)
    (b : Basis (Fin 3) ℝ E) (hb : SuccessiveVectors.IsSuccessive L b)
    (X : ℝ) (hX : 1 ≤ X) (hlast : ‖b 2‖ ≤ X)
    (S : Finset (Matrix (Fin 3) (Fin 3) ℝ))
    (hrows : ∀ A ∈ S, ∀ i, (WithLp.toLp 2 (A i) : E) ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖(WithLp.toLp 2 (A i) : E)‖ ≤ X)
    (t : ℝ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
      ZLattice.covolume L ^ 2 := by
  let L₀ := Submodule.span ℤ (Set.range b)
  let m := L₀.toAddSubgroup.relIndex L.toAddSubgroup
  have hsub : L₀ ≤ L := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hb.mem_lattice i
  have hratio : ZLattice.covolume L₀ / ZLattice.covolume L = (m : ℝ) :=
    ZLattice.covolume_div_covolume_eq_relIndex' L₀ L hsub
  have hm : 0 < m := by
    have hmR : (0 : ℝ) < m := by
      rw [← hratio]
      exact div_pos (ZLattice.covolume_pos L₀) (ZLattice.covolume_pos L)
    exact_mod_cast hmR
  have hm6 : m ≤ 6 := (SuccessiveEstimates.relIndex_le_five L b
    hb.mem_lattice hb.minimal).trans (by norm_num)
  have hest := SuccessiveEstimates.successive_basis_estimates
    (by norm_num : 0 < 3) L b hb.mem_lattice hb.minimal
  have hsqrt : Real.sqrt (3 : ℝ) ^ 3 ≤ 6 := by
    have hs : Real.sqrt (3 : ℝ) ≤ 2 := by norm_num [Real.sqrt_le_iff]
    have heq : Real.sqrt (3 : ℝ) ^ 3 = 3 * Real.sqrt (3 : ℝ) := by
      rw [pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    rw [heq]
    linarith
  have hprod : (∏ i, ‖b i‖) ≤ 6 * |(basisMatrix b).det| := by
    calc
      (∏ i, ‖b i‖) ≤ Real.sqrt (3 : ℝ) ^ 3 * ZLattice.covolume L := hest.2.1
      _ ≤ 6 * ZLattice.covolume L :=
        mul_le_mul_of_nonneg_right hsqrt (ZLattice.covolume_pos L).le
      _ ≤ 6 * ZLattice.covolume L₀ :=
        mul_le_mul_of_nonneg_left (LatticeLowerProduct.covolume_mono_reverse L₀ L hsub)
          (by norm_num)
      _ = 6 * |(basisMatrix b).det| := by rw [covolume_span_basis_eq_det]
  apply FixedDetReduction.fixed_det_count_of_short_basis a ha hanis (basisMatrix b) m hm hm6
    (fun i => ‖b i‖) X (ZLattice.covolume L volume) (basisMatrix_det_ne_zero b)
    (basisMatrix_coord_bound b) _ _ hb.monotone_norm hX (ZLattice.covolume_pos L volume)
    hest.1 hprod S _ _ t ht hdet
  · intro i
    exact hunit (b i) (hb.mem_lattice i) (b.ne_zero i)
  · intro i
    exact (hb.monotone_norm (Fin.le_last i)).trans hlast
  · intro A hA
    exact relIndex_clears_rows L b A (hrows A hA)
  · intro A hA i j
    have hcoord : |A i j| ≤ ‖(WithLp.toLp 2 (A i) : E)‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (WithLp.toLp 2 (A i) : E) j
    exact hcoord.trans (hnorm A hA i)

lemma last_norm_le_of_matrix (L : Submodule ℤ E)
    (b : Basis (Fin 3) ℝ E) (hb : SuccessiveVectors.IsSuccessive L b)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.det ≠ 0)
    (hrows : ∀ i, (WithLp.toLp 2 (A i) : E) ∈ L)
    (X : ℝ) (hnorm : ∀ i, ‖(WithLp.toLp 2 (A i) : E)‖ ≤ X) :
    ‖b 2‖ ≤ X := by
  classical
  let v : Fin 3 → E := fun i => WithLp.toLp 2 (A i)
  have hv : LinearIndependent ℝ v := by
    convert! (Matrix.linearIndependent_rows_of_det_ne_zero hA).map'
        (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap
        (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.injective) using 1
  let c : Basis (Fin 3) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank' v hv (by simp [E])
  let W := Submodule.span ℝ (SuccessiveVectors.earlier b 2)
  have hbW : b 2 ∉ W :=
    hb.independent.notMem_span_image (by simp)
  have hex : ∃ i, v i ∉ W := by
    by_contra h
    have hall : ∀ i, v i ∈ W := by simpa using h
    have hle : Submodule.span ℝ (Set.range c) ≤ W := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      convert! hall i using 1
      exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' v hv (by simp [E])) i
    rw [c.span_eq] at hle
    exact hbW (hle (by trivial))
  obtain ⟨i, hi⟩ := hex
  exact (hb.minimal 2 (v i) (hrows i) hi).trans (hnorm i)

theorem fixed_det_count
    (a : ℝ) (ha : 0 ≤ a) (hanis : FixedDetReduction.AnisotropicEstimate a)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hunit : ∀ x ∈ L, x ≠ 0 → 1 ≤ ‖x‖)
    (X : ℝ) (hX : 1 ≤ X)
    (S : Finset (Matrix (Fin 3) (Fin 3) ℝ))
    (hrows : ∀ A ∈ S, ∀ i, (WithLp.toLp 2 (A i) : E) ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖(WithLp.toLp 2 (A i) : E)‖ ≤ X)
    (t : ℝ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
      ZLattice.covolume L ^ 2 := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨A, hA⟩ := hS
    have hex : ∃ b : Basis (Fin 3) ℝ E, SuccessiveVectors.IsSuccessive L b := by
      obtain ⟨v, hv⟩ := SuccessiveVectors.exists_successive L 3 (by simp [E])
      refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hv.independent (by simp [E]), ?_⟩
      simpa only [coe_basisOfLinearIndependentOfCardEqFinrank'] using hv
    obtain ⟨b, hb⟩ := hex
    have hlast : ‖b 2‖ ≤ X :=
      last_norm_le_of_matrix L b hb A (by simpa only [hdet A hA] using ht)
        (hrows A hA) X (hnorm A hA)
    exact fixed_det_count_of_successive_basis a ha hanis L hunit b hb X hX hlast
      S hrows hnorm t ht hdet
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem integer_fixed_det_count
    (a : ℝ) (ha : 0 ≤ a) (hanis : FixedDetReduction.AnisotropicEstimate a)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hunit : ∀ x ∈ L, x ≠ 0 → 1 ≤ ‖x‖)
    (X : ℝ) (hX : 1 ≤ X)
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hrows : ∀ A ∈ S, ∀ i, (WithLp.toLp 2 (fun j => (A i j : ℝ)) : E) ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖(WithLp.toLp 2 (fun j => (A i j : ℝ)) : E)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
      ZLattice.covolume L ^ 2 := by
  classical
  let f : Matrix (Fin 3) (Fin 3) ℤ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun A => A.map (Int.castRingHom ℝ)
  have hf : Function.Injective f := by
    intro A B h
    ext i j
    have hh := congrArg (fun C => C i j) h
    change (A i j : ℝ) = (B i j : ℝ) at hh
    exact_mod_cast hh
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injective S hf
  rw [← hcard]
  refine fixed_det_count a ha hanis L hunit X hX (S.image f) ?_ ?_ (t : ℝ)
    (by exact_mod_cast ht) ?_
  · intro A hA i
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact hrows B hB i
  · intro A hA i
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact hnorm B hB i
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    change (B.map (Int.castRingHom ℝ)).det = (t : ℝ)
    have hd := (Int.castRingHom ℝ).map_det B
    change (B.det : ℝ) = (B.map (Int.castRingHom ℝ)).det at hd
    rw [← hd, hdet B hB]

end Problem355.FixedDetLattice

end

end OAI
