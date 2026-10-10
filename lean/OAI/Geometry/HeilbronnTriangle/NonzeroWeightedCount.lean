import OAI.Geometry.HeilbronnTriangle.AnisotropicCount
import OAI.Geometry.HeilbronnTriangle.FullIntegralLattice
import OAI.Geometry.HeilbronnTriangle.OrbitRowLattice
import OAI.Geometry.HeilbronnTriangle.HomogeneousGeometry

namespace OAI


noncomputable section
namespace Problem355.NonzeroWeightedCount

open Matrix
open scoped BigOperators Matrix

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ

def columnTriple (A : IntMatrix) : Anisotropic.Triple :=
  (A.col 0, A.col 1, A.col 2)

lemma columnTriple_injective : Function.Injective columnTriple := by
  intro A B h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg (fun x : Anisotropic.Triple => x.2.1) h
  have h2 := congrArg (fun x : Anisotropic.Triple => x.2.2) h
  ext i j
  fin_cases j
  · exact congrFun h0 i
  · exact congrFun h1 i
  · exact congrFun h2 i

lemma columnTriple_det (A : IntMatrix) :
    (columnTriple A).1 ⬝ᵥ ((columnTriple A).2.1 ⨯₃ (columnTriple A).2.2) = A.det := by
  simp [columnTriple, Matrix.det_fin_three, dotProduct, Fin.sum_univ_succ,
    crossProduct, Matrix.col]
  ring

def anisotropicConstant : ℝ := 35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2

lemma anisotropicConstant_pos : 0 < anisotropicConstant :=
  Anisotropic.anisotropic_constant_pos

theorem anisotropic_estimate :
    FixedDetReduction.AnisotropicEstimate anisotropicConstant := by
  classical
  intro r u T hr hr2 hu hT
  have hcount := Anisotropic.anisotropic_count (T.image columnTriple) u hu
    (r 0) (r 1) (r 2) hr2 (hr (by decide : (1 : Fin 3) ≤ 2))
    (hr (by decide : (0 : Fin 3) ≤ 1))
    (by
      intro x hx
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
      rw [columnTriple_det]
      exact (hT A hA).1)
    (by
      intro x hx
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨(hT A hA).2 0, (hT A hA).2 1, (hT A hA).2 2⟩)
  simpa [anisotropicConstant, Finset.card_image_of_injective _ columnTriple_injective,
    Fin.prod_univ_succ, mul_assoc] using hcount

def latticeConstant : ℝ := anisotropicConstant * 1000 ^ 6 * 144

lemma latticeConstant_pos : 0 < latticeConstant := by
  unfold latticeConstant
  exact mul_pos (mul_pos anisotropicConstant_pos (by positivity)) (by norm_num)

theorem lattice_count
    (L : Submodule ℤ (Fin 3 → ℤ)) (m : ℤ) (hm : m ≠ 0)
    (hL : ∀ v, m • v ∈ L)
    (X : ℝ) (hX : 1 ≤ X) (S : Finset IntMatrix)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖IntegralPlaneLattice.castVec (A i)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ latticeConstant * Real.log (2 * X) ^ 2 * X ^ 6 /
      (L.toAddSubgroup.index : ℝ) ^ 2 :=
  FullIntegralLattice.fixed_det_count anisotropicConstant anisotropicConstant_pos.le
    anisotropic_estimate L m hm hL X hX S hrows hnorm t ht hdet

theorem weighted_lattice_count
    (L : Submodule ℤ (Fin 3 → ℤ)) (m : ℤ) (hm : m ≠ 0)
    (hL : ∀ v, m • v ∈ L)
    (X : ℝ) (hX : 1 ≤ X) (S : Finset IntMatrix)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖IntegralPlaneLattice.castVec (A i)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t)
    (W : IntMatrix → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hW : ∀ A ∈ S, W A ≤ w) :
    (∑ A ∈ S, W A) ≤ (w * latticeConstant) * Real.log (2 * X) ^ 2 * X ^ 6 /
      (L.toAddSubgroup.index : ℝ) ^ 2 := by
  calc
    (∑ A ∈ S, W A) ≤ ∑ _A ∈ S, w := Finset.sum_le_sum hW
    _ = w * (S.card : ℝ) := by simp [mul_comm]
    _ ≤ w * (latticeConstant * Real.log (2 * X) ^ 2 * X ^ 6 /
        (L.toAddSubgroup.index : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (lattice_count L m hm hL X hX S hrows hnorm t ht hdet) hw
    _ = _ := by ring

def boxConstant : ℝ := latticeConstant * 144 * 4 ^ 6

lemma boxConstant_pos : 0 < boxConstant := by
  unfold boxConstant
  exact mul_pos (mul_pos latticeConstant_pos (by norm_num)) (by positivity)

theorem weighted_box_count
    (L : Submodule ℤ (Fin 3 → ℤ)) (m : ℤ) (hm : m ≠ 0)
    (hL : ∀ v, m • v ∈ L)
    (N : ℝ) (hN : 1 ≤ N) (S : Finset IntMatrix)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖IntegralPlaneLattice.castVec (A i)‖ ≤ 4 * N)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t)
    (W : IntMatrix → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hW : ∀ A ∈ S, W A ≤ w) :
    (∑ A ∈ S, W A) ≤ (w * boxConstant) * Real.log (2 * N) ^ 2 * N ^ 6 /
      (L.toAddSubgroup.index : ℝ) ^ 2 := by
  have hcount := weighted_lattice_count L m hm hL (4 * N) (by linarith)
    S hrows hnorm t ht hdet W w hw hW
  have hlog := FixedDetReduction.log_radius_bound N (4 * N) hN
    (by linarith) (by nlinarith)
  have hlog0 : 0 ≤ Real.log (2 * (4 * N)) := Real.log_nonneg (by linarith)
  have hlog2 := pow_le_pow_left₀ hlog0 hlog 2
  have hfactor : 0 ≤ w * latticeConstant := mul_nonneg hw latticeConstant_pos.le
  calc
    (∑ A ∈ S, W A) ≤ _ := hcount
    _ ≤ (w * latticeConstant) * (12 * Real.log (2 * N)) ^ 2 * (4 * N) ^ 6 /
        (L.toAddSubgroup.index : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog2 hfactor) (by positivity)) (sq_nonneg _)
    _ = _ := by unfold boxConstant; ring

lemma row_norm_le_four_mul (A : IntMatrix) (N : ℝ) (hN : 0 ≤ N)
    (hbox : ∀ j, Homogeneous.InBox N (fun i => (A i j : ℝ))) (i : Fin 3) :
    ‖IntegralPlaneLattice.castVec (A i)‖ ≤ 4 * N := by
  have hcoord : ∀ j, |(IntegralPlaneLattice.castVec (A i)) j| ≤ 2 * N := by
    intro j
    have hj := hbox j
    fin_cases i
    · change |(A 0 j : ℝ)| ≤ 2 * N
      rw [abs_of_nonneg hj.1]
      linarith [hj.2.1]
    · change |(A 1 j : ℝ)| ≤ 2 * N
      rw [abs_of_nonneg hj.2.2.1]
      linarith [hj.2.2.2.1]
    · change |(A 2 j : ℝ)| ≤ 2 * N
      rw [abs_of_nonneg (hN.trans hj.2.2.2.2.1)]
      exact hj.2.2.2.2.2.le
  have h := LatticeCoordinates.euclidean_norm_le_of_coord_bound
    (IntegralPlaneLattice.castVec (A i)) (2 * N) (by positivity) hcoord
  have hs : Real.sqrt (3 : ℝ) ≤ 2 := by norm_num [Real.sqrt_le_iff]
  simp only [Fintype.card_fin] at h
  apply h.trans
  calc
    Real.sqrt (3 : ℝ) * (2 * N) ≤ 2 * (2 * N) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = 4 * N := by ring

theorem weighted_orbit_count
    (B k b e : ℕ) (hB : 0 < B) (hb : b ≤ k) (he : e ≤ k) (hbe : b ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix _ _ _) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
        (Q : Matrix _ _ _))
    (N : ℝ) (hN : 1 ≤ N) (S : Finset IntMatrix)
    (horbit : ∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
      Section04Orbit.slOrbit C)
    (hbox : ∀ A ∈ S, ∀ j, Homogeneous.InBox N (fun i => (A i j : ℝ)))
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t)
    (W : IntMatrix → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hW : ∀ A ∈ S, W A ≤ w) :
    (∑ A ∈ S, W A) ≤ (w * boxConstant) * Real.log (2 * N) ^ 2 * N ^ 6 /
      ((B : ℝ) ^ b * (B : ℝ) ^ e) ^ 2 := by
  let : NeZero B := ⟨ne_of_gt hB⟩
  let L := (RowLattice.integerRowLattice (B ^ k) C).toIntSubmodule
  have hL : ∀ v, (B ^ e : ℤ) • v ∈ L := by
    intro v
    change (B ^ e : ℤ) • v ∈ RowLattice.integerRowLattice (B ^ k) C
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact RowLattice.nsmul_mem_integerRowLattice_prime_power B k b e hbe C P Q hC v
  have hm : (B ^ e : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero e (ne_of_gt hB)
  have hc := weighted_box_count L (B ^ e : ℤ) hm hL N hN S
    (fun A hA i => OrbitRowLattice.row_mem_integerRowLattice_of_reduction_mem_slOrbit
      (B ^ k) C A (horbit A hA) i)
    (fun A hA i => row_norm_le_four_mul A N (by linarith) (hbox A hA) i)
    t ht hdet W w hw hW
  have hi : L.toAddSubgroup.index = B ^ b * B ^ e :=
    RowLattice.integerRowLattice_index_prime_power B k b e hb he C P Q hC
  simpa only [hi, Nat.cast_mul, Nat.cast_pow] using hc

end Problem355.NonzeroWeightedCount

end

end OAI
