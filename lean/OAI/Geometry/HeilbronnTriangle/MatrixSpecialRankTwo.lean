import OAI.Geometry.HeilbronnTriangle.RowLatticeMatrices
import OAI.Geometry.HeilbronnTriangle.ZeroAffineShell
import OAI.Geometry.HeilbronnTriangle.SpecialRankTwo

namespace OAI


noncomputable section

namespace Problem355.MatrixSpecialRankTwo

open scoped BigOperators Matrix
open Matrix RowLatticeMatrices PrimitiveNormal IntegralPlaneLattice PairingDivisor

theorem canonical_covolume_cube_lower
    (x : Fin 3 → ℤ) (hx : IsPrimitive x)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E I : ℕ)
    (hE : 0 < E) (hI : 0 < I)
    (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L)
    (hindex : L.toAddSubgroup.index = I)
    (R h : ℝ) (hR : 0 ≤ R) (hnorm : R ≤ ‖toEuclidean x‖)
    (hcube : (E : ℝ) ^ 3 ≤ (I : ℝ) * h ^ 2) :
    (I : ℝ) ^ 2 * R ^ 3 ≤ h ^ 2 * ZLattice.covolume (latticeIn x L) ^ 3 := by
  obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one x).mp hx
  obtain ⟨hgpos, hgdvd⟩ := pairingDivisor_pos_and_dvd L.toAddSubgroup x z hz
    E hE hcontain
  have hgE : (pairingDivisor L.toAddSubgroup x : ℝ) ≤ E := by
    exact_mod_cast Nat.le_of_dvd hE hgdvd
  have hg3 : (pairingDivisor L.toAddSubgroup x : ℝ) ^ 3 ≤ (I : ℝ) * h ^ 2 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hgE 3).trans hcube
  apply SpecialRankTwo.covolume_cube_lower (by exact_mod_cast hI) hR hnorm
    (by exact_mod_cast hgpos) _ hg3
  rw [ZeroAffineShell.canonical_pairing_covolume x hx L E hE hcontain, hindex]

theorem canonical_covolume_cube_lower_of_bounds
    (x : Fin 3 → ℤ) (hx : IsPrimitive x)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E h : ℕ) (hE : 0 < E)
    (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L)
    (hEindex : E ≤ L.toAddSubgroup.index) (hEh : E ≤ h)
    (R : ℝ) (hR : 0 ≤ R) (hr : R ≤ ‖toEuclidean x‖) :
    (L.toAddSubgroup.index : ℝ) ^ 2 * R ^ 3 ≤
      (h : ℝ) ^ 2 * ZLattice.covolume (latticeIn x L) ^ 3 := by
  apply canonical_covolume_cube_lower x hx L E L.toAddSubgroup.index hE
    (hE.trans_le hEindex) hcontain rfl R h hR hr
  have hEI : (E : ℝ) ≤ L.toAddSubgroup.index := by exact_mod_cast hEindex
  have hEhR : (E : ℝ) ≤ h := by exact_mod_cast hEh
  calc
    (E : ℝ) ^ 3 = (E : ℝ) * (E : ℝ) ^ 2 := by ring
    _ ≤ (L.toAddSubgroup.index : ℝ) * (h : ℝ) ^ 2 := by gcongr

theorem prime_power_cube_bound (B b e k : ℕ) (hB : 1 ≤ B) (hek : e ≤ k) :
    ((B ^ e : ℕ) : ℝ) ^ 3 ≤ ((B ^ (b + e) : ℕ) : ℝ) *
      (((B ^ k : ℕ) : ℝ)) ^ 2 := by
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hexp : e * 3 ≤ b + e + k * 2 := by omega
  have hp := pow_le_pow_right₀ hBR hexp
  push_cast
  simpa only [← pow_mul, ← pow_add] using hp

theorem canonical_covolume_cube_lower_prime_power
    (x : Fin 3 → ℤ) (hx : IsPrimitive x)
    (L : Submodule ℤ (Fin 3 → ℤ)) (B b e k : ℕ)
    (hB : 0 < B) (hek : e ≤ k)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
    (hindex : L.toAddSubgroup.index = B ^ (b + e))
    (R : ℝ) (hR : 0 ≤ R) (hnorm : R ≤ ‖toEuclidean x‖) :
    ((B : ℝ) ^ (b + e)) ^ 2 * R ^ 3 ≤
      ((B : ℝ) ^ k) ^ 2 * ZLattice.covolume (latticeIn x L) ^ 3 := by
  have h := canonical_covolume_cube_lower x hx L (B ^ e) (B ^ (b + e))
    (pow_pos hB _) (pow_pos hB _) hcontain hindex R (B ^ k : ℕ) hR hnorm
    (prime_power_cube_bound B b e k hB hek)
  simpa only [Nat.cast_pow] using h

theorem weighted_matrix_shell_le
    (S : Finset (Fin 3 → ℤ)) (L : Submodule ℤ (Fin 3 → ℤ))
    (E I R q : ℕ) (hE : 0 < E) (hI : 0 < I) (hR : 0 < R) (hq : 0 < q)
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L)
    (hindex : L.toAddSubgroup.index = I)
    (hnorm : ∀ x ∈ S, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (hnonzero : ∀ x ∈ S, x k ≠ 0)
    (hline : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1})
    (F : (Fin 3 → ℤ) → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ a, A a ∈ L)
    (W : (Fin 3 → ℤ) → IntMatrix → ℝ)
    (N h Cw : ℝ) (hN : 0 ≤ N) (hCw : 0 ≤ Cw)
    (hparam : h ^ 14 ≤ (q : ℝ))
    (hcube : (E : ℝ) ^ 3 ≤ (I : ℝ) * h ^ 2)
    (hW : ∀ x ∈ S, ∀ A ∈ F x, W x A ≤ Cw * (q : ℝ) * h ^ 12)
    (hcoord : ∀ x ∈ S, ∀ A ∈ F x, ∀ a b, |(A a b : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ S, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t) :
    (∑ x ∈ S, ∑ A ∈ F x, W x A) ≤
      512 * (144 * Real.pi) ^ 3 * Cw * N ^ 6 / (I : ℝ) ^ 2 := by
  classical
  have hz : ∀ x : S, ∃ z : Fin 3 → ℤ, dotProduct (x : Fin 3 → ℤ) z = 1 :=
    fun x => (isPrimitive_iff_exists_dot_eq_one x.val).mp (hprimitive x.val x.property)
  choose z hz using hz
  let : ∀ x : S, IsZLattice ℝ (latticeIn x.val L) := fun x =>
    latticeIn_isZLattice x.val (z x) (hz x) L (E : ℤ)
      (by exact_mod_cast Nat.ne_of_gt hE)
      (by simpa only [Nat.cast_smul_eq_nsmul] using hcontain)
  let T := fun x : S => rowFamily x.val L (F x.val) (hF x.val)
  let V := fun (x : S) u => W x.val ((rowsEquiv x.val L).symm u).val
  have hbox : ∀ x ∈ S, ∀ t,
      -((2 * R : ℕ) : ℤ) ≤ x t ∧ x t ≤ ((2 * R : ℕ) : ℤ) := by
    intro x hx t
    have hc : |(x t : ℝ)| ≤ ‖toEuclidean x‖ := by
      change ‖(toEuclidean x).ofLp t‖ ≤ ‖toEuclidean x‖
      exact PiLp.norm_apply_le _ _
    have hb : |(x t : ℝ)| ≤ (2 * R : ℕ) := by
      push_cast
      exact hc.trans (hnorm x hx).2.le
    exact abs_le.mp (show |x t| ≤ ((2 * R : ℕ) : ℤ) by exact_mod_cast hb)
  have hbound := SpecialRankTwo.special_rank_two_shell_subtype S
    (fun x => plane x.val) (fun x => latticeIn x.val L) T V
    R q hR hq i j k hki hkj hbox hnonzero hline N I h Cw hN
    (by exact_mod_cast hI) hCw hparam
    (fun x => plane_finrank x.val (z x) (hz x))
    (fun x => rowFamily_norm_le_four_mul x.val L (F x.val) (hF x.val)
      hN (hcoord x.val x.property))
    (fun x => rowFamily_independent_of_projections x.val L (F x.val) (hF x.val)
      (hproj x.val x.property))
    (fun x u hu => hW x.val x.property _
      ((mem_rowFamily x.val L (F x.val) (hF x.val) u).mp hu))
    (fun x => canonical_covolume_cube_lower x.val (hprimitive x.val x.property)
      L E I hE hI hcontain hindex R h (Nat.cast_nonneg R)
      (hnorm x.val x.property).1 hcube)
  have heq : (∑ x : S, ∑ u ∈ T x, V x u) = ∑ x ∈ S, ∑ A ∈ F x, W x A := by
    calc
      (∑ x : S, ∑ u ∈ T x, V x u) = ∑ x : S, ∑ A ∈ F x.val, W x.val A := by
        apply Finset.sum_congr rfl
        intro x hx
        exact sum_rowFamily x.val L (F x.val) (hF x.val) (W x.val)
      _ = _ := Finset.sum_attach S (fun x => ∑ A ∈ F x, W x A)
  rw [heq] at hbound
  exact hbound

end Problem355.MatrixSpecialRankTwo

end

end OAI
