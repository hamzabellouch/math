import OAI.Analysis.PureInfiniteness.CutMatrixDiagonalization
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerPositive

namespace OAI

/-! The fixed-cut diagonalization in the norm ultrapower, for arbitrary
ultrapower entries. Positive representatives and a uniform finite coefficient
bound are the only lifting ingredients. -/

noncomputable section
open Filter
open scoped NNReal ENNReal Topology

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance : PartialOrder (NormUltra.BoundedFamilies (fun _ : ℕ => A)) :=
  CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (NormUltra.BoundedFamilies (fun _ : ℕ => A)) :=
  CStarAlgebra.spectralOrderedRing _

def boundedCoordinate (k : ℕ) : NormUltra.BoundedFamilies (fun _ : ℕ => A) →⋆ₙₐ[ℂ] A where
  toFun x := x k
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp] lemma boundedCoordinate_apply (k : ℕ)
    (x : NormUltra.BoundedFamilies (fun _ : ℕ => A)) :
    boundedCoordinate (A := A) k x = x k := rfl

lemma positive_bounded_representative (U : Ultrafilter ℕ)
    {a : NormUltra.QuotientAlgebra (fun _ : ℕ => A) U} (ha : 0 ≤ a)
    {M : ℝ} (hM : 0 < M) (han : ‖a‖ ≤ M) :
    ∃ x : NormUltra.BoundedFamilies (fun _ : ℕ => A),
      NormUltra.QuotientAlgebra.mk U x = a ∧ 0 ≤ x ∧ ‖x‖ ≤ M := by
  let q := NormUltra.QuotientAlgebra.mkHom (A := fun _ : ℕ => A) (U := U)
  have hn : ‖M⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
    exact (mul_le_mul_of_nonneg_left han (inv_nonneg.mpr hM.le)).trans_eq
      (inv_mul_cancel₀ hM.ne')
  obtain ⟨x, hx, hxp, hxn⟩ := CStarLift.exists_positive_contraction q
    NormUltra.QuotientAlgebra.mk_surjective (smul_nonneg (inv_nonneg.mpr hM.le) ha) hn
  refine ⟨M • x, ?_, smul_nonneg hM.le hxp, ?_⟩
  · change q (M • x) = a
    rw [LinearMapClass.map_smul_of_tower q M x, hx, smul_smul,
      mul_inv_cancel₀ hM.ne', one_smul]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hM]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hxn hM.le

theorem boundedFamilies_cut_diagonalization (hP : MainGap.PropertyP A)
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (M₀ : ℝ) (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∀ M : Fin n → Fin n → NormUltra.BoundedFamilies (fun _ : ℕ => A),
      (∀ i, 0 ≤ M i i) → (∀ i, ‖M i i‖ ≤ M₀) →
      ∃ d : Fin n → NormUltra.QuotientAlgebra (fun _ : ℕ => A) U,
      (∀ i, ‖d i‖ ≤ C) ∧
      (∀ i, star (d i) * NormUltra.QuotientAlgebra.mk U (M i i) * d i =
        MainGap.cut (NormUltra.QuotientAlgebra.mk U (M i i)) δ) ∧
      ∀ i j, i ≠ j →
        star (d i) * NormUltra.QuotientAlgebra.mk U (M i j) * d j = 0 := by
  classical
  obtain ⟨C, hC, hd⟩ := finite_matrix_cut_diagonalization hP M₀ δ hδ
  refine ⟨C, hC, ?_⟩
  intro n M hpos hM
  have hposk (k : ℕ) (i : Fin n) : 0 ≤ M i i k := by
    simpa only [boundedCoordinate_apply] using
      (map_nonneg (boundedCoordinate (A := A) k) (hpos i))
  have hchoice (k : ℕ) := hd n (fun i j => M i j k)
    (hposk k)
    (fun i => (NormUltra.BoundedFamilies.norm_coordinate_le (M i i) k).trans (hM i))
    (1 / ((k : ℝ) + 1)) (1 / ((k : ℝ) + 1)) (by positivity) (by positivity)
  choose v hvn hvdiag hvoff using hchoice
  let x (i : Fin n) : NormUltra.BoundedFamilies (fun _ : ℕ => A) :=
    ⟨fun k => v k i, memℓp_infty ⟨C, by
      rintro _ ⟨k, rfl⟩
      exact hvn k i⟩⟩
  let d (i : Fin n) := NormUltra.QuotientAlgebra.mk U (x i)
  let q := NormUltra.QuotientAlgebra.mkHom (A := fun _ : ℕ => A) (U := U)
  refine ⟨d, ?_, ?_, ?_⟩
  · intro i
    exact (NormUltra.QuotientAlgebra.norm_mk_le (x i)).trans
      (lp.norm_le_of_forall_le hC (hvn · i))
  · intro i
    have hmap : q (MainGap.cut (M i i) δ) = MainGap.cut (q (M i i)) δ :=
      MainGap.map_cut q (hpos i) δ.2
    apply Eq.trans (b := q (MainGap.cut (M i i) δ)) ?_ hmap
    change NormUltra.QuotientAlgebra.mk U (star (x i) * M i i * x i) =
      NormUltra.QuotientAlgebra.mk U (MainGap.cut (M i i) δ)
    apply (NormUltra.QuotientAlgebra.mk_eq_mk_iff _ _).mpr
    change Tendsto (fun k => ‖star (v k i) * M i i k * v k i - (MainGap.cut (M i i) δ) k‖)
      (U : Filter ℕ) (𝓝 0)
    have heval (k : ℕ) : (MainGap.cut (M i i) δ) k = MainGap.cut (M i i k) δ :=
      MainGap.map_cut (boundedCoordinate (A := A) k) (hpos i) δ.2
    simp_rw [heval]
    apply Filter.Tendsto.mono_left _ (Fact.out : (U : Filter ℕ) ≤ atTop)
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => (hvdiag k i).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro i j hij
    change NormUltra.QuotientAlgebra.mk U (star (x i) * M i j * x j) =
      NormUltra.QuotientAlgebra.mk U 0
    apply (NormUltra.QuotientAlgebra.mk_eq_mk_iff _ _).mpr
    change Tendsto (fun k => ‖star (v k i) * M i j k * v k j - 0‖)
      (U : Filter ℕ) (𝓝 0)
    simp only [sub_zero]
    apply Filter.Tendsto.mono_left _ (Fact.out : (U : Filter ℕ) ≤ atTop)
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => (hvoff k i j hij).le)
      tendsto_one_div_add_atTop_nhds_zero_nat

/-- KR02's exact cut diagonalization for a finite family in the norm
ultrapower. The matrix entries themselves need not be constant sequences. -/
theorem ultrapower_matrix_cut_diagonalization (hP : MainGap.PropertyP A)
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (M₀ : ℝ) (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∀ M : Fin n → Fin n → NormUltra.QuotientAlgebra (fun _ : ℕ => A) U,
      (∀ i, 0 ≤ M i i) → (∀ i, ‖M i i‖ ≤ M₀) →
      ∃ d : Fin n → NormUltra.QuotientAlgebra (fun _ : ℕ => A) U,
      (∀ i, ‖d i‖ ≤ C) ∧
      (∀ i, star (d i) * M i i * d i = MainGap.cut (M i i) δ) ∧
      ∀ i j, i ≠ j → star (d i) * M i j * d j = 0 := by
  classical
  let L := max 1 M₀
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨C, hC, hdiag⟩ := boundedFamilies_cut_diagonalization hP U L δ hδ
  refine ⟨C, hC, ?_⟩
  intro n M hpos hM
  choose p hp hpp hpn using fun i => positive_bounded_representative U
    (hpos i) hL ((hM i).trans (le_max_right _ _))
  choose r hr using fun i j => NormUltra.QuotientAlgebra.mk_surjective (M i j)
  let B (i j : Fin n) := if i = j then p i else r i j
  have hB (i j : Fin n) : NormUltra.QuotientAlgebra.mk U (B i j) = M i j := by
    by_cases hij : i = j
    · subst j
      simpa [B] using hp i
    · simpa [B, hij] using hr i j
  have hBp (i : Fin n) : 0 ≤ B i i := by simpa [B] using hpp i
  have hBn (i : Fin n) : ‖B i i‖ ≤ L := by simpa [B] using hpn i
  obtain ⟨d, hdn, hdd, hdo⟩ := hdiag n B hBp hBn
  exact ⟨d, hdn, fun i => by simpa only [hB] using hdd i,
    fun i j hij => by simpa only [hB] using hdo i j hij⟩

end WeakPureInfiniteness

end

end OAI
