import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TentMatrixPositivity
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FlagSiteCounts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagAveragingMatrices
open Classical MeasureTheory

noncomputable def planeTent (s : ℝ) (x y : ℝ×ℝ) : ℝ :=
  max (1-|(x.1-y.1)/s|) 0 * max (1-|(x.2-y.2)/s|) 0

theorem planeTent_posSemidef {ι : Type*} (s : ℝ) (x : ι → ℝ×ℝ) :
    Matrix.PosSemidef (fun i j => planeTent s (x i) (x j)) := by
  simpa only [planeTent,sub_div] using planeTentMatrix_posSemidef x s

theorem planeTent_nonneg (s : ℝ) (x y : ℝ×ℝ) : 0 ≤ planeTent s x y :=
  mul_nonneg (le_max_right _ _) (le_max_right _ _)

theorem planeTent_le_one (s : ℝ) (x y : ℝ×ℝ) : planeTent s x y ≤ 1 := by
  have h₁ : max (1-|(x.1-y.1)/s|) 0 ≤ 1 := max_le (by linarith [abs_nonneg ((x.1-y.1)/s)]) zero_le_one
  have h₂ : max (1-|(x.2-y.2)/s|) 0 ≤ 1 := max_le (by linarith [abs_nonneg ((x.2-y.2)/s)]) zero_le_one
  exact (mul_le_mul h₁ h₂ (le_max_right _ _) zero_le_one).trans_eq (one_mul 1)

@[simp] theorem planeTent_self (s : ℝ) (x : ℝ×ℝ) : planeTent s x x=1 := by
  simp [planeTent]

noncomputable def flagSiteOrdinary {a m D : ℕ} {v : ℝ×ℝ} (z : FlagSite a m D v) : ℝ×ℝ :=
  z.val.2.val

noncomputable def scaledSiteConjugate {a m D : ℕ} {v : ℝ×ℝ}
    (N : ℝ) (z : FlagSite a m D v) : ℝ×ℝ :=
  ((flagSiteConjugate z).1/N,(flagSiteConjugate z).2/N)

noncomputable def flagAveragingMatrix {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) : Matrix (FlagSite a m D v) (FlagSite a m D v) ℝ := fun z w =>
  if z.val.1=w.val.1 then
    (χ (scaledSiteConjugate N z)*χ (scaledSiteConjugate N w)/(ρ*(r*η)^2)) *
    planeTent (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w) *
    planeTent (N*η) (flagSiteConjugate z) (flagSiteConjugate w) *
    separatorMatrix (thresholdLaw (r/N) κ) z.val.2 w.val.2
  else 0

theorem flagAveragingMatrix_posSemidef {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) {ρ N r η κ : ℝ} (hρ : 0 < ρ) (hN : 0 < N)
    (hr : 0 < r) (hκ : 0 < κ) :
    (flagAveragingMatrix (a:=a) (m:=m) (D:=D) (v:=v) χ ρ N r η κ).PosSemidef := by
  classical
  have : IsProbabilityMeasure (thresholdLaw (r/N) κ) := thresholdLaw_isProbability (div_pos hr hN) hκ
  have hcut := (real_rankOne_posSemidef (fun z : FlagSite a m D v => χ (scaledSiteConjugate N z))).smul
    (show 0 ≤ (ρ*(r*η)^2)⁻¹ from inv_nonneg.mpr (mul_nonneg hρ.le (sq_nonneg _)))
  have hsep := (separatorMatrix_posSemidef (a:=a) (v:=v) (thresholdLaw (r/N) κ)).submatrix
    (fun z : FlagSite a m D v => z.val.2)
  have htrack := equalityMatrix_posSemidef (fun z : FlagSite a m D v => z.val.1)
  let M : Matrix (FlagSite a m D v) (FlagSite a m D v) ℝ :=
    Matrix.hadamard (Matrix.hadamard (Matrix.hadamard (Matrix.hadamard
      ((ρ*(r*η)^2)⁻¹ • (fun (z w : FlagSite a m D v) =>
        χ (scaledSiteConjugate N z)*χ (scaledSiteConjugate N w)))
      (fun z w => planeTent (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w)))
      (fun z w => planeTent (N*η) (flagSiteConjugate z) (flagSiteConjugate w)))
      (Matrix.submatrix (separatorMatrix (a:=a) (v:=v) (thresholdLaw (r/N) κ))
        (fun z : FlagSite a m D v => z.val.2) (fun z : FlagSite a m D v => z.val.2)))
      (fun z w => @ite ℝ (z.val.1=w.val.1) (Classical.propDecidable _) 1 0)
  have h : M.PosSemidef :=
    (((hcut.hadamard (planeTent_posSemidef (r/N) flagSiteOrdinary)).hadamard
      (planeTent_posSemidef (N*η) flagSiteConjugate)).hadamard hsep).hadamard htrack
  have he : flagAveragingMatrix (a:=a) (m:=m) (D:=D) (v:=v) χ ρ N r η κ = M := by
    ext z w
    dsimp only [flagAveragingMatrix, M, Matrix.hadamard, Matrix.submatrix, Matrix.of, Equiv.refl, DFunLike.coe, EquivLike.toFunLike, Equiv.instEquivLike, EquivLike.coe, Matrix, id]
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [he]
  exact h

theorem flagAveragingMatrix_cutoff_left {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v)
    (hz : χ (scaledSiteConjugate N z)=0) : flagAveragingMatrix χ ρ N r η κ z w=0 := by
  simp [flagAveragingMatrix,hz]

theorem flagAveragingMatrix_cutoff_right {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v)
    (hw : χ (scaledSiteConjugate N w)=0) : flagAveragingMatrix χ ρ N r η κ z w=0 := by
  simp [flagAveragingMatrix,hw]

theorem flagSite_cutoff_finite {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    {χ : (ℝ×ℝ) → ℝ} (hχ : HasCompactSupport χ) {N : ℝ} (hN : 0 < N) :
    (Function.support (fun z : FlagSite a m D v => χ (scaledSiteConjugate N z))).Finite := by
  obtain ⟨R,hR,hzero⟩ := hχ.exists_pos_le_norm
  refine (flagSiteBox_finite (a:=a) (m:=m) (v:=v) hD (mul_pos hN hR)).subset ?_
  intro z hz
  have hn : ‖scaledSiteConjugate N z‖ < R := lt_of_not_ge (fun h => hz (hzero _ h))
  have h₁ := norm_fst_le (scaledSiteConjugate N z)
  have h₂ := norm_snd_le (scaledSiteConjugate N z)
  simp only [scaledSiteConjugate,Real.norm_eq_abs,abs_div,abs_of_pos hN] at h₁ h₂
  constructor
  · have hh := (div_lt_iff₀ hN).mp (lt_of_le_of_lt h₁ hn)
    nlinarith
  · have hh := (div_lt_iff₀ hN).mp (lt_of_le_of_lt h₂ hn)
    nlinarith

theorem flagAveragingMatrix_finite_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    {χ : (ℝ×ℝ) → ℝ} (hχ : HasCompactSupport χ) {N : ℝ} (hN : 0 < N) :
    ∃ S : Finset (FlagSite a m D v), ∀ ρ r η κ z w,
      z∉S ∨ w∉S → flagAveragingMatrix χ ρ N r η κ z w=0 := by
  let S := (flagSite_cutoff_finite (a:=a) (m:=m) (v:=v) hD hχ hN).toFinset
  refine ⟨S,fun ρ r η κ z w hz => ?_⟩
  rcases hz with hz|hw
  · apply flagAveragingMatrix_cutoff_left
    simpa only [S,Set.Finite.mem_toFinset,Function.mem_support,not_not] using hz
  · apply flagAveragingMatrix_cutoff_right
    simpa only [S,Set.Finite.mem_toFinset,Function.mem_support,not_not] using hw

end FlagAveragingMatrices

section AveragingRowBounds
open Classical MeasureTheory

theorem tentFactor_ne_zero {s d : ℝ} (hs : 0 < s) :
    max (1-|d/s|) 0 ≠ 0 ↔ |d| < s := by
  rw [ne_eq,max_eq_right_iff,not_le,abs_div,abs_of_pos hs]
  have he : 0 < 1-|d|/s ↔ |d|/s < 1 := by constructor <;> intro h <;> linarith
  rw [he,div_lt_iff₀ hs,one_mul]

theorem planeTent_ne_zero {s : ℝ} (hs : 0 < s) (x y : ℝ×ℝ) :
    planeTent s x y ≠ 0 ↔ |x.1-y.1|<s ∧ |x.2-y.2|<s := by
  rw [planeTent,mul_ne_zero_iff,tentFactor_ne_zero hs,tentFactor_ne_zero hs]

theorem flagAveragingMatrix_localization {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ κ : ℝ) {N r η : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hη : 0 < η) (z w : FlagSite a m D v)
    (hw : flagAveragingMatrix χ ρ N r η κ z w ≠ 0) :
    w.val.1=z.val.1 ∧ w∈flagWindow
      (z.val.2.val.1-r/N,z.val.2.val.2-r/N)
      ((flagSiteConjugate z).1-N*η,(flagSiteConjugate z).2-N*η) (2*(r/N)) (2*(N*η)) := by
  have ht : z.val.1=w.val.1 := by
    by_contra hh
    simp [flagAveragingMatrix,hh] at hw
  have hk₁ : planeTent (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w) ≠ 0 := by
    intro he
    simp [flagAveragingMatrix,he] at hw
  have hk₂ : planeTent (N*η) (flagSiteConjugate z) (flagSiteConjugate w) ≠ 0 := by
    intro he
    simp [flagAveragingMatrix,he] at hw
  have hx := (planeTent_ne_zero (div_pos hr hN) _ _).mp hk₁
  have hy := (planeTent_ne_zero (mul_pos hN hη) _ _).mp hk₂
  have hx₁ := abs_lt.mp hx.1
  have hx₂ := abs_lt.mp hx.2
  have hy₁ := abs_lt.mp hy.1
  have hy₂ := abs_lt.mp hy.2
  refine ⟨ht.symm,?_,?_,?_,?_⟩ <;>
    simp only [flagSiteOrdinary] at hx₁ hx₂ <;> constructor <;> linarith

theorem flagAveragingMatrix_row_card {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (χ : (ℝ×ℝ) → ℝ) (ρ κ : ℝ) {N r η : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hη : 0 < η) (z : FlagSite a m D v) (S : Finset (FlagSite a m D v))
    (hS : ∀w∈S,flagAveragingMatrix χ ρ N r η κ z w ≠ 0) :
    (S.card:ℝ) ≤ (4*(D:ℝ)^2*r*η+2)^2 := by
  have hloc := fun w hw => flagAveragingMatrix_localization χ ρ κ hN hr hη z w (hS w hw)
  have hc := flagWindow_card_bound hD z.val.1
    (show 0 ≤ 2*(r/N) by positivity) (show 0 < 2*(N*η) by positivity) S
    (fun w hw => (hloc w hw).1) (fun w hw => (hloc w hw).2)
  have he : (D:ℝ)^2*(2*(r/N))*(2*(N*η))+2=4*(D:ℝ)^2*r*η+2 := by
    field_simp
    ring
  rwa [he] at hc

theorem flagAveragingMatrix_entry_bounds {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N r η κ : ℝ} (hρ : 0 < ρ) (hN : 0 < N) (hr : 0 < r)
    (hη : 0 < η) (hκ : 0 < κ) (z w : FlagSite a m D v) :
    0 ≤ flagAveragingMatrix χ ρ N r η κ z w ∧
    flagAveragingMatrix χ ρ N r η κ z w ≤ (ρ*(r*η)^2)⁻¹ := by
  have : IsProbabilityMeasure (thresholdLaw (r/N) κ) := thresholdLaw_isProbability (div_pos hr hN) hκ
  have hp := separatorMatrix_bounds (thresholdLaw (r/N) κ) z.val.2 w.val.2
  have hk₁ := planeTent_nonneg (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w)
  have hk₂ := planeTent_nonneg (N*η) (flagSiteConjugate z) (flagSiteConjugate w)
  have hk₁' := planeTent_le_one (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w)
  have hk₂' := planeTent_le_one (N*η) (flagSiteConjugate z) (flagSiteConjugate w)
  have hχz := hχ (scaledSiteConjugate N z)
  have hχw := hχ (scaledSiteConjugate N w)
  have hd : 0 < ρ*(r*η)^2 := mul_pos hρ (sq_pos_of_pos (mul_pos hr hη))
  unfold flagAveragingMatrix
  split_ifs
  · constructor
    · exact mul_nonneg (mul_nonneg (mul_nonneg
        (div_nonneg (mul_nonneg hχz.1 hχw.1) hd.le) hk₁) hk₂) hp.1
    · have hc : χ (scaledSiteConjugate N z)*χ (scaledSiteConjugate N w) ≤ 1 :=
        (mul_le_mul hχz.2 hχw.2 hχw.1 zero_le_one).trans_eq (one_mul 1)
      calc
        _ ≤ (1/(ρ*(r*η)^2))*1*1*1 := by gcongr <;> first | exact hp.1 | exact hp.2
        _ = _ := by ring
  · exact ⟨le_rfl,inv_nonneg.mpr hd.le⟩

theorem flagAveragingMatrix_row_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N r η κ : ℝ} (hρ : 0 < ρ) (hN : 0 < N) (hr : 0 < r)
    (hη : 0 < η) (hκ : 0 < κ) (z : FlagSite a m D v) (S : Finset (FlagSite a m D v)) :
    ∑w∈S,(flagAveragingMatrix χ ρ N r η κ z w)^2 ≤
      (4*(D:ℝ)^2*r*η+2)^2 / (ρ*(r*η)^2)^2 := by
  let T := S.filter (fun w => flagAveragingMatrix χ ρ N r η κ z w ≠ 0)
  have he : (∑w∈S,(flagAveragingMatrix χ ρ N r η κ z w)^2)=
      ∑w∈T,(flagAveragingMatrix χ ρ N r η κ z w)^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w hw hwt
    have hh : flagAveragingMatrix χ ρ N r η κ z w=0 := by simpa [T,hw] using hwt
    simp [hh]
  rw [he]
  have hc := flagAveragingMatrix_row_card hD χ ρ κ hN hr hη z T
    (fun w hw => (Finset.mem_filter.mp hw).2)
  have hb (w : FlagSite a m D v) :
      (flagAveragingMatrix χ ρ N r η κ z w)^2 ≤ ((ρ*(r*η)^2)⁻¹)^2 := by
    have hh := flagAveragingMatrix_entry_bounds χ hχ hρ hN hr hη hκ z w
    exact pow_le_pow_left₀ hh.1 hh.2 2
  calc
    _ ≤ ∑_w∈T,((ρ*(r*η)^2)⁻¹)^2 := Finset.sum_le_sum (fun w _ => hb w)
    _ = (T.card:ℝ)*((ρ*(r*η)^2)⁻¹)^2 := by simp
    _ ≤ (4*(D:ℝ)^2*r*η+2)^2*((ρ*(r*η)^2)⁻¹)^2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by rw [div_eq_mul_inv,inv_pow]

end AveragingRowBounds

end SimpleAmenable
end
end

end OAI
