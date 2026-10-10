import OAI.NumberTheory.TotientAsymptotic.GeometricContractedFamily
import OAI.NumberTheory.TotientAsymptotic.InverseCubeMargin

namespace OAI

/-! The positive-volume family retains half of every margin in its unit grid. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def relaxedGeometricFamily (m n : ℕ) (B c : ℝ) : Set (Fin n → ℝ) :=
  contractedPrefix n (B/(1+rowContractionError m/2))
    (fun i => 1+rowContractionError (m-(i.val+1))/2) ∩
    {v | (∀ i,c*(rho^(m-i.val))⁻¹ ≤ v i) ∧
      ∀ i j,i < j → v j ≤ v i/(1+rowContractionError (m-(i.val+1))/2)}

lemma geometric_family_unit_cube {m n : ℕ} {B c : ℝ} (hn : n ≤ m)
    {u v : Fin n → ℝ} (hu : u ∈ geometricContractedFamily m n B c)
    (hdist : ∀ i,|u i-v i| ≤ 1)
    (hlarge : ∀ i,100*((m-i.val:ℕ):ℝ)^5 ≤ u i)
    (hB : 100*(m+1:ℝ)^5 ≤ B) :
    v ∈ relaxedGeometricFamily m n B (c/2) := by
  have hi (i : Fin n) : 1 ≤ m-i.val := by have := i.isLt; omega
  have herr (i : Fin n) : rowContractionError (m-(i.val+1)) =
      1/(5*((m-i.val:ℕ):ℝ)^3) := by
    unfold rowContractionError
    have he : m-(i.val+1)+1=m-i.val := by have := i.isLt; omega
    have he' : ((m-(i.val+1):ℕ):ℝ)+1=((m-i.val:ℕ):ℝ) := by
      exact_mod_cast he
    rw [he']
  have hhalf (i : Fin n) : rowContractionError (m-(i.val+1))/2 =
      1/(10*((m-i.val:ℕ):ℝ)^3) := by rw [herr]; ring
  have hmargin (i : Fin n) := inverse_cube_margin (hi i) (hlarge i) (hdist i)
  have hpos (i : Fin n) : 0 < v i := (hmargin i).1
  have hgap (i j : Fin n) (hij : i < j) :
      v j ≤ v i/(1+rowContractionError (m-(i.val+1))/2) := by
    let r := (1+rowContractionError (m-(i.val+1)))⁻¹
    let e := (1+rowContractionError (m-(i.val+1))/2)⁻¹-r
    have hr : 0 ≤ r := by
      dsimp [r]
      exact inv_nonneg.mpr (by linarith only [rowContractionError_nonneg (m-(i.val+1))])
    have hr1 : r ≤ 1 := by
      apply inv_le_one_of_one_le₀
      linarith only [rowContractionError_nonneg (m-(i.val+1))]
    have he : 2 ≤ e*v i := by
      have hp : (1:ℝ) ≤ ((m-i.val:ℕ):ℝ)^2 :=
        one_le_pow₀ (by exact_mod_cast hi i)
      have hh := (hmargin i).2
      dsimp [e,r]
      rw [hhalf,herr]
      linarith only [hp,hh]
    have hg := strict_gap_cube u v i j hr hr1
      (by simpa only [r,div_eq_mul_inv,mul_comm] using hu.2.2 i j hij) hdist he
    simpa only [e,r,add_sub_cancel,div_eq_mul_inv,mul_comm] using hg
  refine ⟨⟨fun i => (hpos i).le,?_,?_,?_⟩,?_,hgap⟩
  · intro i j hij
    apply (hgap i j hij).trans_lt
    apply div_lt_self (hpos i)
    have he : 0 < rowContractionError (m-(i.val+1)) := by
      unfold rowContractionError
      positivity
    linarith
  · intro i
    let r := (1+rowContractionError (m-(i.val+1)))⁻¹
    let e := (1+rowContractionError (m-(i.val+1))/2)⁻¹-r
    have hr : 0 ≤ r := by
      dsimp [r]
      exact inv_nonneg.mpr (by linarith only [rowContractionError_nonneg (m-(i.val+1))])
    have hr1 : r ≤ 1 := by
      apply inv_le_one_of_one_le₀
      linarith only [rowContractionError_nonneg (m-(i.val+1))]
    have hh := (hmargin i).2
    have hni : ((n-i.val:ℕ):ℝ) ≤ ((m-i.val:ℕ):ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right hn i.val
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg (n-i.val)) hni 2
    have he : ((n-i.val:ℕ):ℝ)^2+1 ≤ e*v i := by
      dsimp [e,r]
      rw [hhalf,herr]
      linarith only [hs,hh]
    have hrw := strict_row_cube u v i hr hr1
      (by simpa only [r,div_eq_mul_inv,mul_comm] using hu.1.2.2.1 i) hdist he
    simpa only [e,r,add_sub_cancel,div_eq_mul_inv,mul_comm] using hrw
  · apply strict_top_cube u v hu.1.2.2.2 hdist
    have he : 1/(5*(m+1:ℝ)^3)/2=1/(10*(m+1:ℝ)^3) := by
      field_simp
      ring
    simpa only [rowContractionError,he] using inverse_cube_top_margin hn hB
  · intro i
    have hh := (le_abs_self _).trans (hdist i)
    have hp : (1:ℝ) ≤ ((m-i.val:ℕ):ℝ)^5 := one_le_pow₀ (by exact_mod_cast hi i)
    have hcu := hu.2.1 i
    have hlu := hlarge i
    nlinarith only [hh,hp,hcu,hlu]

end TotientAsymptotic

end

end OAI
