import OAI.Geometry.Immersion.ClosedSurface.NormalProjection
import OAI.Geometry.Immersion.ClosedSurface.NormalJets

namespace OAI

/-! Smooth orthonormal frames obtained by interpolating non-antipodal plane directions. -/
noncomputable section
open scoped Matrix ContDiff

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

def normalize (v : Vec) : Vec := (Real.sqrt (v ⬝ᵥ v))⁻¹ • v

lemma dot_self_pos {v : Vec} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have hn : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  exact hn.lt_of_ne' ((dotProduct_self_eq_zero).not.mpr hv)

lemma normalize_unit {v : Vec} (hv : v ≠ 0) : normalize v ⬝ᵥ normalize v = 1 := by
  have hp := dot_self_pos hv
  have hs : Real.sqrt (v ⬝ᵥ v) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  simp only [normalize, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have heq := Real.sq_sqrt hp.le
  field_simp
  nlinarith [heq]

lemma dot_normalize_zero {v w : Vec} (h : w ⬝ᵥ v = 0) : w ⬝ᵥ normalize v = 0 := by
  simp [normalize, dotProduct_smul, h]

lemma normalize_nonzero {v : Vec} (hv : v ≠ 0) : normalize v ≠ 0 := by
  intro hz
  have hu := normalize_unit hv
  rw [hz] at hu
  norm_num at hu

def blend (u v : Vec) (t : ℝ) : Vec := (1 - t) • u + t • v

lemma blend_nonzero_of_not_opposite {u v : Vec} {t : ℝ}
    (hv : v ≠ 0) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu : t = 0 → u ≠ 0)
    (hanti : t < 1 → ∀ r : ℝ, 0 < r → u ≠ -r • v) : blend u v t ≠ 0 := by
  by_cases ht0 : t = 0
  · simpa [blend, ht0] using hu ht0
  by_cases ht1 : t = 1
  · simpa [blend, ht1] using hv
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
  have hden : 0 < 1 - t := sub_pos.mpr htlt
  intro hz
  apply hanti htlt (t / (1 - t)) (div_pos htpos hden)
  ext i
  have hi : (1 - t) * u i + t * v i = 0 := congrFun hz i
  change u i = -(t / (1 - t)) * v i
  field_simp [hden.ne']
  linear_combination hi

lemma blend_nonzero {u v : Vec} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (huv : -1 < u ⬝ᵥ v) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : blend u v t ≠ 0 := by
  by_cases ht0 : t = 0
  · intro hz
    have huz : u = 0 := by simpa [blend, ht0] using hz
    rw [huz] at hu
    norm_num at hu
  by_cases ht1 : t = 1
  · intro hz
    have hvz : v = 0 := by simpa [blend, ht1] using hz
    rw [hvz] at hv
    norm_num at hv
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
  have hs : blend u v t ⬝ᵥ blend u v t =
      (1 - 2 * t) ^ 2 + 2 * t * (1 - t) * (1 + u ⬝ᵥ v) := by
    simp only [blend, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hu, hv, dotProduct_comm v u]
    ring
  have hp : 0 < (1 - 2 * t) ^ 2 + 2 * t * (1 - t) * (1 + u ⬝ᵥ v) :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos
      (mul_pos (mul_pos (by norm_num) htpos) (sub_pos.mpr htlt)) (by linarith))
  intro hz
  rw [hz] at hs
  simp only [dotProduct_zero] at hs
  linarith

def first (u v : Vec) (t : ℝ) : Vec := normalize (blend u v t)

lemma first_unit {u v : Vec} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (huv : -1 < u ⬝ᵥ v) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    first u v t ⬝ᵥ first u v t = 1 := normalize_unit (blend_nonzero hu hv huv ht)

lemma first_perp {u v w : Vec} (hu : w ⬝ᵥ u = 0) (hv : w ⬝ᵥ v = 0) (t : ℝ) :
    w ⬝ᵥ first u v t = 0 := by
  apply dot_normalize_zero
  simp [blend, dotProduct_add, dotProduct_smul, hu, hv]

lemma normalize_of_unit {v : Vec} (hv : v ⬝ᵥ v = 1) : normalize v = v := by
  simp [normalize, hv]

lemma first_zero {u v : Vec} (hu : u ⬝ᵥ u = 1) : first u v 0 = u := by
  simpa [first, blend] using normalize_of_unit hu

lemma first_one {u v : Vec} (hv : v ⬝ᵥ v = 1) : first u v 1 = v := by
  simpa [first, blend] using normalize_of_unit hv

def second (Y C u v : Vec) (t : ℝ) : Vec := unitPerp Y C (first u v t)

theorem frame_orthonormal_of_nonzero {Y C u v : Vec} {t : ℝ}
    (hD : gramDet Y C ≠ 0) (hn : blend u v t ≠ 0)
    (hYu : Y ⬝ᵥ u = 0) (hYv : Y ⬝ᵥ v = 0)
    (hCu : C ⬝ᵥ u = 0) (hCv : C ⬝ᵥ v = 0) :
    first u v t ⬝ᵥ first u v t = 1 ∧
      second Y C u v t ⬝ᵥ second Y C u v t = 1 ∧
      first u v t ⬝ᵥ second Y C u v t = 0 ∧
      Y ⬝ᵥ first u v t = 0 ∧ C ⬝ᵥ first u v t = 0 ∧
      Y ⬝ᵥ second Y C u v t = 0 ∧ C ⬝ᵥ second Y C u v t = 0 := by
  have hfirst := normalize_unit hn
  have hnonzero := normalize_nonzero hn
  have hY := first_perp hYu hYv t
  have hC := first_perp hCu hCv t
  have hsecond := unitPerp_unit hD hnonzero hY hC
  have horth := unitPerp_orthogonal Y C (first u v t)
  exact ⟨hfirst, hsecond, horth.2.2, hY, hC, horth.1, horth.2.1⟩

theorem frame_orthonormal {Y C u v : Vec} {t : ℝ}
    (hD : gramDet Y C ≠ 0) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (huv : -1 < u ⬝ᵥ v) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hYu : Y ⬝ᵥ u = 0) (hYv : Y ⬝ᵥ v = 0)
    (hCu : C ⬝ᵥ u = 0) (hCv : C ⬝ᵥ v = 0) :
    first u v t ⬝ᵥ first u v t = 1 ∧
      second Y C u v t ⬝ᵥ second Y C u v t = 1 ∧
      first u v t ⬝ᵥ second Y C u v t = 0 ∧
      Y ⬝ᵥ first u v t = 0 ∧ C ⬝ᵥ first u v t = 0 ∧
      Y ⬝ᵥ second Y C u v t = 0 ∧ C ⬝ᵥ second Y C u v t = 0 := by
  have hfirst := first_unit hu hv huv ht
  have hnonzero : first u v t ≠ 0 := by
    intro hz
    rw [hz] at hfirst
    norm_num at hfirst
  have hY := first_perp hYu hYv t
  have hC := first_perp hCu hCv t
  have hsecond := unitPerp_unit hD hnonzero hY hC
  have horth := unitPerp_orthogonal Y C (first u v t)
  exact ⟨hfirst, hsecond, horth.2.2, hY, hC, horth.1, horth.2.1⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalize_smoothAt {v : E → Vec} {x : E} (hv : ContDiffAt ℝ ∞ v x) (hn : v x ≠ 0) :
    ContDiffAt ℝ ∞ (fun z => normalize (v z)) x := by
  have hd : ContDiffAt ℝ ∞ (fun z => v z ⬝ᵥ v z) x :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hp := dot_self_pos hn
  exact ((hd.sqrt hp.ne').inv (Real.sqrt_pos.mpr hp).ne').smul hv

lemma first_smoothAt {u v : E → Vec} {t : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x) (ht : ContDiffAt ℝ ∞ t x)
    (hu1 : u x ⬝ᵥ u x = 1) (hv1 : v x ⬝ᵥ v x = 1)
    (huv : -1 < u x ⬝ᵥ v x) (ht01 : t x ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun z => first (u z) (v z) (t z)) x :=
  normalize_smoothAt (((contDiffAt_const.sub ht).smul hu).add (ht.smul hv))
    (blend_nonzero hu1 hv1 huv ht01)

lemma first_smoothAt_of_nonzero {u v : E → Vec} {t : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x) (ht : ContDiffAt ℝ ∞ t x)
    (hn : blend (u x) (v x) (t x) ≠ 0) :
    ContDiffAt ℝ ∞ (fun z => first (u z) (v z) (t z)) x :=
  normalize_smoothAt (((contDiffAt_const.sub ht).smul hu).add (ht.smul hv)) hn

lemma second_smoothAt {Y C u v : E → Vec} {t : E → ℝ} {x : E}
    (hY : ContDiffAt ℝ ∞ Y x) (hC : ContDiffAt ℝ ∞ C x)
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x) (ht : ContDiffAt ℝ ∞ t x)
    (hD : gramDet (Y x) (C x) ≠ 0)
    (hu1 : u x ⬝ᵥ u x = 1) (hv1 : v x ⬝ᵥ v x = 1)
    (huv : -1 < u x ⬝ᵥ v x) (ht01 : t x ∈ Set.Icc (0 : ℝ) 1)
    (hYu : Y x ⬝ᵥ u x = 0) (hYv : Y x ⬝ᵥ v x = 0)
    (hCu : C x ⬝ᵥ u x = 0) (hCv : C x ⬝ᵥ v x = 0) :
    ContDiffAt ℝ ∞ (fun z => second (Y z) (C z) (u z) (v z) (t z)) x := by
  have hfirst := first_smoothAt hu hv ht hu1 hv1 huv ht01
  have hnonzero : first (u x) (v x) (t x) ≠ 0 := by
    intro hz
    have he := first_unit hu1 hv1 huv ht01
    rw [hz] at he
    norm_num at he
  exact contDiffAt_unitPerp hY hC hfirst hD hnonzero
    (first_perp hYu hYv _) (first_perp hCu hCv _)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
