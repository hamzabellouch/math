import Mathlib
import OAI.Geometry.Borsuk.Support.Chambers

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section ChamberPath
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def chamberPath (c u : E) (t : ℝ) : E :=
  ‖(1-t) • u + t • c‖⁻¹ • ((1-t) • u + t • c)

lemma signChamber_smul {Z : Set E} {c u : E} (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : 0 < t) : t • u ∈ signChamber Z c := by
  intro z hz
  rw [real_inner_smul_left,mul_left_comm]
  exact mul_pos ht (hu z hz)

lemma chamber_interpolation_mem {Z : Set E} {c u : E} (hc : c ∈ safeNormals Z)
    (hu : u ∈ signChamber Z c) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (1-t) • u + t • c ∈ signChamber Z c :=
  signChamber_convex Z c hu (mem_signChamber_self hc) (sub_nonneg.mpr ht.2) ht.1 (by ring)

lemma chamber_interpolation_ne_zero {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : (1-t) • u + t • c ≠ 0 := by
  intro he
  have h := chamber_interpolation_mem hc hu ht c hcZ
  simp [he] at h

lemma chamberPath_norm {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : ‖chamberPath c u t‖ = 1 := by
  have hn := chamber_interpolation_ne_zero hcZ hc hu ht
  simp only [chamberPath,norm_smul,norm_inv,norm_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]

lemma chamberPath_mem {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : chamberPath c u t ∈ signChamber Z c :=
  signChamber_smul (chamber_interpolation_mem hc hu ht)
    (inv_pos.mpr (norm_pos_iff.mpr (chamber_interpolation_ne_zero hcZ hc hu ht)))

lemma chamberPath_zero (c u : E) (hu : ‖u‖ = 1) : chamberPath c u 0 = u := by
  simp [chamberPath,hu]

lemma chamberPath_one (c u : E) (hc : ‖c‖ = 1) : chamberPath c u 1 = c := by
  simp [chamberPath,hc]

lemma chamber_add_ne_zero {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c) : c+u ≠ 0 := by
  intro he
  have h := hu c hcZ
  have hn := hc c hcZ
  have hei : ⟪c,c⟫ + ⟪u,c⟫ = 0 := by rw [← inner_add_left,he,inner_zero_left]
  have hei' : ⟪u,c⟫ = -⟪c,c⟫ := by linarith
  rw [hei'] at h
  nlinarith [sq_nonneg ⟪c,c⟫]

lemma chamberPath_continuousOn {Z : Set E} {c : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) : ContinuousOn (fun p : ℝ × E => chamberPath c p.2 p.1)
      (Set.Icc (0:ℝ) 1 ×ˢ signChamber Z c) := by
  have hs : Continuous (fun p : ℝ × E => (1-p.1) • p.2 + p.1 • c) :=
    ((continuous_const.sub continuous_fst).smul continuous_snd).add
      (continuous_fst.smul continuous_const)
  exact (hs.norm.continuousOn.inv₀ (fun p hp => norm_ne_zero_iff.mpr
    (chamber_interpolation_ne_zero hcZ hc hp.2 hp.1))).smul hs.continuousOn

end ChamberPath
end BorsukNine

end OAI
