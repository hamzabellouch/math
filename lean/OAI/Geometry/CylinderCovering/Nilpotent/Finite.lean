import OAI.Geometry.CylinderCovering.Nilpotent.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.Construction
import OAI.Geometry.CylinderCovering.Nilpotent.C1
import OAI.Geometry.CylinderCovering.Nilpotent.Field

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CylinderCovering.Nilpotent
open RuledApproximation

lemma height_continuous (k : ℝ) : Continuous (height k) := by
  unfold height a v
  fun_prop

lemma height_le_uniform (k : ℝ) {p : ℝ} (hp : |p| ≤ 1) :
    height k p ≤ 1/2 + k^2/8 + k^3 := by
  have ha := (a_bounds hp).2
  have hm := mul_le_mul_of_nonneg_left ha (sq_nonneg k)
  unfold height
  nlinarith

lemma truncatedLabels_isCompact (k ρ : ℝ) : IsCompact (truncatedLabels k ρ) := by
  let P : Set (ℝ × ℝ) := {z | |z.1| ≤ 1 ∧ ρ ≤ z.2 ∧ z.2 ≤ height k z.1}
  have hPc : IsClosed P := by
    apply IsClosed.inter
    · exact isClosed_le (continuous_fst.abs) continuous_const
    · exact (isClosed_le continuous_const continuous_snd).inter
        (isClosed_le continuous_snd ((height_continuous k).comp continuous_fst))
  have hPb : P ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc ρ (1/2+k^2/8+k^3) := by
    intro z hz
    exact ⟨abs_le.mp hz.1, hz.2.1, hz.2.2.trans (height_le_uniform k hz.1)⟩
  have hP : IsCompact P := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hPc hPb
  have he : truncatedLabels k ρ = (fun z : ℝ × ℝ => vec2 (z.1*z.2) z.2) '' P := by
    ext b
    constructor
    · rintro ⟨p,t,hp,ht,htH,rfl⟩
      exact ⟨(p,t),⟨hp,ht,htH⟩,rfl⟩
    · rintro ⟨⟨p,t⟩,⟨hp,ht,htH⟩,rfl⟩
      exact ⟨p,t,hp,ht,htH,rfl⟩
  rw [he]
  apply hP.image
  unfold vec2
  fun_prop

lemma truncatedLabels_upper {k ρ : ℝ} (hρ : 0 < ρ) :
    truncatedLabels k ρ ⊆ {b : Plane | 0 < b 1} := by
  rintro b ⟨p,t,hp,ht,htH,rfl⟩
  exact lt_of_lt_of_le hρ ht

lemma angularField_contDiffOn (κ : ℝ) :
    ContDiffOn ℝ ∞ (angularField κ) {b : Plane | 0 < b 1} := by
  intro b hb
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_euclidean.mpr
  intro i
  have hr : ContDiffAt ℝ ∞ (fun b : Plane => b 0/b 1) b :=
    (by fun_prop : ContDiffAt ℝ ∞ (fun b : Plane => b 0) b).div
      (by fun_prop) (ne_of_gt hb)
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun b : Plane => κ*((1+(b 0/b 1)^2)/4)) b
    exact contDiffAt_const.mul ((contDiffAt_const.add (hr.pow 2)).div_const 4)
  · change ContDiffAt ℝ ∞ (fun b : Plane => κ*((b 0/b 1)/2)) b
    exact contDiffAt_const.mul (hr.div_const 2)

lemma angularField_smoothNear (κ k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    SmoothNear 1 (truncatedLabels k ρ) (angularField κ) := by
  refine ⟨{b : Plane | 0 < b 1}, isOpen_lt continuous_const (by fun_prop),
    truncatedLabels_upper hρ, ?_⟩
  exact (angularField_contDiffOn κ).of_le (by norm_num)

lemma angularField_radial (κ p : ℝ) {t : ℝ} (ht : t ≠ 0) :
    angularField κ (vec2 (p*t) t) = vec2 (κ*v p) (κ*w p) := by
  simp [angularField,vec2,mul_div_cancel_right₀ _ ht]

lemma signedSweep_subset_apex_union (κ k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    signedSweep κ k ⊆ apexSweep κ ρ ∪ physicalRuled 1 (truncatedLabels k ρ)
      (angularField κ) 1 := by
  rintro z ⟨s,p,t,hs,hp,ht,htH,rfl⟩
  by_cases htr : t ≤ ρ
  · exact Or.inl ⟨s,p,t,hs,hp,ht,htr,rfl⟩
  · apply Or.inr
    have htpos : 0 < t := hρ.trans (lt_of_not_ge htr)
    refine ⟨vec2 (p*t) t,⟨p,t,hp,le_of_lt (lt_of_not_ge htr),htH,rfl⟩,
      s,hs,?_⟩
    rw [angularField_radial κ p htpos.ne']
    ext i
    fin_cases i <;> simp [vec3,vec2] <;> ring

lemma angularField_square_zero (κ : ℝ) {b : Plane} (hb : 0 < b 1) :
    (fderiv ℝ (angularField κ) b).comp (fderiv ℝ (angularField κ) b) = 0 := by
  have he : signedField 1 κ = angularField κ := by
    funext z
    simp [signedField, angularField]
  rw [← he]
  exact signedField_fderiv_square_zero 1 κ hb.ne'

lemma truncated_physical_cover (κ k : ℝ) {h ρ ε : ℝ}
    (hh : 0 < h) (hρ : 0 < ρ) (hε : 0 < ε) :
    HasFiniteCover Cylinder.parallelogram
      (physicalRuled h (truncatedLabels k ρ) (angularField κ) 1)
      (h * (∫ b in truncatedLabels k ρ, physicalWeight h (angularField κ b)) + ε) := by
  obtain ⟨n,C,hC,hcov,hcost⟩ := nilpotent_physical_cover hh
    (truncatedLabels_isCompact k ρ) (angularField_smoothNear κ k hρ)
    (fun b hb => angularField_square_zero κ (truncatedLabels_upper hρ hb)) hε
  refine ⟨n,C,?_,hcov,hcost⟩
  intro i
  obtain ⟨T,g,hT,hEq⟩ := hC i
  rw [hEq]
  exact projectedCylinder_parallelogram hh g hT.parallelogram

lemma physical_second_cover {S : Set Space} {B h a : ℝ}
    (hS : HasFiniteCover Cylinder.parallelogram (firstPhysicalMap h '' S) B) :
    HasFiniteCover Cylinder.parallelogram (secondPhysicalMap h a '' S) B := by
  have hc := (hS.isometry swapReflect.toIsometryEquiv).isometry
    (IsometryEquiv.addLeft (vec3 0 0 (h*a)))
  change HasFiniteCover Cylinder.parallelogram
    ((fun z => vec3 0 0 (h*a)+z) '' (swapReflect '' (firstPhysicalMap h '' S))) B at hc
  have he : ((fun z => vec3 0 0 (h*a)+z) '' (swapReflect '' (firstPhysicalMap h '' S))) =
      secondPhysicalMap h a '' S := by
    rw [← image_comp, ← image_comp]
    congr 1
    funext z
    exact (physicalMaps_relation h a z).symm
  rwa [he] at hc

lemma lowerSweep_mem_signed (k x y z : ℝ) (hS : InLowerSweep k x y z) :
    vec3 x y z ∈ signedSweep k k := by
  obtain ⟨p,t,hx,hp,ht,htH,hy,hz⟩ := hS
  refine ⟨x,p,t,hx,hp,ht,htH,?_⟩
  ext i
  fin_cases i <;> simp [vec3] <;> nlinarith

lemma upperSweep_mem_signed (k x y z : ℝ) (hS : InUpperSweep k x y z) :
    vec3 y x (1-z) ∈ signedSweep (-k) k := by
  obtain ⟨p,t,hy,hp,ht,htH,hx,hz⟩ := hS
  refine ⟨y,p,t,hy,hp,ht,htH,?_⟩
  ext i
  fin_cases i <;> simp [vec3] <;> nlinarith

lemma tetrahedron_subset_signed_sweeps {k : ℝ} (hk : 0 < k) (hk1 : k < 1) :
    tetrahedron ⊆ firstPhysicalMap (Real.sqrt 2) '' signedSweep k k ∪
      secondPhysicalMap (Real.sqrt 2) 1 '' signedSweep (-k) k := by
  rintro z ⟨t,ht0,ht1,hx,hy,hz⟩
  rcases sweep_cover hk hk1 ⟨ht0,ht1,hx,hy⟩ with hL | hU
  · left
    refine ⟨vec3 (z 0) (z 1) t, lowerSweep_mem_signed k _ _ _ hL, ?_⟩
    ext i
    fin_cases i <;> simp [firstPhysicalMap,vec3,hz]
  · right
    refine ⟨vec3 (z 1) (z 0) (1-t), upperSweep_mem_signed k _ _ _ hU, ?_⟩
    ext i
    fin_cases i <;> simp [secondPhysicalMap,vec3,hz]

lemma complete_signed_cover_of_estimates (κ k I : ℝ) {h ρ ε : ℝ}
    (hh : 0 < h) (hρ : 0 < ρ) (hε : 0 < ε)
    (hI : (∫ b in truncatedLabels k ρ, physicalWeight h (angularField κ b)) ≤ I)
    (hA : HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap h '' apexSweep κ ρ) (h*ε/2)) :
    HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap h '' signedSweep κ k) (h*(I+ε)) := by
  have hT := truncated_physical_cover κ k hh hρ
    (show 0 < h*ε/2 by positivity)
  apply (hA.union hT).mono
  · have hs := Set.image_mono (f := firstPhysicalMap h) (signedSweep_subset_apex_union κ k hρ)
    rw [image_union, firstPhysicalMap_ruled] at hs
    exact hs
  · have hmul := mul_le_mul_of_nonneg_left hI hh.le
    linarith

lemma finite_counterexample_of_signed_covers {k I ε : ℝ}
    (hk : 0 < k) (hk1 : k < 1) (hslack : I+ε < 1/4)
    (hpos : HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap (Real.sqrt 2) '' signedSweep k k) (Real.sqrt 2*(I+ε)))
    (hneg : HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap (Real.sqrt 2) '' signedSweep (-k) k) (Real.sqrt 2*(I+ε))) :
    ∃ n : ℕ, ∃ C : Fin n → Cylinder,
      (∀ i, (C i).parallelogram) ∧ tetrahedron ⊆ familySet C ∧
      familyArea C < Real.sqrt 2/2 := by
  have hsecond := physical_second_cover (a := 1) hneg
  obtain ⟨n,C,hC,hcov,hcost⟩ := (hpos.union hsecond).mono
    (tetrahedron_subset_signed_sweeps hk hk1) (le_refl _)
  refine ⟨n,C,hC,hcov,?_⟩
  have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlt := mul_lt_mul_of_pos_left hslack hroot
  linarith

lemma exists_padding_and_collar {k I : ℝ} (hk : 0 < k) (hI : I < 1/4) :
    ∃ ε ρ : ℝ, 0 < ε ∧ I+ε < 1/4 ∧ 0 < ρ ∧ ρ < 1/2 ∧
      16*(1+k/2)^2*ρ < ε/2 := by
  let ε : ℝ := (1/4-I)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hden : 0 < 32*(1+k/2)^2 := by positivity
  obtain ⟨ρ,hρ,hρupper⟩ := exists_between
    (lt_min (by norm_num : (0 : ℝ) < 1/2) (div_pos hε hden))
  refine ⟨ε,ρ,hε,?_,hρ,(lt_min_iff.mp hρupper).1,?_⟩
  · dsimp [ε]; linarith
  · have hmul := (lt_div_iff₀ hden).mp (lt_min_iff.mp hρupper).2
    nlinarith

end CylinderCovering.Nilpotent

end

end OAI
