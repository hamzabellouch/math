import OAI.Analysis.CStarAlgebra.PureInfiniteness.FourChoices

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance deficiencyOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance deficiencyStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

lemma deficiency_eq_sub {d : A} (hd : 0 ≤ d) (hb : d ≤ (1/2 : ℝ) • (1 : A)) :
    deficiency d = (1/2 : ℝ) • (1 : A) - d := by
  have hdsa : IsSelfAdjoint d := .of_nonneg hd
  have hb' : cfc (fun t : ℝ => t) d ≤ cfc (fun _ : ℝ => (1/2 : ℝ)) d := by
    rw [cfc_id' ℝ d hdsa, cfc_const (1/2 : ℝ) d hdsa, Algebra.algebraMap_eq_smul_one]
    exact hb
  have hs := (cfc_le_iff _ _ d continuousOn_id continuousOn_const hdsa).mp hb'
  calc
    deficiency d = cfc (fun t : ℝ => (1/2 : ℝ)-t) d := by
      apply cfc_congr
      intro t ht
      exact max_eq_left (sub_nonneg.mpr (hs t ht))
    _ = cfc (fun _ : ℝ => (1/2 : ℝ)) d - cfc (fun t : ℝ => t) d :=
      cfc_sub _ _ d continuousOn_const continuousOn_id
    _ = (1/2 : ℝ) • (1 : A) - d := by
      rw [cfc_const (1/2 : ℝ) d hdsa, cfc_id' ℝ d hdsa, Algebra.algebraMap_eq_smul_one]

lemma sandwich_zero_eigen {x d : A} (hx : 0 ≤ x) (hd : 0 ≤ d)
    (hdle : d ≤ (1/2 : ℝ) • (1 : A))
    (hU : x * deficiency d * deficiency d * x = 0) : d * x = (1/2 : ℝ) • x := by
  have hQx : deficiency d * x = 0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    simpa only [star_mul, IsSelfAdjoint.of_nonneg hx |>.star_eq,
      deficiency_selfAdjoint d |>.star_eq, mul_assoc] using hU
  rw [deficiency_eq_sub hd hdle, sub_mul, smul_mul_assoc, one_mul] at hQx
  exact (sub_eq_zero.mp hQx).symm

lemma Her_eigen_left {x d k : A} {h : ℝ} (hx : d*x=h•x) (hk : k ∈ Her x) :
    d*k=h•k := by
  have hz : (d-h • (1:A))*x=0 := by
    simp only [sub_mul, smul_mul_assoc, one_mul, hx, sub_self]
  have := Her_killed_left hz hk
  simpa only [sub_mul, smul_mul_assoc, one_mul, sub_eq_zero] using this

lemma firstH_mem_firstX {X : A} (hX : 0 ≤ X) : firstH X ∈ Her (firstX X) :=
  Her_mono_of_mem (cut_mem_cutHer hX (by norm_num : (0:ℝ) ≤ 1/16)
    (by norm_num : (1/16:ℝ) ≤ 3/32)) (ramp_mem_Her_cut hX (by norm_num))

lemma firstK_fixes_H {X : A} (hX : 0 ≤ X) : firstK X * firstH X = firstH X :=
  Her_fixed_left (ramp_mul_cut hX (by norm_num : (0:ℝ) ≤ 3/64)
    (by norm_num : (3/64:ℝ) < 1/16) le_rfl) (firstH_mem_firstX hX)

lemma firstR_fixed_left {X B : A} (hX : 0 ≤ X) (hB : star B * B ∈ Her (firstV X)) :
    firstH X * firstR X B = firstR X B := by
  have hstar : firstH X * star B = star B := by
    apply fixed_left_of_modulus
    simp only [star_star]
    exact Her_fixed_left (firstH_fixes_V hX) hB
  simp only [firstR, mul_smul_comm, ← mul_assoc, hstar]

lemma firstR_inner {X B C : A} (hmod : B * star C = B * star B)
    (hDH : B * star B * firstH X = (1/2 : ℝ) • firstH X) :
    star (firstR X B) * firstR X C = firstH X * firstH X := by
  have hH : star (firstH X) = firstH X := (IsSelfAdjoint.of_nonneg (ramp_nonneg X (by norm_num : (3/32:ℝ) ≤ 1/8))).star_eq
  simp only [firstR, star_smul, star_trivial, star_mul, hH, star_star,
    smul_mul_smul]
  rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  calc
    (2:ℝ) • ((firstH X * B) * (star C * firstH X)) =
      (2:ℝ) • (firstH X * ((B * star C) * firstH X)) := by congr 1; noncomm_ring
    _ = firstH X * firstH X := by rw [hmod, hDH, mul_smul_comm, smul_smul]; norm_num

lemma firstR_orthogonal {X B C : A} (hcross : B * star C = 0) :
    star (firstR X B) * firstR X C = 0 := by
  simp only [firstR, star_smul, star_trivial, star_mul, star_star, smul_mul_smul]
  calc
    _ = (Real.sqrt 2 * Real.sqrt 2) • (star (firstH X) * (B * star C) * firstH X) := by
      congr 1; noncomm_ring
    _ = 0 := by rw [hcross, mul_zero, zero_mul, smul_zero]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance scalingDefectOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance scalingDefectStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

lemma ramp_projection {P : A} (hP : IsStarProjection P) {l u : ℝ} (hl : 0 ≤ l)
    (hlu : l < u) (hu : u ≤ 1) : ramp P l u = P := by
  conv_rhs => rw [← cfcₙ_id ℝ P hP.isSelfAdjoint]
  apply cfcₙ_congr
  intro t ht
  rcases Set.mem_insert_iff.mp (hP.isIdempotentElem.quasispectrum_subset ℝ ht) with ht | ht
  · subst t
    exact rampFn_zero hl
  · have ht : t = 1 := Set.mem_singleton_iff.mp ht
    subst t
    exact rampFn_one hlu hu

lemma cut_projection {P : A} (hP : IsStarProjection P) {l : ℝ} (hl : 0 ≤ l) (hl1 : l ≤ 1) :
    cut P l = (1-l) • P := by
  conv_rhs => rw [← cfcₙ_id ℝ P hP.isSelfAdjoint]
  rw [← cfcₙ_smul (1-l) id P continuousOn_id rfl]
  apply cfcₙ_congr
  intro t ht
  rcases Set.mem_insert_iff.mp (hP.isIdempotentElem.quasispectrum_subset ℝ ht) with ht | ht
  · subst t
    simp [max_eq_right (neg_nonpos.mpr hl)]
  · have ht : t = 1 := Set.mem_singleton_iff.mp ht
    subst t
    simp [max_eq_left (sub_nonneg.mpr hl1)]

lemma scalingDefect_expansion {H r : A} (hH : IsSelfAdjoint H) (hnorm : ‖H‖ ≤ 1) :
    scalingDefect H r = H*H-r*star r-r*scalingComplement H-scalingComplement H*star r := by
  have hb := scalingComplement_mul_self hH hnorm
  simp only [scalingDefect, scalingIsometry, star_add, scalingComplement_selfAdjoint H |>.star_eq,
    add_mul, mul_add]
  rw [hb]
  noncomm_ring

lemma scalingDefect_compress {H K r : A} (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K)
    (hnorm : ‖H‖ ≤ 1) (hKH : K*H=H) (hHr : H*r=r) (hrK : r*K=r) :
    K * scalingDefect H r * K = scalingDefect H r := by
  have hHK : H*K=H := by
    simpa only [star_mul, hH.star_eq, hK.star_eq] using congrArg star hKH
  have hKr : K*r=r := by rw [← hHr, ← mul_assoc, hKH]
  have hsrK : star r*K=star r := by
    simpa only [star_mul, hK.star_eq, star_star] using congrArg star hKr
  have hKsr : K*star r=star r := by
    simpa only [star_mul, hK.star_eq, star_star] using congrArg star hrK
  have hcomm : Commute K H := (show K*H=H*K by rw [hKH,hHK])
  have hbcomm : Commute K (scalingComplement H) := by
    exact ((Commute.one_right K).sub_right (hcomm.mul_right hcomm)).symm.cfcₙ_nnreal NNReal.sqrt |>.symm
  have hleft : K * scalingDefect H r = scalingDefect H r := by
    rw [scalingDefect_expansion hH hnorm]
    simp only [mul_sub, ← mul_assoc, hKH, hKr]
    rw [hbcomm.eq, mul_assoc, hKsr]
  have hright : scalingDefect H r * K = scalingDefect H r := by
    simpa only [star_mul, hK.star_eq, show star (scalingDefect H r) = scalingDefect H r from
      ((IsSelfAdjoint.one A).sub (IsSelfAdjoint.mul_star_self _)).star_eq] using congrArg star hleft
  rw [hleft, hright]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance fourFixedOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance fourFixedStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem four_fixed_impossible {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hV : firstV X ≠ 0)
    (hD : B 0 * star (B 0) ≤ (1/2 : ℝ) • (1 : A))
    (hmod : B 1 * star (B 1) = B 0 * star (B 0))
    (hcross : B 0 * star (B 1) = 0)
    (hHB₀ : firstH X * star (B 0) = star (B 0))
    (hHB₁ : firstH X * star (B 1) = star (B 1))
    (hU : firstU X (B 0) = 0)
    (hD₃ : B 2 * star (B 2) ≤ (1/2 : ℝ) • (1 : A))
    (hc₃ : star (B 2) * B 3 = 0)
    (hm₃ : star (B 2) * B 2 = star (B 3) * B 3)
    (hR : lastR X (B 0) (B 2) = 0)
    (hs₃ : ramp (prospectiveDefect X (B 0)) 0 (1/2) * B 3 = B 3) : False := by
  have hH : IsSelfAdjoint (firstH X) := .of_nonneg (ramp_nonneg X (by norm_num))
  have hK : IsSelfAdjoint (firstK X) := .of_nonneg (ramp_nonneg X (by norm_num))
  have hHnorm : ‖firstH X‖ ≤ 1 := norm_ramp_le_one _ (by norm_num)
  have hHne : firstH X ≠ 0 := by
    intro hz
    apply hV
    simpa only [hz, zero_mul] using (firstH_fixes_V hX).symm
  have hDx : (B 0 * star (B 0)) * firstX X = (1/2 : ℝ) • firstX X :=
    sandwich_zero_eigen (cut_nonneg X _) (mul_star_self_nonneg _) hD hU
  have hDH : (B 0 * star (B 0)) * firstH X = (1/2 : ℝ) • firstH X :=
    Her_eigen_left hDx (firstH_mem_firstX hX)
  have hρ₀ : star (firstR X (B 0)) * firstR X (B 0) = firstH X * firstH X :=
    firstR_inner rfl hDH
  have hρ₁ : star (firstR X (B 1)) * firstR X (B 1) = firstH X * firstH X :=
    firstR_inner rfl (hmod ▸ hDH)
  have hρc : star (firstR X (B 0)) * firstR X (B 1) = 0 := firstR_orthogonal hcross
  have hHr₀ : firstH X * firstR X (B 0) = firstR X (B 0) := by
    simp only [firstR, mul_smul_comm, ← mul_assoc, hHB₀]
  have hHr₁ : firstH X * firstR X (B 1) = firstR X (B 1) := by
    simp only [firstR, mul_smul_comm, ← mul_assoc, hHB₁]
  let P := scalingDefect (firstH X) (firstR X (B 0))
  have hP : IsStarProjection P := scalingDefect_projection hH hHnorm hHr₀ hρ₀
  have hPne : P ≠ 0 := scalingDefect_ne_zero hH hHnorm hHne hHr₁ hρc hρ₁
  have hKH : firstK X * firstH X = firstH X := firstK_fixes_H hX
  have hHK : firstH X * firstK X = firstH X := by
    simpa only [star_mul, hK.star_eq, hH.star_eq] using congrArg star hKH
  have hrK : firstR X (B 0) * firstK X = firstR X (B 0) := by
    simp only [firstR, smul_mul_assoc, mul_assoc, hHK]
  have hP₀ : prospectiveDefect X (B 0) = P := by
    change ramp (firstK X * P * firstK X) 0 1 = P
    rw [scalingDefect_compress hH hK hHnorm hKH hHr₀ hrK]
    exact ramp_projection hP (by norm_num) (by norm_num) le_rfl
  have hx' : lastX X (B 0) = (1/2 : ℝ) • P := by
    simp only [lastX, hP₀, cut_projection hP (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1)]
    norm_num
  have hD₃x : (B 2 * star (B 2)) * lastX X (B 0) = (1/2 : ℝ) • lastX X (B 0) :=
    sandwich_zero_eigen (lastX_nonneg X _) (mul_star_self_nonneg _) hD₃ hR
  have hD₃P : (B 2 * star (B 2)) * P = (1/2 : ℝ) • P := by
    rw [hx', mul_smul_comm, smul_comm] at hD₃x
    exact (smul_right_injective A (by norm_num : (1/2 : ℝ) ≠ 0)) hD₃x
  have hPB : P * B 3 = B 3 := by
    rw [hP₀, ramp_projection hP (by norm_num) (by norm_num) (by norm_num)] at hs₃
    exact hs₃
  exact hPne (last_pair_kills_defect (by norm_num : (1/2 : ℝ) ≠ 0) hPB hc₃ hm₃ hD₃P)

end MainGap

namespace MainGap
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
local instance defectSandwichOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance defectSandwichStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance representedDefectOrder : PartialOrder D := CStarAlgebra.spectralOrder D
local instance representedDefectStarOrder : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D

lemma firstSandwich_single_le {U V w : A} (hV : 0 ≤ V) (η : ℝ) {E : Finset A}
    (hw : w ∈ E) :
    (cut U η * w * CFC.sqrt V) * star (cut U η * w * CFC.sqrt V) ≤
      firstSandwich U V η E := by
  have hsum : w * V * star w ≤ ∑ v ∈ E, v * V * star v :=
    Finset.single_le_sum (fun v _ => star_right_conjugate_nonneg hV v) hw
  have h := conjugate_le_conjugate_of_nonneg hsum (cut_nonneg U η)
  have heq : (cut U η * w * CFC.sqrt V) * star (cut U η * w * CFC.sqrt V) =
      cut U η * (w * V * star w) * cut U η := by
    simp only [star_mul, IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg V) |>.star_eq,
      IsSelfAdjoint.of_nonneg (cut_nonneg U η) |>.star_eq]
    calc
      _ = cut U η * w * (CFC.sqrt V * CFC.sqrt V) * star w * cut U η := by noncomm_ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self V hV]; noncomm_ring
  rw [heq]
  exact h

lemma represented_single_sq_le (π : A →⋆ₐ[ℂ] D) {U V w : A} (hV : 0 ≤ V)
    (η : ℝ) {E : Finset A} (hw : w ∈ E) :
    ‖π (cut U η * w * CFC.sqrt V)‖ ^ 2 ≤ ‖π (firstSandwich U V η E)‖ := by
  have h := OrderHomClass.mono π (firstSandwich_single_le (U := U) hV η hw)
  rw [map_mul, map_star] at h
  simpa only [CStarRing.norm_self_mul_star, sq] using
    CStarAlgebra.norm_le_norm_of_le_of_nonneg h (mul_star_self_nonneg _)

lemma represented_mixed_estimate (π : A →⋆ₐ[ℂ] D) {U V w : A} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {η : ℝ} (hη : 0 < η) {E : Finset A} (hw : w ∈ E)
    (hD : ‖π (firstSandwich U V η E)‖ ≤ 2*η) :
    ‖π (U*w*V)‖ ≤ Real.sqrt (2*η) * ‖CFC.sqrt V‖ + η*‖w‖*‖V‖ := by
  have hr : ‖π (cut U η * w * CFC.sqrt V)‖ ≤ Real.sqrt (2*η) := by
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
      ((represented_single_sq_le π hV η hw).trans hD)
  have hsplit : U*w*V = (cut U η * w * CFC.sqrt V) * CFC.sqrt V +
      (U-cut U η)*w*V := by
    rw [mul_assoc (cut U η * w), CFC.sqrt_mul_sqrt_self V hV]
    noncomm_ring
  rw [hsplit, map_add]
  apply norm_add_le _ _ |>.trans
  apply add_le_add
  · rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul hr (NonUnitalStarAlgHom.norm_apply_le π _) (norm_nonneg _) (by positivity))
  · rw [map_mul, map_mul]
    calc
      ‖(π (U-cut U η) * π w) * π V‖ ≤ ‖π (U-cut U η)‖ * ‖π w‖ * ‖π V‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ η*‖w‖*‖V‖ := mul_le_mul
        (mul_le_mul ((NonUnitalStarAlgHom.norm_apply_le π _).trans (norm_sub_cut_le hU hη.le))
          (NonUnitalStarAlgHom.norm_apply_le π w) (norm_nonneg _) hη.le)
        (NonUnitalStarAlgHom.norm_apply_le π V) (norm_nonneg _) (by positivity)

end MainGap

end

end OAI
