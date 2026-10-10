import OAI.NumberTheory.CubicMoment.Estimates.WideGramSeminormControl

namespace OAI


/-! Finite seminorm control survives the norm-denominator multiplier
and Fourier transform, uniformly before choosing a shrinking profile. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem wideGramFourier_seminorm_control (M : ℝ) (hM : 0 < M) (k n K : ℕ) :
    ∃ (I : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ (F : 𝓢(ℂ,ℂ)) (c : ℝ), 0 ≤ c →
      (1+c)^K*SchwartzMap.seminorm ℝ k n
        (𝓕 (wideAnnularLogSchwartz M hM F c)) ≤
        C*(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F := by
  let A : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    SchwartzMap.fourierTransformCLM ℝ (V := ℝ) (E := ℂ)
  let p := schwartzSeminormFamily ℝ ℝ ℂ
  let q := (SchwartzMap.seminorm ℝ k n).comp A.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (k,n)).comp A.continuous
  obtain ⟨s,C,hC,hA⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  choose D hD hwide using fun i : ℕ × ℕ =>
    wideAnnularLogSchwartz_seminorm_control M hM i.1 i.2 K
  let I := s.biUnion (fun i => Finset.Iic (i.2+K,i.2))
  let E := 1+∑ i ∈ s, D i
  have hE : 0 < E := by
    have hs : 0 ≤ ∑ i ∈ s, D i := Finset.sum_nonneg (fun i _ => (hD i).le)
    dsimp [E]
    linarith
  refine ⟨I,(C:ℝ)*E,mul_pos (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC)) hE,?_⟩
  intro F c hc
  let B := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp : 0 < (1+c)^K := by positivity
  have hi (i : ℕ × ℕ) (his : i ∈ s) :
      (1+c)^K*(p i) (wideAnnularLogSchwartz M hM F c) ≤ E*B := by
    have hsub : Finset.Iic (i.2+K,i.2) ⊆ I := by
      intro m hm
      exact Finset.mem_biUnion.mpr ⟨i,his,hm⟩
    have hb := Seminorm.le_def.mp (show
        (Finset.Iic (i.2+K,i.2)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ≤
          I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) from Finset.sup_mono hsub) F
    have hd : D i ≤ E := by
      have hh := Finset.single_le_sum (fun j _ => (hD j).le) his
      dsimp [E]
      linarith
    exact (hwide i F c hc).trans ((mul_le_mul_of_nonneg_left hb (hD i).le).trans
      (mul_le_mul_of_nonneg_right hd hB))
  have hsup : (1+c)^K*(s.sup p) (wideAnnularLogSchwartz M hM F c) ≤ E*B := by
    rw [←le_div_iff₀' hp]
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i his
    exact (le_div_iff₀' hp).mpr (hi i his)
  have ht := Seminorm.le_def.mp hA (wideAnnularLogSchwartz M hM F c)
  change SchwartzMap.seminorm ℝ k n (A (wideAnnularLogSchwartz M hM F c)) ≤
    (C:ℝ)*(s.sup p) (wideAnnularLogSchwartz M hM F c) at ht
  calc
    _ ≤ (1+c)^K*((C:ℝ)*(s.sup p) (wideAnnularLogSchwartz M hM F c)) :=
      mul_le_mul_of_nonneg_left ht hp.le
    _ = (C:ℝ)*((1+c)^K*(s.sup p) (wideAnnularLogSchwartz M hM F c)) := by ring
    _ ≤ (C:ℝ)*(E*B) := mul_le_mul_of_nonneg_left hsup C.coe_nonneg
    _ = _ := by dsimp [B]; ring



theorem wideGramMellinCoefficient_moment_control (M : ℝ) (hM : 0 < M) (A B : ℕ) :
    ∃ (I : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
        (ρ : ℝ), 0 ≤ ρ →
      (1+ρ)^A*(∫ t : ℝ, ‖t‖^B*‖wideGramMellinCoefficient M hM W hW hW' ρ t‖) ≤
        C*(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
          (normProfileFourierSchwartz W hW hW') := by
  let k := (volume : Measure ℝ).integrablePower
  let D : ℝ := 2^k*∫ t : ℝ, (1+‖t‖)^(-(k:ℝ))
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg (fun _ => by positivity))
  obtain ⟨I₀,C₀,hC₀,h₀⟩ := wideGramFourier_seminorm_control M hM 0 0 (2*A)
  obtain ⟨I₁,C₁,hC₁,h₁⟩ := wideGramFourier_seminorm_control M hM (B+k) 0 (2*A)
  let I := I₀ ∪ I₁
  refine ⟨I,D*(C₀+C₁)+1,by positivity,?_⟩
  intro W hW hW' ρ hρ
  let F := normProfileFourierSchwartz W hW hW'
  let S := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_nonneg ρ]
  have h := (𝓕 (wideGramLogSchwartz M hM W hW hW' ρ)).integral_pow_mul_iteratedFDeriv_le ℝ volume B 0
  simp only [norm_iteratedFDeriv_zero] at h
  have hsup₀ : (I₀.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) F
  have hsup₁ : (I₁.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) F
  have hc₀ := (h₀ F (Real.sqrt ρ) (Real.sqrt_nonneg ρ)).trans
    (mul_le_mul_of_nonneg_left hsup₀ hC₀.le)
  have hc₁ := (h₁ F (Real.sqrt ρ) (Real.sqrt_nonneg ρ)).trans
    (mul_le_mul_of_nonneg_left hsup₁ hC₁.le)
  rw [wideAnnularLogSchwartz_eq_wideGramLogSchwartz] at hc₀ hc₁
  calc
    _ ≤ (1+Real.sqrt ρ)^(2*A)*(D*
        (SchwartzMap.seminorm ℝ 0 0 (𝓕 (wideGramLogSchwartz M hM W hW hW' ρ))+
         SchwartzMap.seminorm ℝ (B+k) 0 (𝓕 (wideGramLogSchwartz M hM W hW hW' ρ)))) :=
      mul_le_mul hs h (integral_nonneg (fun _ => by positivity)) (by positivity)
    _ = D*((1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ 0 0
        (𝓕 (wideGramLogSchwartz M hM W hW hW' ρ))+
      (1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ (B+k) 0
        (𝓕 (wideGramLogSchwartz M hM W hW hW' ρ))) := by ring
    _ ≤ D*(C₀*S+C₁*S) := mul_le_mul_of_nonneg_left (add_le_add hc₀ hc₁) hD
    _ ≤ (D*(C₀+C₁)+1)*S := by nlinarith

end CubicFirstMoment

end

end OAI
