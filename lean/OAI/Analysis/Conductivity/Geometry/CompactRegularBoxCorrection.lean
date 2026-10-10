import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactRegularCorrection
import OAI.Analysis.Conductivity.Flux.CompactInteriorDivergence

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem compact_regular_box_correction {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i)
    {r₁ r₂ : Box3 → ℝ}
    (hr₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (hr₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hs₁ : HasCompactSupport r₁) (hs₂ : HasCompactSupport r₂)
    (hv₁ : tsupport r₁⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))
    (hv₂ : tsupport r₂⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))
    (hz₁ : (∫ p,r₁ p)=0) (hz₂ : (∫ p,r₂ p)=0)
    (ht : (∫ p,p.1.2*r₁ p-p.1.1*r₂ p)=0) :
    ∃ H : Fin 3 → Fin 3 → Box3 → ℝ,
      (∀ i j, ContDiff ℝ (↑(⊤ : ℕ∞)) (H i j)) ∧
      (∀ i j, HasCompactSupport (H i j)) ∧
      (∀ i j, tsupport (H i j)⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2)) ∧
      (∀ i j p,H i j p=H j i p) ∧
      (∀ p,cubePartial (H 0 0) ((1,0),0) p+cubePartial (H 1 0) ((0,1),0) p+
        cubePartial (H 2 0) ((0,0),1) p=r₁ p) ∧
      (∀ p,cubePartial (H 0 1) ((1,0),0) p+cubePartial (H 1 1) ((0,1),0) p+
        cubePartial (H 2 1) ((0,0),1) p=r₂ p) := by
  obtain ⟨F₁,F₂,F₃,hF₁,hF₂,hF₃,hsF₁,hsF₂,hsF₃,hdF,htF⟩ := compact_box_divergence_inside hab hr₁ hs₁ hv₁ hz₁
  obtain ⟨G₁,G₂,G₃,hG₁,hG₂,hG₃,hsG₁,hsG₂,hsG₃,hdG,htG⟩ := compact_box_divergence_inside hab hr₂ hs₂ hv₂ hz₂
  have hf₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Box3 => p.1.1) := contDiff_fst.comp contDiff_fst
  have hf₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Box3 => p.1.2) := contDiff_snd.comp contDiff_fst
  have hIF := cube_coordinate_divergence_moment hF₁ hF₂ hF₃ hsF₁ hsF₂ hsF₃ hdF hf₂
  have hIG := cube_coordinate_divergence_moment hG₁ hG₂ hG₃ hsG₁ hsG₂ hsG₃ hdG hf₁
  simp only [cubePartial_fst_fst,cubePartial_snd_fst,zero_mul,one_mul,integral_zero,neg_zero,
    sub_zero,zero_sub] at hIF hIG
  have hi₁ : Integrable (fun p : Box3 => p.1.2*r₁ p) := (hf₂.continuous.mul hr₁.continuous).integrable_of_hasCompactSupport (μ := volume) hs₁.mul_left
  have hi₂ : Integrable (fun p : Box3 => p.1.1*r₂ p) := (hf₁.continuous.mul hr₂.continuous).integrable_of_hasCompactSupport (μ := volume) hs₂.mul_left
  have hzq : (∫ p,F₂ p-G₁ p)=0 := by
    rw [integral_sub (hF₂.continuous.integrable_of_hasCompactSupport hsF₂)
      (hG₁.continuous.integrable_of_hasCompactSupport hsG₁)]
    rw [integral_sub hi₁ hi₂,hIF,hIG] at ht
    linarith
  let U := (Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2)
  have htF₁ : tsupport F₁⊆U := (subset_union_left.trans subset_union_left).trans htF
  have htF₂ : tsupport F₂⊆U := (subset_union_right.trans subset_union_left).trans htF
  have htF₃ : tsupport F₃⊆U := subset_union_right.trans htF
  have htG₁ : tsupport G₁⊆U := (subset_union_left.trans subset_union_left).trans htG
  have htG₂ : tsupport G₂⊆U := (subset_union_right.trans subset_union_left).trans htG
  have htG₃ : tsupport G₃⊆U := subset_union_right.trans htG
  have htq : tsupport (fun p => F₂ p-G₁ p)⊆U :=
    (tsupport_sub _ _).trans (union_subset htF₂ htG₁)
  obtain ⟨h₁,h₂,h₃,hh₁,hh₂,hh₃,hsh₁,hsh₂,hsh₃,hdh,hth⟩ :=
    compact_box_divergence_inside hab (hF₂.sub hG₁) (hsF₂.sub hsG₁) htq hzq
  have hth₁ : tsupport h₁⊆U := (subset_union_left.trans subset_union_left).trans hth
  have hth₂ : tsupport h₂⊆U := (subset_union_right.trans subset_union_left).trans hth
  have hth₃ : tsupport h₃⊆U := subset_union_right.trans hth
  let A := fun p => F₁ p+cubePartial h₁ ((0,1),0) p
  let B := fun p => G₁ p+cubePartial h₂ ((0,1),0) p
  let C := fun p => F₃ p+cubePartial h₃ ((0,1),0) p
  let D := fun p => G₂ p-cubePartial h₂ ((1,0),0) p
  let H : Fin 3 → Fin 3 → Box3 → ℝ := ![![A,B,C],![B,D,G₃],![C,G₃,fun _ => 0]]
  have hA := hF₁.add (cubePartial_smooth hh₁ ((0,1),0))
  have hB := hG₁.add (cubePartial_smooth hh₂ ((0,1),0))
  have hC := hF₃.add (cubePartial_smooth hh₃ ((0,1),0))
  have hD := hG₂.sub (cubePartial_smooth hh₂ ((1,0),0))
  have hsA := hsF₁.add (cubePartial_compact hsh₁ ((0,1),0))
  have hsB := hsG₁.add (cubePartial_compact hsh₂ ((0,1),0))
  have hsC := hsF₃.add (cubePartial_compact hsh₃ ((0,1),0))
  have hsD := hsG₂.sub (cubePartial_compact hsh₂ ((1,0),0))
  have hB' : B=(fun p => F₂ p-cubePartial h₁ ((1,0),0) p-cubePartial h₃ ((0,0),1) p) := by
    funext p
    change G₁ p+cubePartial h₂ ((0,1),0) p=_
    linarith [hdh p]
  have htA : tsupport A⊆U := (tsupport_add _ _).trans
    (union_subset htF₁ ((cubePartial_tsupport _).trans hth₁))
  have htB : tsupport B⊆U := (tsupport_add _ _).trans
    (union_subset htG₁ ((cubePartial_tsupport _).trans hth₂))
  have htC : tsupport C⊆U := (tsupport_add _ _).trans
    (union_subset htF₃ ((cubePartial_tsupport _).trans hth₃))
  have htD : tsupport D⊆U := (tsupport_sub _ _).trans
    (union_subset htG₂ ((cubePartial_tsupport _).trans hth₂))
  have ht0 : tsupport (fun _ : Box3 => (0:ℝ))⊆U := by simp
  refine ⟨H,?_,?_,?_,?_,?_,?_⟩
  · intro i j; fin_cases i <;> fin_cases j
    all_goals first | exact hA | exact hB | exact hC | exact hD | exact hG₃ | exact contDiff_const
  · intro i j; fin_cases i <;> fin_cases j
    all_goals first | exact hsA | exact hsB | exact hsC | exact hsD | exact hsG₃ | exact HasCompactSupport.zero
  · intro i j; fin_cases i <;> fin_cases j
    all_goals first | exact htA | exact htB | exact htC | exact htD | exact htG₃ | exact ht0
  · intro i j p; fin_cases i <;> fin_cases j <;> rfl
  · intro p
    change cubePartial A ((1,0),0) p+cubePartial B ((0,1),0) p+cubePartial C ((0,0),1) p=r₁ p
    rw [hB']
    change cubePartial (fun p => F₁ p+cubePartial h₁ ((0,1),0) p) ((1,0),0) p+
      cubePartial (fun p => F₂ p-cubePartial h₁ ((1,0),0) p-cubePartial h₃ ((0,0),1) p) ((0,1),0) p+
      cubePartial (fun p => F₃ p+cubePartial h₃ ((0,1),0) p) ((0,0),1) p=r₁ p
    rw [cubePartial_add (hF₁.differentiable (by simp)) ((cubePartial_smooth hh₁ _).differentiable (by simp)),
      cubePartial_sub ((hF₂.sub (cubePartial_smooth hh₁ _)).differentiable (by simp))
        ((cubePartial_smooth hh₃ _).differentiable (by simp)),
      cubePartial_sub (hF₂.differentiable (by simp)) ((cubePartial_smooth hh₁ _).differentiable (by simp)),
      cubePartial_add (hF₃.differentiable (by simp)) ((cubePartial_smooth hh₃ _).differentiable (by simp)),
      cubePartial_commute hh₁ ((0,1),0) ((1,0),0),cubePartial_commute hh₃ ((0,1),0) ((0,0),1)]
    linarith [hdF p]
  · intro p
    change cubePartial B ((1,0),0) p+cubePartial D ((0,1),0) p+cubePartial G₃ ((0,0),1) p=r₂ p
    change cubePartial (fun p => G₁ p+cubePartial h₂ ((0,1),0) p) ((1,0),0) p+
      cubePartial (fun p => G₂ p-cubePartial h₂ ((1,0),0) p) ((0,1),0) p+
      cubePartial G₃ ((0,0),1) p=r₂ p
    rw [cubePartial_add (hG₁.differentiable (by simp)) ((cubePartial_smooth hh₂ _).differentiable (by simp)),
      cubePartial_sub (hG₂.differentiable (by simp)) ((cubePartial_smooth hh₂ _).differentiable (by simp)),
      cubePartial_commute hh₂ ((0,1),0) ((1,0),0)]
    linarith [hdG p]

end ScalarConductivity

end

end OAI
