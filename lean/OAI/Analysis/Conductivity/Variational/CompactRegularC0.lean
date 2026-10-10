import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactRegularCorrection
import OAI.Analysis.Conductivity.Flux.CompactInteriorDivergence
import OAI.Analysis.Conductivity.Flux.CompactBoxDivergenceC1

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma cubePartial_bound_of_C1 {f : Box3 → ℝ} {M : ℝ}
    (hb : UniformC1Bound f M) {v : Box3} (hv : ‖v‖≤1) (p : Box3) :
    |cubePartial f v p|≤M := by
  have hM : 0≤M := (norm_nonneg _).trans (hb p).2
  exact ((fderiv ℝ f p).le_opNorm v).trans
    ((mul_le_mul (hb p).2 hv (norm_nonneg _) hM).trans_eq (mul_one M))

theorem compact_regular_box_correction_C0 {a b c d : Fin 3 → ℝ}
    (hab : ∀ i,a i<b i) (hca : ∀ i,c i<a i) (hbd : ∀ i,b i<d i) :
    ∃ L : ℝ,0<L ∧ ∀ (r₁ r₂ : Box3 → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) r₁ → ContDiff ℝ (↑(⊤ : ℕ∞)) r₂ →
      HasCompactSupport r₁ → HasCompactSupport r₂ →
      tsupport r₁⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      tsupport r₂⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      (∫ p,r₁ p)=0 → (∫ p,r₂ p)=0 →
      (∫ p,p.1.2*r₁ p-p.1.1*r₂ p)=0 → ∀ M : ℝ,0≤M →
      UniformC1Bound r₁ M → UniformC1Bound r₂ M →
    ∃ H : Fin 3 → Fin 3 → Box3 → ℝ,
      (∀ i j, ContDiff ℝ (↑(⊤ : ℕ∞)) (H i j)) ∧
      (∀ i j, HasCompactSupport (H i j)) ∧
      (∀ i j, tsupport (H i j)⊆(Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2)) ∧
      (∀ i j p,H i j p=H j i p) ∧
      (∀ p,cubePartial (H 0 0) ((1,0),0) p+cubePartial (H 1 0) ((0,1),0) p+
        cubePartial (H 2 0) ((0,0),1) p=r₁ p) ∧
      (∀ p,cubePartial (H 0 1) ((1,0),0) p+cubePartial (H 1 1) ((0,1),0) p+
        cubePartial (H 2 1) ((0,0),1) p=r₂ p) ∧
      (∀ i j p,|H i j p|≤L*M) := by
  have hcd : ∀ i,c i<d i := fun i => (hca i).trans ((hab i).trans (hbd i))
  obtain ⟨D₀,hD₀,solve₀⟩ := compact_box_divergence_C1 hab
  obtain ⟨D₁,hD₁,solve₁⟩ := compact_box_divergence_C1 hcd
  let L := D₀+2*D₁*D₀
  refine ⟨L,by dsimp [L]; positivity,?_⟩
  intro r₁ r₂ hr₁ hr₂ hs₁ hs₂ hv₁ hv₂ hz₁ hz₂ ht M hM hb₁ hb₂
  obtain ⟨F₁,F₂,F₃,hF₁,hF₂,hF₃,hsF₁,hsF₂,hsF₃,hdF,htF,hbF₁,hbF₂,hbF₃⟩ := solve₀ r₁ hr₁ hs₁ hv₁ hz₁ M hM hb₁
  obtain ⟨G₁,G₂,G₃,hG₁,hG₂,hG₃,hsG₁,hsG₂,hsG₃,hdG,htG,hbG₁,hbG₂,hbG₃⟩ := solve₀ r₂ hr₂ hs₂ hv₂ hz₂ M hM hb₂
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
  let U := (Icc (c 0) (d 0) ×ˢ Icc (c 1) (d 1)) ×ˢ Icc (c 2) (d 2)
  let V := (Ioo (c 0) (d 0) ×ˢ Ioo (c 1) (d 1)) ×ˢ Ioo (c 2) (d 2)
  have hinner : (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) ×ˢ Icc (a 2) (b 2) ⊆ V := by
    intro p hp
    exact ⟨⟨⟨(hca 0).trans_le hp.1.1.1,hp.1.1.2.trans_lt (hbd 0)⟩,
      ⟨(hca 1).trans_le hp.1.2.1,hp.1.2.2.trans_lt (hbd 1)⟩⟩,
      ⟨(hca 2).trans_le hp.2.1,hp.2.2.trans_lt (hbd 2)⟩⟩
  have hVU : V⊆U := fun _ hp =>
    ⟨⟨Ioo_subset_Icc_self hp.1.1,Ioo_subset_Icc_self hp.1.2⟩,Ioo_subset_Icc_self hp.2⟩
  have htFV := htF.trans hinner
  have htGV := htG.trans hinner
  have htF₁ : tsupport F₁⊆U := ((subset_union_left.trans subset_union_left).trans htFV).trans hVU
  have htF₂ : tsupport F₂⊆U := ((subset_union_right.trans subset_union_left).trans htFV).trans hVU
  have htF₃ : tsupport F₃⊆U := (subset_union_right.trans htFV).trans hVU
  have htG₁ : tsupport G₁⊆U := ((subset_union_left.trans subset_union_left).trans htGV).trans hVU
  have htG₂ : tsupport G₂⊆U := ((subset_union_right.trans subset_union_left).trans htGV).trans hVU
  have htG₃ : tsupport G₃⊆U := (subset_union_right.trans htGV).trans hVU
  have htq : tsupport (fun p => F₂ p-G₁ p)⊆V :=
    (tsupport_sub _ _).trans (union_subset
      ((subset_union_right.trans subset_union_left).trans htFV)
      ((subset_union_left.trans subset_union_left).trans htGV))
  have hbq : UniformC1Bound (fun p => F₂ p-G₁ p) (2*D₀*M) := by
    convert hbF₂.sub (hF₂.differentiable (by simp)) (hG₁.differentiable (by simp)) hbG₁ using 1
    ring
  obtain ⟨h₁,h₂,h₃,hh₁,hh₂,hh₃,hsh₁,hsh₂,hsh₃,hdh,hth,hbh₁,hbh₂,hbh₃⟩ :=
    solve₁ (fun p => F₂ p-G₁ p) (hF₂.sub hG₁) (hsF₂.sub hsG₁) htq hzq
      (2*D₀*M) (by positivity) hbq
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
  refine ⟨H,?_,?_,?_,?_,?_,?_,?_⟩
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

  · have hcomb (f g : Box3 → ℝ) (hf : UniformC1Bound f (D₀*M))
        (hg : UniformC1Bound g (D₁*(2*D₀*M))) (v : Box3) (hv : ‖v‖≤1) (p : Box3) :
        |f p+cubePartial g v p|≤L*M ∧ |f p-cubePartial g v p|≤L*M := by
      have hd := cubePartial_bound_of_C1 hg hv p
      have he : D₀*M+D₁*(2*D₀*M)=L*M := by dsimp [L]; ring
      exact ⟨(abs_add_le _ _).trans ((add_le_add (hf p).1 hd).trans_eq he),
        (abs_sub _ _).trans ((add_le_add (hf p).1 hd).trans_eq he)⟩
    have hA₀ (p : Box3) : |A p|≤L*M := (hcomb F₁ h₁ hbF₁ hbh₁ ((0,1),0) (by simp [Prod.norm_def]) p).1
    have hB₀ (p : Box3) : |B p|≤L*M := (hcomb G₁ h₂ hbG₁ hbh₂ ((0,1),0) (by simp [Prod.norm_def]) p).1
    have hC₀ (p : Box3) : |C p|≤L*M := (hcomb F₃ h₃ hbF₃ hbh₃ ((0,1),0) (by simp [Prod.norm_def]) p).1
    have hD₀' (p : Box3) : |D p|≤L*M := (hcomb G₂ h₂ hbG₂ hbh₂ ((1,0),0) (by simp [Prod.norm_def]) p).2
    have hG₀ (p : Box3) : |G₃ p|≤L*M := (hbG₃ p).1.trans
      (mul_le_mul_of_nonneg_right (by dsimp [L]; exact le_add_of_nonneg_right (by positivity)) hM)
    intro i j p
    fin_cases i <;> fin_cases j
    all_goals first | exact hA₀ p | exact hB₀ p | exact hC₀ p | exact hD₀' p | exact hG₀ p | skip
    change |(0:ℝ)|≤L*M
    rw [abs_zero]
    dsimp [L]
    positivity

end ScalarConductivity

end
end

end OAI
