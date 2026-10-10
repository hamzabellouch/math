import Mathlib
import OAI.Analysis.Conductivity.Variational.UniformC1Bounds

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem compact_box_divergence_C1 {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i) :
    ∃ C : ℝ,0<C ∧ ∀ (r : Box3 → ℝ),ContDiff ℝ (↑(⊤ : ℕ∞)) r →
      HasCompactSupport r →
      tsupport r⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) →
      (∫ p,r p)=0 → ∀ M : ℝ,0≤M → UniformC1Bound r M →
      ∃ F₁ F₂ F₃ : Box3 → ℝ,
        ContDiff ℝ (↑(⊤ : ℕ∞)) F₁ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) F₂ ∧
        ContDiff ℝ (↑(⊤ : ℕ∞)) F₃ ∧
        HasCompactSupport F₁ ∧ HasCompactSupport F₂ ∧ HasCompactSupport F₃ ∧
        (∀ p,cubePartial F₁ ((1,0),0) p+cubePartial F₂ ((0,1),0) p+
          cubePartial F₃ ((0,0),1) p=r p) ∧
        tsupport F₁∪tsupport F₂∪tsupport F₃⊆
          (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) ×ˢ Icc (a 2) (b 2) ∧
        UniformC1Bound F₁ (C*M) ∧ UniformC1Bound F₂ (C*M) ∧ UniformC1Bound F₃ (C*M) := by
  obtain ⟨η₃,hη₃,hsη₃,hvη₃,hiη₃⟩ := exists_unit_interval_bump (hab 2)
  obtain ⟨η₂,hη₂,hsη₂,hvη₂,hiη₂⟩ := exists_unit_interval_bump (hab 1)
  obtain ⟨K₃,hK₃,hbη₃⟩ := exists_uniformC1Bound hη₃ hsη₃
  obtain ⟨K₂,hK₂,hbη₂⟩ := exists_uniformC1Bound hη₂ hsη₂
  have hl₀ : 0<b 0-a 0 := sub_pos.mpr (hab 0)
  have hl₁ : 0<b 1-a 1 := sub_pos.mpr (hab 1)
  have hl₂ : 0<b 2-a 2 := sub_pos.mpr (hab 2)
  let c₁ := 4*K₃*K₂*(b 0-a 0+1)*(b 1-a 1)*(b 2-a 2)
  let c₂ := 2*K₃*(b 1-a 1+1)*(1+K₂*(b 1-a 1))*(b 2-a 2)
  let c₃ := (b 2-a 2+1)*(1+K₃*(b 2-a 2))
  have hc₁ : 0≤c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0≤c₂ := by dsimp [c₂]; positivity
  have hc₃ : 0≤c₃ := by dsimp [c₃]; positivity
  let C := c₁+c₂+c₃+1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro r hr hs hv hz M hM hbound
  let R := compactFiberMarginal (a 2) (b 2) r
  have hR := compactFiberMarginal_smooth (hab 2).le hr
  have hsR := (compactFiberMarginal_support hs (a := a 2) (b := b 2)).1
  have hvR : tsupport R⊆Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1) := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := (compactFiberMarginal_support hs).2 hx
    exact (hv hp).1
  have hbR : UniformC1Bound R ((b 2-a 2)*M) := compactFiberMarginal_C1Bound (hab 2).le hr hM hbound
  obtain ⟨F₃,hF₃,hsF₃,hd₃,ht₃,hb₃,hdB₃⟩ := compact_fiber_decomposition_C1 (hab 2) hr hs
    (fun p hp => (hv hp).2) hη₃ hsη₃ hvη₃ hiη₃ hM hK₃.le
    (fun p => (hbound p).1) (fun p => (hbound p).2) (fun t => (hbη₃ t).1)
  let S := compactFiberMarginal (a 1) (b 1) R
  have hS := compactFiberMarginal_smooth (hab 1).le hR
  have hsS := (compactFiberMarginal_support hsR (a := a 1) (b := b 1)).1
  have hvS : tsupport S⊆Ioo (a 0) (b 0) := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := (compactFiberMarginal_support hsR).2 hx
    exact (hvR hp).1
  have hbS : UniformC1Bound S ((b 1-a 1)*((b 2-a 2)*M)) :=
    compactFiberMarginal_C1Bound (hab 1).le hR (by positivity) hbR
  obtain ⟨G,hG,hsG,hdG,htG,hbG₀,hdbG⟩ := compact_fiber_decomposition_C1 (hab 1) hR hsR
    (fun p hp => (hvR hp).2) hη₂ hsη₂ hvη₂ hiη₂ (by positivity) hK₂.le
    (fun p => (hbR p).1) (fun p => (hbR p).2) (fun t => (hbη₂ t).1)
  have hbG : UniformC1Bound G ((b 1-a 1+1)*(1+K₂*(b 1-a 1))*((b 2-a 2)*M)) := by
    intro p
    refine ⟨(hbG₀ p).trans ?_,hdbG p⟩
    nlinarith [mul_nonneg (by positivity : 0≤1+K₂*(b 1-a 1)) (by positivity : 0≤(b 2-a 2)*M)]
  have hzR : (∫ x,R x)=0 := by
    rw [compactFiberMarginal_integral (hab 2).le
      (hr.continuous.integrable_of_hasCompactSupport hs)
      (fun p hp => (hv (subset_tsupport r hp)).2)]
    exact hz
  have hzS : (∫ x,S x)=0 := by
    rw [compactFiberMarginal_integral (hab 1).le
      (hR.continuous.integrable_of_hasCompactSupport hsR)
      (fun p hp => (hvR (subset_tsupport R hp)).2)]
    exact hzR
  obtain ⟨P,hP,hsP,hdP,htP,hbP⟩ := compact_scalar_primitive_bounded (hab 0) hS
    (fun x hx => hvS (subset_tsupport S hx)) hzS (by positivity) (fun t => (hbS t).1)
  let F₁ : Box3 → ℝ := fun p => η₃ p.2*η₂ p.1.2*P p.1.1
  let F₂ : Box3 → ℝ := fun p => η₃ p.2*G p.1
  have hF₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₁ :=
    ((hη₃.comp contDiff_snd).mul (hη₂.comp (contDiff_snd.comp contDiff_fst))).mul
      (hP.comp (contDiff_fst.comp contDiff_fst))
  have hF₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₂ :=
    (hη₃.comp contDiff_snd).mul (hG.comp contDiff_fst)
  have hbf : UniformC1Bound (fun p : Box3 => η₃ p.2) K₃ :=
    hbη₃.comp_snd (hη₃.differentiable (by simp)) hK₃.le
  have hbg : UniformC1Bound (fun p : Box3 => η₂ p.1.2) K₂ :=
    (hbη₂.comp_snd (E := ℝ) (hη₂.differentiable (by simp)) hK₂.le).comp_fst
      ((hη₂.comp contDiff_snd).differentiable (by simp)) hK₂.le
  have hbp : UniformC1Bound (fun p : Box3 => P p.1.1)
      ((b 0-a 0+1)*((b 1-a 1)*((b 2-a 2)*M))) :=
    (hbP.comp_fst (P := ℝ) (hP.differentiable (by simp)) (by positivity)).comp_fst
      ((hP.comp contDiff_fst).differentiable (by simp)) (by positivity)
  have hbf₁ : UniformC1Bound F₁ (c₁*M) := by
    have hh := (hbf.mul ((hη₃.comp contDiff_snd).differentiable (by simp))
      ((hη₂.comp (contDiff_snd.comp contDiff_fst)).differentiable (by simp)) hK₃.le hK₂.le hbg).mul
      (((hη₃.comp contDiff_snd).mul (hη₂.comp (contDiff_snd.comp contDiff_fst))).differentiable (by simp))
      ((hP.comp (contDiff_fst.comp contDiff_fst)).differentiable (by simp)) (by positivity) (by positivity) hbp
    convert hh using 1 <;> dsimp [F₁,c₁]
    ring
  have hbf₂ : UniformC1Bound F₂ (c₂*M) := by
    have hh := hbf.mul ((hη₃.comp contDiff_snd).differentiable (by simp))
      ((hG.comp contDiff_fst).differentiable (by simp)) hK₃.le (by positivity)
      (hbG.comp_fst (hG.differentiable (by simp)) (by positivity))
    convert hh using 1 <;> dsimp [F₂,c₂]
    ring
  have hbf₃ : UniformC1Bound F₃ (c₃*M) := by
    intro p
    refine ⟨(hb₃ p).trans ?_,hdB₃ p⟩
    dsimp [c₃]
    nlinarith [mul_nonneg (by positivity : 0≤1+K₃*(b 2-a 2)) hM]
  let K := (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) ×ˢ Icc (a 2) (b 2)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have ht₁ : tsupport F₁⊆K := by
    apply closure_minimal _ hK.isClosed
    intro p hp
    obtain ⟨h₁,h₂⟩ := mul_ne_zero_iff.mp hp
    obtain ⟨h₃,h₄⟩ := mul_ne_zero_iff.mp h₁
    exact ⟨⟨htP (subset_tsupport P h₂),Ioo_subset_Icc_self (hvη₂ (subset_tsupport η₂ h₄))⟩,
      Ioo_subset_Icc_self (hvη₃ (subset_tsupport η₃ h₃))⟩
  have ht₂ : tsupport F₂⊆K := by
    apply closure_minimal _ hK.isClosed
    intro p hp
    obtain ⟨h₁,h₂⟩ := mul_ne_zero_iff.mp hp
    have hh := htG (subset_tsupport G h₂)
    obtain ⟨q,hq,hqx⟩ := hh.1
    exact ⟨⟨Ioo_subset_Icc_self (hqx ▸ (hvR hq).1),hh.2⟩,
      Ioo_subset_Icc_self (hvη₃ (subset_tsupport η₃ h₁))⟩
  have ht₃' : tsupport F₃⊆K := by
    intro p hp
    have hh := ht₃ hp
    obtain ⟨q,hq,hqp⟩ := hh.1
    have hxy := (hv hq).1
    change q.1∈_ at hxy
    rw [hqp] at hxy
    exact ⟨⟨Ioo_subset_Icc_self hxy.1,Ioo_subset_Icc_self hxy.2⟩,hh.2⟩
  refine ⟨F₁,F₂,F₃,hF₁,hF₂,hF₃,
    HasCompactSupport.of_support_subset_isCompact hK (subset_tsupport F₁ |>.trans ht₁),
    HasCompactSupport.of_support_subset_isCompact hK (subset_tsupport F₂ |>.trans ht₂),hsF₃,?_,
    union_subset (union_subset ht₁ ht₂) ht₃',
    hbf₁.mono (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hM),
    hbf₂.mono (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hM),
    hbf₃.mono (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hM)⟩
  intro p
  have hd₁ : cubePartial F₁ ((1,0),0) p=η₃ p.2*η₂ p.1.2*S p.1.1 := by
    have hline := (hasDerivAt_id p.1.1).prodMk (hasDerivAt_const p.1.1 p.1.2)
    have he := ((hF₁.differentiable (by simp)) p).hasFDerivAt.comp_hasDerivAt p.1.1
      (hline.prodMk (hasDerivAt_const p.1.1 p.2))
    have he' : HasDerivAt (fun t => F₁ ((t,p.1.2),p.2))
        (cubePartial F₁ ((1,0),0) p) p.1.1 := he
    have hp := ((hP.differentiable (by simp)) p.1.1).hasDerivAt.const_mul
      (η₃ p.2*η₂ p.1.2)
    rw [hdP] at hp
    exact he'.unique hp
  have hd₂ : cubePartial F₂ ((0,1),0) p=η₃ p.2*wallDerivative G p.1 := by
    have hline := (hasDerivAt_const p.1.2 p.1.1).prodMk (hasDerivAt_id p.1.2)
    have he := ((hF₂.differentiable (by simp)) p).hasFDerivAt.comp_hasDerivAt p.1.2
      (hline.prodMk (hasDerivAt_const p.1.2 p.2))
    have he' : HasDerivAt (fun t => F₂ ((p.1.1,t),p.2))
        (cubePartial F₂ ((0,1),0) p) p.1.2 := he
    have hg := (((hG.differentiable (by simp)) p.1).hasFDerivAt.comp_hasDerivAt
      p.1.2 hline).const_mul (η₃ p.2)
    exact he'.unique hg
  rw [hd₁,hd₂,cube_partial_fiber]
  have h₁ := hdG p.1
  have h₂ := hd₃ p
  dsimp [S,R] at *
  linear_combination (η₃ p.2)*h₁+h₂

end ScalarConductivity

end
end

end OAI
