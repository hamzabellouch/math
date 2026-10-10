import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactFiberDecomposition

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma interval_integral_eq_integral_of_support {a b : ℝ} (hab : a≤b)
    {f : ℝ → ℝ} (hv : ∀ t, f t≠0 → t∈Ioo a b) :
    (∫ t in a..b, f t)=∫ t, f t := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  by_contra hn
  exact hx ⟨(hv x hn).1,(hv x hn).2.le⟩

lemma compactFiberMarginal_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    {a b : ℝ} (hab : a≤b) {f : E×ℝ → ℝ} (hf : Integrable f)
    (hv : ∀ p, f p≠0 → p.2∈Ioo a b) :
    (∫ x, compactFiberMarginal a b f x)=∫ p, f p := by
  have he (x : E) : compactFiberMarginal a b f x=∫ t, f (x,t) :=
    interval_integral_eq_integral_of_support hab (fun t ht => hv (x,t) ht)
  simp_rw [he]
  exact (integral_prod f hf).symm

lemma compact_scalar_primitive {a b : ℝ} (hab : a<b) {r : ℝ → ℝ}
    (hr : ContDiff ℝ (↑(⊤ : ℕ∞)) r)
    (hv : ∀ t, r t≠0 → t∈Ioo a b) (hz : (∫ t, r t)=0) :
    ∃ P : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) P ∧ HasCompactSupport P ∧
      (∀ t, deriv P t=r t) ∧ tsupport P⊆Icc a b := by
  let f : ℝ×ℝ → ℝ := fun p => r p.2
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f := hr.comp contDiff_snd
  let P : ℝ → ℝ := fun t => fiberPrimitive a f (0,t)
  have hP : ContDiff ℝ (↑(⊤ : ℕ∞)) P :=
    (fiberPrimitive_smooth a hf).comp (contDiff_const.prodMk contDiff_id)
  have hvf : ∀ p, f p≠0 → p.2∈Ioo a b := fun p hp => hv p.2 hp
  have hzf : ∀ x, (∫ t in a..b, f (x,t))=0 := by
    intro x
    exact (interval_integral_eq_integral_of_support hab.le hv).trans hz
  have hs : Function.support P⊆Icc a b := by
    intro t ht
    refine ⟨?_,?_⟩
    · by_contra hn
      exact ht (fiberPrimitive_below hf.continuous hvf (0,t) (le_of_not_ge hn))
    · by_contra hn
      exact ht (fiberPrimitive_above hf.continuous hvf hzf (0,t) (le_of_not_ge hn))
  refine ⟨P,hP,HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs,?_,
    closure_minimal hs isClosed_Icc⟩
  intro t
  have hd := (((fiberPrimitive_smooth a hf).differentiable (by simp)) (0,t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t (0:ℝ)).prodMk (hasDerivAt_id t))
  exact hd.deriv.trans (fiberPrimitive_derivative a hf (0,t))

lemma cube_partial_fiber (f : Box3 → ℝ) (p : Box3) :
    cubePartial f ((0,0),1) p=wallDerivative f p := rfl

theorem compact_box_divergence {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i)
    {r : Box3 → ℝ} (hr : ContDiff ℝ (↑(⊤ : ℕ∞)) r) (hs : HasCompactSupport r)
    (hv : tsupport r⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))
    (hz : (∫ p, r p)=0) :
    ∃ F₁ F₂ F₃ : Box3 → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) F₁ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) F₂ ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) F₃ ∧
      HasCompactSupport F₁ ∧ HasCompactSupport F₂ ∧ HasCompactSupport F₃ ∧
      (∀ p, cubePartial F₁ ((1,0),0) p+cubePartial F₂ ((0,1),0) p+
        cubePartial F₃ ((0,0),1) p=r p) ∧
      tsupport F₁∪tsupport F₂∪tsupport F₃⊆
        (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) ×ˢ Icc (a 2) (b 2) := by
  obtain ⟨η₃,hη₃,hsη₃,hvη₃,hiη₃⟩ := exists_unit_interval_bump (hab 2)
  obtain ⟨η₂,hη₂,hsη₂,hvη₂,hiη₂⟩ := exists_unit_interval_bump (hab 1)
  let R := compactFiberMarginal (a 2) (b 2) r
  have hR := compactFiberMarginal_smooth (hab 2).le hr
  have hsR := (compactFiberMarginal_support hs (a := a 2) (b := b 2)).1
  have hvR : tsupport R⊆Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1) := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := (compactFiberMarginal_support hs).2 hx
    exact (hv hp).1
  obtain ⟨F₃,hF₃,hsF₃,hd₃,ht₃⟩ := compact_fiber_decomposition (hab 2) hr hs
    (fun p hp => (hv (subset_tsupport r hp)).2) hη₃ hsη₃ hvη₃ hiη₃
  let S := compactFiberMarginal (a 1) (b 1) R
  have hS := compactFiberMarginal_smooth (hab 1).le hR
  have hsS := (compactFiberMarginal_support hsR (a := a 1) (b := b 1)).1
  have hvS : tsupport S⊆Ioo (a 0) (b 0) := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := (compactFiberMarginal_support hsR).2 hx
    exact (hvR hp).1
  obtain ⟨G,hG,hsG,hdG,htG⟩ := compact_fiber_decomposition (hab 1) hR hsR
    (fun p hp => (hvR (subset_tsupport R hp)).2) hη₂ hsη₂ hvη₂ hiη₂
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
  obtain ⟨P,hP,hsP,hdP,htP⟩ := compact_scalar_primitive (hab 0) hS
    (fun x hx => hvS (subset_tsupport S hx)) hzS
  let F₁ : Box3 → ℝ := fun p => η₃ p.2*η₂ p.1.2*P p.1.1
  let F₂ : Box3 → ℝ := fun p => η₃ p.2*G p.1
  have hF₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₁ :=
    ((hη₃.comp contDiff_snd).mul (hη₂.comp (contDiff_snd.comp contDiff_fst))).mul
      (hP.comp (contDiff_fst.comp contDiff_fst))
  have hF₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₂ :=
    (hη₃.comp contDiff_snd).mul (hG.comp contDiff_fst)
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
    union_subset (union_subset ht₁ ht₂) ht₃'⟩
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

end OAI
