import OAI.Analysis.LipschitzHilbert.Trees.SourceMaximalBound

namespace OAI

/-! Three-grid coordinate majorants on the plane. The construction has
uniform bounds both on L² and on bounded functions. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.DyadicLineGrid

def threeHorizontalMaximal (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) : ℝ :=
  ∑ q : GridChoice, allHorizontalMaximal q.val f z

def threeVerticalMaximal (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) : ℝ :=
  threeHorizontalMaximal (f ∘ Prod.swap) z.swap

def threeStrongMaximal (f : ℝ×ℝ → ℝ) : ℝ×ℝ → ℝ :=
  threeHorizontalMaximal (threeVerticalMaximal f)

theorem threeHorizontalMaximal_eq_line (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    threeHorizontalMaximal f z=threeGridMaximal (fun x => f (x,z.2)) z.1 := rfl

theorem threeVerticalMaximal_eq_line (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    threeVerticalMaximal f z=threeGridMaximal (fun y => f (z.1,y)) z.2 := rfl

theorem threeHorizontalMaximal_measurable {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (threeHorizontalMaximal f) :=
  Finset.measurable_sum _ (fun _ _ => allHorizontalMaximal_measurable _ hf)

theorem threeVerticalMaximal_measurable {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (threeVerticalMaximal f) :=
  (threeHorizontalMaximal_measurable (hf.comp measurable_swap)).comp measurable_swap

theorem threeStrongMaximal_measurable {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (threeStrongMaximal f) :=
  threeHorizontalMaximal_measurable (threeVerticalMaximal_measurable hf)

theorem threeHorizontalMaximal_nonneg (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤threeHorizontalMaximal f z := threeGridMaximal_nonneg _ _

theorem threeVerticalMaximal_nonneg (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤threeVerticalMaximal f z := threeGridMaximal_nonneg _ _

theorem threeStrongMaximal_nonneg (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤threeStrongMaximal f z := threeHorizontalMaximal_nonneg _ _

theorem threeHorizontalMaximal_bound (f : ℝ×ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (hf : ∀ z, |f z|≤B) (z : ℝ×ℝ) :
    threeHorizontalMaximal f z≤3*B :=
  threeGridMaximal_bound _ B hB (fun x => hf (x,z.2)) z.1

theorem threeVerticalMaximal_bound (f : ℝ×ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (hf : ∀ z, |f z|≤B) (z : ℝ×ℝ) :
    threeVerticalMaximal f z≤3*B :=
  threeGridMaximal_bound _ B hB (fun y => hf (z.1,y)) z.2

theorem threeHorizontalMaximal_energy {f : ℝ×ℝ → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (threeHorizontalMaximal f) 2 (volume.prod volume) ∧
    (∫ z, (threeHorizontalMaximal f z)^2 ∂volume.prod volume)≤
      36*∫ z, (f z)^2 ∂volume.prod volume := by
  have hq (q : GridChoice) := allHorizontalMaximal_energy q.val hfm hf
  have hm : MemLp (threeHorizontalMaximal f) 2 (volume.prod volume) :=
    memLp_finsetSum Finset.univ (fun q _ => (hq q).1)
  have he := weighted_integral_sum_square (volume.prod volume)
    (fun q : GridChoice => allHorizontalMaximal q.val f) (fun q => (hq q).1)
    (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [div_one,Real.norm_eq_abs,sq_abs,Finset.sum_const,Finset.card_univ,
    gridChoice_card,nsmul_eq_mul,mul_one] at he
  refine ⟨hm,he.trans ?_⟩
  calc
    _ ≤ 3*∑ q : GridChoice, (4*∫ z, (f z)^2 ∂volume.prod volume) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => (hq q).2.1)) (by norm_num)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,gridChoice_card,nsmul_eq_mul]; ring

theorem threeVerticalMaximal_energy {f : ℝ×ℝ → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (threeVerticalMaximal f) 2 (volume.prod volume) ∧
    (∫ z, (threeVerticalMaximal f z)^2 ∂volume.prod volume)≤
      36*∫ z, (f z)^2 ∂volume.prod volume := by
  have hs : MemLp (f ∘ Prod.swap) 2 (volume.prod volume) :=
    hf.comp_measurePreserving Measure.measurePreserving_swap
  have h := threeHorizontalMaximal_energy (hfm.comp measurable_swap) hs
  refine ⟨h.1.comp_measurePreserving Measure.measurePreserving_swap,?_⟩
  change (∫ z, (threeHorizontalMaximal (f ∘ Prod.swap) z.swap)^2 ∂volume.prod volume)≤_
  rw [show (∫ z, (threeHorizontalMaximal (f ∘ Prod.swap) z.swap)^2 ∂volume.prod volume)=
      ∫ z, (threeHorizontalMaximal (f ∘ Prod.swap) z)^2 ∂volume.prod volume from
    integral_prod_swap (fun z => (threeHorizontalMaximal (f ∘ Prod.swap) z)^2)]
  calc
    _ ≤ 36*∫ z, ((f ∘ Prod.swap) z)^2 ∂volume.prod volume := h.2
    _ = _ := by congr 1; exact integral_prod_swap (fun z => (f z)^2)

theorem threeStrongMaximal_energy {f : ℝ×ℝ → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (threeStrongMaximal f) 2 (volume.prod volume) ∧
    (∫ z, (threeStrongMaximal f z)^2 ∂volume.prod volume)≤
      1296*∫ z, (f z)^2 ∂volume.prod volume := by
  have hv := threeVerticalMaximal_energy hfm hf
  have hh := threeHorizontalMaximal_energy (threeVerticalMaximal_measurable hfm) hv.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _ ≤ 36*(36*∫ z, (f z)^2 ∂volume.prod volume) := mul_le_mul_of_nonneg_left hv.2 (by norm_num)
    _ = _ := by ring

end LipschitzHilbert.DyadicLineGrid

end

end OAI
