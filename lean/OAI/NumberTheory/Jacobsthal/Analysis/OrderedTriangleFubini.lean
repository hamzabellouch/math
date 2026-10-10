import OAI.NumberTheory.Jacobsthal.Partitions.BoundedRectangleFubini

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings

theorem ordered_triangle_swap {f : ℝ×ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Icc (1:ℝ) 2,∀ t ∈ Icc (1:ℝ) 2,|f (x,t)| ≤ C) :
    (∫ x : ℝ in 1..2,∫ t : ℝ in 1..x,f (x,t))=
      ∫ t : ℝ in 1..2,∫ x : ℝ in t..2,f (x,t) := by
  classical
  let g : ℝ×ℝ → ℝ := fun p => if p.2 ≤ p.1 then f p else 0
  have hg : Measurable g := Measurable.ite (measurableSet_le measurable_snd measurable_fst) hf measurable_const
  have hb : ∀ x ∈ Icc (1:ℝ) 2,∀ t ∈ Icc (1:ℝ) 2,|g (x,t)| ≤ C := by
    intro x hx t ht
    dsimp only [g]
    split_ifs
    · exact hbound x hx t ht
    · simpa only [abs_zero] using hC
  have hs := bounded_rectangle_swap hg 1 2 1 2 C hb
  have hleft (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
      (∫ t in Icc (1:ℝ) 2,g (x,t))=∫ t : ℝ in 1..x,f (x,t) := by
    have hset : Icc (1:ℝ) 2 ∩ Iic x=Icc 1 x := by
      ext t
      constructor
      · rintro ⟨ht,hx'⟩; exact ⟨ht.1,hx'⟩
      · intro ht; exact ⟨⟨ht.1,ht.2.trans hx.2⟩,ht.2⟩
    change (∫ t in Icc (1:ℝ) 2,(Iic x).indicator (fun t => f (x,t)) t)=_
    rw [setIntegral_indicator measurableSet_Iic,hset,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hx.1]
  have hright (t : ℝ) (ht : t ∈ Icc (1:ℝ) 2) :
      (∫ x in Icc (1:ℝ) 2,g (x,t))=∫ x : ℝ in t..2,f (x,t) := by
    have hset : Icc (1:ℝ) 2 ∩ Ici t=Icc t 2 := by
      ext x
      constructor
      · rintro ⟨hx,ht'⟩; exact ⟨ht',hx.2⟩
      · intro hx; exact ⟨⟨ht.1.trans hx.1,hx.2⟩,hx.1⟩
    change (∫ x in Icc (1:ℝ) 2,(Ici t).indicator (fun x => f (x,t)) x)=_
    rw [setIntegral_indicator measurableSet_Ici,hset,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht.2]
  have he : (∫ x in Icc (1:ℝ) 2,∫ t in Icc (1:ℝ) 2,g (x,t))=
      ∫ x in Icc (1:ℝ) 2,∫ t : ℝ in 1..x,f (x,t) :=
    setIntegral_congr_fun measurableSet_Icc hleft
  have ho : (∫ t in Icc (1:ℝ) 2,∫ x in Icc (1:ℝ) 2,g (x,t))=
      ∫ t in Icc (1:ℝ) 2,∫ x : ℝ in t..2,f (x,t) :=
    setIntegral_congr_fun measurableSet_Icc hright
  rw [he,ho] at hs
  simpa only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)] using hs

end ErdosOmissionBindings

end

end Erdos970

end OAI
