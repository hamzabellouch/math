import OAI.MathematicalPhysics.Transonic.Exterior.Continuation

namespace OAI

section
noncomputable section

namespace SepticProfile.RegularContinuation
open Set Metric
open scoped NNReal

/-- Parameter dependence for the regular portion of the shooting construction.
We use the actual scalar vector field with explicit clamping, and freeze the
parameter as a second ODE coordinate. Clamping is removed only after comparison. -/
theorem exists_continuous_clamped_family {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {a b p q c d : ℝ} (hab : a≤b) (hpq : p≤q) (hcd : c≤d)
    {f : ℝ × (ℝ×ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b ×ˢ (Icc p q ×ˢ Icc c d)))
    (parameter initial : A → ℝ) (hpar : Continuous parameter) (hini : Continuous initial)
    (hparmem : ∀ x, parameter x ∈ Icc p q) :
    ∃ u : A → ℝ → ℝ,
      Continuous (fun v : A × ↥(Icc a b) => u v.1 v.2) ∧
      (∀ x, u x a=initial x) ∧
      ∀ x t, t ∈ Icc a b → HasDerivWithinAt (u x)
        (f (t,parameter x,clamp c d (u x t))) (Icc a b) t := by
  let S := Icc a b ×ˢ (Icc p q ×ˢ Icc c d)
  have hcomp : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨K,hK⟩ := hf.exists_lipschitzOnWith (by norm_num)
    ((convex_Icc a b).prod ((convex_Icc p q).prod (convex_Icc c d))) hcomp
  obtain ⟨B,hB⟩ := hcomp.exists_bound_of_continuousOn hf.continuousOn
  let L : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  let init : A → ℝ×ℝ := fun x => (parameter x,initial x)
  have hic : Continuous init := hpar.prodMk hini
  obtain ⟨B0,hB0⟩ := isCompact_univ.exists_bound_of_continuousOn hic.continuousOn
  let r : ℝ≥0 := ⟨max B0 0+1,by positivity⟩
  let R : ℝ≥0 := ⟨(L:ℝ)*(b-a)+(r:ℝ)+1,by have := L.coe_nonneg;have := r.coe_nonneg;nlinarith⟩
  let F : ℝ → (ℝ×ℝ) → (ℝ×ℝ) := fun t w => (0,f (t,clamp p q w.1,clamp c d w.2))
  have hLip (t:ℝ) (ht:t ∈ Icc a b) : LipschitzWith K (F t) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    have hb1 := hK.norm_sub_le
      (show (t,clamp p q x.1,clamp c d x.2) ∈ S from ⟨ht,clamp_mem hpq _,clamp_mem hcd _⟩)
      (show (t,clamp p q y.1,clamp c d y.2) ∈ S from ⟨ht,clamp_mem hpq _,clamp_mem hcd _⟩)
    have hb2 := (clamp_lipschitz p q).norm_sub_le x.1 y.1
    have hb3 := (clamp_lipschitz c d).norm_sub_le x.2 y.2
    simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero] at hb1
    rw [max_eq_right (le_trans (norm_nonneg _) (le_max_left _ _))] at hb1
    simp only [NNReal.coe_one,one_mul] at hb2 hb3
    change ‖((0:ℝ),f (t,clamp p q x.1,clamp c d x.2))-
      (0,f (t,clamp p q y.1,clamp c d y.2))‖≤_
    rw [Prod.norm_def]
    simp only [Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,max_eq_right (norm_nonneg _)]
    simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub] using
      hb1.trans (mul_le_mul_of_nonneg_left (max_le_max hb2 hb3) K.coe_nonneg)
  let t0 : Icc a b := ⟨a,le_rfl,hab⟩
  have hPic : IsPicardLindelof F t0 (0:ℝ×ℝ) R r L K := by
    refine ⟨fun t ht => (hLip t ht).lipschitzOnWith,?_,?_,?_⟩
    · intro w _
      have hc := hf.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => (show (t,clamp p q w.1,clamp c d w.2) ∈ S from
          ⟨ht,clamp_mem hpq _,clamp_mem hcd _⟩))
      exact continuousOn_const.prodMk hc
    · intro t ht w _
      change ‖((0:ℝ),f (t,clamp p q w.1,clamp c d w.2))‖≤(L:ℝ)
      rw [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
      exact (hB _ ⟨ht,clamp_mem hpq _,clamp_mem hcd _⟩).trans (le_max_left _ _)
    · change (L:ℝ)*max (b-a) (a-a)≤(R:ℝ)-(r:ℝ)
      rw [sub_self,max_eq_left (sub_nonneg.mpr hab)]
      change (L:ℝ)*(b-a)≤((L:ℝ)*(b-a)+(r:ℝ)+1)-(r:ℝ)
      linarith
  obtain ⟨α,hα,hαc⟩ := hPic.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have himem (x:A) : init x ∈ closedBall (0:ℝ×ℝ) r := by
    rw [mem_closedBall_zero_iff]
    have hb := hB0 x (mem_univ x)
    exact hb.trans (by change B0 ≤ max B0 0+1;linarith [le_max_left B0 0])
  have hfreeze (x:A) (t:ℝ) (ht:t ∈ Icc a b) : (α (init x,t)).1=parameter x := by
    have hd : ∀ s ∈ Icc a b, HasDerivWithinAt (fun t => (α (init x,t)).1) 0 (Icc a b) s :=
      fun s hs => (hα (init x) (himem x)).2 s hs |>.fst
    have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (fun s hs => (show ‖(0:ℝ)‖≤(0:ℝ) by norm_num)) (convex_Icc a b)
      (show a ∈ Icc a b from ⟨le_rfl,hab⟩) ht
    rw [(hα (init x) (himem x)).1] at hb
    simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero,init] using hb
  let u : A → ℝ → ℝ := fun x t => (α (init x,t)).2
  refine ⟨u,?_,?_,?_⟩
  · exact (hαc.comp_continuous ((hic.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
      (fun v => ⟨himem v.1,v.2.property⟩)).snd
  · intro x
    exact congrArg Prod.snd (hα (init x) (himem x)).1
  · intro x t ht
    have hd := ((hα (init x) (himem x)).2 t ht).snd
    change HasDerivWithinAt (u x) (f (t,clamp p q (α (init x,t)).1,clamp c d (u x t))) _ t at hd
    rw [hfreeze x t ht,clamp_eq (hparmem x)] at hd
    exact hd

end SepticProfile.RegularContinuation

end
end

end OAI
