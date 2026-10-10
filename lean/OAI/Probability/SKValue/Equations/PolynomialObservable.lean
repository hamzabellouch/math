import Mathlib
import OAI.Probability.SKValue.Evolution.SmoothFamily

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace SKValue
structure BoundedJoint (T:ℝ) (F:ℝ → ℝ → ℝ) : Prop where
  bounded : ∃ C:ℝ,0≤C ∧ ∀ t∈Icc (0:ℝ) T,∀ x,|F t x|≤C
  joint : ∃ L:ℝ,0≤L ∧ ∀ t∈Icc (0:ℝ) T,∀ s∈Icc (0:ℝ) T,∀ x y,
    |F s y-F t x|≤L*(|s-t|+|y-x|)
lemma BoundedJoint.const (T c:ℝ):BoundedJoint T (fun _ _ ↦ c) := by
  refine ⟨⟨|c|,abs_nonneg c,fun _ _ _ ↦ le_rfl⟩,⟨0,le_rfl,?_⟩⟩
  intros;simp
lemma BoundedJoint.add {T:ℝ} {F G:ℝ → ℝ → ℝ} (hF:BoundedJoint T F) (hG:BoundedJoint T G):
    BoundedJoint T (fun t x ↦ F t x+G t x) := by
  obtain ⟨A,hA,hFA⟩:=hF.bounded;obtain ⟨B,hB,hGB⟩:=hG.bounded
  obtain ⟨L,hL,hFL⟩:=hF.joint;obtain ⟨M,hM,hGM⟩:=hG.joint
  refine ⟨⟨A+B,add_nonneg hA hB,fun t ht x ↦ (abs_add_le _ _).trans (add_le_add (hFA t ht x) (hGB t ht x))⟩,
    ⟨L+M,add_nonneg hL hM,?_⟩⟩
  intro t ht s hs x y
  calc
    _ = |(F s y-F t x)+(G s y-G t x)| := by congr 1;ring
    _ ≤ |F s y-F t x|+|G s y-G t x| := abs_add_le _ _
    _ ≤ L*(|s-t|+|y-x|)+M*(|s-t|+|y-x|) := add_le_add (hFL t ht s hs x y) (hGM t ht s hs x y)
    _ = _ := by ring
lemma BoundedJoint.mul {T:ℝ} {F G:ℝ → ℝ → ℝ} (hF:BoundedJoint T F) (hG:BoundedJoint T G):
    BoundedJoint T (fun t x ↦ F t x*G t x) := by
  obtain ⟨A,hA,hFA⟩:=hF.bounded;obtain ⟨B,hB,hGB⟩:=hG.bounded
  obtain ⟨L,hL,hFL⟩:=hF.joint;obtain ⟨M,hM,hGM⟩:=hG.joint
  refine ⟨⟨A*B,mul_nonneg hA hB,?_⟩,⟨L*B+A*M,by positivity,?_⟩⟩
  · intro t ht x;rw [abs_mul];exact mul_le_mul (hFA t ht x) (hGB t ht x) (abs_nonneg _) hA
  · intro t ht s hs x y
    calc
      _ = |(F s y-F t x)*G s y+F t x*(G s y-G t x)| := by congr 1;ring
      _ ≤ |(F s y-F t x)*G s y|+|F t x*(G s y-G t x)| := abs_add_le _ _
      _ ≤ L*(|s-t|+|y-x|)*B+A*(M*(|s-t|+|y-x|)) := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul (hFL t ht s hs x y) (hGB s hs y) (abs_nonneg _) (by positivity))
          (mul_le_mul (hFA t ht x) (hGM t ht s hs x y) (abs_nonneg _) hA)
      _ = _ := by ring
lemma BoundedJoint.continuous {T:ℝ} {F:ℝ → ℝ → ℝ} (hF:BoundedJoint T F):
    ContinuousOn (fun p:ℝ×ℝ ↦ F p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  obtain ⟨L,hL,hl⟩:=hF.joint
  have hh:LipschitzOnWith ⟨2*L,by positivity⟩ (fun p:ℝ×ℝ ↦ F p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    simp only [Real.dist_eq,Prod.dist_eq]
    have hb:=hl q.1 hq.1 p.1 hp.1 q.2 p.2
    change |F p.1 p.2-F q.1 q.2|≤(2*L)*max |p.1-q.1| |p.2-q.2|
    nlinarith [le_max_left |p.1-q.1| |p.2-q.2|,le_max_right |p.1-q.1| |p.2-q.2|]
  exact hh.continuousOn
lemma BoundedJoint.spatial {T:ℝ} {F:ℝ → ℝ → ℝ} (hF:BoundedJoint T F):
    ∃ L:ℝ≥0,∀ t∈Icc (0:ℝ) T,LipschitzWith L (F t) := by
  obtain ⟨L,hL,hl⟩:=hF.joint
  refine ⟨Real.toNNReal L,fun t ht ↦ ?_⟩
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [Real.coe_toNNReal _ hL,Real.dist_eq,sub_self,abs_zero,zero_add] using hl t ht t ht y x
namespace JetExpr
noncomputable def spatial (e:JetExpr):JetExpr := D (fun n ↦ coord (n+1)) e
noncomputable def spatialIter : ℕ → JetExpr → JetExpr
  | 0,e => e
  | n+1,e => spatial (spatialIter n e)
end JetExpr
noncomputable def polyJet (V:ℝ → ℝ → ℝ) (e:JetExpr) (t x:ℝ):ℝ :=
  e.eval (fun n ↦ iteratedDeriv n (deriv (V t)) x)
lemma SmoothEvolution.polyJet_joint {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (e:JetExpr):BoundedJoint T (polyJet V e) := by
  induction e with
  | const c => exact BoundedJoint.const T c
  | coord n =>
    obtain ⟨L,hL,hl⟩:=h.jet_joint n
    exact ⟨h.bound n,⟨L,hL,fun t ht s hs x y ↦ hl s hs t ht x y⟩⟩
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf
lemma SmoothEvolution.polyJet_smooth {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (e:JetExpr) {t:ℝ} (ht:t∈Icc (0:ℝ) T):
    ContDiff ℝ ∞ (polyJet V e t) := by
  induction e with
  | const c => exact contDiff_const
  | coord n => exact ((h.slices t ht).jets.iteratedDeriv n).smooth
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf
lemma SmoothEvolution.polyJet_hasDeriv {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (e:JetExpr) {t:ℝ} (ht:t∈Icc (0:ℝ) T) (x:ℝ):
    HasDerivAt (polyJet V e t) (polyJet V e.spatial t x) x := by
  apply JetExpr.hasDerivAt_eval
  intro n
  simpa only [JetExpr.eval,iteratedDeriv_succ] using
    (((h.slices t ht).jets.iteratedDeriv n).smooth.differentiable (by norm_num) x).hasDerivAt
lemma SmoothEvolution.polyJet_iterated {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (e:JetExpr) {t:ℝ} (ht:t∈Icc (0:ℝ) T) (n:ℕ):
    iteratedDeriv n (polyJet V e t)=polyJet V (e.spatialIter n) t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    exact (h.polyJet_hasDeriv _ ht x).deriv
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmoothFamily.at_continuous {T:ℝ} {F:ℝ → ℝ → ℝ}
    (h:BoundedSmoothFamily T F) (x:ℝ) : ContinuousOn (fun t ↦ F t x) (Icc (0:ℝ) T) := by
  have hh := (h.joint 0).comp (continuousOn_id.prodMk continuousOn_const) (fun t ht ↦ ⟨ht,mem_univ x⟩)
  simpa only [iteratedDeriv_zero,Function.comp_def,id_eq] using hh

noncomputable def weightedFamilyIntegral (a b : ℝ) (γ : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in a..b, γ s*F s x

lemma BoundedSmoothFamily.weightedFamilyIntegral_hasDerivAt {T a b : ℝ} {γ : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (hi : IntervalIntegrable γ volume a b)
    (ha : 0≤a) (hab : a≤b) (hb : b≤T) (x : ℝ) :
    HasDerivAt (weightedFamilyIntegral a b γ F) (weightedFamilyIntegral a b γ (fun t ↦ _root_.deriv (F t)) x) x := by
  have hfi (u : ℝ) : IntervalIntegrable (fun s ↦ γ s*F s u) volume a b := by
    apply hi.mul_continuousOn
    simpa only [uIcc_of_le hab] using (h.at_continuous u).mono (Icc_subset_Icc ha hb)
  have hf'i (u : ℝ) : IntervalIntegrable (fun s ↦ γ s*_root_.deriv (F s) u) volume a b := by
    apply hi.mul_continuousOn
    simpa only [uIcc_of_le hab] using (h.deriv.at_continuous u).mono (Icc_subset_Icc ha hb)
  obtain ⟨C,hC,hbd⟩ := h.bound 1
  simp only [iteratedDeriv_one] at hbd
  have hi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u s ↦ γ s*F s u)
    (F' := fun u s ↦ γ s*_root_.deriv (F s) u)
    (s := univ) (bound := fun s ↦ |γ s| * C) (μ := volume.restrict (Ioc a b))
    univ_mem (Eventually.of_forall (fun u ↦ ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfi u)).aestronglyMeasurable))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfi x))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hf'i x)).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      intro u _
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (hbd s ⟨ha.trans hs.1.le,hs.2.trans hb⟩ u) (abs_nonneg _))
    (hi'.abs.mul_const C)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      intro u _
      have hfs := h.slices s ⟨ha.trans hs.1.le,hs.2.trans hb⟩
      exact ((hfs.smooth.differentiable (by norm_num)) u).hasDerivAt.const_mul (γ s))
  change HasDerivAt (fun u ↦ ∫ s in a..b, γ s*F s u)
    (∫ s in a..b, γ s*_root_.deriv (F s) x) x
  simpa only [intervalIntegral.integral_of_le hab] using hd.2

end SKValue

end

end OAI
