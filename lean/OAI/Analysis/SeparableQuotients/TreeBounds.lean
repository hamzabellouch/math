import OAI.Analysis.SeparableQuotients.StoppedCharges

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def TypeII.childEvals {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) : TypeII.ChildVectors e s :=
  fun g h => w.evalVector s (TypeI.lowAssign w ((e.path g.1).piece g.2) s I h)
    (restrict ((e.crop g.1).set f) (((e.path g.1).piece g.2).child h))

lemma TypeII.recombineEarly_add {f : Family} (e : TypeII f) (J : ℕ) (s : Finset ℕ)
    (v u : TypeII.ChildVectors e s) (i : s) :
    TypeII.recombineEarly e J s (fun g h i => v g h i + u g h i) i =
      TypeII.recombineEarly e J s v i + TypeII.recombineEarly e J s u i := by
  simp only [TypeII.recombineEarly,Finset.sum_add_distrib,mul_add]

lemma TypeII.recombineEarly_mono {f : Family} (e : TypeII f) (J : ℕ) (s : Finset ℕ)
    (v u : TypeII.ChildVectors e s) (h : ∀ g h i, v g h i ≤ u g h i) (i : s) :
    TypeII.recombineEarly e J s v i ≤ TypeII.recombineEarly e J s u i := by
  apply Finset.sum_le_sum
  intro g _
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun k _ => h g k i)

lemma ThinnedWindows.low_refined_bound {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s)
    (i : s) (hi : i ∈ I) :
    (∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| *
        (if TypeII.groupWeight e g < w.lower i then
          |norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g)| else 0)) ≤
      TypeII.earlyBoundary e w s I i + TypeII.lateVector e w s I i +
        TypeII.recombineEarly e J s (TypeII.childEvals e w s I) i := by
  have hh (g : TypeII.Group e) : (if TypeII.groupWeight e g < w.lower i then
        |norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g)| else 0) ≤
      if TypeII.groupWeight e g < J then TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I i +
        TypeII.continuation e w s I g i else TypeI.stoppedCharge w ((e.path g.1).piece g.2) s I i := by
    by_cases hlow : TypeII.groupWeight e g < w.lower i
    · rw [ite_eq_left hlow]
      split_ifs with hj
      · exact TypeI.low_eval_bound w ((e.path g.1).piece g.2) (e.crop g.1) (hm g.1 g.2) s I i hi hlow
      · exact TypeI.stopped_eval_bound w ((e.path g.1).piece g.2) (e.crop g.1) (hm g.1 g.2) s I i hi hlow
    · rw [ite_eq_right hlow]
      split_ifs
      · exact add_nonneg (TypeI.boundaryCharge_nonneg ..) (TypeII.continuation_nonneg ..)
      · exact TypeI.stoppedCharge_nonneg ..
  calc
    _ ≤ ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| *
        (if TypeII.groupWeight e g < J then TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I i +
          TypeII.continuation e w s I g i else TypeI.stoppedCharge w ((e.path g.1).piece g.2) s I i) :=
      Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (hh g) (abs_nonneg _))
    _ = _ := by
      unfold TypeII.earlyBoundary TypeII.lateVector TypeII.recombineEarly TypeII.earlyGroups TypeII.lateGroups
      simp only [Finset.sum_filter]
      rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hj : TypeII.groupWeight e g < J
      · simp only [hj,ite_true,not_le.mpr hj,ite_false,add_zero,TypeII.continuation,TypeII.childEvals,mul_add]
      · simp only [hj,ite_false,not_lt.mp hj,ite_true,zero_add,add_zero]

lemma ThinnedWindows.node_refined_majorant {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s) (i : s) :
    w.evalVector s I e.value i ≤ w.localSmall e s I i+w.localLarge e hm s I i+
      TypeII.recombineEarly e J s (TypeII.childEvals e w s I) i := by
  by_cases hi : i ∈ I
  · have hn := w.node_split e hm s i
    have hl := w.low_refined_bound e hm s I i hi
    simp only [ThinnedWindows.evalVector,ThinnedWindows.localSmall,ThinnedWindows.localLarge,hi,ite_true]
    linarith
  · rw [w.localSmall_support e s I i hi,w.localLarge_support e hm s I i hi]
    simp only [ThinnedWindows.evalVector,hi,ite_false,zero_add]
    exact TypeII.recombineEarly_nonneg e J s (TypeII.childEvals e w s I) (fun _ _ _ => w.evalVector_nonneg ..) i

lemma Family.norming_crop (f : Family) (A : Crop) (g : Array) (hg : g ∈ f.norming) :
    restrict (A.set f) g ∈ f.norming := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hg
  exact Set.mem_iUnion.mpr ⟨n,Family.stage_crop f n A g hn⟩

lemma Family.norming_cases (f : Family) (g : Array) (hg : g ∈ f.norming) :
    g ∈ f.base ∨ ∃ e : TypeII f, e.value = g ∧ ∀ b i j, ((e.path b).piece i).child j ∈ f.norming := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hg
  induction n with
  | zero => exact Or.inl hn
  | succ n ih =>
    rcases hn with (hn | ⟨e,rfl,he⟩) | ⟨e,rfl,he⟩
    · exact ih hn
    · refine Or.inr ⟨e.toTypeII,e.toTypeII_value,fun _ _ h => ?_⟩
      exact Set.mem_iUnion.mpr ⟨n,he h⟩
    · exact Or.inr ⟨e,rfl,fun b i j => Set.mem_iUnion.mpr ⟨n,he b i j⟩⟩

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def smallBudget (f : Family) (J d : ℕ) : ℝ :=
  (1552/7)*f.theta J+64*(1/8)^d
noncomputable def largeUnit (f : Family) (J : ℕ) (s : Finset ℕ) : ℝ :=
  16*(1+(Parameters.B f.s (J-1) : ℝ)+(s.card : ℝ)^(1-1/f.q))
noncomputable def largeBudget (f : Family) (J : ℕ) (s : Finset ℕ) (d : ℕ) : ℝ :=
  largeUnit f J s*(1+(Parameters.B f.s (J-1) : ℝ))^d

lemma smallBudget_nonneg (f : Family) (J d : ℕ) : 0 ≤ smallBudget f J d := by
  unfold smallBudget
  have := f.theta_nonneg J
  positivity
lemma largeUnit_ge (f : Family) (J : ℕ) (s : Finset ℕ) : 16 ≤ largeUnit f J s := by
  unfold largeUnit
  have : 0 ≤ (s.card : ℝ)^(1-1/f.q) := Real.rpow_nonneg (by positivity) _
  have : 0 ≤ (Parameters.B f.s (J-1) : ℝ) := by positivity
  linarith
lemma largeBudget_ge (f : Family) (J : ℕ) (s : Finset ℕ) (d : ℕ) : largeUnit f J s ≤ largeBudget f J s d := by
  unfold largeBudget
  exact le_mul_of_one_le_right (by linarith [largeUnit_ge f J s]) (one_le_pow₀ (by
    have hb : 0 ≤ (Parameters.B f.s (J-1) : ℝ) := by positivity
    linarith))
lemma largeBudget_nonneg (f : Family) (J : ℕ) (s : Finset ℕ) (d : ℕ) : 0 ≤ largeBudget f J s d := by
  linarith [largeUnit_ge f J s,largeBudget_ge f J s d]
lemma smallBudget_succ (f : Family) (J d : ℕ) :
    194*f.theta J+smallBudget f J d/8 = smallBudget f J (d+1) := by
  unfold smallBudget
  rw [pow_succ]
  ring
lemma largeBudget_step (f : Family) (J : ℕ) (s : Finset ℕ) (d : ℕ) :
    largeUnit f J s+(Parameters.B f.s (J-1) : ℝ)*largeBudget f J s d ≤ largeBudget f J s (d+1) := by
  calc
    _ ≤ largeBudget f J s d+(Parameters.B f.s (J-1) : ℝ)*largeBudget f J s d :=
      add_le_add (largeBudget_ge f J s d) le_rfl
    _ = _ := by unfold largeBudget; rw [pow_succ]; ring

structure DepthMajorant {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (g : Array) (d : ℕ) where
  small : s → ℝ
  large : s → ℝ
  small_nonneg : ∀ i, 0 ≤ small i
  large_nonneg : ∀ i, 0 ≤ large i
  small_support : ∀ i, i ∉ I → small i = 0
  large_support : ∀ i, i ∉ I → large i = 0
  majorizes : ∀ i, w.evalVector s I g i ≤ small i+large i
  norm_small : ‖vec f.exponent small‖ ≤ smallBudget f J d
  sum_large : (∑ i : s, large i) ≤ largeBudget f J s d

lemma ThinnedWindows.exists_depthMajorant {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ)
    (hJ : 1 ≤ J) (hs : s.card ≤ f.L J) (hε : ε*(s.card : ℝ)^(1/f.r) ≤ f.theta J)
    (d : ℕ) (I : Finset s) (g : Array) (hg : g ∈ f.norming) :
    Nonempty (DepthMajorant w s I g d) := by
  induction d generalizing I g with
  | zero =>
    refine ⟨⟨w.evalVector s I g,fun _ => 0,w.evalVector_nonneg s I g,fun _ => le_rfl,?_,?_,?_,?_,?_⟩⟩
    · intro i hi
      simp only [ThinnedWindows.evalVector,hi,ite_false]
    · exact fun _ _ => rfl
    · intro i
      exact (add_zero _).ge
    · apply (w.norming_uniform s (hε.trans (Family.theta_le_one f J)) g hg I).trans
      unfold smallBudget
      simp only [pow_zero,mul_one]
      have := f.theta_nonneg J
      linarith
    · simpa only [Finset.sum_const_zero] using largeBudget_nonneg f J s 0
  | succ d ih =>
    rcases Family.norming_cases f g hg with hbase | ⟨e,rfl,he⟩
    · refine ⟨⟨fun _ => 0,w.evalVector s I g,fun _ => le_rfl,w.evalVector_nonneg s I g,?_,?_,?_,?_,?_⟩⟩
      · exact fun _ _ => rfl
      · intro i hi
        simp only [ThinnedWindows.evalVector,hi,ite_false]
      · intro i
        exact (zero_add _).ge
      · simpa only [show vec f.exponent (fun _ : s => (0 : ℝ)) = 0 from rfl,norm_zero] using smallBudget_nonneg f J (d+1)
      · linarith [(w.evalVector_base s I g hbase).2,largeUnit_ge f J s,largeBudget_ge f J s (d+1)]
    · let C (k : TypeII.Group e) (h : Fin ((e.path k.1).piece k.2).length) :=
        Classical.choice (ih (TypeI.lowAssign w ((e.path k.1).piece k.2) s I h)
          (restrict ((e.crop k.1).set f) (((e.path k.1).piece k.2).child h))
          (Family.norming_crop f _ _ (he k.1 k.2 h)))
      let v : TypeII.ChildVectors e s := fun k h => (C k h).small
      let u : TypeII.ChildVectors e s := fun k h => (C k h).large
      refine ⟨⟨fun i => w.localSmall e s I i+TypeII.recombineEarly e J s v i,
        fun i => w.localLarge e he s I i+TypeII.recombineEarly e J s u i,?_,?_,?_,?_,?_,?_,?_⟩⟩
      · intro i
        exact add_nonneg (w.localSmall_nonneg e s I i)
          (TypeII.recombineEarly_nonneg e J s v (fun k h i => (C k h).small_nonneg i) i)
      · intro i
        exact add_nonneg (w.localLarge_nonneg e he s I i)
          (TypeII.recombineEarly_nonneg e J s u (fun k h i => (C k h).large_nonneg i) i)
      · intro i hi
        rw [w.localSmall_support e s I i hi,TypeII.recombineEarly_support e w s I v
          (fun k h i hi => (C k h).small_support i hi) i hi,add_zero]
      · intro i hi
        rw [w.localLarge_support e he s I i hi,TypeII.recombineEarly_support e w s I u
          (fun k h i hi => (C k h).large_support i hi) i hi,add_zero]
      · intro i
        have hh := TypeII.recombineEarly_mono e J s (TypeII.childEvals e w s I)
          (fun k h i => v k h i+u k h i) (fun k h i => (C k h).majorizes i) i
        rw [TypeII.recombineEarly_add] at hh
        linarith [w.node_refined_majorant e he s I i]
      · change ‖vec f.exponent (w.localSmall e s I)+vec f.exponent (TypeII.recombineEarly e J s v)‖ ≤ _
        apply (norm_add_le _ _).trans
        rw [← smallBudget_succ]
        exact add_le_add (w.localSmall_norm e s I hJ hs hε)
          (TypeII.recombineEarly_norm e w s I v (smallBudget f J d) (smallBudget_nonneg f J d)
            (fun k h i hi => (C k h).small_support i hi) (fun k h => (C k h).norm_small))
      · rw [Finset.sum_add_distrib]
        exact (add_le_add (w.localLarge_l1 e he s I)
          (TypeII.recombineEarly_l1 e J s u (largeBudget f J s d) (largeBudget_nonneg f J s d)
            (fun k h i => (C k h).large_nonneg i) (fun k h => (C k h).sum_large))).trans
          (largeBudget_step f J s d)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

lemma Family.qprime_formula (f : Family) : 1-1/f.q = 1/((f.s : ℝ)+1) := by
  have hs : (0 : ℝ) < f.s := by exact_mod_cast (show 0 < f.s by have := f.s_ge_two; omega)
  unfold Norming.Family.q Parameters.q
  field_simp
  ring

lemma Family.holder_theta (f : Family) (J : ℕ) :
    (f.L J : ℝ)^(1-1/f.r)*f.theta J = (f.L J : ℝ)/(f.m J : ℝ) := by
  have hL : (0 : ℝ) < f.L J := by exact_mod_cast f.L_pos J
  rw [f.theta_formula,← mul_div_assoc,← Real.rpow_add hL]
  rw [show 1-1/f.r+1/f.r = 1 by ring,Real.rpow_one]

lemma ThinnedWindows.sum_eval_bound {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (hJ : 1 ≤ J) (hs : s.card = f.L J)
    (hε : ε*(s.card : ℝ)^(1/f.r) ≤ f.theta J) (g : Array) (hg : g ∈ f.norming) :
    (∑ i : s, |norming.evaluateArray (w.blocks.embed i) g|) ≤ 500*(f.L J : ℝ)/(f.m J : ℝ) := by
  let d := Parameters.d (J-1)
  obtain ⟨c⟩ := w.exists_depthMajorant s hJ hs.le hε d Finset.univ g hg
  have hb : smallBudget f J d ≤ (2000/7)*f.theta J := by
    have hh := Parameters.depth_theta_bound f.s_ge_two (J-1)
    change (1/8 : ℝ)^d ≤ f.theta J at hh
    unfold smallBudget
    linarith
  have hlarge : largeBudget f J s d ≤ 16*((f.L J : ℝ)/(f.m J : ℝ)) := by
    have hh := Parameters.depth_bound f.s_ge_two (J-1)
    unfold largeBudget largeUnit
    rw [hs,Family.qprime_formula]
    change 16*(1+(Parameters.B f.s (J-1) : ℝ)+(Parameters.L f.s (J-1) : ℝ)^(1/((f.s : ℝ)+1))) *
      (1+(Parameters.B f.s (J-1) : ℝ))^d ≤ 16*((Parameters.L f.s (J-1) : ℝ)/(Parameters.m f.s (J-1) : ℝ))
    nlinarith [hh]
  have hsmall : (∑ i : s, c.small i) ≤ (2000/7)*((f.L J : ℝ)/(f.m J : ℝ)) := by
    have hh := sum_abs_le_holder (by simpa only [Family.exponent_toReal] using f.r_gt_one : 1 < f.exponent.toReal) c.small
    simp only [abs_of_nonneg (c.small_nonneg _),Family.exponent_toReal,Fintype.card_coe,hs] at hh
    calc
      _ ≤ (f.L J : ℝ)^(1-1/f.r)*‖vec f.exponent c.small‖ := hh
      _ ≤ (f.L J : ℝ)^(1-1/f.r)*((2000/7)*f.theta J) :=
        mul_le_mul_of_nonneg_left (c.norm_small.trans hb) (Real.rpow_nonneg (by positivity) _)
      _ = _ := by rw [mul_left_comm,Family.holder_theta]
  have hmain : (∑ i : s, |norming.evaluateArray (w.blocks.embed i) g|) ≤
      (∑ i : s, c.small i)+(∑ i : s, c.large i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    simpa only [ThinnedWindows.evalVector,Finset.mem_univ,ite_true] using c.majorizes i
  have hpos : 0 ≤ (f.L J : ℝ)/(f.m J : ℝ) := by positivity
  have hl := c.sum_large.trans hlarge
  calc
    _ ≤ (2000/7+16)*((f.L J : ℝ)/(f.m J : ℝ)) := by linarith
    _ ≤ 500*((f.L J : ℝ)/(f.m J : ℝ)) := mul_le_mul_of_nonneg_right (by norm_num) hpos
    _ = _ := by ring

lemma ThinnedWindows.norm_sum_bound {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (hJ : 1 ≤ J) (hs : s.card = f.L J)
    (hε : ε*(s.card : ℝ)^(1/f.r) ≤ f.theta J) :
    ‖norming.includeFinite (∑ i : s, w.blocks.vector i)‖ ≤ 500*(f.L J : ℝ)/(f.m J : ℝ) := by
  have hb (g : Array) (hg : g ∈ f.norming) :
      |norming.evaluateArray (norming.includeFinite (∑ i : s, w.blocks.vector i)) g| ≤
      500*(f.L J : ℝ)/(f.m J : ℝ) := by
    have hf : g ∈ Full := f.norming_subset_full hg
    rw [norming.evaluateArray_eq_functional _ ⟨g,hf⟩,map_sum,map_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [BlockSequence.embed,norming.evaluateArray_eq_functional _ ⟨g,hf⟩] using w.sum_eval_bound s hJ hs hε g hg
  cases f with
  | mixed => exact norming.norm_le_of_evaluateArray _ _ (by positivity) hb
  | pure k =>
    apply norm_le_of_pure k _ _ _ (by positivity) hb
    intro α hα
    rw [norming.coordinate_includeFinite,Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    exact Finsupp.notMem_support_iff.mp (fun hi => hα (w.blocks.pure_color k rfl i α hi))

end SeparableQuotient.ActualSpace

end

end OAI
