import OAI.Analysis.SeparableQuotients.NormingTrees

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

lemma TypeI.eval_crop_sum {f : Family} (e : TypeI f) (A : Crop) (x : E) :
    norming.evaluateArray x (restrict (A.set f) e.value) =
      (1/(f.m e.weight : ℝ)) * ∑ h, norming.evaluateArray x (restrict (A.set f) (e.child h)) := by
  simp only [TypeI.value,restrict_smul,restrict_sum,map_smul,map_sum,Rat.smul_def,
    Rat.cast_div,Rat.cast_one,Rat.cast_natCast]

noncomputable def TypeI.lowAssign {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) (h : Fin e.length) : Finset s :=
  I.filter (fun i => e.weight < w.lower i ∧ TypeI.hitChildren e (w.blocks.vector i) = {h})

lemma TypeI.lowAssign_subset {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) (h : Fin e.length) :
    TypeI.lowAssign w e s I h ⊆ I := Finset.filter_subset _ _

lemma TypeI.lowAssign_disjoint {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s)
    (h k : Fin e.length) (hhk : h ≠ k) :
    Disjoint (TypeI.lowAssign w e s I h) (TypeI.lowAssign w e s I k) := by
  apply Finset.disjoint_left.mpr
  intro i hi hk
  exact hhk (Finset.singleton_injective ((Finset.mem_filter.mp hi).2.2.symm.trans (Finset.mem_filter.mp hk).2.2))

noncomputable def TypeI.boundaryDegree {f : Family} (e : TypeI f) (z : BlockSequence f) (i : ℕ) : ℝ :=
  if 2 ≤ (TypeI.hitChildren e (z.vector i)).card then (TypeI.hitChildren e (z.vector i)).card else 0

lemma TypeI.boundaryDegree_nonneg {f : Family} (e : TypeI f) (z : BlockSequence f) (i : ℕ) :
    0 ≤ TypeI.boundaryDegree e z i := by unfold TypeI.boundaryDegree; split_ifs <;> positivity

lemma TypeI.boundaryDegree_sum {f : Family} (e : TypeI f) (z : BlockSequence f) (s : Finset ℕ) :
    (∑ i : s, TypeI.boundaryDegree e z i) ≤ 2 * (e.length : ℝ) := by
  have he : (∑ i : s, TypeI.boundaryDegree e z i) =
      ((∑ i ∈ s.filter (fun i => 2 ≤ (TypeI.hitChildren e (z.vector i)).card),
        (TypeI.hitChildren e (z.vector i)).card : ℕ) : ℝ) := by
    simp only [TypeI.boundaryDegree,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
    exact (Finset.sum_coe_sort s (fun i : ℕ => if 2 ≤ (TypeI.hitChildren e (z.vector i)).card then ((TypeI.hitChildren e (z.vector i)).card : ℝ) else 0))
  rw [he]
  exact_mod_cast TypeI.boundary_incidence e z s

noncomputable def TypeI.boundaryCharge {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  if i ∈ I ∧ e.weight < w.lower i then
    (16 / (f.m e.weight : ℝ)) * (TypeI.boundaryDegree e w.blocks i)^(1/f.r) else 0

lemma TypeI.boundaryCharge_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) (i : s) :
    0 ≤ TypeI.boundaryCharge w e s I i := by
  have hd := TypeI.boundaryDegree_nonneg e w.blocks i
  unfold TypeI.boundaryCharge
  split_ifs <;> positivity

lemma TypeI.boundaryCharge_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) :
    ‖vec f.exponent (TypeI.boundaryCharge w e s I)‖ ≤ 32 * f.theta e.weight := by
  have hm : 0 < (f.m e.weight : ℝ) := by exact_mod_cast f.m_pos e.weight
  have hb := norm_degree_le (by simpa only [Family.exponent_toReal] using f.r_pos : 0 < f.exponent.toReal)
    (fun i : s => TypeI.boundaryDegree e w.blocks i) (16/(f.m e.weight : ℝ)) (2*e.length)
    (by positivity) (by positivity) (fun i => TypeI.boundaryDegree_nonneg e w.blocks i)
    (TypeI.boundaryDegree_sum e w.blocks s) (TypeI.boundaryCharge w e s I) (fun i => by
      rw [abs_of_nonneg (TypeI.boundaryCharge_nonneg w e s I i)]
      unfold TypeI.boundaryCharge
      split_ifs
      · simp only [Family.exponent_toReal,le_refl]
      · exact mul_nonneg (by positivity) (Real.rpow_nonneg (TypeI.boundaryDegree_nonneg e w.blocks i) _))
  have hr : 1/f.r ≤ 1 := (div_le_one f.r_pos).mpr f.r_gt_one.le
  have h2 : (2 : ℝ)^(1/f.r) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hr
  calc
    _ ≤ (16/(f.m e.weight : ℝ)) * (2*(e.length : ℝ))^(1/f.r) := by simpa only [Family.exponent_toReal] using hb
    _ ≤ (16/(f.m e.weight : ℝ)) * (2*(f.L e.weight : ℝ)^(1/f.r)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg _)]
      exact mul_le_mul h2 (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast e.length_le) (one_div_nonneg.mpr f.r_pos.le))
        (by positivity) (by norm_num)
    _ = _ := by rw [Family.theta_formula]; ring

lemma TypeI.low_eval_bound {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (A : Crop)
    (hm : ∀ h, e.child h ∈ f.norming) (s : Finset ℕ) (I : Finset s) (i : s)
    (hi : i ∈ I) (hj : e.weight < w.lower i) :
    |norming.evaluateArray (w.blocks.embed i) (restrict (A.set f) e.value)| ≤
      TypeI.boundaryCharge w e s I i + (1/(f.m e.weight : ℝ)) *
      ∑ h, if i ∈ TypeI.lowAssign w e s I h then
        |norming.evaluateArray (w.blocks.embed i) (restrict (A.set f) (e.child h))| else 0 := by
  have hr : 0 < 1/f.r := one_div_pos.mpr f.r_pos
  have hb := TypeI.cropped_child_sum_bound e A hm (w.blocks.vector i) (f.L (w.lower i)) 16
    (by norm_num) (w.partition i) (e.length_le.trans (FamilyL_mono f hj.le))
  rw [TypeI.eval_crop_sum,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/(f.m e.weight : ℝ))]
  apply le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity))
  let H := TypeI.hitChildren e (w.blocks.vector i)
  by_cases hd : 2 ≤ H.card
  · have hu : TypeI.boundaryCharge w e s I i = 16/(f.m e.weight : ℝ) * (H.card : ℝ)^(1/f.r) := by
      simp only [TypeI.boundaryCharge,hi,hj,and_self,ite_true,TypeI.boundaryDegree,show 2 ≤ (TypeI.hitChildren e (w.blocks.vector i)).card from hd,H]
    rw [hu]
    have hc := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1/(f.m e.weight : ℝ))
    have hn : 0 ≤ (1/(f.m e.weight : ℝ)) * ∑ h, if i ∈ TypeI.lowAssign w e s I h then
        |norming.evaluateArray (w.blocks.embed i) (restrict (A.set f) (e.child h))| else 0 := by positivity
    dsimp only [BlockSequence.embed] at hc hn ⊢
    dsimp only [H] at ⊢
    calc
      _ ≤ (1/(f.m e.weight : ℝ)) * (16*((TypeI.hitChildren e (w.blocks.vector i)).card : ℝ)^(1/f.r)) := hc
      _ = 16/(f.m e.weight : ℝ) * ((TypeI.hitChildren e (w.blocks.vector i)).card : ℝ)^(1/f.r) := by ring
      _ ≤ _ := le_add_of_nonneg_right hn
  · have hsmall : H.card ≤ 1 := by omega
    have heq (h : Fin e.length) : (if i ∈ TypeI.lowAssign w e s I h then
        |norming.evaluateArray (w.blocks.embed i) (restrict (A.set f) (e.child h))| else 0) =
        |norming.evaluateArray (w.blocks.embed i) (restrict (A.set f) (e.child h))| := by
      by_cases hh : h ∈ H
      · have hH : H = {h} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hh, fun k hk =>
          (Finset.card_le_one.mp hsmall k hk h hh)⟩
        have ha : i ∈ TypeI.lowAssign w e s I h := Finset.mem_filter.mpr ⟨hi,hj,hH⟩
        simp only [ha,ite_true]
      · dsimp only [BlockSequence.embed]
        rw [TypeI.cropped_child_zero e A (w.blocks.vector i) h hh,abs_zero]
        simp
    simp_rw [heq]
    exact le_add_of_nonneg_left (TypeI.boundaryCharge_nonneg w e s I i)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

lemma Family.sum_theta_le {κ : Type*} (f : Family) (S : Finset κ) (j : κ → ℕ)
    (hp : ∀ g ∈ S, 1 ≤ j g) (hinj : Set.InjOn j S) :
    ∑ g ∈ S, f.theta (j g) ≤ 1/8 := by
  have hi : Set.InjOn (fun g => j g - 1) S := by
    intro g hg h hh he
    apply hinj hg hh
    have := hp g hg
    have := hp h hh
    dsimp only at he
    omega
  calc
    _ = ∑ n ∈ S.image (fun g => j g - 1), Parameters.theta f.s n := by
      rw [Finset.sum_image hi]
      rfl
    _ ≤ ∑' n, Parameters.theta f.s n :=
      (Parameters.hasSum_theta f.s_ge_two).summable.sum_le_tsum _
        (fun n _ => by rw [Parameters.theta_eq f.s_ge_two]; positivity)
    _ ≤ 1/8 := (Parameters.theta_sum_small f.s_ge_two).le

lemma TypeII.group_theta_sum {f : Family} (e : TypeII f) :
    ∑ g ∈ TypeII.activeGroups e, f.theta (TypeII.groupWeight e g) ≤ 1/8 :=
  Family.sum_theta_le f _ _ (fun g _ => ((e.path g.1).piece g.2).weight_pos) (TypeII.groupWeight_injOn e)

lemma TypeI.recombine_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s)
    (v : Fin e.length → s → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ h i, i ∉ TypeI.lowAssign w e s I h → v h i = 0)
    (hv : ∀ h, ‖vec f.exponent (v h)‖ ≤ K) :
    ‖vec f.exponent (fun i => (1/(f.m e.weight : ℝ)) * ∑ h, v h i)‖ ≤ K*f.theta e.weight := by
  have hd : ∀ h ∈ (Finset.univ : Finset (Fin e.length)), ∀ k ∈ Finset.univ, h ≠ k →
      ∀ i, v h i = 0 ∨ v k i = 0 := by
    intro h _ k _ hhk i
    by_cases hi : i ∈ TypeI.lowAssign w e s I h
    · exact Or.inr (hs k i (fun hk => Finset.disjoint_left.mp (TypeI.lowAssign_disjoint w e s I h k hhk) hi hk))
    · exact Or.inl (hs h i hi)
  have hb := norm_sum_disjoint_le (by simpa only [Family.exponent_toReal] using f.r_pos : 0 < f.exponent.toReal)
    Finset.univ v K hK hd (fun h _ => hv h)
  change ‖(1/(f.m e.weight : ℝ)) • vec f.exponent (fun i => ∑ h, v h i)‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1/(f.m e.weight : ℝ))]
  calc
    _ ≤ (1/(f.m e.weight : ℝ)) * (K*(e.length : ℝ)^(1/f.r)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Family.exponent_toReal,Finset.card_univ,Fintype.card_fin] using hb
    _ ≤ (1/(f.m e.weight : ℝ)) * (K*(f.L e.weight : ℝ)^(1/f.r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast e.length_le) (one_div_nonneg.mpr f.r_pos.le)) hK) (by positivity)
    _ = _ := by rw [Family.theta_formula]; ring

lemma TypeII.sum_vector_norm {f : Family} (e : TypeII f) (s : Finset ℕ)
    (v : TypeII.Group e → s → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hv : ∀ g ∈ TypeII.activeGroups e, ‖vec f.exponent (v g)‖ ≤ K*f.theta (TypeII.groupWeight e g)) :
    ‖vec f.exponent (fun i => ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| * v g i)‖ ≤ K/8 := by
  have hr : ∀ g, ‖vec f.exponent (fun i => |(e.coefficient g.1 : ℝ)| * v g i)‖ ≤ ‖vec f.exponent (v g)‖ := by
    intro g
    change ‖|(e.coefficient g.1 : ℝ)| • vec f.exponent (v g)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_abs]
    exact (mul_le_mul_of_nonneg_right (e.coefficient_le_one g.1) (norm_nonneg _)).trans_eq (one_mul _)
  calc
    _ ≤ ∑ g ∈ TypeII.activeGroups e, ‖vec f.exponent (fun i => |(e.coefficient g.1 : ℝ)| * v g i)‖ := by
      rw [vec_sum]
      exact norm_sum_le _ _
    _ ≤ ∑ g ∈ TypeII.activeGroups e, K*f.theta (TypeII.groupWeight e g) :=
      Finset.sum_le_sum (fun g hg => (hr g).trans (hv g hg))
    _ = K * ∑ g ∈ TypeII.activeGroups e, f.theta (TypeII.groupWeight e g) := (Finset.mul_sum ..).symm
    _ ≤ K*(1/8) := mul_le_mul_of_nonneg_left (TypeII.group_theta_sum e) hK
    _ = K/8 := by ring

lemma TypeI.boundaryCharge_l1 {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) :
    (∑ i : s, TypeI.boundaryCharge w e s I i) ≤ 32*e.length := by
  have hm : (1 : ℝ) ≤ f.m e.weight := by exact_mod_cast f.m_pos e.weight
  have hb (i : s) : TypeI.boundaryCharge w e s I i ≤ 16*TypeI.boundaryDegree e w.blocks i := by
    have hpos := TypeI.boundaryDegree_nonneg e w.blocks i
    unfold TypeI.boundaryCharge
    split_ifs
    · have hd : (TypeI.boundaryDegree e w.blocks i)^(1/f.r) ≤ TypeI.boundaryDegree e w.blocks i := by
        unfold TypeI.boundaryDegree
        split_ifs with hi
        · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast (show 1 ≤ (TypeI.hitChildren e (w.blocks.vector i)).card by omega))
            ((div_le_one f.r_pos).mpr f.r_gt_one.le)
        · rw [Real.zero_rpow (ne_of_gt (one_div_pos.mpr f.r_pos))]
      exact mul_le_mul (div_le_self (by norm_num) hm) hd (by positivity) (by norm_num)
    · positivity
  calc
    _ ≤ ∑ i : s, 16*TypeI.boundaryDegree e w.blocks i := Finset.sum_le_sum (fun i _ => hb i)
    _ = 16 * ∑ i : s, TypeI.boundaryDegree e w.blocks i := (Finset.mul_sum ..).symm
    _ ≤ 16*(2*e.length) := mul_le_mul_of_nonneg_left (TypeI.boundaryDegree_sum e w.blocks s) (by norm_num)
    _ = _ := by ring

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

lemma TypeII.sum_group_mask {f : Family} (e : TypeII f) (x : E) (p : ℕ → Prop) [DecidablePred p] :
    (∑ g ∈ TypeII.activeGroups e, if p (TypeII.groupWeight e g) then
      (e.coefficient g.1 : ℝ) * norming.evaluateArray x (TypeII.groupValue e g) else 0) =
    ∑ g : TypeII.Group e, if p (TypeII.groupWeight e g) then
      (e.coefficient g.1 : ℝ) * norming.evaluateArray x (TypeII.groupValue e g) else 0 := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro g _ hg
  have hz : TypeII.groupValue e g = 0 := by
    simpa only [TypeII.activeGroups,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hg
  simp [hz]

lemma TypeII.middle_group_sum {f : Family} (e : TypeII f) (x : E) (lo up : ℕ) :
    (∑ g ∈ TypeII.activeGroups e, if lo ≤ TypeII.groupWeight e g ∧ TypeII.groupWeight e g ≤ up then
      (e.coefficient g.1 : ℝ) * norming.evaluateArray x (TypeII.groupValue e g) else 0) =
    ∑ b, (e.coefficient b : ℝ) * norming.evaluateArray x
      (restrict ((e.crop b).set f) ((e.path b).window lo up)) := by
  rw [TypeII.sum_group_mask e x (fun j => lo ≤ j ∧ j ≤ up),Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro b _
  simp only [FinitePath.window,restrict_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  simp only [TypeII.groupWeight,TypeII.groupValue,(e.path b).weight_eq,(e.path b).value_eq]
  split_ifs <;> simp [restrict_zero]

lemma TypeII.eval_three_parts {f : Family} (e : TypeII f) (x : E) (lo up : ℕ) (hl : lo ≤ up) :
    norming.evaluateArray x e.value =
    (∑ g ∈ TypeII.activeGroups e, if TypeII.groupWeight e g < lo then
      (e.coefficient g.1 : ℝ) * norming.evaluateArray x (TypeII.groupValue e g) else 0) +
    (∑ b, (e.coefficient b : ℝ) * norming.evaluateArray x
      (restrict ((e.crop b).set f) ((e.path b).window lo up))) +
    (∑ g ∈ TypeII.activeGroups e, if up < TypeII.groupWeight e g then
      (e.coefficient g.1 : ℝ) * norming.evaluateArray x (TypeII.groupValue e g) else 0) := by
  rw [TypeII.eval_group_sum,← TypeII.middle_group_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hL : TypeII.groupWeight e g < lo
  · have hm : ¬ (lo ≤ TypeII.groupWeight e g ∧ TypeII.groupWeight e g ≤ up) := by omega
    have hU : ¬ up < TypeII.groupWeight e g := by omega
    simp only [hL,hm,hU,ite_true,ite_false,add_zero]
  · by_cases hU : up < TypeII.groupWeight e g
    · have hm : ¬ (lo ≤ TypeII.groupWeight e g ∧ TypeII.groupWeight e g ≤ up) := by omega
      simp only [hL,hm,hU,ite_true,ite_false,zero_add]
    · have hm : lo ≤ TypeII.groupWeight e g ∧ TypeII.groupWeight e g ≤ up := by omega
      simp [hL,hU,hm]

lemma ThinnedWindows.epsilon_pos {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) : 0 < ε := by
  have hh := w.threshold_charge_succ 0
  have ht := w.threshold_pos 0
  have hu : (0 : ℝ) ≤ w.upper 0 := Nat.cast_nonneg _
  norm_num at hh
  nlinarith

lemma ThinnedWindows.middle_abs_bound {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (i : s) :
    |∑ b, (e.coefficient b : ℝ) * w.middleEval e b i| ≤ w.markedCharge e hm s i + ε := by
  calc
    _ ≤ ∑ b, |(e.coefficient b : ℝ)| * |w.middleEval e b i| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun b => (e.coefficient b : ℝ)*w.middleEval e b i) Finset.univ
    _ = w.markedCharge e hm s i +
        ∑ b, if i.val ∉ w.marks e hm s b then |(e.coefficient b : ℝ)| * |w.middleEval e b i| else 0 := by
      rw [ThinnedWindows.markedCharge,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hi : i.val ∈ w.marks e hm s b <;> simp [hi]
    _ ≤ _ := add_le_add_right (w.unmarked_column w.epsilon_pos.le e hm s i i.property) _

lemma ThinnedWindows.node_split {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (i : s) :
    |norming.evaluateArray (w.blocks.embed i) e.value| ≤ 2*ε+w.markedCharge e hm s i +
      ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| *
        (if TypeII.groupWeight e g < w.lower i then
          |norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g)| else 0) := by
  have hh : |∑ g ∈ TypeII.activeGroups e, if w.upper i < TypeII.groupWeight e g then
      (e.coefficient g.1 : ℝ)*norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g) else 0| ≤ ε := by
    calc
      _ ≤ ∑ g ∈ TypeII.activeGroups e, |if w.upper i < TypeII.groupWeight e g then
          (e.coefficient g.1 : ℝ)*norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g) else 0| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ g ∈ (TypeII.activeGroups e).filter (fun g => w.upper i < TypeII.groupWeight e g),
          |(e.coefficient g.1 : ℝ)| * |norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g)| := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro g _
        split_ifs <;> simp only [abs_mul,abs_zero]
      _ ≤ vectorL1 (w.blocks.vector i) * SeriesTails.tail (fun j => 1/(f.m j : ℝ)) (w.upper i+1) :=
        TypeII.high_weight_bound e hm (w.blocks.vector i) (w.upper i)
      _ ≤ ε := w.tail_small i
  have hmB := w.middle_abs_bound e hm s i
  have hl : |∑ g ∈ TypeII.activeGroups e, if TypeII.groupWeight e g < w.lower i then
      (e.coefficient g.1 : ℝ)*norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g) else 0| ≤
      ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| *
        (if TypeII.groupWeight e g < w.lower i then |norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g)| else 0) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
    apply Finset.sum_congr rfl
    intro g _
    split_ifs <;> simp only [abs_mul,abs_zero,mul_zero]
  rw [TypeII.eval_three_parts e _ _ _ (w.order i)]
  exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hl hmB)) hh)).trans_eq (by ring)

end SeparableQuotient.ActualSpace

end

end OAI
