import OAI.Analysis.SeparableQuotients.NormingBounds

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def TypeI.stoppedCharge {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  if i ∈ I ∧ e.weight < w.lower i then
    (16/(f.m e.weight : ℝ)) * ((TypeI.hitChildren e (w.blocks.vector i)).card : ℝ)^(1/f.r) else 0

lemma TypeI.stoppedCharge_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) (i : s) :
    0 ≤ TypeI.stoppedCharge w e s I i := by unfold TypeI.stoppedCharge; split_ifs <;> positivity

lemma TypeI.total_incidence {f : Family} (e : TypeI f) (z : BlockSequence f) (s : Finset ℕ) :
    (∑ i : s, ((TypeI.hitChildren e (z.vector i)).card : ℝ)) ≤ 2*e.length+s.card := by
  have hh (i : s) : ((TypeI.hitChildren e (z.vector i)).card : ℝ) ≤ TypeI.boundaryDegree e z i + 1 := by
    unfold TypeI.boundaryDegree
    split_ifs with h
    · linarith
    · have : (TypeI.hitChildren e (z.vector i)).card ≤ 1 := by omega
      simpa only [zero_add] using (show ((TypeI.hitChildren e (z.vector i)).card : ℝ) ≤ 1 by exact_mod_cast this)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one] at hs
  linarith [TypeI.boundaryDegree_sum e z s]

lemma TypeI.stoppedCharge_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s)
    (hs : s.card ≤ f.L J) (hj : J ≤ e.weight) :
    ‖vec f.exponent (TypeI.stoppedCharge w e s I)‖ ≤ 48*f.theta e.weight := by
  have hsum : (∑ i : s, ((TypeI.hitChildren e (w.blocks.vector i)).card : ℝ)) ≤ 3*(f.L e.weight : ℝ) := by
    have hL : (e.length : ℝ) ≤ f.L e.weight := by exact_mod_cast e.length_le
    have hc : (s.card : ℝ) ≤ f.L e.weight := by exact_mod_cast hs.trans (FamilyL_mono f hj)
    linarith [TypeI.total_incidence e w.blocks s]
  have hb := norm_degree_le (by simpa only [Family.exponent_toReal] using f.r_pos : 0 < f.exponent.toReal)
    (fun i : s => ((TypeI.hitChildren e (w.blocks.vector i)).card : ℝ)) (16/(f.m e.weight : ℝ)) (3*f.L e.weight)
    (by positivity) (by positivity) (fun _ => by positivity) hsum (TypeI.stoppedCharge w e s I) (fun i => by
      rw [abs_of_nonneg (TypeI.stoppedCharge_nonneg w e s I i)]
      unfold TypeI.stoppedCharge
      split_ifs
      · simp only [Family.exponent_toReal,le_refl]
      · positivity)
  have h3 : (3 : ℝ)^(1/f.r) ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
      ((div_le_one f.r_pos).mpr f.r_gt_one.le)
  calc
    _ ≤ (16/(f.m e.weight : ℝ)) * (3*(f.L e.weight : ℝ))^(1/f.r) := by simpa only [Family.exponent_toReal] using hb
    _ ≤ (16/(f.m e.weight : ℝ)) * (3*(f.L e.weight : ℝ)^(1/f.r)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (by positivity)) (by positivity)
    _ = _ := by rw [Family.theta_formula]; ring

lemma TypeI.stopped_eval_bound {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (A : Crop)
    (hm : ∀ h, e.child h ∈ f.norming) (s : Finset ℕ) (I : Finset s) (i : s)
    (hi : i ∈ I) (hj : e.weight < w.lower i) :
    |norming.evaluateArray (w.blocks.embed i) (restrict (A.set f) e.value)| ≤
      TypeI.stoppedCharge w e s I i := by
  have hb := TypeI.cropped_child_sum_bound e A hm (w.blocks.vector i) (f.L (w.lower i)) 16
    (by norm_num) (w.partition i) (e.length_le.trans (FamilyL_mono f hj.le))
  rw [TypeI.eval_crop_sum,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/(f.m e.weight : ℝ))]
  have hh := (Finset.abs_sum_le_sum_abs _ _).trans hb
  have hu := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1/(f.m e.weight : ℝ))
  simpa only [TypeI.stoppedCharge,hi,hj,and_self,ite_true,BlockSequence.embed,div_mul_eq_mul_div,one_mul,mul_div_assoc] using hu

lemma Family.sum_theta_tail_le {κ : Type*} (f : Family) (S : Finset κ) (j : κ → ℕ) (J : ℕ)
    (hJ : 1 ≤ J) (hp : ∀ g ∈ S, J ≤ j g) (hinj : Set.InjOn j S) :
    ∑ g ∈ S, f.theta (j g) ≤ 4*f.theta J := by
  have hi : Set.InjOn (fun g => j g-J) S := by
    intro g hg h hh he
    apply hinj hg hh
    have := hp g hg
    have := hp h hh
    dsimp only at he
    omega
  have he (g : κ) (hg : g ∈ S) : j g-1 = (J-1)+(j g-J) := by have := hp g hg; omega
  have hs : Summable (fun n => Parameters.theta f.s ((J-1)+n)) :=
    ((Parameters.hasSum_theta f.s_ge_two).summable.comp_injective (fun n m h => by omega))
  calc
    _ = ∑ n ∈ S.image (fun g => j g-J), Parameters.theta f.s ((J-1)+n) := by
      rw [Finset.sum_image hi]
      exact Finset.sum_congr rfl (fun g hg => congrArg (Parameters.theta f.s) (he g hg))
    _ ≤ ∑' n, Parameters.theta f.s ((J-1)+n) := hs.sum_le_tsum _
      (fun n _ => by rw [Parameters.theta_eq f.s_ge_two]; positivity)
    _ ≤ _ := Parameters.theta_tail f.s_ge_two (J-1)

lemma Parameters.B_sum (s n : ℕ) : Parameters.B s n = 2*∑ j ∈ Finset.range n, Parameters.L s j := by
  induction n with
  | zero => simp only [Parameters.B_zero,Finset.range_zero,Finset.sum_empty,mul_zero]
  | succ n ih => rw [Parameters.B_succ,ih,Finset.sum_range_succ]; ring

lemma Family.sum_low_lengths {κ : Type*} (f : Family) (S : Finset κ) (j : κ → ℕ) (J : ℕ)
    (hp : ∀ g ∈ S, 1 ≤ j g) (hlt : ∀ g ∈ S, j g < J) (hinj : Set.InjOn j S) :
    2*(∑ g ∈ S, f.L (j g)) ≤ Parameters.B f.s (J-1) := by
  have hi : Set.InjOn (fun g => j g-1) S := by
    intro g hg h hh he
    apply hinj hg hh
    have := hp g hg
    have := hp h hh
    dsimp only at he
    omega
  have hsub : S.image (fun g => j g-1) ⊆ Finset.range (J-1) := by
    intro n hn
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hn
    have := hp g hg
    have := hlt g hg
    simp only [Finset.mem_range]
    omega
  rw [Parameters.B_sum]
  apply Nat.mul_le_mul_left
  rw [show (∑ g ∈ S, f.L (j g)) = ∑ n ∈ S.image (fun g => j g-1), Parameters.L f.s n by rw [Finset.sum_image hi]; rfl]
  exact Finset.sum_le_sum_of_subset hsub

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def TypeII.earlyGroups {f : Family} (e : TypeII f) (J : ℕ) : Finset (TypeII.Group e) :=
  (TypeII.activeGroups e).filter (fun g => TypeII.groupWeight e g < J)

abbrev TypeII.ChildVectors {f : Family} (e : TypeII f) (s : Finset ℕ) :=
  (g : TypeII.Group e) → Fin ((e.path g.1).piece g.2).length → s → ℝ

noncomputable def TypeII.recombineEarly {f : Family} (e : TypeII f) (J : ℕ) (s : Finset ℕ)
    (v : TypeII.ChildVectors e s) (i : s) : ℝ :=
  ∑ g ∈ TypeII.earlyGroups e J, |(e.coefficient g.1 : ℝ)| *
    ((1/(f.m (TypeII.groupWeight e g) : ℝ)) * ∑ h, v g h i)

lemma TypeII.early_lengths_bound {f : Family} (e : TypeII f) (J : ℕ) :
    2*(∑ g ∈ TypeII.earlyGroups e J, ((e.path g.1).piece g.2).length) ≤ Parameters.B f.s (J-1) := by
  apply le_trans (Nat.mul_le_mul_left 2 (Finset.sum_le_sum (fun g _ => ((e.path g.1).piece g.2).length_le)))
  exact Family.sum_low_lengths f _ (TypeII.groupWeight e) J (fun g _ => ((e.path g.1).piece g.2).weight_pos)
    (fun _ hg => (Finset.mem_filter.mp hg).2) ((TypeII.groupWeight_injOn e).mono (Finset.filter_subset _ _))

lemma TypeII.early_theta_bound {f : Family} (e : TypeII f) (J : ℕ) :
    ∑ g ∈ TypeII.earlyGroups e J, f.theta (TypeII.groupWeight e g) ≤ 1/8 :=
  Family.sum_theta_le f _ _ (fun g _ => ((e.path g.1).piece g.2).weight_pos)
    ((TypeII.groupWeight_injOn e).mono (Finset.filter_subset _ _))

lemma TypeII.recombineEarly_nonneg {f : Family} (e : TypeII f) (J : ℕ) (s : Finset ℕ)
    (v : TypeII.ChildVectors e s) (hv : ∀ g h i, 0 ≤ v g h i) (i : s) :
    0 ≤ TypeII.recombineEarly e J s v i := by
  unfold TypeII.recombineEarly
  exact Finset.sum_nonneg (fun g _ => mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (Finset.sum_nonneg (fun h _ => hv g h i))))

lemma TypeII.recombineEarly_support {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (v : TypeII.ChildVectors e s)
    (hv : ∀ g h i, i ∉ TypeI.lowAssign w ((e.path g.1).piece g.2) s I h → v g h i = 0)
    (i : s) (hi : i ∉ I) : TypeII.recombineEarly e J s v i = 0 := by
  apply Finset.sum_eq_zero
  intro g _
  rw [Finset.sum_eq_zero (fun h _ => hv g h i (fun hh => hi (TypeI.lowAssign_subset w _ s I h hh))),mul_zero,mul_zero]

lemma TypeII.recombineEarly_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (v : TypeII.ChildVectors e s) (K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ g h i, i ∉ TypeI.lowAssign w ((e.path g.1).piece g.2) s I h → v g h i = 0)
    (hv : ∀ g h, ‖vec f.exponent (v g h)‖ ≤ K) :
    ‖vec f.exponent (TypeII.recombineEarly e J s v)‖ ≤ K/8 := by
  have hg (g : TypeII.Group e) : ‖vec f.exponent (fun i => |(e.coefficient g.1 : ℝ)| *
      ((1/(f.m (TypeII.groupWeight e g) : ℝ))*∑ h, v g h i))‖ ≤ K*f.theta (TypeII.groupWeight e g) := by
    change ‖|(e.coefficient g.1 : ℝ)| • vec f.exponent (fun i => (1/(f.m (TypeII.groupWeight e g) : ℝ))*∑ h, v g h i)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_abs]
    exact ((mul_le_mul_of_nonneg_right (e.coefficient_le_one g.1) (norm_nonneg _)).trans_eq (one_mul _)).trans
      (TypeI.recombine_norm w ((e.path g.1).piece g.2) s I (v g) K hK (hs g) (hv g))
  calc
    _ ≤ ∑ g ∈ TypeII.earlyGroups e J, ‖vec f.exponent (fun i => |(e.coefficient g.1 : ℝ)| *
        ((1/(f.m (TypeII.groupWeight e g) : ℝ))*∑ h, v g h i))‖ := by
      unfold TypeII.recombineEarly
      rw [vec_sum]
      exact norm_sum_le _ _
    _ ≤ ∑ g ∈ TypeII.earlyGroups e J, K*f.theta (TypeII.groupWeight e g) := Finset.sum_le_sum (fun g _ => hg g)
    _ = K * ∑ g ∈ TypeII.earlyGroups e J, f.theta (TypeII.groupWeight e g) := (Finset.mul_sum ..).symm
    _ ≤ K*(1/8) := mul_le_mul_of_nonneg_left (TypeII.early_theta_bound e J) hK
    _ = _ := by ring

lemma TypeII.recombineEarly_l1 {f : Family} (e : TypeII f) (J : ℕ) (s : Finset ℕ)
    (v : TypeII.ChildVectors e s) (K : ℝ) (hK : 0 ≤ K)
    (hv : ∀ g h i, 0 ≤ v g h i) (hs : ∀ g h, (∑ i : s, v g h i) ≤ K) :
    (∑ i : s, TypeII.recombineEarly e J s v i) ≤ (Parameters.B f.s (J-1) : ℝ)*K := by
  have hc (g : TypeII.Group e) : |(e.coefficient g.1 : ℝ)| * (1/(f.m (TypeII.groupWeight e g) : ℝ)) ≤ 1 := by
    have hm : (1 : ℝ) ≤ f.m (TypeII.groupWeight e g) := by exact_mod_cast f.m_pos _
    exact (mul_le_mul (e.coefficient_le_one g.1) (one_div_le_one_div_of_le (by norm_num) hm) (by positivity) (by norm_num)).trans_eq (by norm_num)
  have hd : (∑ g ∈ TypeII.earlyGroups e J, (((e.path g.1).piece g.2).length : ℝ)) ≤ Parameters.B f.s (J-1) := by
    have hh := TypeII.early_lengths_bound e J
    exact_mod_cast (show (∑ g ∈ TypeII.earlyGroups e J, ((e.path g.1).piece g.2).length) ≤ Parameters.B f.s (J-1) by omega)
  calc
    _ = ∑ g ∈ TypeII.earlyGroups e J, (|(e.coefficient g.1 : ℝ)| * (1/(f.m (TypeII.groupWeight e g) : ℝ))) *
        ∑ h, ∑ i : s, v g h i := by
      unfold TypeII.recombineEarly
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      simp only [← Finset.mul_sum,← mul_assoc]
      congr 1
      exact Finset.sum_comm
    _ ≤ ∑ g ∈ TypeII.earlyGroups e J, ∑ h, ∑ i : s, v g h i := by
      exact Finset.sum_le_sum (fun g _ => (mul_le_mul_of_nonneg_right (hc g)
        (Finset.sum_nonneg (fun h _ => Finset.sum_nonneg (fun i _ => hv g h i)))).trans_eq (one_mul _))
    _ ≤ ∑ g ∈ TypeII.earlyGroups e J, (((e.path g.1).piece g.2).length : ℝ)*K := by
      apply Finset.sum_le_sum
      intro g _
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun h _ => hs g h)
    _ = (∑ g ∈ TypeII.earlyGroups e J, (((e.path g.1).piece g.2).length : ℝ))*K := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hd hK

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def TypeII.lateGroups {f : Family} (e : TypeII f) (J : ℕ) : Finset (TypeII.Group e) :=
  (TypeII.activeGroups e).filter (fun g => J ≤ TypeII.groupWeight e g)

noncomputable def TypeII.lateVector {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  ∑ g ∈ TypeII.lateGroups e J, |(e.coefficient g.1 : ℝ)| * TypeI.stoppedCharge w ((e.path g.1).piece g.2) s I i

noncomputable def TypeII.earlyBoundary {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  ∑ g ∈ TypeII.earlyGroups e J, |(e.coefficient g.1 : ℝ)| * TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I i

lemma TypeII.lateVector_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (i : s) :
    0 ≤ TypeII.lateVector e w s I i :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (TypeI.stoppedCharge_nonneg ..))

lemma TypeII.earlyBoundary_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (i : s) :
    0 ≤ TypeII.earlyBoundary e w s I i :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (TypeI.boundaryCharge_nonneg ..))

lemma TypeII.lateVector_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (hJ : 1 ≤ J) (hs : s.card ≤ f.L J) :
    ‖vec f.exponent (TypeII.lateVector e w s I)‖ ≤ 192*f.theta J := by
  have hg (g : TypeII.Group e) (hg : g ∈ TypeII.lateGroups e J) :
      ‖vec f.exponent (fun i => |(e.coefficient g.1 : ℝ)| * TypeI.stoppedCharge w ((e.path g.1).piece g.2) s I i)‖ ≤
      48*f.theta (TypeII.groupWeight e g) := by
    change ‖|(e.coefficient g.1 : ℝ)| • vec f.exponent (TypeI.stoppedCharge w ((e.path g.1).piece g.2) s I)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_abs]
    exact ((mul_le_mul_of_nonneg_right (e.coefficient_le_one g.1) (norm_nonneg _)).trans_eq (one_mul _)).trans
      (TypeI.stoppedCharge_norm w _ s I hs (Finset.mem_filter.mp hg).2)
  calc
    _ ≤ ∑ g ∈ TypeII.lateGroups e J, ‖vec f.exponent (fun i => |(e.coefficient g.1 : ℝ)| *
        TypeI.stoppedCharge w ((e.path g.1).piece g.2) s I i)‖ := by
      unfold TypeII.lateVector
      rw [vec_sum]
      exact norm_sum_le _ _
    _ ≤ ∑ g ∈ TypeII.lateGroups e J, 48*f.theta (TypeII.groupWeight e g) := Finset.sum_le_sum hg
    _ = 48 * ∑ g ∈ TypeII.lateGroups e J, f.theta (TypeII.groupWeight e g) := (Finset.mul_sum ..).symm
    _ ≤ 48*(4*f.theta J) := mul_le_mul_of_nonneg_left (Family.sum_theta_tail_le f _ _ J hJ
      (fun _ hg => (Finset.mem_filter.mp hg).2) ((TypeII.groupWeight_injOn e).mono (Finset.filter_subset _ _))) (by norm_num)
    _ = _ := by ring

lemma TypeII.earlyBoundary_l1 {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) :
    (∑ i : s, TypeII.earlyBoundary e w s I i) ≤ 16*(Parameters.B f.s (J-1) : ℝ) := by
  have hlen : 2*(∑ g ∈ TypeII.earlyGroups e J, (((e.path g.1).piece g.2).length : ℝ)) ≤ Parameters.B f.s (J-1) :=
    by exact_mod_cast TypeII.early_lengths_bound e J
  calc
    _ = ∑ g ∈ TypeII.earlyGroups e J, |(e.coefficient g.1 : ℝ)| * ∑ i : s, TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I i := by
      unfold TypeII.earlyBoundary
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ g ∈ TypeII.earlyGroups e J, 32*(((e.path g.1).piece g.2).length : ℝ) := by
      apply Finset.sum_le_sum
      intro g _
      exact ((mul_le_mul_of_nonneg_right (e.coefficient_le_one g.1)
        (Finset.sum_nonneg (fun i _ => TypeI.boundaryCharge_nonneg w _ s I i))).trans_eq (one_mul _)).trans
          (TypeI.boundaryCharge_l1 w _ s I)
    _ = 32*(∑ g ∈ TypeII.earlyGroups e J, (((e.path g.1).piece g.2).length : ℝ)) := (Finset.mul_sum ..).symm
    _ ≤ _ := by linarith

noncomputable def ThinnedWindows.localSmall {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  (if i ∈ I then 2*ε else 0) + TypeII.lateVector e w s I i

noncomputable def ThinnedWindows.localLarge {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming)
    (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  (if i ∈ I then w.markedCharge e hm s i else 0) + TypeII.earlyBoundary e w s I i

lemma ThinnedWindows.localSmall_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f) (s : Finset ℕ) (I : Finset s) (i : s) :
    0 ≤ w.localSmall e s I i := by
  apply add_nonneg _ (TypeII.lateVector_nonneg ..)
  split_ifs <;> nlinarith [w.epsilon_pos]

lemma ThinnedWindows.localLarge_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s) (i : s) :
    0 ≤ w.localLarge e hm s I i := by
  apply add_nonneg _ (TypeII.earlyBoundary_nonneg ..)
  split_ifs
  · exact w.markedCharge_nonneg e hm s i
  · exact le_rfl

lemma ThinnedWindows.localSmall_support {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f) (s : Finset ℕ) (I : Finset s) (i : s) (hi : i ∉ I) :
    w.localSmall e s I i = 0 := by
  simp only [ThinnedWindows.localSmall,hi,ite_false,zero_add,TypeII.lateVector,TypeI.stoppedCharge,false_and]
  simp

lemma ThinnedWindows.localLarge_support {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s) (i : s) (hi : i ∉ I) :
    w.localLarge e hm s I i = 0 := by
  simp only [ThinnedWindows.localLarge,hi,ite_false,zero_add,TypeII.earlyBoundary,TypeI.boundaryCharge,false_and]
  simp

lemma ThinnedWindows.localSmall_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f) (s : Finset ℕ) (I : Finset s)
    (hJ : 1 ≤ J) (hs : s.card ≤ f.L J) (hε : ε*(s.card : ℝ)^(1/f.r) ≤ f.theta J) :
    ‖vec f.exponent (w.localSmall e s I)‖ ≤ 194*f.theta J := by
  change ‖vec f.exponent (fun i : s => if i ∈ I then 2*ε else 0) + vec f.exponent (TypeII.lateVector e w s I)‖ ≤ _
  have hh := norm_add_le (vec f.exponent (fun i : s => if i ∈ I then 2*ε else 0)) (vec f.exponent (TypeII.lateVector e w s I))
  linarith [w.epsilonVector_norm s I,TypeII.lateVector_norm e w s I hJ hs]

lemma ThinnedWindows.localLarge_l1 {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s) :
    (∑ i : s, w.localLarge e hm s I i) ≤ 16*(1+(Parameters.B f.s (J-1) : ℝ)+(s.card : ℝ)^(1-1/f.q)) := by
  have hM : (∑ i : s, if i ∈ I then w.markedCharge e hm s i else 0) ≤ ∑ i : s, w.markedCharge e hm s i := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact le_rfl
    · exact w.markedCharge_nonneg e hm s i
  have hh := (w.marked_vector_bounds e hm s).2
  have hB := TypeII.earlyBoundary_l1 e w s I
  simp only [ThinnedWindows.localLarge,Finset.sum_add_distrib]
  linarith

end SeparableQuotient.ActualSpace

end

end OAI
