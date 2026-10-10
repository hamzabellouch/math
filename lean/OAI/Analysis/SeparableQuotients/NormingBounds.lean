import OAI.Analysis.SeparableQuotients.TreeCharges

namespace OAI

noncomputable section

namespace SeparableQuotient.FiniteVectors
open scoped Classical BigOperators ENNReal
universe u
variable {ι : Type u} [Fintype ι]

lemma norm_mask_le_explicit {p : ℝ≥0∞} [DecidableEq ι] (hp : p ≠ 0) (v : ι → ℝ) (s : Finset ι) :
    ‖vec p (fun i => if i ∈ s then v i else 0)‖ ≤ ‖vec p v‖ := by
  apply lp.norm_mono hp
  intro i
  by_cases hi : i ∈ s <;> simp [vec_apply,hi]

lemma norm_le_four {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0) (v a b c d : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i)
    (h : ∀ i, |v i| ≤ a i+b i+c i+d i) :
    ‖vec p v‖ ≤ ‖vec p a‖+‖vec p b‖+‖vec p c‖+‖vec p d‖ := by
  calc
    _ ≤ ‖vec p (fun i => a i+b i+c i+d i)‖ := by
      apply lp.norm_mono hp
      intro i
      simpa only [vec_apply,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (add_nonneg (add_nonneg (ha i) (hb i)) (hc i)) (hd i))] using h i
    _ = ‖vec p a+vec p b+vec p c+vec p d‖ := rfl
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)

lemma single_support_bounds {p : ℝ≥0∞} (hp : 0 < p.toReal) (v : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hv : ∀ i, |v i| ≤ K) (hs : ∀ i j, v i ≠ 0 → v j ≠ 0 → i = j) :
    ‖vec p v‖ ≤ K ∧ (∑ i, |v i|) ≤ K := by
  by_cases he : ∃ i, v i ≠ 0
  · obtain ⟨i,hi⟩ := he
    have hz (j : ι) (hji : j ≠ i) : v j = 0 := by
      by_contra hj
      exact hji (hs j i hj hi)
    constructor
    · apply norm_le hp v K hK
      rw [Finset.sum_eq_single i]
      · exact Real.rpow_le_rpow (abs_nonneg _) (hv i) hp.le
      · intro j _ hji
        simp only [hz j hji,abs_zero,Real.zero_rpow hp.ne']
      · simp
    · rw [Finset.sum_eq_single i]
      · exact hv i
      · intro j _ hji
        simp [hz j hji]
      · simp
  · have hz : ∀ i, v i = 0 := by simpa only [not_exists,not_not] using he
    constructor
    · apply norm_le hp v K hK
      simp only [hz,abs_zero,Real.zero_rpow hp.ne',Finset.sum_const_zero]
      exact Real.rpow_nonneg hK _
    · simpa only [hz,abs_zero,Finset.sum_const_zero] using hK
end SeparableQuotient.FiniteVectors

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

lemma Family.base_zero (f : Family) : (0 : Array) ∈ f.base := by
  cases f with
  | pure k => exact pureBase_zero k
  | mixed => exact Set.mem_iUnion.mpr ⟨0,pure_zero 0⟩

lemma Family.base_crop (f : Family) (A : Crop) (g : Array) (hg : g ∈ f.base) :
    restrict (A.set f) g ∈ f.base := by
  cases f with
  | pure k => exact pureBase_crop k A g hg
  | mixed =>
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hg
    apply Set.mem_iUnion.mpr
    refine ⟨k,?_⟩
    rw [pure_mixed_crop k A g hk]
    split_ifs
    · exact pure_crop k A g hk
    · exact pure_zero k

lemma Family.stage_crop (f : Family) (n : ℕ) (A : Crop) (g : Array) (hg : g ∈ stage f.base f n) :
    restrict (A.set f) g ∈ stage f.base f n :=
  Norming.stage_crop f (Family.base_zero f) (Family.base_crop f) n A g hg

lemma evaluateArray_nonzero_witness (x : Γ →₀ ℝ) (g : Array)
    (h : norming.evaluateArray (norming.includeFinite x) g ≠ 0) :
    ∃ α ∈ x.support, g α ≠ 0 := by
  rw [evaluateArray_finite] at h
  obtain ⟨α,hα,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨α,hα, fun hg => hne (by simp [hg])⟩

lemma BlockSequence.base_eval_unique {f : Family} (z : BlockSequence f) (g : Array) (hg : g ∈ f.base)
    (i j : ℕ) (hi : norming.evaluateArray (z.embed i) g ≠ 0)
    (hj : norming.evaluateArray (z.embed j) g ≠ 0) : i = j := by
  obtain ⟨α,hα,hgα⟩ := evaluateArray_nonzero_witness (z.vector i) g hi
  obtain ⟨β,hβ,hgβ⟩ := evaluateArray_nonzero_witness (z.vector j) g hj
  have hbad (i j : ℕ) (hij : i < j) (α β : Γ)
      (hα : α ∈ (z.vector i).support) (hβ : β ∈ (z.vector j).support)
      (hgα : g α ≠ 0) (hgβ : g β ≠ 0) : False := by
    cases f with
    | pure k =>
      rcases hg with rfl | ⟨γ,_hc,rfl | rfl⟩
      · exact hgα rfl
      all_goals
        have hαγ : α = γ := by by_contra hn; exact hgα (Finsupp.single_eq_of_ne hn)
        have hβγ : β = γ := by by_contra hn; exact hgβ (Finsupp.single_eq_of_ne hn)
        subst α; subst β
        exact (lt_irrefl γ) (z.successive i j hij γ hα γ hβ).1
    | mixed =>
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hg
      have hαc : Colors.color α = k := by by_contra hn; exact hgα (pure_vanish k g hk α hn)
      have hβc : Colors.color β = k := by by_contra hn; exact hgβ (pure_vanish k g hk β hn)
      have hh := (z.successive i j hij α hα β hβ).2 rfl
      rw [hαc,hβc] at hh
      exact (lt_irrefl k) hh
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hbad i j hij α β hα hβ hgα hgβ).elim
  · exact hij
  · exact (hbad j i hij β α hβ hα hgβ hgα).elim

noncomputable def ThinnedWindows.evalVector {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (g : Array) (i : s) : ℝ :=
  if i ∈ I then |norming.evaluateArray (w.blocks.embed i) g| else 0

lemma ThinnedWindows.evalVector_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (g : Array) (i : s) :
    0 ≤ w.evalVector s I g i := by unfold ThinnedWindows.evalVector; split_ifs <;> positivity

lemma ThinnedWindows.evalVector_base {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (g : Array) (hg : g ∈ f.base) :
    ‖vec f.exponent (w.evalVector s I g)‖ ≤ 2 ∧ (∑ i : s, w.evalVector s I g i) ≤ 2 := by
  have hb (i : s) : |w.evalVector s I g i| ≤ 2 := by
    rw [abs_of_nonneg (w.evalVector_nonneg s I g i)]
    unfold ThinnedWindows.evalVector
    split_ifs
    · have hgfull : g ∈ Full := f.norming_subset_full (Set.mem_iUnion.mpr ⟨0,hg⟩)
      rw [norming.evaluateArray_eq_functional _ ⟨g,hgfull⟩]
      exact (norming.functional_bound _ _).trans (w.upper_norm i)
    · norm_num
  have hu (i j : s) (hi : w.evalVector s I g i ≠ 0) (hj : w.evalVector s I g j ≠ 0) : i = j := by
    have hn (i : s) (hi : w.evalVector s I g i ≠ 0) : norming.evaluateArray (w.blocks.embed i) g ≠ 0 := by
      intro hz
      apply hi
      simp [ThinnedWindows.evalVector,hz]
    exact Subtype.ext (w.blocks.base_eval_unique g hg i j (hn i hi) (hn j hj))
  have hh := single_support_bounds (by simpa only [Family.exponent_toReal] using f.r_pos : 0 < f.exponent.toReal)
    (w.evalVector s I g) 2 (by norm_num) hb hu
  simpa only [abs_of_nonneg (w.evalVector_nonneg s I g _)] using hh

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def TypeII.continuation {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (g : TypeII.Group e) (i : s) : ℝ :=
  (1/(f.m (TypeII.groupWeight e g) : ℝ)) * ∑ h,
    w.evalVector s (TypeI.lowAssign w ((e.path g.1).piece g.2) s I h)
      (restrict ((e.crop g.1).set f) (((e.path g.1).piece g.2).child h)) i

lemma TypeII.continuation_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (g : TypeII.Group e) (i : s) : 0 ≤ TypeII.continuation e w s I g i := by
  unfold TypeII.continuation
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => w.evalVector_nonneg ..))

lemma ThinnedWindows.node_majorant {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s) (i : s) :
    w.evalVector s I e.value i ≤ (if i ∈ I then 2*ε else 0) +
      (if i ∈ I then w.markedCharge e hm s i else 0) +
      (∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| * TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I i) +
      ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| * TypeII.continuation e w s I g i := by
  by_cases hi : i ∈ I
  · simp only [ThinnedWindows.evalVector,hi,ite_true]
    apply (w.node_split e hm s i).trans
    rw [add_assoc (2*ε+w.markedCharge e hm s i),← Finset.sum_add_distrib]
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro g _
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    by_cases hj : TypeII.groupWeight e g < w.lower i
    · rw [ite_eq_left hj]
      exact TypeI.low_eval_bound w ((e.path g.1).piece g.2) (e.crop g.1) (hm g.1 g.2) s I i hi hj
    · rw [ite_eq_right hj]
      exact add_nonneg (TypeI.boundaryCharge_nonneg ..) (TypeII.continuation_nonneg ..)
  · simp only [ThinnedWindows.evalVector,hi,ite_false,zero_add]
    exact add_nonneg (Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (TypeI.boundaryCharge_nonneg ..)))
      (Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (TypeII.continuation_nonneg ..)))

noncomputable def TypeII.boundaryVector {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| * TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I i

noncomputable def TypeII.continuationVector {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| * TypeII.continuation e w s I g i

lemma ThinnedWindows.epsilonVector_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) :
    ‖vec f.exponent (fun i : s => if i ∈ I then 2*ε else 0)‖ ≤ 2*(ε*(s.card : ℝ)^(1/f.r)) := by
  have hp : 0 < f.exponent.toReal := by simpa only [Family.exponent_toReal] using f.r_pos
  have hn : f.exponent ≠ 0 := by intro h; simp [h] at hp
  calc
    _ ≤ ‖vec f.exponent (fun _ : s => 2*ε)‖ := norm_mask_le_explicit hn _ I
    _ = _ := by
      rw [norm_const hp,abs_of_nonneg (mul_nonneg (by norm_num) w.epsilon_pos.le)]
      simp only [Fintype.card_coe,Family.exponent_toReal]
      ring

lemma TypeII.boundaryVector_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) :
    ‖vec f.exponent (TypeII.boundaryVector e w s I)‖ ≤ 4 := by
  exact (TypeII.sum_vector_norm e s (fun g => TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I) 32
    (by norm_num) (fun _ _ => TypeI.boundaryCharge_norm ..)).trans_eq (by norm_num)

lemma TypeII.continuation_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (g : TypeII.Group e) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ h, ‖vec f.exponent (w.evalVector s (TypeI.lowAssign w ((e.path g.1).piece g.2) s I h)
        (restrict ((e.crop g.1).set f) (((e.path g.1).piece g.2).child h)))‖ ≤ K) :
    ‖vec f.exponent (TypeII.continuation e w s I g)‖ ≤ K*f.theta (TypeII.groupWeight e g) := by
  apply TypeI.recombine_norm w ((e.path g.1).piece g.2) s I _ K hK
  · intro h i hi
    simp only [ThinnedWindows.evalVector,hi,ite_false]
  · exact hc

lemma TypeII.continuationVector_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (hc : ∀ (g : TypeII.Group e) h, ‖vec f.exponent (w.evalVector s (TypeI.lowAssign w ((e.path g.1).piece g.2) s I h)
        (restrict ((e.crop g.1).set f) (((e.path g.1).piece g.2).child h)))‖ ≤ 64) :
    ‖vec f.exponent (TypeII.continuationVector e w s I)‖ ≤ 8 := by
  exact (TypeII.sum_vector_norm e s (TypeII.continuation e w s I) 64 (by norm_num)
    (fun g _ => TypeII.continuation_norm e w s I g 64 (by norm_num) (hc g))).trans_eq (by norm_num)

lemma ThinnedWindows.node_uniform {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s)
    (hε : ε*(s.card : ℝ)^(1/f.r) ≤ 1)
    (hc : ∀ (g : TypeII.Group e) h, ‖vec f.exponent
      (w.evalVector s (TypeI.lowAssign w ((e.path g.1).piece g.2) s I h)
        (restrict ((e.crop g.1).set f) (((e.path g.1).piece g.2).child h)))‖ ≤ 64) :
    ‖vec f.exponent (w.evalVector s I e.value)‖ ≤ 64 := by
  have hp : 0 < f.exponent.toReal := by simpa only [Family.exponent_toReal] using f.r_pos
  have hn : f.exponent ≠ 0 := by intro h; simp [h] at hp
  have hM : ‖vec f.exponent (fun i : s => if i ∈ I then w.markedCharge e hm s i else 0)‖ ≤ 16 :=
    (norm_mask_le_explicit hn _ I).trans (w.marked_vector_bounds e hm s).1
  have h := norm_le_four hn (w.evalVector s I e.value)
    (fun i : s => if i ∈ I then 2*ε else 0)
    (fun i : s => if i ∈ I then w.markedCharge e hm s i else 0)
    (TypeII.boundaryVector e w s I) (TypeII.continuationVector e w s I)
    (fun i => by split_ifs <;> nlinarith [w.epsilon_pos])
    (fun i => by split_ifs <;> first | exact w.markedCharge_nonneg e hm s i | exact le_rfl)
    (fun i => Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (TypeI.boundaryCharge_nonneg ..)))
    (fun i => Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (TypeII.continuation_nonneg ..)))
    (fun i => by rw [abs_of_nonneg (w.evalVector_nonneg s I e.value i)]; exact w.node_majorant e hm s I i)
  linarith [w.epsilonVector_norm s I, TypeII.boundaryVector_norm e w s I, TypeII.continuationVector_norm e w s I hc]

lemma ThinnedWindows.stage_uniform {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (hε : ε*(s.card : ℝ)^(1/f.r) ≤ 1) :
    ∀ n (g : Array), g ∈ stage f.base f n → ∀ I : Finset s,
      ‖vec f.exponent (w.evalVector s I g)‖ ≤ 64 := by
  intro n
  induction n with
  | zero =>
    intro g hg I
    exact (w.evalVector_base s I g hg).1.trans (by norm_num)
  | succ n ih =>
    intro g hg I
    have hn : ∀ g, g ∈ stage f.base f n → g ∈ f.norming := fun g hg => Set.mem_iUnion.mpr ⟨n,hg⟩
    have ht (e : TypeII f) (he : ∀ b i h, ((e.path b).piece i).child h ∈ stage f.base f n) :
        ‖vec f.exponent (w.evalVector s I e.value)‖ ≤ 64 := by
      apply w.node_uniform e (fun b i h => hn _ (he b i h)) s I hε
      intro g h
      exact ih _ (Family.stage_crop f n _ _ (he g.1 g.2 h)) _
    rcases hg with (hg | ⟨e,rfl,he⟩) | ⟨e,rfl,he⟩
    · exact ih _ hg I
    · simpa only [Norming.TypeI.toTypeII_value] using ht e.toTypeII (fun _ _ h => he h)
    · exact ht e he

lemma ThinnedWindows.norming_uniform {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (hε : ε*(s.card : ℝ)^(1/f.r) ≤ 1)
    (g : Array) (hg : g ∈ f.norming) (I : Finset s) :
    ‖vec f.exponent (w.evalVector s I g)‖ ≤ 64 := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hg
  exact w.stage_uniform s hε n g hn I

end SeparableQuotient.ActualSpace

end

end OAI
