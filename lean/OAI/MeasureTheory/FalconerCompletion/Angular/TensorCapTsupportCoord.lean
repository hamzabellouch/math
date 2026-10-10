import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.ScalarCapPartition2

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set Metric
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable

lemma tensorCapND_tsupport_coord {d : ℕ} (δ : ℝ) (a : Fin d → ℤ)
    {w : EuclideanSpace ℝ (Fin d)} (hw : w ∈ tsupport (tensorCapND δ a)) (i : Fin d) :
    |δ⁻¹*w i-a i| ≤ 1 := by
  have hc : IsClosed {x : EuclideanSpace ℝ (Fin d) | |δ⁻¹*x i-a i| ≤ 1} :=
    isClosed_le (((EuclideanSpace.proj i).continuous.const_mul _).sub continuous_const).abs continuous_const
  exact (closure_minimal (fun x hx => tensorCapKernelND_support hx i) hc) hw

noncomputable def localCapGridND {d : ℕ} (δ : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (⌊δ⁻¹*w i⌋-1) (⌊δ⁻¹*w i⌋+2))

lemma localCapGridND_card {d : ℕ} (δ : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    (localCapGridND δ w).card=4^d := by
  simp only [localCapGridND,Fintype.card_piFinset]
  have hc (i : Fin d) : (Finset.Icc (⌊δ⁻¹*w i⌋-1) (⌊δ⁻¹*w i⌋+2)).card=4 := by
    rw [Int.card_Icc]
    omega
  simp only [hc,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma tensorCapND_support_label {d : ℕ} (δ : ℝ) (a : Fin d → ℤ)
    {w : EuclideanSpace ℝ (Fin d)} (hw : w ∈ tsupport (tensorCapND δ a)) :
    a ∈ localCapGridND δ w := by
  rw [localCapGridND,Fintype.mem_piFinset]
  intro i
  have h := abs_le.mp (tensorCapND_tsupport_coord δ a hw i)
  have hfl := Int.floor_le (δ⁻¹*w i)
  have hfu := Int.lt_floor_add_one (δ⁻¹*w i)
  apply Finset.mem_Icc.mpr
  constructor
  · have hh : (⌊δ⁻¹*w i⌋:ℝ)-1 ≤ (a i:ℝ) := by linarith
    exact_mod_cast hh
  · have hh : (a i:ℝ) ≤ (⌊δ⁻¹*w i⌋:ℝ)+2 := by linarith
    exact_mod_cast hh

lemma tensorCapND_overlap {d : ℕ} (δ : ℝ) (A : Finset (Fin d → ℤ))
    (w : EuclideanSpace ℝ (Fin d)) :
    (A.filter (fun a => w ∈ tsupport (tensorCapND δ a))).card ≤ 4^d := by
  classical
  rw [← localCapGridND_card δ w]
  apply Finset.card_le_card
  intro a ha
  exact tensorCapND_support_label δ a (Finset.mem_filter.mp ha).2

noncomputable def selectedCapND {d : ℕ} (δ : ℝ) (A : Finset (Fin d → ℤ))
    (w : EuclideanSpace ℝ (Fin d)) : ℝ := ∑ a ∈ A, tensorCapND δ a w

lemma selectedCapND_contDiff {d : ℕ} (δ : ℝ) (A : Finset (Fin d → ℤ)) :
    ContDiff ℝ ∞ (selectedCapND δ A) := ContDiff.sum (fun a _ => tensorCapND_contDiff δ a)

lemma selectedCapND_bounds {d : ℕ} {δ : ℝ} (hδ : 0<δ) (A : Finset (Fin d → ℤ))
    (hA : A ⊆ fullCapGridND d δ) (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ ≤ 1) :
    0 ≤ selectedCapND δ A w ∧ selectedCapND δ A w ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun a _ => tensorCapKernelND_nonneg _ _)
  · rw [← fullCapGridND_partition hδ w hw]
    exact Finset.sum_le_sum_of_subset_of_nonneg hA (fun a _ _ => tensorCapKernelND_nonneg _ _)

lemma selectedCapND_derivative_bound (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (A : Finset (Fin d → ℤ)), 0<δ →
      ∀ k ≤ m, ∀ w, ‖iteratedFDeriv ℝ k (selectedCapND δ A) w‖ ≤ C*δ⁻¹^k := by
  classical
  obtain ⟨C,hC,hb⟩ := tensorCapND_derivative_bound d m
  refine ⟨4^d*C,by positivity,?_⟩
  intro δ A hδ k hk w
  have hs (a) (_ha : a ∈ A) : ContDiff ℝ (k:WithTop ℕ∞) (tensorCapND δ a) :=
    (tensorCapND_contDiff δ a).of_le (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))
  change ‖iteratedFDeriv ℝ k (fun y => ∑ a ∈ A, tensorCapND δ a y) w‖ ≤ _
  rw [iteratedFDeriv_sum hs,Finset.sum_apply]
  let B := A.filter (fun a => w ∈ tsupport (tensorCapND δ a))
  have he : (∑ a ∈ B, iteratedFDeriv ℝ k (tensorCapND δ a) w) =
      ∑ a ∈ A, iteratedFDeriv ℝ k (tensorCapND δ a) w := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a ha hna
    exact Function.notMem_support.mp (fun hd => hna (Finset.mem_filter.mpr
      ⟨ha,support_iteratedFDeriv_subset k hd⟩))
  rw [← he]
  calc
    _ ≤ ∑ a ∈ B, C*δ⁻¹^k := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => hb δ a hδ k hk w))
    _ = (B.card:ℝ)*(C*δ⁻¹^k) := by simp
    _ ≤ (4:ℝ)^d*(C*δ⁻¹^k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast tensorCapND_overlap δ A w
    _ = _ := by ring

lemma fullCapGridND_card_bound {d : ℕ} {δ : ℝ} (hδ : 0<δ) (hδ1 : δ ≤ 1) :
    ((fullCapGridND d δ).card:ℝ) ≤ (9*δ⁻¹)^d := by
  have hp : (0:ℤ) ≤ ⌈δ⁻¹⌉ := by exact_mod_cast (le_of_lt (inv_pos.mpr hδ)).trans (Int.le_ceil _)
  have he : (Finset.Icc (-(⌈δ⁻¹⌉+2)) (⌈δ⁻¹⌉+2)).card = (2*⌈δ⁻¹⌉+5).toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  simp only [fullCapGridND,Fintype.card_piFinset,Finset.prod_const,Finset.card_univ,Fintype.card_fin,he,Nat.cast_pow]
  apply pow_le_pow_left₀ (by positivity)
  rw [← Int.cast_natCast,Int.toNat_of_nonneg (by omega)]
  push_cast
  have hh := Int.ceil_lt_add_one (δ⁻¹)
  have hi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  linarith

end CurrentFalconer
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set Metric
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable

lemma selectedCapND_tsupport {d : ℕ} (δ : ℝ) (A : Finset (Fin d → ℤ)) :
    tsupport (selectedCapND δ A) ⊆ ⋃ a ∈ A, tsupport (tensorCapND δ a) := by
  apply closure_minimal _ (isClosed_biUnion_finset (fun _ _ => isClosed_closure))
  intro w hw
  obtain ⟨a,ha,hwa⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  exact mem_iUnion.mpr ⟨a,mem_iUnion.mpr ⟨ha,subset_closure hwa⟩⟩

noncomputable def maskCapSelectionND {d : ℕ} (δ : ℝ) (K : Set (EuclideanSpace ℝ (Fin d))) :
    Finset (Fin d → ℤ) :=
  (fullCapGridND d δ).filter (fun a => ∃ w ∈ K, tensorCapND δ a w ≠ 0)

noncomputable def bufferedMaskND {d : ℕ} (δ : ℝ) (K : Set (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) → ℝ := selectedCapND δ (maskCapSelectionND δ K)

lemma bufferedMaskND_contDiff {d : ℕ} (δ : ℝ) (K : Set (EuclideanSpace ℝ (Fin d))) :
    ContDiff ℝ ∞ (bufferedMaskND δ K) := selectedCapND_contDiff δ _

lemma bufferedMaskND_bounds {d : ℕ} {δ : ℝ} (hδ : 0<δ)
    (K : Set (EuclideanSpace ℝ (Fin d))) {w : EuclideanSpace ℝ (Fin d)} (hw : ‖w‖ ≤ 1) :
    0 ≤ bufferedMaskND δ K w ∧ bufferedMaskND δ K w ≤ 1 :=
  selectedCapND_bounds hδ _ (Finset.filter_subset _ _) w hw

lemma bufferedMaskND_eq_one {d : ℕ} {δ : ℝ} (hδ : 0<δ)
    {K : Set (EuclideanSpace ℝ (Fin d))} {w : EuclideanSpace ℝ (Fin d)}
    (hw : ‖w‖ ≤ 1) (hwK : w ∈ K) : bufferedMaskND δ K w=1 := by
  rw [← fullCapGridND_partition hδ w hw]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a ha hna
  by_contra hn
  exact hna (Finset.mem_filter.mpr ⟨ha,w,hwK,hn⟩)

lemma bufferedMaskND_support_near {d : ℕ} {δ : ℝ} (hδ : 0<δ)
    {K : Set (EuclideanSpace ℝ (Fin d))} {w : EuclideanSpace ℝ (Fin d)}
    (hw : w ∈ tsupport (bufferedMaskND δ K)) :
    ∃ z ∈ K, dist w z ≤ 2*(d+1:ℝ)*δ := by
  obtain ⟨a,ha,hwa⟩ := mem_iUnion₂.mp (selectedCapND_tsupport δ _ hw)
  obtain ⟨z,hz,hza⟩ := (Finset.mem_filter.mp ha).2
  have hwd := tensorCapND_tsupport_dist hδ a hwa
  have hzd := tensorCapND_support_dist hδ a hza
  refine ⟨z,hz,?_⟩
  have ht := dist_triangle w (capGridPointND δ a) z
  rw [dist_comm (capGridPointND δ a) z] at ht
  linarith

noncomputable def evenBufferedMaskND {d : ℕ} (δ : ℝ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1/2:ℝ)*(bufferedMaskND δ K w+bufferedMaskND δ K (-w))

lemma evenBufferedMaskND_contDiff {d : ℕ} (δ : ℝ) (K : Set (EuclideanSpace ℝ (Fin d))) :
    ContDiff ℝ ∞ (evenBufferedMaskND δ K) :=
  contDiff_const.mul ((bufferedMaskND_contDiff δ K).add
    ((bufferedMaskND_contDiff δ K).comp contDiff_neg))

lemma evenBufferedMaskND_even {d : ℕ} (δ : ℝ) (K : Set (EuclideanSpace ℝ (Fin d))) :
    Function.Even (evenBufferedMaskND δ K) := by
  intro w
  simp only [evenBufferedMaskND,neg_neg,add_comm]

lemma evenBufferedMaskND_bounds {d : ℕ} {δ : ℝ} (hδ : 0<δ)
    (K : Set (EuclideanSpace ℝ (Fin d))) {w : EuclideanSpace ℝ (Fin d)} (hw : ‖w‖ ≤ 1) :
    0 ≤ evenBufferedMaskND δ K w ∧ evenBufferedMaskND δ K w ≤ 1 := by
  have h₁ := bufferedMaskND_bounds hδ K hw
  have h₂ := bufferedMaskND_bounds hδ K (w:= -w) (by simpa only [norm_neg] using hw)
  dsimp [evenBufferedMaskND]
  constructor <;> linarith

lemma evenBufferedMaskND_eq_one {d : ℕ} {δ : ℝ} (hδ : 0<δ)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : ∀ w ∈ K, -w ∈ K)
    {w : EuclideanSpace ℝ (Fin d)} (hw : ‖w‖ ≤ 1) (hwK : w ∈ K) :
    evenBufferedMaskND δ K w=1 := by
  have h₁ := bufferedMaskND_eq_one hδ hw hwK
  have h₂ := bufferedMaskND_eq_one hδ (by simpa only [norm_neg] using hw) (hK w hwK)
  norm_num [evenBufferedMaskND,h₁,h₂]

lemma evenBufferedMaskND_support_near {d : ℕ} {δ : ℝ} (hδ : 0<δ)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : ∀ w ∈ K, -w ∈ K)
    {w : EuclideanSpace ℝ (Fin d)} (hw : w ∈ tsupport (evenBufferedMaskND δ K)) :
    ∃ z ∈ K, dist w z ≤ 2*(d+1:ℝ)*δ := by
  have hw' : w ∈ tsupport (fun x => bufferedMaskND δ K x+bufferedMaskND δ K (-x)) :=
    tsupport_mul_subset_right hw
  rcases tsupport_add (bufferedMaskND δ K) (fun x => bufferedMaskND δ K (-x)) hw' with h | h
  · exact bufferedMaskND_support_near hδ h
  · have hn : -w ∈ tsupport (bufferedMaskND δ K) :=
      tsupport_comp_subset_preimage (bufferedMaskND δ K) continuous_neg h
    obtain ⟨z,hz,hzw⟩ := bufferedMaskND_support_near hδ hn
    refine ⟨-z,hK z hz,?_⟩
    simpa only [dist_neg_neg,neg_neg] using (show dist (-(-w)) (-z) ≤ _ by
      simpa only [dist_neg_neg] using hzw)

lemma smooth_reflect_derivative_boundND {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (hb : ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => f (-y)) x‖ ≤ C := by
  let T : E →L[ℝ] E := -ContinuousLinearMap.id ℝ E
  have hn : ‖T‖ ≤ 1 := by simpa only [T,norm_neg] using (ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=E))
  change ‖iteratedFDeriv ℝ k (f ∘ T) x‖ ≤ _
  rw [T.iteratedFDeriv_comp_right hf x (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hk : ‖T‖^k ≤ 1 := pow_le_one₀ (norm_nonneg _) hn
  exact (mul_le_mul (hb _) hk (by positivity) hC).trans (by rw [mul_one])

lemma evenBufferedMaskND_derivative_bound (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (K : Set (EuclideanSpace ℝ (Fin d))), 0<δ →
      ∀ k ≤ m, ∀ w, ‖iteratedFDeriv ℝ k (evenBufferedMaskND δ K) w‖ ≤ C*δ⁻¹^k := by
  obtain ⟨C,hC,hb⟩ := selectedCapND_derivative_bound d m
  refine ⟨C,hC,?_⟩
  intro δ K hδ k hk w
  have hfin : (k:WithTop ℕ∞) ≤ (↑(⊤:ℕ∞):WithTop ℕ∞) := by
    exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤)
  have h₁ := bufferedMaskND_contDiff δ K
  have h₂ : ContDiff ℝ ∞ (fun x => bufferedMaskND δ K (-x)) := h₁.comp contDiff_neg
  change ‖iteratedFDeriv ℝ k (fun x => (1/2:ℝ) • (bufferedMaskND δ K x+bufferedMaskND δ K (-x))) w‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (a := (1/2:ℝ)) ((h₁.add h₂).of_le hfin).contDiffAt]
  have he := congrFun (iteratedFDeriv_add (h₁.of_le hfin) (h₂.of_le hfin)) w
  change iteratedFDeriv ℝ k (fun x => bufferedMaskND δ K x+bufferedMaskND δ K (-x)) w = _ at he
  rw [he,norm_smul]
  norm_num only [Real.norm_eq_abs]
  have hb₁ := hb δ (maskCapSelectionND δ K) hδ k hk w
  have hb₂ := smooth_reflect_derivative_boundND h₁ (show 0 ≤ C*δ⁻¹^k by positivity) k
    (hb δ (maskCapSelectionND δ K) hδ k hk) w
  have hh := norm_add_le (iteratedFDeriv ℝ k (bufferedMaskND δ K) w)
    (iteratedFDeriv ℝ k (fun x => bufferedMaskND δ K (-x)) w)
  change ‖iteratedFDeriv ℝ k (bufferedMaskND δ K) w‖ ≤ _ at hb₁
  simp only [Pi.add_apply] at *
  linarith

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
