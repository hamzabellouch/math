import OAI.Analysis.SeparableQuotients.TreeBounds

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

lemma exists_finite_vector_normer {f : Family} (x : Γ →₀ ℝ) (hx0 : x ≠ 0)
    (hx : 1 ≤ ‖norming.includeFinite x‖)
    (hcolor : ∀ k, f = .pure k → ∀ a ∈ x.support, Colors.color a = k) :
    ∃ (g : Array), g ∈ f.norming ∧ g ≠ 0 ∧
      (∀ a ∈ g.support, a ∈ (vectorCrop x hx0).set f) ∧
      1/2 < norming.evaluateArray (norming.includeFinite x) g := by
  have hn : ∃ g ∈ f.norming, 1/2 < norming.evaluateArray (norming.includeFinite x) g := by
    cases f with
    | pure k =>
      apply exists_pure_normer k _ _ _ (by norm_num) (by linarith)
      intro a ha
      rw [norming.coordinate_includeFinite]
      exact Finsupp.notMem_support_iff.mp (fun h => ha (hcolor k rfl a h))
    | mixed => exact exists_full_normer _ _ (by norm_num) (by linarith)
  obtain ⟨g,hg,hgv⟩ := hn
  let A := vectorCrop x hx0
  have heq : norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) g) =
      norming.evaluateArray (norming.includeFinite x) g := by
    apply evaluateArray_crop_of_zero
    intro a ha
    rw [norming.coordinate_includeFinite]
    exact Finsupp.notMem_support_iff.mp (fun h => ha (support_mem_vectorCrop f x hx0 a h))
  refine ⟨restrict (A.set f) g,family_norming_crop f A g hg,?_,?_,by rwa [heq]⟩
  · intro hz
    rw [hz,map_zero] at heq
    linarith
  · intro a ha
    by_contra hn
    change a ∉ A.set f at hn
    exact Finsupp.mem_support_iff.mp ha (by simp [restrict,hn])

lemma vectorCrop_mono {f : Family} {x y : Γ →₀ ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x.support ⊆ y.support) : (vectorCrop x hx).set f ⊆ (vectorCrop y hy).set f := by
  have ho : (vectorCrop x hx).ordinal ⊆ (vectorCrop y hy).ordinal := by
    intro a ha
    exact ⟨(Finset.min'_le _ _ (hxy (Finset.min'_mem _ _))).trans ha.1,
      ha.2.trans (Finset.le_max' _ _ (hxy (Finset.max'_mem _ _)))⟩
  have hc : (vectorCrop x hx).colors ⊆ (vectorCrop y hy).colors := by
    intro a ha
    have hsub : x.support.image Colors.color ⊆ y.support.image Colors.color := Finset.image_subset_image hxy
    exact ⟨(Finset.min'_le _ _ (hsub (Finset.min'_mem _ _))).trans ha.1,
      ha.2.trans (Finset.le_max' _ _ (hsub (Finset.max'_mem _ _)))⟩
  intro a ha
  cases f with
  | pure k => exact ho ha
  | mixed => exact ⟨ho ha.1,hc ha.2⟩

lemma BlockSequence.support_subset_sum {f : Family} (z : BlockSequence f) (k : ℕ) (i : Fin k) :
    (z.vector i).support ⊆ (∑ j : Fin k, z.vector j).support := by
  intro α hα
  apply Finsupp.mem_support_iff.mpr
  rw [Finsupp.finsetSum_apply,Finset.sum_eq_single i]
  · exact Finsupp.mem_support_iff.mp hα
  · intro j _ hji
    apply Finsupp.notMem_support_iff.mp
    intro hj
    have hne : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (lt_irrefl α) (z.successive j i hlt α hj α hα).1
    · exact (lt_irrefl α) (z.successive i j hlt α hα α hj).1
  · simp

lemma BlockSequence.sum_nonzero {f : Family} (z : BlockSequence f) (k : ℕ) (hk : 0 < k) :
    (∑ j : Fin k, z.vector j) ≠ 0 := by
  intro hz
  obtain ⟨α,hα⟩ := Finsupp.support_nonempty_iff.mpr (z.nonzero 0)
  have hh := z.support_subset_sum k ⟨0,hk⟩ hα
  simp only [hz,Finsupp.support_zero,Finset.notMem_empty] at hh

lemma BlockSequence.normer_cross {f : Family} (z : BlockSequence f) (i j : ℕ) (hij : i ≠ j)
    (g : Array) (hg : ∀ α ∈ g.support, α ∈ (vectorCrop (z.vector i) (z.nonzero i)).set f) :
    norming.evaluateArray (z.embed j) g = 0 := by
  apply evaluateArray_finite_disjoint
  apply Finset.disjoint_left.mpr
  intro α hα hgα
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (lt_irrefl α) (vectorCrop_successive (z.nonzero i) (z.nonzero j) (z.successive i j hij)
      α (hg α hgα) α (support_mem_vectorCrop f _ _ α hα)).1
  · exact (lt_irrefl α) (vectorCrop_successive (z.nonzero j) (z.nonzero i) (z.successive j i hji)
      α (support_mem_vectorCrop f _ _ α hα) α (hg α hgα)).1

/-- Exact pairs with uncropped child legality and support bounds in both orders. -/
structure ExactPair {f : Family} (z : BlockSequence f) (a J : ℕ) where
  vector : Γ →₀ ℝ
  nonzero : vector ≠ 0
  mem_tail : vector ∈ z.tailSpan a
  norm_le : ‖norming.includeFinite vector‖ ≤ 500
  pure_color : ∀ k, f = .pure k → ∀ α ∈ vector.support, Colors.color α = k
  piece : TypeI f
  weight_eq : piece.weight = J
  child_mem : ∀ h, piece.child h ∈ f.norming
  eval_ge : 1/2 ≤ norming.evaluateArray (norming.includeFinite vector) piece.value
  support : ∀ α ∈ piece.value.support, α ∈ (vectorCrop vector nonzero).set f

lemma BlockSequence.exists_exactPair {f : Family} (z : BlockSequence f) (a J : ℕ) (hJ : 1 ≤ J) :
    Nonempty (ExactPair z a J) := by
  have hθ : 0 < f.theta J := by rw [Family.theta,Parameters.theta_eq f.s_ge_two]; positivity
  have hL : (0 : ℝ) < f.L J := by exact_mod_cast f.L_pos J
  have hm : (0 : ℝ) < f.m J := by exact_mod_cast f.m_pos J
  let ε := f.theta J / (f.L J : ℝ)^(1/f.r)
  have hε : 0 < ε := div_pos hθ (Real.rpow_pos_of_pos hL _)
  obtain ⟨w⟩ := exists_thinnedWindows z J ε hε a
  have heps : ε*(f.L J : ℝ)^(1/f.r) ≤ f.theta J := by
    dsimp [ε]
    rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hL _).ne']
  let X := ∑ i : Fin (f.L J), w.blocks.vector i
  have hX : X ≠ 0 := w.blocks.sum_nonzero _ (f.L_pos J)
  let c : ℝ := (f.m J : ℝ)/(f.L J : ℝ)
  have hc : 0 < c := div_pos hm hL
  let y := c • X
  have hy : y ≠ 0 := smul_ne_zero hc.ne' hX
  have hys : y.support = X.support := Finsupp.support_smul_eq hc.ne'
  have hn := fun i : Fin (f.L J) => exists_finite_vector_normer (w.blocks.vector i) (w.blocks.nonzero i)
    (w.lower_norm i) (fun k hk α hα => w.blocks.pure_color k hk i α hα)
  choose g hg hgn hgs hgv using hn
  let e : TypeI f := {
    weight := J
    weight_pos := hJ
    length := f.L J
    length_pos := f.L_pos J
    length_le := le_rfl
    child := g
    child_nonzero := hgn
    successive := by
      intro i j hij α hα β hβ
      exact vectorCrop_successive (w.blocks.nonzero i) (w.blocks.nonzero j)
        (w.blocks.successive i j hij) α (hgs i α hα) β (hgs j β hβ) }
  have hgeval (i : Fin (f.L J)) : norming.evaluateArray (norming.includeFinite X) (g i) =
      norming.evaluateArray (w.blocks.embed i) (g i) := by
    have hgf : g i ∈ Full := f.norming_subset_full (hg i)
    simp only [X,norming.evaluateArray_eq_functional _ ⟨g i,hgf⟩,map_sum]
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [← norming.evaluateArray_eq_functional]
      exact w.blocks.normer_cross i j (fun he => hji (Fin.ext he.symm)) (g i) (hgs i)
    · simp
  have hyEval : 1/2 ≤ norming.evaluateArray (norming.includeFinite y) e.value := by
    have hef : e.value ∈ Full := f.norming_subset_full (e.mem_family hg)
    rw [norming.evaluateArray_eq_functional _ ⟨e.value,hef⟩]
    change 1/2 ≤ norming.functional ⟨e.value,hef⟩ (norming.includeFinite (c • X))
    rw [map_smul,map_smul]
    rw [smul_eq_mul, ← norming.evaluateArray_eq_functional (norming.includeFinite X) ⟨e.value,hef⟩]
    change 1/2 ≤ c * norming.evaluateArray (norming.includeFinite X) e.value
    rw [TypeI.value,map_smul,map_sum]
    simp only [show e.weight = J from rfl,show e.child = g from rfl,Rat.smul_def,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
    have he : (f.L J : ℝ)*(1/2 : ℝ) ≤ ∑ i, norming.evaluateArray (norming.includeFinite X) (g i) := by
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin (f.L J) => (1/2 : ℝ))
          (g := fun i => norming.evaluateArray (norming.includeFinite X) (g i))
          (fun i _ => by rw [hgeval i]; exact (hgv i).le)
    calc
      1/2 = c * ((1/(f.m J : ℝ))*((f.L J : ℝ)*(1/2))) := by dsimp [c]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) hc.le
  refine ⟨⟨y,hy,?_,?_,?_,e,rfl,hg,hyEval,?_⟩⟩
  · exact Submodule.smul_mem _ c (Submodule.sum_mem _ (fun i _ => w.mem_tail i))
  · have hb := w.norm_sum_bound (Finset.range (f.L J)) hJ (Finset.card_range _) (by simpa using heps)
    have hXnorm : ‖norming.includeFinite X‖ ≤ 500*(f.L J : ℝ)/(f.m J : ℝ) := by
      simpa only [X,Finset.sum_coe_sort,Fin.sum_univ_eq_sum_range] using hb
    change ‖norming.includeFinite (c • X)‖ ≤ 500
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    calc
      _ ≤ c*(500*(f.L J : ℝ)/(f.m J : ℝ)) := mul_le_mul_of_nonneg_left hXnorm hc.le
      _ = 500 := by dsimp [c]; field_simp
  · intro k hk α hα
    rw [hys] at hα
    obtain ⟨i,_,hi⟩ := Finsupp.mem_support_finsetSum α hα
    exact w.blocks.pure_color k hk i α hi
  · intro α hα
    have hh : α ∈ (∑ i : Fin (f.L J),g i).support := Finsupp.support_smul hα
    obtain ⟨i,_,hi⟩ := Finsupp.mem_support_finsetSum α hh
    apply vectorCrop_mono (w.blocks.nonzero i) hy _ (hgs i α hi)
    rw [hys]
    exact w.blocks.support_subset_sum _ i

end SeparableQuotient.ActualSpace

end

end OAI
