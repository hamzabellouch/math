import OAI.GroupTheory.UniversalGroup.UniversalPresentation

namespace OAI

open Set Metric Topology BigOperators
namespace UniversalFInfinity.SimplexDisk
noncomputable section

def Simplex (A : Type*) [Fintype A] : Set (A → ℝ) :=
  {x | (∀ a, 0 ≤ x a) ∧ ∑ a, x a = 1}

instance (A : Type*) [Fintype A] : CompactSpace (Simplex A) := by
  apply isCompact_iff_compactSpace.mp
  have closed : IsClosed (Simplex A) := by
    have description : Simplex A =
        (⋂ index, {point | (0 : ℝ) ≤ point index}) ∩ {point | ∑ index, point index = 1} := by
      ext point
      simp [Simplex]
    rw [description]
    exact (isClosed_iInter fun index => isClosed_le continuous_const (continuous_apply index)).inter
      (isClosed_eq (continuous_finsetSum _ fun index _ => continuous_apply index) continuous_const)
  apply (isCompact_Icc (a := (0 : A → ℝ)) (b := 1)).of_isClosed_subset closed
  intro point membership
  refine ⟨membership.1, fun index => ?_⟩
  change point index ≤ (1 : ℝ)
  rw [← membership.2]
  exact Finset.single_le_sum (fun other _ => membership.1 other) (Finset.mem_univ index)

def Truncated (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}
def Positive (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}
def sumCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, ContinuousLinearMap.proj i
@[simp] lemma sumCLM_apply (n : ℕ) (x : Fin n → ℝ) : sumCLM n x = ∑ i, x i := by
  simp [sumCLM]

lemma truncated_closed (n : ℕ) : IsClosed (Truncated n) := by
  have h : Truncated n = (⋂ i, {x | (0:ℝ) ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
    ext x; simp [Truncated]
  rw [h]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

lemma positive_open (n : ℕ) : IsOpen (Positive n) := by
  have h : Positive n = (⋂ i, {x | (0:ℝ) < x i}) ∩ {x | ∑ i, x i < 1} := by
    ext x; simp [Positive]
  rw [h]
  exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

lemma interior_truncated (n : ℕ) : interior (Truncated n) = Positive n := by
  apply Subset.antisymm
  · intro x hx
    have hc : ∀ i, 0 < x i := by
      intro i
      have hh := interior_mono (show Truncated n ⊆ (Function.eval i) ⁻¹' Ici (0:ℝ) from fun _ h => h.1 i) hx
      rw [← (isOpenMap_eval i).preimage_interior_eq_interior_preimage (continuous_apply i),interior_Ici] at hh
      exact hh
    refine ⟨hc,?_⟩
    cases n with
    | zero => simp
    | succ n =>
      have hs : Function.Surjective (sumCLM (n+1)) := by
        intro r
        refine ⟨Pi.single 0 r,?_⟩
        simp
      have hh := interior_mono (show Truncated (n+1) ⊆ (sumCLM (n+1)) ⁻¹' Iic (1:ℝ) from fun _ h => by simpa using h.2) hx
      rw [← ((sumCLM (n+1)).isOpenMap hs).preimage_interior_eq_interior_preimage (sumCLM (n+1)).continuous,interior_Iic] at hh
      simpa only [mem_preimage,mem_Iio,sumCLM_apply] using hh
  · apply (positive_open n).subset_interior_iff.mpr
    exact fun _ h => ⟨fun i => (h.1 i).le,h.2.le⟩

lemma truncated_convex (n : ℕ) : Convex ℝ (Truncated n) := by
  have h : Truncated n = (⋂ i, ((LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) ⁻¹' Ici 0)) ∩
      (sumCLM n) ⁻¹' Iic 1 := by ext x; simp [Truncated]
  rw [h]
  exact (convex_iInter fun i => (convex_Ici (0:ℝ)).linear_preimage (LinearMap.proj i)).inter
    ((convex_Iic (1:ℝ)).linear_preimage (sumCLM n).toLinearMap)

lemma truncated_bounded (n : ℕ) : Bornology.IsBounded (Truncated n) := by
  apply (isBounded_Icc (a := (0 : Fin n → ℝ)) (b := 1)).subset
  intro x hx
  refine ⟨hx.1,fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

lemma positive_nonempty (n : ℕ) : (Positive n).Nonempty := by
  refine ⟨fun _ => 1 / (n+1 : ℝ),fun _ => by positivity,?_⟩
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn : (0:ℝ) < n+1 := by positivity
  rw [mul_one_div,div_lt_one hn]
  linarith

noncomputable def ambient (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  Classical.choose (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (truncated_convex n) (by rw [interior_truncated]; exact positive_nonempty n) (truncated_bounded n))

lemma ambient_positive (n : ℕ) : ambient n '' Positive n = ball 0 1 := by
  simpa only [ambient,interior_truncated] using
    (Classical.choose_spec (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (truncated_convex n) (by rw [interior_truncated]; exact positive_nonempty n) (truncated_bounded n))).1
lemma ambient_truncated (n : ℕ) : ambient n '' Truncated n = closedBall 0 1 := by
  simpa only [ambient,(truncated_closed n).closure_eq] using
    (Classical.choose_spec (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (truncated_convex n) (by rw [interior_truncated]; exact positive_nonempty n) (truncated_bounded n))).2.1

noncomputable def truncatedDisk (n : ℕ) : Truncated n ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  ((ambient n).image (Truncated n)).trans (Homeomorph.setCongr (ambient_truncated n))

noncomputable def simplexTruncated (n : ℕ) : SimplexDisk.Simplex (Fin (n+1)) ≃ₜ Truncated n where
  toFun x := ⟨fun i => x.1 i.succ,fun i => x.2.1 _,by
    have h := x.2.2
    rw [Fin.sum_univ_succ] at h
    linarith [x.2.1 0]⟩
  invFun x := ⟨Fin.cons (1 - ∑ i, x.1 i) x.1,by
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr x.2.2
      · exact x.2.1 j
    · simp [Fin.sum_univ_succ]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    have h := x.2.2
    rw [Fin.sum_univ_succ] at h
    change 1 - ∑ i : Fin n, x.1 i.succ = x.1 0
    linarith
  right_inv x := by rfl
  continuous_toFun := (continuous_pi fun i => (continuous_apply i.succ).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_const.sub (continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_subtype_val)
    · exact (continuous_apply j).comp continuous_subtype_val

noncomputable def simplexDisk (n : ℕ) : SimplexDisk.Simplex (Fin (n+1)) ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (simplexTruncated n).trans (truncatedDisk n)

lemma simplexTruncated_positive (n : ℕ) (x : SimplexDisk.Simplex (Fin (n+1))) :
    (simplexTruncated n x).1 ∈ Positive n ↔ ∀ i, 0 < x.1 i := by
  have h := x.2.2
  rw [Fin.sum_univ_succ] at h
  constructor
  · rintro ⟨hc,hs⟩ i
    refine Fin.cases ?_ (fun j => hc j) i
    change ∑ i : Fin n, x.1 i.succ < 1 at hs
    linarith
  · intro hc
    refine ⟨fun j => hc _,?_⟩
    change ∑ i : Fin n, x.1 i.succ < 1
    linarith [hc 0]

lemma simplexDisk_open (n : ℕ) (x : SimplexDisk.Simplex (Fin (n+1))) :
    (simplexDisk n x).1 ∈ ball 0 1 ↔ ∀ i, 0 < x.1 i := by
  rw [← simplexTruncated_positive]
  change ambient n (simplexTruncated n x).1 ∈ ball 0 1 ↔ _
  rw [← ambient_positive]
  exact (ambient n).injective.mem_set_image

lemma simplexDisk_boundary (n : ℕ) (x : SimplexDisk.Simplex (Fin (n+1))) :
    (simplexDisk n x).1 ∈ sphere 0 1 ↔ ∃ i, x.1 i = 0 := by
  have h := (simplexDisk n x).2
  rw [mem_sphere,mem_closedBall] at *
  have ho := simplexDisk_open n x
  simp only [mem_ball] at ho
  constructor
  · intro he
    have hn : ¬ ∀ i, 0 < x.1 i := by rw [←ho,he]; exact lt_irrefl _
    push Not at hn
    obtain ⟨i,hi⟩ := hn
    exact ⟨i,le_antisymm hi (x.2.1 i)⟩
  · rintro ⟨i,hi⟩
    apply le_antisymm h
    by_contra hn
    have hp := ho.mp (lt_of_not_ge hn)
    linarith [hp i]

noncomputable def reindex {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    SimplexDisk.Simplex A ≃ₜ SimplexDisk.Simplex B where
  toFun x := ⟨fun b => x.1 (e.symm b),fun b => x.2.1 _,(e.symm.sum_comp x.1).trans x.2.2⟩
  invFun x := ⟨fun a => x.1 (e a),fun a => x.2.1 _,(e.sum_comp x.1).trans x.2.2⟩
  left_inv x := by ext a; simp
  right_inv x := by ext b; simp
  continuous_toFun := (continuous_pi fun b => ((continuous_apply (e.symm b)).comp continuous_subtype_val : Continuous (fun x : SimplexDisk.Simplex A => x.1 (e.symm b)))).subtype_mk _
  continuous_invFun := (continuous_pi fun a => ((continuous_apply (e a)).comp continuous_subtype_val : Continuous (fun x : SimplexDisk.Simplex B => x.1 (e a)))).subtype_mk _

lemma reindex_positive {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (x : SimplexDisk.Simplex A) :
    (∀ b, 0 < (reindex e x).1 b) ↔ ∀ a, 0 < x.1 a := by
  constructor
  · intro h a
    change ∀ b, 0 < x.1 (e.symm b) at h
    simpa only [e.symm_apply_apply] using h (e a)
  · intro h b
    change 0 < x.1 (e.symm b)
    exact h _

end
end UniversalFInfinity.SimplexDisk

end OAI
