import OAI.Geometry.SurfaceImmersion.Correction.SpecialPointCorrection

namespace OAI

/-! Simultaneous small affine corrections around finitely many distinct special points. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.TransverseSmallFunction

theorem exists_finite_special_correction {ι : Type*} [Fintype ι]
    (p : ι → Base) (hp : Function.Injective p) {U : Set Base}
    (hU : IsOpen U) (hpU : ∀ i, p i ∈ U) (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Base → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ U ∧
      (∀ x, |H x| < ε) ∧ ∃ V : Set Base, IsOpen V ∧ (∀ i, p i ∈ V) ∧ V ⊆ U ∧
        ∀ x ∈ V, fderiv ℝ H x (0, 1) = B := by
  classical
  obtain ⟨W, hW, hdisj⟩ := (Set.finite_range p).t2_separation
  let e := ε / ((Fintype.card ι : ℝ) + 1)
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have he : 0 < e := div_pos hε hden
  have hlocal (i : ι) := exists_special_point_correction
    ((hW (p i)).2.inter hU) ⟨(hW (p i)).1, hpU i⟩ B he
  choose H hH hHc hHs hHb V hVo hpV hVU hVD using hlocal
  let F : Base → ℝ := fun x => ∑ i, H i x
  have hFs : tsupport F ⊆ ⋃ i, tsupport (H i) := by
    apply closure_minimal
    · intro x hx
      by_contra hnot
      have hz : F x = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact image_eq_zero_of_notMem_tsupport (fun hi => hnot (mem_iUnion.mpr ⟨i, hi⟩))
      exact hx hz
    · exact isClosed_iUnion_of_finite (fun i => isClosed_tsupport (H i))
  have hFc : HasCompactSupport F :=
    (isCompact_iUnion (fun i => hHc i)).of_isClosed_subset (isClosed_tsupport F) hFs
  have hFU : tsupport F ⊆ U := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hFs hx)
    exact (hHs i hi).2
  refine ⟨F, ContDiff.sum (fun i _ => hH i), hFc, hFU, ?_, ⋃ i, V i,
    isOpen_iUnion hVo, (fun i => mem_iUnion.mpr ⟨i, hpV i⟩), ?_, ?_⟩
  · intro x
    have hsum : |F x| ≤ (Fintype.card ι : ℝ) * e := by
      calc
        |F x| ≤ ∑ i, |H i x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : ι, e := Finset.sum_le_sum (fun i _ => (hHb i x).le)
        _ = (Fintype.card ι : ℝ) * e := by simp
    apply lt_of_le_of_lt hsum
    change (Fintype.card ι : ℝ) * (ε / ((Fintype.card ι : ℝ) + 1)) < ε
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (hVU i hi).2
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    change fderiv ℝ (fun y => ∑ j, H j y) x (0, 1) = B
    rw [fderiv_fun_sum (fun j _ => (hH j).differentiable (by simp) x), sum_apply]
    rw [Finset.sum_eq_single i]
    · exact hVD i x hi
    · intro j _ hji
      have hxWi : x ∈ W (p i) := (hVU i hi).1
      have hd : Disjoint (W (p i)) (W (p j)) :=
        hdisj (mem_range_self i) (mem_range_self j) (fun hij => hji (hp hij).symm)
      have hnot : x ∉ tsupport (H j) := fun hh =>
        (Set.disjoint_left.mp hd) hxWi (hHs j hh).1
      rw [fderiv_of_notMem_tsupport ℝ hnot]
      rfl
    · simp

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
