import OAI.MeasureTheory.Falconer.Fourier.InverseMaskJets

namespace OAI

/-! # A fixed finite family for the inverse's geometric coefficients

Changing which mask receives a derivative changes its jet index, but not
the smooth coefficient or evaluation point. Collapse all mask choices to
one label to obtain a coefficient family independent of the list length.
-/

namespace Falconer.MaskJetExpansion
open scoped ContDiff
variable {ι τ : Type} {d : ℕ} {E H : Type*}
  [Fintype ι] [Fintype τ] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def GeometryCoveredBy (S : MaskJetExpansion ι d E) (T : MaskJetExpansion τ d E) : Prop :=
  ∀ a, ∃ b, (S.term a).coefficient = (T.term b).coefficient ∧
    (S.term a).point = (T.term b).point

omit [Fintype ι] [Fintype τ] in
theorem product_geometryCoveredBy :
    (product : MaskJetExpansion ι d (Space d)).GeometryCoveredBy
      (product : MaskJetExpansion τ d (Space d)) := fun _ => ⟨(),rfl,rfl⟩

omit [Fintype ι] [Fintype τ] in
theorem GeometryCoveredBy.mulFixed {S : MaskJetExpansion ι d E}
    {T : MaskJetExpansion τ d E} (h : S.GeometryCoveredBy T)
    (c : E → ℂ) (hc : ContDiff ℝ ∞ c) :
    (S.mulFixed c hc).GeometryCoveredBy (T.mulFixed c hc) := by
  intro a
  obtain ⟨b,hc',hp⟩ := h a
  refine ⟨b,?_,hp⟩
  change (fun z => c z*(S.term a).coefficient z) = _
  rw [hc']
  rfl

omit [Fintype ι] [Fintype τ] in
theorem GeometryCoveredBy.pullback {S : MaskJetExpansion ι d E}
    {T : MaskJetExpansion τ d E} (h : S.GeometryCoveredBy T)
    (g : H → E) (hg : ContDiff ℝ ∞ g) :
    (S.pullback g hg).GeometryCoveredBy (T.pullback g hg) := by
  intro a
  obtain ⟨b,hc,hp⟩ := h a
  refine ⟨b,?_,?_⟩
  · change (S.term a).coefficient ∘ g = _
    rw [hc]
    rfl
  · change (S.term a).point ∘ g = _
    rw [hp]
    rfl

omit [Fintype ι] [Fintype τ] in
theorem sum_geometryCoveredBy {J : Type} [Fintype J]
    (S : J → MaskJetExpansion ι d E) (T : J → MaskJetExpansion τ d E)
    (h : ∀ j, (S j).GeometryCoveredBy (T j)) : (sum S).GeometryCoveredBy (sum T) := by
  rintro ⟨j,a⟩
  obtain ⟨b,hc,hp⟩ := h j a
  exact ⟨⟨j,b⟩,hc,hp⟩

theorem GeometryCoveredBy.derivative [DecidableEq ι] [DecidableEq τ] [Nonempty τ]
    {S : MaskJetExpansion ι d E} {T : MaskJetExpansion τ d E}
    (h : S.GeometryCoveredBy T) (v : E) :
    (S.derivative v).GeometryCoveredBy (T.derivative v) := by
  classical
  rintro ⟨a,c⟩
  obtain ⟨b,hc,hp⟩ := h a
  cases c with
  | inl c =>
    refine ⟨(b,.inl c),?_,?_⟩
    · change (fun z => fderiv ℝ (S.term a).coefficient z v) = _
      rw [hc]
      rfl
    · exact hp
  | inr c =>
    rcases c with ⟨i,j⟩
    refine ⟨(b,.inr (Classical.choice inferInstance,j)),?_,?_⟩
    · change (fun z => (S.term a).coefficient z *
        ((fderiv ℝ (S.term a).point z v) j : ℂ)) = _
      rw [hc,hp]
      rfl
    · exact hp

theorem GeometryCoveredBy.laplacian [DecidableEq ι] [DecidableEq τ] [Nonempty τ]
    {n : ℕ} {S : MaskJetExpansion ι d E} {T : MaskJetExpansion τ d E}
    (h : S.GeometryCoveredBy T) (v : Fin n → E) :
    (S.laplacian v).GeometryCoveredBy (T.laplacian v) :=
  sum_geometryCoveredBy _ _ (fun j => (h.derivative (v j)).derivative (v j))

theorem GeometryCoveredBy.iteratedLaplacian [DecidableEq ι] [DecidableEq τ] [Nonempty τ]
    {n : ℕ} {S : MaskJetExpansion ι d E} {T : MaskJetExpansion τ d E}
    (h : S.GeometryCoveredBy T) (v : Fin n → E) (j : ℕ) :
    (S.iteratedLaplacian v j).GeometryCoveredBy (T.iteratedLaplacian v j) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    simpa only [MaskJetExpansion.iteratedLaplacian,Function.iterate_succ_apply'] using
      ih.laplacian v

theorem GeometryCoveredBy.stationaryJet [DecidableEq ι] [DecidableEq τ] [Nonempty τ]
    {m : ℕ} {S : MaskJetExpansion ι d (Space (m+3))}
    {T : MaskJetExpansion τ d (Space (m+3))} (h : S.GeometryCoveredBy T) (j : ℕ) :
    (S.stationaryJet m j).GeometryCoveredBy (T.stationaryJet m j) := by
  unfold MaskJetExpansion.stationaryJet
  exact (((h.pullback _ (safeStationaryChart_contDiff m)).mulFixed _
    (SmoothSeparation.stationaryJointDensity_contDiff m)).iteratedLaplacian _ j).pullback _
      (contDiff_id.prodMk contDiff_const) |>.mulFixed _
        (SmoothSeparation.stationaryJetMultiplier_contDiff m j)

theorem GeometryCoveredBy.inverse [DecidableEq ι] [DecidableEq τ] [Nonempty τ]
    {m : ℕ} {S : MaskJetExpansion ι d (Space (m+3))}
    {T : MaskJetExpansion τ d (Space (m+3))} (h : S.GeometryCoveredBy T) (j : ℕ) :
    (S.inverse m j).GeometryCoveredBy (T.inverse m j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      rw [MaskJetExpansion.inverse,MaskJetExpansion.inverse]
      exact h.mulFixed _ _
    | succ j =>
      rw [MaskJetExpansion.inverse,MaskJetExpansion.inverse]
      apply GeometryCoveredBy.mulFixed
      apply sum_geometryCoveredBy
      intro k
      exact (ih (j-k) (by have hk := k.isLt; omega)).stationaryJet _

theorem inverse_product_geometryCoveredBy_unit [DecidableEq ι] (m j : ℕ) :
    ((product : MaskJetExpansion ι (m+3) (Space (m+3))).inverse m j).GeometryCoveredBy
      ((product : MaskJetExpansion Unit (m+3) (Space (m+3))).inverse m j) :=
  product_geometryCoveredBy.inverse j

omit [Fintype ι] [Fintype τ] in
theorem coefficient_derivatives_bounded_on (T : MaskJetExpansion τ d E)
    (k : ℕ) {s : Set E} (hs : IsCompact s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a z, z ∈ s →
      ‖iteratedFDeriv ℝ k (T.term a).coefficient z‖ ≤ C := by
  classical
  have hbound (a : T.index) := hs.exists_bound_of_continuousOn
    (((T.term a).coefficient_smooth.iteratedFDeriv_right (m := ∞) (i := k)
      (by simp)).continuous.continuousOn)
  choose c hc using hbound
  refine ⟨∑ a : T.index, |c a|,Finset.sum_nonneg (fun a _ => abs_nonneg _),?_⟩
  intro a z hz
  exact (hc a z hz).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun b _ => abs_nonneg (c b)) (Finset.mem_univ a)))

/-- The coefficient bound is selected before the finite mask type. -/
theorem inverse_product_coefficient_derivatives (m j k : ℕ)
    {s : Set (Space (m+3))} (hs : IsCompact s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ a : ((product : MaskJetExpansion ι (m+3) (Space (m+3))).inverse m j).index,
        ∀ z ∈ s, ‖iteratedFDeriv ℝ k
          ((((product : MaskJetExpansion ι (m+3) (Space (m+3))).inverse m j).term a).coefficient)
          z‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := coefficient_derivatives_bounded_on
    ((product : MaskJetExpansion Unit (m+3) (Space (m+3))).inverse m j) k hs
  refine ⟨C,hC,?_⟩
  intro ι _ _ a z hz
  obtain ⟨b,hcoeff,_⟩ := inverse_product_geometryCoveredBy_unit (ι := ι) m j a
  rw [hcoeff]
  exact hbound b z hz

end Falconer.MaskJetExpansion

end OAI
