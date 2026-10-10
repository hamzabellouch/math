import OAI.MeasureTheory.Falconer.Fourier.MaskJetGeometry

namespace OAI

/-! # Starting the inverse expansion with existing individual mask jets

Previously charged derivatives remain in their original occurrences. The
new inverse adds at most twice its index to the total order, and radius
normalization cancels every previously charged power exactly.
-/

namespace Falconer.MaskJetExpansion
open scoped ContDiff
variable {ι : Type} {d : ℕ} {E H X : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

noncomputable def seed (k : ι → MaskJetIndex d) : MaskJetExpansion ι d (Space d) where
  index := Unit
  finite := inferInstance
  term := fun _ => ⟨fun _ => 1,id,k,contDiff_const,contDiff_id⟩

omit [DecidableEq ι] in
theorem seed_value (k : ι → MaskJetIndex d) (B : ι → X → Space d → ℂ)
    (x : X) (z : Space d) :
    (seed k).value B x z = ∏ i, (k i).value (B i x) z := by
  change (∑ _a : Unit, (1 : ℂ)*∏ i, (k i).value (B i x) z) = _
  simp

omit [DecidableEq ι] in
theorem seed_hasOrder (k : ι → MaskJetIndex d) :
    (seed k).HasOrder (∑ i, (k i).order) := fun _ => le_rfl

omit [Fintype ι] [DecidableEq ι] in
theorem seed_hasPointAt (k : ι → MaskJetIndex d) (z : Space d) :
    (seed k).HasPointAt z z := fun _ => rfl

omit [Fintype ι] [DecidableEq ι] in
theorem seed_geometryCoveredBy_unit (k : ι → MaskJetIndex d) :
    (seed k).GeometryCoveredBy (product : MaskJetExpansion Unit d (Space d)) :=
  fun _ => ⟨(),rfl,rfl⟩

def OrdersExtend (S : MaskJetExpansion ι d E) (k : ι → MaskJetIndex d) : Prop :=
  ∀ a i, (k i).order ≤ ((S.term a).jet i).order

omit [Fintype ι] [DecidableEq ι] in
theorem seed_ordersExtend (k : ι → MaskJetIndex d) : (seed k).OrdersExtend k :=
  fun _ _ => le_rfl

omit [Fintype ι] [DecidableEq ι] in
theorem OrdersExtend.mulFixed {S : MaskJetExpansion ι d E} {k : ι → MaskJetIndex d}
    (h : S.OrdersExtend k) (c : E → ℂ) (hc : ContDiff ℝ ∞ c) :
    (S.mulFixed c hc).OrdersExtend k := h

omit [Fintype ι] [DecidableEq ι] in
theorem OrdersExtend.pullback {S : MaskJetExpansion ι d E} {k : ι → MaskJetIndex d}
    (h : S.OrdersExtend k) (g : H → E) (hg : ContDiff ℝ ∞ g) :
    (S.pullback g hg).OrdersExtend k := h

omit [Fintype ι] [DecidableEq ι] in
theorem sum_ordersExtend {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E)
    (k : ι → MaskJetIndex d) (h : ∀ j, (S j).OrdersExtend k) :
    (sum S).OrdersExtend k := fun a => h a.1 a.2

theorem OrdersExtend.derivative {S : MaskJetExpansion ι d E} {k : ι → MaskJetIndex d}
    (h : S.OrdersExtend k) (v : E) : (S.derivative v).OrdersExtend k := by
  rintro ⟨a,b⟩ i
  cases b with
  | inl b => exact h a i
  | inr b =>
    rcases b with ⟨l,t⟩
    change (k i).order ≤ (Function.update (S.term a).jet l _ i).order
    by_cases hi : i = l
    · subst i
      rw [Function.update_self]
      exact (h a l).trans (Nat.le_succ _)
    · rw [Function.update_of_ne hi]
      exact h a i

theorem OrdersExtend.laplacian {n : ℕ} {S : MaskJetExpansion ι d E}
    {k : ι → MaskJetIndex d} (h : S.OrdersExtend k) (v : Fin n → E) :
    (S.laplacian v).OrdersExtend k :=
  sum_ordersExtend _ _ (fun j => (h.derivative (v j)).derivative (v j))

theorem OrdersExtend.iteratedLaplacian {n : ℕ} {S : MaskJetExpansion ι d E}
    {k : ι → MaskJetIndex d} (h : S.OrdersExtend k) (v : Fin n → E) (j : ℕ) :
    (S.iteratedLaplacian v j).OrdersExtend k := by
  induction j with
  | zero => exact h
  | succ j ih =>
    simpa only [MaskJetExpansion.iteratedLaplacian,Function.iterate_succ_apply'] using
      ih.laplacian v

theorem OrdersExtend.stationaryJet {m : ℕ} {S : MaskJetExpansion ι d (Space (m+3))}
    {k : ι → MaskJetIndex d} (h : S.OrdersExtend k) (j : ℕ) :
    (S.stationaryJet m j).OrdersExtend k := by
  unfold MaskJetExpansion.stationaryJet
  exact (((h.pullback _ (safeStationaryChart_contDiff m)).mulFixed _
    (SmoothSeparation.stationaryJointDensity_contDiff m)).iteratedLaplacian _ j).pullback _
      (contDiff_id.prodMk contDiff_const) |>.mulFixed _
        (SmoothSeparation.stationaryJetMultiplier_contDiff m j)

theorem OrdersExtend.inverse {m : ℕ} {S : MaskJetExpansion ι d (Space (m+3))}
    {k : ι → MaskJetIndex d} (h : S.OrdersExtend k) (j : ℕ) :
    (S.inverse m j).OrdersExtend k := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      rw [MaskJetExpansion.inverse]
      exact h.mulFixed _ _
    | succ j =>
      rw [MaskJetExpansion.inverse]
      apply OrdersExtend.mulFixed
      apply sum_ordersExtend
      intro l
      exact (ih (j-l) (by have hl := l.isLt; omega)).stationaryJet _

theorem seed_inverse_added_order (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (a : ((seed k).inverse m j).index) :
    (∑ i, (((((seed k).inverse m j).term a).jet i).order-(k i).order)) ≤ 2*j := by
  have hbase := (seed_ordersExtend k).inverse j a
  have htotal := (seed_hasOrder k).inverse j a
  have heq :
      (∑ i, (((((seed k).inverse m j).term a).jet i).order-(k i).order)) +
        (∑ i, (k i).order) = (((seed k).inverse m j).term a).order := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel (hbase i)
  omega

omit [Fintype ι] [DecidableEq ι] in
theorem radius_power_cancel {r : ℝ} (hr : r ≠ 0) {a b : ℕ} (hab : a ≤ b) :
    r^a * (r⁻¹)^b = (r⁻¹)^(b-a) := by
  calc
    _ = r^a * ((r⁻¹)^a * (r⁻¹)^(b-a)) := by
      rw [← pow_add,Nat.add_sub_of_le hab]
    _ = (r*r⁻¹)^a * (r⁻¹)^(b-a) := by rw [mul_pow]; ring
    _ = _ := by rw [mul_inv_cancel₀ hr,one_pow,one_mul]

theorem seed_inverse_radius_cancel (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (a : ((seed k).inverse m j).index) :
    (∏ i, (r i)^(k i).order) *
      (∏ i, (r i)⁻¹^((((seed k).inverse m j).term a).jet i).order) =
    ∏ i, (r i)⁻¹^(((((seed k).inverse m j).term a).jet i).order-(k i).order) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact radius_power_cancel (hr i) ((seed_ordersExtend k).inverse j a i)

theorem seed_inverse_radius_le (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) {D : ℝ} (hD : 1 ≤ D)
    (hscale : ∀ i, (r i)⁻¹ ≤ D) (a : ((seed k).inverse m j).index) :
    (∏ i, (r i)^(k i).order) *
      (∏ i, (r i)⁻¹^((((seed k).inverse m j).term a).jet i).order) ≤ D^(2*j) := by
  rw [seed_inverse_radius_cancel m j k r (fun i => (hr i).ne') a]
  calc
    _ ≤ ∏ i, D^(((((seed k).inverse m j).term a).jet i).order-(k i).order) := by
      apply Finset.prod_le_prod₀ (fun i _ => pow_nonneg (inv_nonneg.mpr (hr i).le) _)
      intro i _
      exact pow_le_pow_left₀ (inv_nonneg.mpr (hr i).le) (hscale i) _
    _ = D^(∑ i, (((((seed k).inverse m j).term a).jet i).order-(k i).order)) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ D^(2*j) := pow_le_pow_right₀ hD (seed_inverse_added_order m j k a)

end Falconer.MaskJetExpansion

end OAI
