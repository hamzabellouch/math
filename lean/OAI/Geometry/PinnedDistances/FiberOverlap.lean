import OAI.Geometry.PinnedDistances.SmallCells

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy Variance
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]

def slice (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (lam : ℝ) (C : Finset P) : ℝ :=
  ∑ i, w i * (if x i ∈ C ∧ mass (p i) C < lam then mass (p i) C else 0)

def edgeCell (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (C : Finset P) : ℝ :=
  ∑ a ∈ C, ∑ b ∈ C, edgeLaw w p x a b

omit [Fintype P] in
lemma edgeCell_formula (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (C : Finset P) :
    edgeCell w p x C = ∑ i, w i * (if x i ∈ C then mass (p i) C else 0) := by
  classical
  unfold edgeCell edgeLaw
  calc
    _ = ∑ a ∈ C, ∑ i, ∑ b ∈ C, if x i = a then w i * p i b else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ i, ∑ a ∈ C, ∑ b ∈ C, if x i = a then w i * p i b else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have he (a : P) : (∑ b ∈ C, if x i = a then w i*p i b else 0) =
          if x i = a then w i*mass (p i) C else 0 := by
        by_cases h : x i = a <;> simp [h,mass,Finset.mul_sum]
      simp_rw [he]
      by_cases h : x i ∈ C <;> simp [h,eq_comm]

omit [Fintype P] in
lemma slice_nonneg (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i y, 0 ≤ p i y) (lam : ℝ) (C : Finset P) :
    0 ≤ slice w p x lam C := by
  classical
  unfold slice
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (by split_ifs; exact mass_nonneg (hp i) _; rfl))

omit [Fintype P] in
lemma slice_le_edgeCell (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i y, 0 ≤ p i y) (lam : ℝ) (C : Finset P) :
    slice w p x lam C ≤ edgeCell w p x C := by
  rw [edgeCell_formula]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  split_ifs <;> simp_all [mass_nonneg (hp i)]

omit [Fintype P] in
lemma slice_le_lam (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (lam : ℝ) (hlam : 0 ≤ lam) (C : Finset P) :
    slice w p x lam C ≤ lam := by
  calc
    _ ≤ ∑ i, w i * lam := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      split_ifs with h
      · exact h.2.le
      · exact hlam
    _ = _ := by rw [← Finset.sum_mul,hW,one_mul]

omit [Fintype P] in
lemma edgeLaw_diag (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hx : ∀ i, p i (x i) = 0) (a : P) : edgeLaw w p x a a = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : x i = a
  · rw [ite_eq_left h,← h,hx i,mul_zero]
  · simp [h]

lemma edgeCell_dom (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hx : ∀ i, p i (x i) = 0) (B : ℝ)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1)))
    (C : Finset P) : edgeCell w p x C ≤ B*pairCell Finset.univ C := by
  classical
  simp only [pairCell,Finset.mul_sum,edgeCell]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases hab : a = b
  · subst b; simp [edgeLaw_diag w p x hx,pairProb_diag]
  · simpa [pairProb,hab,div_eq_mul_inv] using hdom a b hab

omit [Fintype P] in
lemma slice_singleton (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hx : ∀ i, p i (x i) = 0) (lam : ℝ) (C : Finset P) (hC : C.card ≤ 1) :
    slice w p x lam C = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : x i ∈ C
  · have he : C = {x i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hi,fun y hy => (Finset.card_le_one.mp hC y hy (x i) hi)⟩
    simp [he,mass,hx]
  · simp [hi]

lemma large_slice_bound (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (hn : 2 ≤ Fintype.card P)
    (lam τ : ℝ) (hlam : 0 ≤ lam) (hτ : 0 < τ)
    (hτn : 2 ≤ τ*(Fintype.card P:ℝ)) (C : Finset P)
    (hC : τ*(Fintype.card P:ℝ) ≤ C.card) :
    slice w p x lam C ≤ (2*lam/τ^2)*pairCell Finset.univ C := by
  have hn0 : 0 < (Fintype.card P:ℝ) := by exact_mod_cast (show 0 < Fintype.card P by omega)
  have hm : 2 ≤ C.card := by exact_mod_cast hτn.trans hC
  have hcomp := (uniform_pair_comparison C hm).1
  have ha : τ ≤ cellProb Finset.univ C := by
    simpa [cellProb] using (le_div_iff₀ hn0).mpr hC
  have hτsq : τ^2 ≤ (cellProb Finset.univ C)^2 := sq_le_sq₀ hτ.le (hτ.le.trans ha) |>.mpr ha
  have hlow : τ^2 ≤ 2*pairCell Finset.univ C := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlow hlam
  have he : lam ≤ (2*lam/τ^2)*pairCell Finset.univ C := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
    nlinarith
  exact (slice_le_lam w p x hw hW lam hlam C).trans he

lemma small_slice_bound (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i y, 0 ≤ p i y) (hx : ∀ i, p i (x i) = 0)
    (B τ lam : ℝ) (hB : 0 ≤ B) (hτ : 0 ≤ τ)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1)))
    (C : Finset P) (hC : (C.card:ℝ) < τ*Fintype.card P) :
    slice w p x lam C ≤ B*τ*cellProb Finset.univ C := by
  by_cases hm : 2 ≤ C.card
  · have hn : 0 < (Fintype.card P:ℝ) := by exact_mod_cast (show 0 < Fintype.card P from lt_of_lt_of_le (by omega) (Finset.card_le_univ C))
    have ha : cellProb Finset.univ C ≤ τ := by
      simpa [cellProb] using (div_le_iff₀ hn).mpr hC.le
    have ha0 : 0 ≤ cellProb (Finset.univ : Finset P) C := cellProb_nonneg _ _
    calc
      _ ≤ B*pairCell Finset.univ C := (slice_le_edgeCell w p x hw hp lam C).trans (edgeCell_dom w p x hx B hdom C)
      _ ≤ B*(cellProb Finset.univ C)^2 := mul_le_mul_of_nonneg_left (uniform_pair_comparison C hm).2 hB
      _ ≤ B*τ*cellProb Finset.univ C := by nlinarith [mul_nonneg hB (mul_nonneg ha0 (sub_nonneg.mpr ha))]
  · rw [slice_singleton w p x hx lam C (by omega)]
    exact mul_nonneg (mul_nonneg hB hτ) (cellProb_nonneg _ _)

end WeakPinned.SmallFiber

namespace WeakPinned.Hierarchy.Depth
variable {P : Type u3} [Fintype P] [DecidableEq P]
variable (d : Depth P)
lemma sum_source_cell (f : Finset P → ℝ) (r : ℝ) (x : P) :
    (∑ C ∈ d.cells r, if x ∈ C then f C else 0) = f (d.cell r x) := by
  classical
  have he : ∀ C ∈ d.cells r, (if x ∈ C then f C else 0) =
      if C = d.cell r x then f (d.cell r x) else 0 := by
    intro C hC
    by_cases hx : x ∈ C
    · rw [d.cell_of_mem hC hx]; simp [d.share_refl]
    · have hn : C ≠ d.cell r x := by intro h; apply hx; rw [h]; exact d.self_mem_cell r x
      simp [hx,hn]
  rw [Finset.sum_congr rfl he]
  simp [d.cell_mem_cells r x]

lemma sumCells_split (f : Finset P → ℝ) (r : ℝ) :
    d.sumCells f r =
      (∑ C ∈ d.cells r, if ¬Fintype.card P < 2*C.card then f C else 0) +
      ∑ C ∈ d.giants r, f Cᶜ := by
  classical
  simp only [sumCells,transformed,Multiset.map_add,Multiset.sum_add,
    Multiset.map_map,Function.comp_def]
  change (∑ C ∈ (d.cells r).filter (fun C => ¬Fintype.card P < 2*C.card), f C) + _ = _
  rw [Finset.sum_filter]
  rfl

lemma sum_complement_prob (r : ℝ) :
    (∑ C ∈ d.giants r, Variance.cellProb Finset.univ Cᶜ) =
      (∑ y, d.outsideIndicator r y)/(Fintype.card P:ℝ) := by
  classical
  by_cases hg : (d.giants r).Nonempty
  · obtain ⟨G,hG⟩ := hg
    have hs : d.giants r = {G} := Finset.ext fun C => by
      simp only [Finset.mem_singleton]
      exact ⟨fun hC => d.giants_unique hC hG,fun h => h ▸ hG⟩
    have hne : (d.giants r).Nonempty := ⟨G,hG⟩
    have hi (y : P) : d.outsideIndicator r y = if y ∈ Gᶜ then 1 else 0 := by
      simp [outsideIndicator,hne,d.giant_eq hG]
    simp_rw [hi]
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,mul_one]
    simp [hs,Variance.cellProb]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hg,outsideIndicator]
end WeakPinned.Hierarchy.Depth

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy Variance
variable {P : Type u4} {I : Type u5} [Fintype P] [DecidableEq P] [Fintype I]

lemma nongiant_small_slice (d : Depth P) (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (T lam r : ℝ) :
    (∑ C ∈ d.cells r, if ¬Fintype.card P < 2*C.card ∧ (C.card:ℝ) < T then slice w p x lam C else 0) =
      ∑ i, w i * activeMass d (p i) (x i) T lam r := by
  classical
  have he (C : Finset P) :
      (if ¬Fintype.card P < 2*C.card ∧ (C.card:ℝ) < T then slice w p x lam C else 0) =
      ∑ i, w i * (if x i ∈ C then
        (if ¬Fintype.card P < 2*C.card ∧ (C.card:ℝ) < T ∧ mass (p i) C < lam then mass (p i) C else 0) else 0) := by
    by_cases h : ¬Fintype.card P < 2*C.card ∧ (C.card:ℝ) < T
    · simp only [h,slice]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx : x i ∈ C <;> simp [hx]
    · simp only [h,ite_false]
      symm
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hx hh
      · exact False.elim (h ⟨hh.1,hh.2.1⟩)
      · exact mul_zero _
      · exact mul_zero _
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.mul_sum,d.sum_source_cell]
  congr 1
  unfold activeMass Depth.sourceGiant
  split_ifs <;> rfl

lemma pointwise_split (d : Depth P) (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (hp : ∀ i y, 0 ≤ p i y)
    (hx : ∀ i, p i (x i) = 0) (hn : 2 ≤ Fintype.card P)
    (B τ lam r : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hτ : 0 < τ)
    (hτn : 2 ≤ τ*(Fintype.card P:ℝ))
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    d.sumCells (slice w p x lam) r ≤
      (2*lam/τ^2)*d.sumCells (pairCell Finset.univ) r +
      B*τ/(Fintype.card P:ℝ)*(∑ y, d.outsideIndicator r y) +
      ∑ i, w i*activeMass d (p i) (x i) (τ*Fintype.card P) lam r := by
  classical
  have hcoef : 0 ≤ 2*lam/τ^2 := by positivity
  have hnng : ∀ C : Finset P, 0 ≤ (2*lam/τ^2)*pairCell Finset.univ C :=
    fun C => mul_nonneg hcoef (pairCell_nonneg _ _)
  have hactual :
      (∑ C ∈ d.cells r, if ¬Fintype.card P < 2*C.card then slice w p x lam C else 0) ≤
      (2*lam/τ^2)*(∑ C ∈ d.cells r, if ¬Fintype.card P < 2*C.card then pairCell Finset.univ C else 0) +
      ∑ i, w i*activeMass d (p i) (x i) (τ*Fintype.card P) lam r := by
    rw [←nongiant_small_slice,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro C _
    by_cases hg : ¬Fintype.card P < 2*C.card
    · by_cases hc : (C.card:ℝ) < τ*Fintype.card P
      · simp only [hg,hc,not_false_eq_true,true_and,ite_true]
        linarith [hnng C]
      · simp only [hg,hc,not_false_eq_true,true_and,ite_true,ite_false,add_zero]
        exact large_slice_bound w p x hw hW hn lam τ hlam hτ hτn C (le_of_not_gt hc)
    · simp [hg]
  have hgiant : (∑ C ∈ d.giants r, slice w p x lam Cᶜ) ≤
      (2*lam/τ^2)*(∑ C ∈ d.giants r, pairCell Finset.univ Cᶜ) +
      B*τ*(∑ C ∈ d.giants r, cellProb Finset.univ Cᶜ) := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro C _
    by_cases hc : (Cᶜ.card:ℝ) < τ*Fintype.card P
    · exact (small_slice_bound w p x hw hp hx B τ lam hB hτ.le hdom Cᶜ hc).trans (le_add_of_nonneg_left (hnng Cᶜ))
    · exact (large_slice_bound w p x hw hW hn lam τ hlam hτ hτn Cᶜ (le_of_not_gt hc)).trans
        (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hB hτ.le) (cellProb_nonneg _ _)))
  rw [d.sum_complement_prob] at hgiant
  rw [d.sumCells_split,d.sumCells_split]
  have he : B*τ*((∑ y, d.outsideIndicator r y)/(Fintype.card P:ℝ)) =
      B*τ/(Fintype.card P:ℝ)*(∑ y, d.outsideIndicator r y) := by ring
  rw [he] at hgiant
  linarith

end WeakPinned.SmallFiber

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u6} [Fintype P] [DecidableEq P]
variable (d : Depth P)
lemma integrable_sumCells (hn : 2 ≤ Fintype.card P) (f : Finset P → ℝ)
    (hf : ∀ C, C.card ≤ 1 → f C = 0) : Integrable (d.sumCells f) := by
  change Integrable (fun r => d.sumCells f r)
  simp_rw [d.sumCells_count]
  apply integrable_finsetSum
  intro C _
  by_cases hC : 2 ≤ C.card
  · exact (d.integrable_count hn C hC).mul_const _
  · simp only [hf C (by omega),mul_zero]
    exact integrable_zero _ _ _
end WeakPinned.Hierarchy.Depth

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy Variance
variable {P : Type u7} {I : Type u8} [Fintype P] [DecidableEq P] [Fintype I]

lemma integral_split (d : Depth P) (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y = 1) (hx : ∀ i, p i (x i) = 0) (hn : 2 ≤ Fintype.card P)
    (B τ lam : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hτ : 0 < τ)
    (hτn : 2 ≤ τ*(Fintype.card P:ℝ))
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C, d.mass C * slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, d.mass C*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*(∑ y, d.potential y) +
      ∑ i, w i*(∫ r, activeMass d (p i) (x i) (τ*Fintype.card P) lam r) := by
  classical
  have hi₁ := (d.integrable_sumCells hn (pairCell Finset.univ) (singleton_pairCell _)).const_mul (2*lam/τ^2)
  have hi₂ := (integrable_finsetSum (s:=Finset.univ) (fun y _ => d.integrable_outsideIndicator hn y)).const_mul (B*τ/Fintype.card P)
  have hi₃ := integrable_finsetSum (s:=Finset.univ) (fun i _ =>
    (activeMass_integrable d hn (p i) (hp i) (hp1 i) (x i) (hx i) (τ*Fintype.card P) lam).const_mul (w i))
  have hb := integral_mono (d.integrable_sumCells hn _ (slice_singleton w p x hx lam))
    ((hi₁.add hi₂).add hi₃) (fun r => pointwise_split d w p x hw hW hp hx hn B τ lam r hB hlam hτ hτn hdom)
  have ha := integral_add (hi₁.add hi₂) hi₃
  have hb' := integral_add hi₁ hi₂
  simp only [Pi.add_apply] at hb ha hb'
  rw [ha,hb',integral_const_mul,integral_const_mul,
    d.integral_sumCells hn _ (singleton_pairCell _),
    d.integral_sumCells hn _ (slice_singleton w p x hx lam),
    integral_finsetSum _ (fun y _ => d.integrable_outsideIndicator hn y),
    integral_finsetSum _ (fun i _ =>
      (activeMass_integrable d hn (p i) (hp i) (hp1 i) (x i) (hx i) (τ*Fintype.card P) lam).const_mul (w i))] at hb
  simpa only [integral_const_mul,Depth.potential] using hb

lemma local_small_fiber (d d' : Depth P) (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y = 1) (hx : ∀ i, p i (x i) = 0) (hn : 2 ≤ Fintype.card P)
    (h : I → ℝ) (B τ lam H : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ)) (hH : 0 ≤ H)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C, d.mass C * slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, d.mass C*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, d.potential y)+(∑ y, d'.potential y)) +
      2*lam*(∑ i, w i*∑ y, p i y*∫ r, d'.pairOverlap r (x i) y) + 2*lam*H +
      ∑ i, w i*∑ y, p i y*max (|d.value (x i) y+d'.value (x i) y-h i|-H) 0 := by
  have hb := integral_split d w p x hw hW hp hp1 hx hn B τ lam hB hlam hτ hτn hdom
  have ha := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left
    (active_integral d d' hn (p i) (hp i) (hp1 i) (x i) (hx i) (h i) H (τ*Fintype.card P) lam hH hlam hlam2) (hw i))
  have hnbr := fiber_neighbor_bound d d' hn w p x B τ hB hτ hτ1 hdom
  simp only [mul_add,Finset.sum_add_distrib] at ha
  have hc : (∑ i, w i*(2*lam*H)) = 2*lam*H := by rw [←Finset.sum_mul,hW,one_mul]
  have hi : (∑ i, w i*(2*lam*(∑ y, p i y*∫ r, d'.pairOverlap r (x i) y))) =
      2*lam*(∑ i, w i*(∑ y, p i y*∫ r, d'.pairOverlap r (x i) y)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hc,hi] at ha
  linarith

end WeakPinned.SmallFiber

namespace WeakPinned.SmallFiber
open MeasureTheory Hierarchy Variance
variable {P : Type u9} {I : Type u10} [Fintype P] [DecidableEq P] [Fintype I]

lemma pair_integral_edgeCell (d : Depth P) (hn : 2 ≤ Fintype.card P)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (hx : ∀ i, p i (x i) = 0) :
    (∑ i, w i*∑ y, p i y * ∫ r, d.pairOverlap r (x i) y) =
      ∑ C, d.mass C * edgeCell w p x C := by
  classical
  have hpair (i : I) (y : P) :
      p i y * (∫ r, d.pairOverlap r (x i) y) =
      ∑ C, d.mass C * (if x i ∈ C ∧ y ∈ C then p i y else 0) := by
    by_cases hxy : x i = y
    · subst y; simp [hx]
    · have h := d.mass_overlap hn (x i) y hxy
      dsimp [Depth.overlapLength] at h
      rw [← h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C _
      split_ifs <;> ring
  simp_rw [hpair,Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [edgeCell_formula,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ∈ C
  · simp only [hi,true_and,ite_true,mass_as_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> ring
  · simp [hi]

lemma local_small_fiber_reduced (d d' : Depth P) (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y = 1) (hx : ∀ i, p i (x i) = 0) (hn : 2 ≤ Fintype.card P)
    (h : I → ℝ) (B τ lam H : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ)) (hH : 0 ≤ H)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C, d.mass C * slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, d.mass C*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, d.potential y)+(∑ y, d'.potential y)) +
      2*lam*B*(∑ C, d'.mass C*pairCell Finset.univ C) + 2*lam*H +
      ∑ i, w i*∑ y, p i y*max (|d.value (x i) y+d'.value (x i) y-h i|-H) 0 := by
  have hb := local_small_fiber d d' w p x hw hW hp hp1 hx hn h B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom
  rw [pair_integral_edgeCell d' hn w p x hx] at hb
  have hd : (∑ C, d'.mass C*edgeCell w p x C) ≤ B*∑ C, d'.mass C*pairCell Finset.univ C := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro C _
    calc
      _ ≤ d'.mass C*(B*pairCell Finset.univ C) := mul_le_mul_of_nonneg_left (edgeCell_dom w p x hx B hdom C) (d'.mass_nonneg C)
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*lam by positivity)
  nlinarith
end WeakPinned.SmallFiber

end
end
end
end
end
end

end OAI
