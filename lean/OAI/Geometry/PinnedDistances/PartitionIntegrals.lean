import OAI.Geometry.PinnedDistances.GridBounds

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Hierarchy.Depth
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma sum_by_cells (r : ℝ) (f : P → ℝ) :
    (∑ C ∈ d.cells r, ∑ x∈C, f x)=∑ x,f x := by
  have hh (x : P) : (∑ C ∈ d.cells r, if x∈C then f x else 0)=f x := by
    rw [Finset.sum_eq_single (d.cell r x)]
    · simp [d.share_refl]
    · intro C hC hne
      rw [ite_eq_right]
      exact fun hx => hne (d.cell_of_mem hC hx)
    · simp
  calc
    _ = ∑ C ∈ d.cells r, ∑ x, if x∈C then f x else 0 := by simp
    _ = ∑ x, ∑ C ∈ d.cells r, if x∈C then f x else 0 := Finset.sum_comm
    _ = _ := by simp_rw [hh]

lemma sum_cell_value (r : ℝ) (p : P → ℝ) (v : Finset P → ℝ) :
    (∑ x,p x*v (d.cell r x))=∑ C∈d.cells r, v C*(∑ x∈C,p x) := by
  rw [← d.sum_by_cells r (fun x => p x*v (d.cell r x))]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← d.cell_of_mem hC hx]
  ring

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Bounded
open Hierarchy Variance
variable {P : Type u2} [Fintype P] [DecidableEq P]

omit [DecidableEq P] in
lemma weighted_test_bound (p f g : P → ℝ) (hp : ∀ x,0 ≤ p x) (h1 : ∑ x,p x=1)
    (η : ℝ) (hfg : ∀ x,|f x-g x| ≤ η) :
    |(∑ x,p x*f x)-(∑ x,p x*g x)| ≤ η := by
  rw [← Finset.sum_sub_distrib]
  calc
    _  ≤  ∑ x, |p x*f x-p x*g x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x,p x*|f x-g x| := by simp_rw [← mul_sub,abs_mul,abs_of_nonneg (hp _)]
    _  ≤  ∑ x,p x*η := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hp x))
    _ = η := by rw [← Finset.sum_mul,h1,one_mul]

lemma partition_test_bound (d : Depth P) (r : ℝ) (p a f : P → ℝ)
    (hp : ∀ x,0 ≤ p x) (ha : ∀ x,0 ≤ a x) (hp1 : ∑ x,p x=1) (ha1 : ∑ x,a x=1)
    (A : Finset (Finset P)) (hA : A⊆d.cells r) (v : Finset P → ℝ) (η H : ℝ)
    (hf : ∀ x,|f x-v (d.cell r x)| ≤ η)
    (hv : ∀ C∈d.cells r, |v C| ≤ if C∈A then H else 0) :
    |(∑ x,p x*f x)-(∑ x,a x*f x)|  ≤
      2*η+H*(∑ C∈A, |(∑ x∈C,p x)-(∑ x∈C,a x)|) := by
  have hpa : |(∑ x,p x*v (d.cell r x))-(∑ x,a x*v (d.cell r x))| ≤
      H*(∑ C∈A,|(∑ x∈C,p x)-(∑ x∈C,a x)|) := by
    rw [d.sum_cell_value,d.sum_cell_value,← Finset.sum_sub_distrib]
    calc
      _  ≤  ∑ C∈d.cells r, |v C*(∑ x∈C,p x)-v C*(∑ x∈C,a x)| := Finset.abs_sum_le_sum_abs _ _
      _  ≤  ∑ C∈d.cells r, if C∈A then H*|(∑ x∈C,p x)-(∑ x∈C,a x)| else 0 := by
        apply Finset.sum_le_sum
        intro C hC
        rw [← mul_sub,abs_mul]
        simpa only [ite_mul,zero_mul] using mul_le_mul_of_nonneg_right (hv C hC) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_ite_mem,Finset.inter_eq_right.mpr hA,Finset.mul_sum]
  have h₁ := weighted_test_bound p f (fun x => v (d.cell r x)) hp hp1 η hf
  have h₂ := weighted_test_bound a f (fun x => v (d.cell r x)) ha ha1 η hf
  have hh := abs_add_three ((∑ x,p x*f x)-(∑ x,p x*v (d.cell r x)))
    ((∑ x,p x*v (d.cell r x))-(∑ x,a x*v (d.cell r x)))
    ((∑ x,a x*v (d.cell r x))-(∑ x,a x*f x))
  rw [abs_sub_comm (∑ x,a x*v (d.cell r x))] at hh
  convert le_trans hh (by linarith : _ ≤ 2*η+H*(∑ C∈A, |(∑ x∈C,p x)-(∑ x∈C,a x)|)) using 1
  congr 1
  ring

lemma cellProb_compl (B C : Finset P) (hB : B.Nonempty) :
    cellProb B Cᶜ=1-cellProb B C := by
  rw [← sum_prob_cell,← sum_prob_cell,← sum_prob B hB]
  have hh := Finset.sum_compl_add_sum C (prob B)
  linarith

variable {I : Type u3} [Fintype I]

def meanCellDiscrep (w : I → ℝ) (B : I → Finset P) (C : Finset P) : ℝ :=
  ∑ i,w i*|cellProb (B i) C-cellProb Finset.univ C|

lemma meanCellDiscrep_nonneg (w : I → ℝ) (B : I → Finset P) (hw : ∀ i,0 ≤ w i) (C : Finset P) :
    0 ≤ meanCellDiscrep w B C := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (abs_nonneg _))

lemma meanCellDiscrep_compl (w : I → ℝ) (B : I → Finset P) (hB : ∀ i,(B i).Nonempty)
    (hn : 0<Fintype.card P) (C : Finset P) :
    meanCellDiscrep w B Cᶜ=meanCellDiscrep w B C := by
  unfold meanCellDiscrep
  apply Finset.sum_congr rfl
  intro i _
  rw [cellProb_compl _ _ (hB i),cellProb_compl _ _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn)),
    sub_sub_sub_cancel_left,abs_sub_comm]

lemma meanCellDiscrep_small (w : I → ℝ) (B : I → Finset P) (M : ℝ)
    (hw : ∀ i,0 ≤ w i) (hW : ∑ i,w i ≤ 1)
    (hdom : ∀ x,(∑ i,w i*prob (B i) x) ≤ M*prob Finset.univ x) (C : Finset P) :
    meanCellDiscrep w B C ≤ (M+1)*cellProb Finset.univ C := by
  have hmean := mean_cell_bound w B C M hdom
  calc
    _  ≤  ∑ i,w i*(cellProb (B i) C+cellProb Finset.univ C) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (abs_sub_le_iff.mpr ⟨by linarith [cellProb_nonneg (Finset.univ : Finset P) C],by linarith [cellProb_nonneg (B i) C]⟩) (hw i)
    _ = (∑ i,w i*cellProb (B i) C)+(∑ i,w i)*cellProb Finset.univ C := by simp [mul_add,Finset.sum_add_distrib,Finset.sum_mul]
    _  ≤  (M+1)*cellProb Finset.univ C := by nlinarith [mul_le_mul_of_nonneg_right hW (cellProb_nonneg (Finset.univ : Finset P) C)]

lemma meanCellDiscrep_young (w : I → ℝ) (B : I → Finset P) (M T δ : ℝ)
    (hw : ∀ i,0 ≤ w i) (hW : ∑ i,w i ≤ 1) (hM : 0 ≤ M) (hT : 0 ≤ T) (hδ : 0<δ)
    (hdom : ∀ x,(∑ i,w i*prob (B i) x) ≤ M*prob Finset.univ x)
    (C : Finset P) :
    meanCellDiscrep w B C  ≤  varianceCell w B T C/δ+δ+(M+1)*T/Fintype.card P := by
  by_cases hC : T<(C.card:ℝ)
  · have hy (t : ℝ) : |t| ≤ t^2/δ+δ := by
      have hh : |t| *δ ≤ t^2+δ*δ := by nlinarith [sq_nonneg (|t| -δ),sq_abs t]
      calc
        |t| = (|t| *δ)/δ := by field_simp
        _ ≤ (t^2+δ*δ)/δ := div_le_div_of_nonneg_right hh hδ.le
        _ = _ := by field_simp
    have hh : meanCellDiscrep w B C ≤ varianceCell w B T C/δ+δ := by
      rw [varianceCell,ite_eq_left hC]
      calc
        _  ≤  ∑ i,w i*((cellProb (B i) C-cellProb Finset.univ C)^2/δ+δ) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hy _) (hw i))
        _ = (∑ i,w i*(cellProb (B i) C-cellProb Finset.univ C)^2)/δ+(∑ i,w i)*δ := by
          simp only [mul_add,← mul_div_assoc,Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_mul]
        _  ≤  _ := by nlinarith [mul_le_mul_of_nonneg_right hW hδ.le]
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  · have hh := meanCellDiscrep_small w B M hw hW hdom C
    have hc : cellProb (Finset.univ : Finset P) C ≤ T/Fintype.card P := by
      simp only [cellProb,Finset.univ_inter,Finset.card_univ]
      exact div_le_div_of_nonneg_right (le_of_not_gt hC) (by positivity)
    have hv := varianceCell_nonneg w B T hw C
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ M+1 by linarith)
    rw [← mul_div_assoc] at hm
    linarith [div_nonneg hv hδ.le]

end WeakPinned.Bounded

end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Hierarchy.Depth
variable {P : Type u4} [Fintype P] [DecidableEq P]
variable (d : Depth P)

def transformCell (C : Finset P) : Finset P := if Fintype.card P<2*C.card then Cᶜ else C

lemma sum_transformCell (r : ℝ) (f : Finset P → ℝ) :
    (∑ C∈d.cells r,f (transformCell C))=d.sumCells f r := by
  classical
  simp only [sumCells,transformed,Multiset.map_add,Multiset.sum_add,Multiset.map_map,
    Function.comp_def,transformCell]
  simp_rw [apply_ite f]
  rw [Finset.sum_ite]
  change (∑ C∈(d.cells r).filter (fun C => Fintype.card P<2*C.card),f Cᶜ)+
    (∑ C∈(d.cells r).filter (fun C => ¬Fintype.card P<2*C.card),f C) =
    (∑ C∈(d.cells r).filter (fun C => ¬Fintype.card P<2*C.card),f C)+
    (∑ C∈(d.cells r).filter (fun C => Fintype.card P<2*C.card),f Cᶜ)
  ring

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Bounded
open Hierarchy Variance
variable {P : Type u5} {I : Type u6} [Fintype P] [DecidableEq P] [Fintype I]

lemma meanCellDiscrep_transform (w : I → ℝ) (B : I → Finset P) (hB : ∀ i,(B i).Nonempty)
    (hn : 0<Fintype.card P) (C : Finset P) :
    meanCellDiscrep w B (Depth.transformCell C)=meanCellDiscrep w B C := by
  unfold Depth.transformCell
  split_ifs
  · exact meanCellDiscrep_compl w B hB hn C
  · rfl

lemma active_meanDiscrep_bound (d : Depth P) (r : ℝ) (A : Finset (Finset P))
    (N M T δ : ℝ) (w : I → ℝ) (B : I → Finset P)
    (hn : 0<Fintype.card P) (hA : A⊆d.cells r) (hN : (A.card:ℝ) ≤ N)
    (hw : ∀ i,0 ≤ w i) (hW : ∑ i,w i ≤ 1) (hB : ∀ i,(B i).Nonempty)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hδ : 0<δ)
    (hdom : ∀ x,(∑ i,w i*prob (B i) x) ≤ M*prob Finset.univ x) :
    (∑ C∈A,meanCellDiscrep w B C) ≤
      d.sumCells (varianceCell w B T) r/δ+N*(δ+(M+1)*T/Fintype.card P) := by
  have hv (C) : 0 ≤ varianceCell w B T C := varianceCell_nonneg w B T hw C
  calc
    _ = ∑ C∈A,meanCellDiscrep w B (Depth.transformCell C) := by
      simp_rw [meanCellDiscrep_transform w B hB hn]
    _ ≤ ∑ C∈A,(varianceCell w B T (Depth.transformCell C)/δ+(δ+(M+1)*T/Fintype.card P)) := by
      apply Finset.sum_le_sum
      intro C _
      simpa only [add_assoc] using meanCellDiscrep_young w B M T δ hw hW hM hT hδ hdom (Depth.transformCell C)
    _ = (∑ C∈A,varianceCell w B T (Depth.transformCell C))/δ+
        (A.card:ℝ)*(δ+(M+1)*T/Fintype.card P) := by
      simp [Finset.sum_add_distrib,Finset.sum_div]
      ring
    _ ≤ (∑ C∈d.cells r,varianceCell w B T (Depth.transformCell C))/δ+
        N*(δ+(M+1)*T/Fintype.card P) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hA (fun C _ _ => hv _)) hδ.le
      · apply mul_le_mul_of_nonneg_right hN
        positivity
    _ = _ := by rw [d.sum_transformCell]

def testDiscrep (w : I → ℝ) (B : I → Finset P) (f : P → ℝ) : ℝ :=
  ∑ i,w i*|(∑ x,prob (B i) x*f x)-(∑ x,prob Finset.univ x*f x)|

lemma testDiscrep_nonneg (w : I → ℝ) (B : I → Finset P) (f : P → ℝ) (hw : ∀ i,0 ≤ w i) :
    0 ≤ testDiscrep w B f := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (abs_nonneg _))

lemma family_partition_test_bound (d : Depth P) (r : ℝ) (A : Finset (Finset P))
    (N M T δ η H : ℝ) (w : I → ℝ) (B : I → Finset P)
    (hn : 0<Fintype.card P) (hA : A⊆d.cells r) (hN : (A.card:ℝ) ≤ N)
    (hw : ∀ i,0 ≤ w i) (hW : ∑ i,w i ≤ 1) (hB : ∀ i,(B i).Nonempty)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hδ : 0<δ) (hη : 0 ≤ η) (hH : 0 ≤ H)
    (hdom : ∀ x,(∑ i,w i*prob (B i) x) ≤ M*prob Finset.univ x)
    (f : P → ℝ) (v : Finset P → ℝ)
    (hf : ∀ x,|f x-v (d.cell r x)| ≤ η)
    (hv : ∀ C∈d.cells r,|v C| ≤ if C∈A then H else 0) :
    testDiscrep w B f ≤ 2*η+H*(d.sumCells (varianceCell w B T) r/δ+
      N*(δ+(M+1)*T/Fintype.card P)) := by
  have hp (S : Finset P) (x : P) : 0 ≤ prob S x := by unfold prob; split_ifs <;> positivity
  have hh (i : I) := partition_test_bound d r (prob (B i)) (prob Finset.univ) f
    (hp _) (hp _) (sum_prob _ (hB i))
    (sum_prob _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn))) A hA v η H hf hv
  simp only [sum_prob_cell] at hh
  have hmean := active_meanDiscrep_bound d r A N M T δ w B hn hA hN hw hW hB hM hT hδ hdom
  calc
    _ ≤ ∑ i,w i*(2*η+H*(∑ C∈A,|cellProb (B i) C-cellProb Finset.univ C|)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hh i) (hw i))
    _ = (∑ i,w i)*(2*η)+H*(∑ C∈A,meanCellDiscrep w B C) := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul]
      congr 1
      simp only [meanCellDiscrep,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := add_le_add (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hW (show 0≤2*η by positivity))
      (mul_le_mul_of_nonneg_left hmean hH)

end WeakPinned.Bounded

end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Bounded
open Hierarchy
variable {P : Type u7} [Fintype P] [DecidableEq P]

lemma grid_test_data (d : Depth P) (u : P → ℂ) (ω : Grid.FullSample) (r m : ℝ) (b : ℂ)
    (hn : 0<Fintype.card P)
    (hshare : ∀ x y,d.share r x y ↔ Grid.label ω r (u x)=Grid.label ω r (u y))
    (R L η H ε : ℝ) (M : ℕ) (hR : 0≤R) (hL : 0<L)
    (hside : L ≤ Grid.side ω r m) (hupper : Grid.side ω r m ≤ ε)
    (hM : 2*R/L+1≤M)
    (f : ℂ → ℝ) (hbound : ∀ z,|f z|≤H)
    (hcont : ∀ z w,‖z-w‖<2*ε → |f z-f w|≤η)
    (hout : ∀ z,R<‖z‖ → |f z|≤η) :
    ∃ A : Finset (Finset P), ∃ v : Finset P → ℝ,
      A⊆d.cells r ∧ A.card≤(2*M+1)^2 ∧
      (∀ x,|f ((Real.exp m:ℂ)*u x+b)-v (d.cell r x)|≤η) ∧
      (∀ C∈d.cells r,|v C|≤ if C∈A then H else 0) := by
  classical
  let : Nonempty P := Fintype.card_pos_iff.mp hn
  let D : Finset P := Finset.univ.filter (fun x => ‖(Real.exp m:ℂ)*u x+b‖≤R)
  let A := D.image (d.cell r)
  let rep (C : Finset P) : P := if h : C∈A then (Finset.mem_image.mp h).choose else Classical.arbitrary P
  have hr (C : Finset P) (hC : C∈A) : rep C∈D ∧ d.cell r (rep C)=C := by
    simpa only [rep,dite_eq_left hC] using (Finset.mem_image.mp hC).choose_spec
  have hAc : A⊆d.cells r := Finset.image_subset_image (Finset.filter_subset _ _)
  have hcount : A.card≤(2*M+1)^2 := by
    apply le_trans (Finset.card_le_card_of_injOn (fun C => Grid.label ω r (u (rep C)))
      (t:=D.image (fun x => Grid.label ω r (u x))) ?_ ?_)
    · apply Grid.card_labels_bound D u ω r m b R L M hR hL hside hM
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro C hC
      exact Finset.mem_image.mpr ⟨rep C,(hr C hC).1,rfl⟩
    · intro C hC E hE he
      rw [← (hr C hC).2,← (hr E hE).2]
      exact d.cell_eq_of_share ((hshare _ _).mpr he)
  let v (C : Finset P) := if C∈A then f ((Real.exp m:ℂ)*u (rep C)+b) else 0
  refine ⟨A,v,hAc,hcount,?_,?_⟩
  · intro x
    by_cases hx : d.cell r x∈A
    · simp only [v,ite_eq_left hx]
      apply hcont
      have he : d.share r x (rep (d.cell r x)) := by
        rw [← d.mem_cell]
        have hmem := d.self_mem_cell r (rep (d.cell r x))
        rwa [(hr _ hx).2] at hmem
      have hd := Grid.label_diameter (m:=m) ((hshare _ _).mp he)
      have heq : ((Real.exp m:ℂ)*u x+b)-((Real.exp m:ℂ)*u (rep (d.cell r x))+b)=
          (Real.exp m:ℂ)*u x-(Real.exp m:ℂ)*u (rep (d.cell r x)) := by ring
      rw [heq]
      exact hd.trans_le (by linarith)
    · simp only [v,ite_eq_right hx,sub_zero]
      apply hout
      by_contra hh
      have hxD : x∈D := Finset.mem_filter.mpr ⟨Finset.mem_univ x,le_of_not_gt hh⟩
      exact hx (Finset.mem_image.mpr ⟨x,hxD,rfl⟩)
  · intro C _
    by_cases hC : C∈A
    · simpa only [v,ite_eq_left hC] using hbound ((Real.exp m:ℂ)*u (rep C)+b)
    · simp only [v,ite_eq_right hC,abs_zero,le_refl]

end WeakPinned.Bounded

end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Bounded

lemma le_unit_integral (g : ℝ → ℝ) (hg : Integrable g) (hg0 : ∀ r,0≤g r)
    (t D a b : ℝ) (hb : 0≤b) (h : ∀ r∈Set.Icc t (t+1), D≤a+b*g r) :
    D≤a+b*(∫ r,g r) := by
  have hi (c : ℝ) : IntegrableOn (fun _ : ℝ => c) (Set.Icc t (t+1)) :=
    integrableOn_const isCompact_Icc.measure_lt_top.ne
  have hv : (volume (Set.Icc t (t+1))).toReal=1 := by simp [Real.volume_Icc]
  have hc (c : ℝ) : (∫ r in Set.Icc t (t+1),c)=c := by
    rw [integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,hv,one_smul]
  have hh := setIntegral_mono_on (hi D) ((hi a).add (hg.integrableOn.const_mul b)) measurableSet_Icc h
  simp only [Pi.add_apply] at hh
  rw [integral_add (hi a) (hg.integrableOn.const_mul b),hc D,hc a,integral_const_mul] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hg (ae_of_all _ hg0)) hb))

end WeakPinned.Bounded

namespace WeakPinned.Grid
lemma side_unit_bounds (ω : FullSample) (m ε r : ℝ) (hε : 0<ε)
    (hr : r∈Set.Icc (m-Real.log ε) (m-Real.log ε+1)) :
    ε/(2*Real.exp 1) ≤ side ω r m ∧ side ω r m ≤ ε := by
  have he : Real.exp (Real.log ε-1)/2=ε/(2*Real.exp 1) := by
    rw [Real.exp_sub,Real.exp_log hε]
    ring
  constructor
  · rw [← he]
    exact (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hr.2])) (by norm_num)).trans
      (side_bounds ω r m).1.le
  · exact (side_bounds ω r m).2.trans (by rw [← Real.exp_log hε]; exact Real.exp_le_exp.mpr (by linarith [hr.1]))
end WeakPinned.Grid

end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField
variable {P : Type u8} {I : Type u9} [Fintype P] [DecidableEq P] [Fintype I]

lemma grid_test_integrated (d : Depth P) (u : P → ℂ) (ω : Grid.FullSample) (m : ℝ) (b : ℂ)
    (hn : 2≤ Fintype.card P)
    (hshare : ∀ r x y,d.share r x y ↔ Grid.label ω r (u x)=Grid.label ω r (u y))
    (R ε η H M T δ : ℝ) (N : ℕ) (hR : 0≤ R) (hε : 0<ε)
    (hN : 2*R/(ε/(2*Real.exp 1))+1≤ N)
    (hη : 0≤ η) (hH : 0≤ H) (hM : 0≤ M) (hT : 1≤ T) (hδ : 0<δ)
    (w : I → ℝ) (B : I → Finset P)
    (hw : ∀ i,0≤ w i) (hW : ∑ i,w i≤ 1) (hB : ∀ i,2≤ (B i).card)
    (hdom : ∀ x, (∑ i,w i*prob (B i) x)≤ M*prob Finset.univ x)
    (f : ℂ → ℝ) (hbound : ∀ z,|f z|≤ H)
    (hcont : ∀ z z',‖z-z'‖<2*ε → |f z-f z'|≤ η)
    (hout : ∀ z,R<‖z‖ → |f z|≤ η) :
    testDiscrep w B (fun x => f ((Real.exp m:ℂ)*u x+b)) ≤
      2*η+H*(weightedIntegral d.mass (varianceCell w B T)/δ+
        ((2*N+1)^2:ℕ)*(δ+(M+1)*T/Fintype.card P)) := by
  have hq (C) : 0≤ varianceCell w B T C := varianceCell_nonneg w B T hw C
  have hi := d.integrable_sumCells hn _ (varianceCell_singleton w B T hT hB)
  have hsum (r) : 0≤ d.sumCells (varianceCell w B T) r := by
    rw [d.sumCells_count]
    exact Finset.sum_nonneg (fun C _ => mul_nonneg (d.count_nonneg r C) (hq C))
  let a := 2*η+H*((((2*N+1)^2:ℕ):ℝ)*(δ+(M+1)*T/Fintype.card P))
  have hh := le_unit_integral _ hi hsum (m-Real.log ε)
    (testDiscrep w B (fun x => f ((Real.exp m:ℂ)*u x+b))) a (H/δ) (by positivity) ?_
  · rw [d.integral_sumCells hn _ (varianceCell_singleton w B T hT hB)] at hh
    convert hh using 1; simp only [a,weightedIntegral]; ring
  · intro r hr
    have hs := Grid.side_unit_bounds ω m ε r hε hr
    obtain ⟨A,v,hA,hAc,hf,hv⟩ := grid_test_data d u ω r m b (by omega) (hshare r)
      R (ε/(2*Real.exp 1)) η H ε N hR (by positivity) hs.1 hs.2 hN f hbound hcont hout
    have h := family_partition_test_bound d r A (((2*N+1)^2:ℕ):ℝ) M T δ η H w B
      (by omega) hA (by exact_mod_cast hAc) hw hW
      (fun i => Finset.card_pos.mp (by have := hB i; omega)) hM (by linarith) hδ hη hH hdom _ v hf hv
    convert h using 1; simp only [a]; ring

variable {K : Type u10} [Field K] [NumberField K]

omit [NumberField K] in
lemma arch_test_bound (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
    (v : InfinitePlace K) (m : ℝ) (b : ℂ) (hn : 2≤ Fintype.card P)
    (R ε η H M T δ : ℝ) (N : ℕ) (hR : 0≤ R) (hε : 0<ε)
    (hN : 2*R/(ε/(2*Real.exp 1))+1≤ N)
    (hη : 0≤ η) (hH : 0≤ H) (hM : 0≤ M) (hT : 1≤ T) (hδ : 0<δ)
    (w : I → ℝ) (B : I → Finset P)
    (hw : ∀ i,0≤ w i) (hW : ∑ i,w i≤ 1) (hB : ∀ i,2≤ (B i).card)
    (hdom : ∀ x, (∑ i,w i*prob (B i) x)≤ M*prob Finset.univ x)
    (f : ℂ → ℝ) (hbound : ∀ z,|f z|≤ H)
    (hcont : ∀ z z',‖z-z'‖<2*ε → |f z-f z'|≤ η)
    (hout : ∀ z,R<‖z‖ → |f z|≤ η) :
    testDiscrep w B (fun x => f ((Real.exp m:ℂ)*v.embedding (Z₁ x)+b)) ≤
      2*η+H*(archMean Z₁ Z₂ (massEval (varianceCell w B T)) v/δ+
        ((2*N+1)^2:ℕ)*(δ+(M+1)*T/Fintype.card P)) := by
  let D := testDiscrep w B (fun x => f ((Real.exp m:ℂ)*v.embedding (Z₁ x)+b))
  let a := 2*η+H*((((2*N+1)^2:ℕ):ℝ)*(δ+(M+1)*T/Fintype.card P))
  let q := varianceCell w B T
  have hq (C) : 0≤ q C := varianceCell_nonneg w B T hw C
  have hi := integrable_massEval Z₁ Z₂ h₁ h₂ hn q v
  have hh : ∀ᵐ ω ∂ Grid.fullLaw,D≤ a+(H/δ)*massEval q (arch Z₁ v ω) (arch Z₂ v ω) := by
    filter_upwards [arch_label_ae Z₁ h₁ v] with ω hω
    have hh := grid_test_integrated (arch Z₁ v ω) (fun x => v.embedding (Z₁ x)) ω m b hn hω
      R ε η H M T δ N hR hε hN hη hH hM hT hδ w B hw hW hB hdom f hbound hcont hout
    have hmass : weightedIntegral (arch Z₁ v ω).mass q≤ massEval q (arch Z₁ v ω) (arch Z₂ v ω) := by
      apply le_add_of_nonneg_right
      exact Finset.sum_nonneg (fun C _ => mul_nonneg ((arch Z₂ v ω).mass_nonneg C) (hq C))
    have he : 2*η+H*(weightedIntegral (arch Z₁ v ω).mass q/δ+
        ((2*N+1)^2:ℕ)*(δ+(M+1)*T/Fintype.card P))=a+(H/δ)*weightedIntegral (arch Z₁ v ω).mass q := by
      simp only [a]; ring
    rw [show varianceCell w B T=q from rfl,he] at hh
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass (by positivity)))
  have hh' := integral_mono_ae (integrable_const D) ((integrable_const a).add (hi.const_mul (H/δ))) hh
  simp only [Pi.add_apply] at hh'
  rw [integral_add (integrable_const a) (hi.const_mul (H/δ)),integral_const_mul] at hh'
  simp only [integral_const,probReal_univ,one_smul] at hh'
  calc
    _ ≤ a+(H/δ)*archMean Z₁ Z₂ (massEval q) v := hh'
    _ = _ := by dsimp only [a,q]; ring

end WeakPinned.Bounded

end
end

end OAI
