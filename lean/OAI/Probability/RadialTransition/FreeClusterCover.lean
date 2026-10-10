import OAI.Probability.RadialTransition.FreeGeometry

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma starWeight_ge_one {A : Set Position} {r : ℝ} {s : Multiset Position} {x : Position}
    (hx : x ∈ s) (hA : x ∈ A) (hr : ∀ y ∈ s, y ∈ nearCube r x) :
    1 ≤ starWeight A r s := by
  have hp : (s.map (nearMask r x)).prod = 1 := by
    apply Multiset.prod_eq_one
    intro a ha
    obtain ⟨y,hy,rfl⟩ := Multiset.mem_map.mp ha
    exact indicator_of_mem (hr y hy) _
  have hs := Multiset.single_le_sum (fun _ _ => (bot_le : (0:ℝ≥0∞) ≤ _))
    _ (Multiset.mem_map.mpr ⟨x,hx,rfl⟩ : regionMask A x*(s.map (nearMask r x)).prod ∈
      s.map (fun y => regionMask A y*(s.map (nearMask r y)).prod))
  simpa only [hp, regionMask, indicator_of_mem hA, mul_one, starWeight] using hs

lemma cellClusterWeight_empty (t α r : ℝ) (k : Cell) : 1 ≤ cellClusterWeight t α r k 0 := by
  simp [cellClusterWeight, emptyWeight, starWeight]

lemma cellClusterWeight_ge {t α r : ℝ} {k : Cell} {s : Multiset Position}
    (hc : s.card ≤ 4) {x : Position} (hx : x ∈ s) (hk : cellOf x=k)
    (hr : ∀ y ∈ s, y ∈ nearCube r x) :
    ENNReal.ofReal (Real.exp (-t*α)) ≤ cellClusterWeight t α r k s := by
  have hh := mul_le_mul' (le_rfl : ENNReal.ofReal (Real.exp (-t*α)) ≤ _) (starWeight_ge_one hx (show x ∈ gridRegion k from hk) hr)
  rw [mul_one] at hh
  exact hh.trans (by simp only [cellClusterWeight, ite_eq_left hc]; exact le_add_self)

lemma coreFree_cell_cover {ι : Type} [Fintype ι] {t α L : ℝ} {x : ι → Position}
    (hx : CoreFree t x) (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (hbox : ∀ i, x i ∈ cube L) (hta : 0 ≤ t*α) :
    ENNReal.ofReal (Real.exp (-t*α*(packingNumber L:ℝ))) ≤
      indexedClusterProduct (fun k : cubeCells L =>
        cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k.val) (configurationMultiset x) := by
  classical
  let Q := Quotient (coreFreeSetoid hx ht)
  let S (q : Q) := Finset.univ.filter (fun i => Quotient.mk (coreFreeSetoid hx ht) i = q)
  let s (q : Q) := (S q).val.map x
  let f (q : Q) : cubeCells L := ⟨cellOf (x q.out), cellOf_mem_cubeCells (hbox _)⟩
  let W (k : cubeCells L) := cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k.val
  have hroot := coreFree_roots hx ht hbox
  have hf : Function.Injective f := by
    intro q q' he
    exact hroot.2 (congrArg Subtype.val he)
  have hsum : ∑ q, s q = configurationMultiset x := by
    convert configurationMultiset_fibers x (Quotient.mk (coreFreeSetoid hx ht)) using 1
    apply Finset.sum_congr rfl
    intro q _
    dsimp [s, S]
    congr 1
    ext i
    simp only [Multiset.count_filter]
    split_ifs <;> rfl
  have hW (q : Q) : ENNReal.ofReal (Real.exp (-t*α)) ≤ W (f q) (s q) := by
    apply cellClusterWeight_ge
    · simpa only [s, Multiset.card_map, S, Finset.card_def] using coreFree_fiber_card hx ht q
    · apply Multiset.mem_map.mpr
      refine ⟨q.out, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Quotient.out_eq q⟩
    · rfl
    · intro y hy
      obtain ⟨j,hj,rfl⟩ := Multiset.mem_map.mp hy
      have hjq : Quotient.mk (coreFreeSetoid hx ht) j = q := (Finset.mem_filter.mp hj).2
      have hd : dist (x j) (x q.out) < 1 := Quotient.exact (hjq.trans (Quotient.out_eq q).symm)
      intro d
      simpa only [Real.dist_eq] using (PiLp.dist_apply_le (x j) (x q.out) d).trans (hx.dist_bound j q.out hd)
  have hprod : ENNReal.ofReal (Real.exp (-t*α*(Fintype.card Q:ℝ))) ≤ ∏ q, W (f q) (s q) := by
    have hh := Finset.prod_le_prod (fun q (_ : q ∈ (Finset.univ : Finset Q)) => hW q)
    simp only [Finset.prod_const, Finset.card_univ] at hh
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul] at hh
    rw [mul_comm (Fintype.card Q : ℝ)] at hh
    exact hh
  have hcount : ENNReal.ofReal (Real.exp (-t*α*(packingNumber L:ℝ))) ≤
      ENNReal.ofReal (Real.exp (-t*α*(Fintype.card Q:ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hc : (Fintype.card Q:ℝ) ≤ packingNumber L := by exact_mod_cast hroot.1
    nlinarith
  have hcover := indexedClusterProduct_embedding W (fun k => cellClusterWeight_empty _ _ _ _) f hf s
  rw [hsum] at hcover
  exact hcount.trans (hprod.trans hcover)

end RadialTransition
end

end OAI
