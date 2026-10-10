import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionMixture

namespace OAI

namespace ProjectionComparison

open Set

variable {V E : Type*} [Fintype V]

lemma mem_faceComponent (S : System V E) (F : Finset E) (x y : V) :
    y∈faceComponent S F x ↔ (faceGraph S F).Reachable x y := by
  classical exact Set.mem_toFinset

lemma faceComponent_eq (S : System V E) (F : Finset E) (x y : V)
    (hxy : (faceGraph S F).Reachable x y) : faceComponent S F x=faceComponent S F y := by
  ext z
  simp only [mem_faceComponent]
  exact ⟨fun hx => hxy.symm.trans hx,fun hy => hxy.trans hy⟩

omit [Fintype V] in
lemma faceFree_iff (S : System V E) (F : Finset E) (x y : V)
    (hxy : (faceGraph S F).Reachable x y) :
    (∀p∈S.pins,¬(faceGraph S F).Reachable x p) ↔ (∀p∈S.pins,¬(faceGraph S F).Reachable y p) := by
  constructor <;> intro h p hp hr
  · exact h p hp (hxy.trans hr)
  · exact h p hp (hxy.symm.trans hr)

noncomputable def faceKernel (S : System V E) (F : Finset E) (x y : V) : ℝ := by
  classical exact if (∀p∈S.pins,¬(faceGraph S F).Reachable x p) ∧ (faceGraph S F).Reachable x y
    then ((faceComponent S F x).card:ℝ)⁻¹ else 0

lemma faceKernel_nonneg (S : System V E) (F : Finset E) (x y : V) : 0≤faceKernel S F x y := by
  classical
  unfold faceKernel
  split_ifs <;> positivity

lemma faceKernel_symm (S : System V E) (F : Finset E) (x y : V) : faceKernel S F x y=faceKernel S F y x := by
  classical
  unfold faceKernel
  by_cases hr : (faceGraph S F).Reachable x y
  · simp only [faceComponent_eq S F x y hr,faceFree_iff S F x y hr,hr,hr.symm,and_true]
  · have hn : ¬(faceGraph S F).Reachable y x := fun hy => hr hy.symm
    simp only [hr,hn,and_false,ite_false]

lemma faceAverage_eq_sum (S : System V E) (F : Finset E) (d : V → ℝ) (x : V) :
    faceAverage S F d x=∑y,faceKernel S F x y*d y := by
  classical
  unfold faceAverage faceKernel
  by_cases hf : ∀p∈S.pins,¬(faceGraph S F).Reachable x p
  · simp only [ite_and,ite_eq_left hf,div_eq_mul_inv]
    rw [Finset.sum_mul]
    calc
      (∑ y∈faceComponent S F x,d y*((faceComponent S F x).card:ℝ)⁻¹)=
          ∑ y∈faceComponent S F x,(if (faceGraph S F).Reachable x y then ((faceComponent S F x).card:ℝ)⁻¹ else 0)*d y := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [ite_eq_left ((mem_faceComponent S F x y).mp hy),mul_comm]
      _ = _ := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro y hy hn
        have hn' : ¬(faceGraph S F).Reachable x y := by simpa only [mem_faceComponent] using hn
        rw [ite_eq_right hn',zero_mul]
  · simp only [ite_and,ite_eq_right hf,zero_mul,Finset.sum_const_zero]

lemma faceKernel_row (S : System V E) (F : Finset E) (x : V) : (∑y,faceKernel S F x y)≤1 := by
  classical
  have h := faceAverage_eq_sum S F (fun _ => 1) x
  simp only [mul_one] at h
  rw [← h]
  unfold faceAverage
  split_ifs with hf
  · have hx : x∈faceComponent S F x := (mem_faceComponent S F x x).mpr (.refl x)
    have hp : (0:ℝ)<(faceComponent S F x).card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x,hx⟩)
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one,div_self hp.ne']
    rfl
  · norm_num

lemma faceKernel_column (S : System V E) (F : Finset E) (y : V) : (∑x,faceKernel S F x y)≤1 := by
  simpa only [faceKernel_symm S F] using faceKernel_row S F y

lemma faceAverage_constant (S : System V E) (F : Finset E) (d : V → ℝ) (x y : V)
    (hxy : (faceGraph S F).Reachable x y) : faceAverage S F d x=faceAverage S F d y := by
  classical
  unfold faceAverage
  simp only [faceFree_iff S F x y hxy,faceComponent_eq S F x y hxy]

lemma faceAverage_idempotent (S : System V E) (F : Finset E) (d : V → ℝ) (x : V) :
    faceAverage S F (faceAverage S F d) x=faceAverage S F d x := by
  classical
  unfold faceAverage at ⊢
  split_ifs with hf
  · have hsum : (∑ y∈faceComponent S F x,faceAverage S F d y)=(faceComponent S F x).card*faceAverage S F d x := by
      trans ∑ _y∈faceComponent S F x,faceAverage S F d x
      · apply Finset.sum_congr rfl
        intro y hy
        exact (faceAverage_constant S F d x y ((mem_faceComponent S F x y).mp hy)).symm
      · simp only [Finset.sum_const,nsmul_eq_mul]
    have hx : x∈faceComponent S F x := (mem_faceComponent S F x x).mpr (.refl x)
    have hp : (0:ℝ)<(faceComponent S F x).card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x,hx⟩)
    change (∑ y∈faceComponent S F x,faceAverage S F d y)/(faceComponent S F x).card=_
    rw [hsum,mul_div_cancel_left₀ _ hp.ne']
    simp only [faceAverage,ite_eq_left hf]
  · rfl

end ProjectionComparison

end OAI
