import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakAddLemmas
import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakRestrictionLemmas

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_weak_divergence_equation_differentiation {n : ℕ} {K : Set (Coord n)}
    (hK : IsCompact K) (C : Coord n → Fin n → Fin n → ℝ)
    (V W D E : Fin n → Coord n → ℝ) (F G : Coord n → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j))
    (hV : ∀ a, MemLp (V a) 2 (volume.restrict K))
    (hW : ∀ a, MemLp (W a) 2 (volume.restrict K))
    (_ : ∀ j, MemLp (D j) 2 (volume.restrict K))
    (hE : ∀ j, MemLp (E j) 2 (volume.restrict K))
    (_ : MemLp F 2 (volume.restrict K)) (hG : MemLp G 2 (volume.restrict K))
    (l : Fin n)
    (hVW : ∀ a psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, V a x*coordPartial psi x l)=-(∫ x in K, W a x*psi x))
    (hDE : ∀ j psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, D j x*coordPartial psi x l)=-(∫ x in K, E j x*psi x))
    (hFG : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, F x*coordPartial psi x l)=-(∫ x in K, G x*psi x))
    (heq : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∑ a, ∑ j, ∫ x in K, C x a j*V a x*coordPartial psi x j) =
        (∫ x in K, F x*psi x)-∑ j, ∫ x in K, D j x*coordPartial psi x j)
    (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ K) :
    (∀ a j, IntegrableOn (fun x ↦ C x a j*W a x*coordPartial psi x j) K) ∧
    IntegrableOn (fun x ↦ G x*psi x) K ∧
    (∀ j, IntegrableOn (fun x ↦
      (realWeakGradientCommutator C V l j x+E j x)*coordPartial psi x j) K) ∧
    (∑ a, ∑ j, ∫ x in K, C x a j*W a x*coordPartial psi x j) =
      (∫ x in K, G x*psi x)-∑ j, ∫ x in K,
        (realWeakGradientCommutator C V l j x+E j x)*coordPartial psi x j := by
  have hd (j : Fin n) := real_coordPartial_smooth psi hp j
  have hdc (j : Fin n) : HasCompactSupport (fun x ↦ coordPartial psi x j) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ (Pi.single j 1))
  have hds (j : Fin n) : tsupport (fun x ↦ coordPartial psi x j) ⊆ K :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans hs
  have ht := real_continuous_memLp_compact hK psi hp.continuous
  have hdt (j : Fin n) := real_continuous_memLp_compact hK _ (hd j).continuous
  have hprod (a j : Fin n) := real_interior_weak_product hK (V a) (W a)
    (fun x ↦ C x a j) (hV a) (hW a) (hC a j) l (hVW a)
  have hi (a j : Fin n) : IntegrableOn (fun x ↦ C x a j*W a x*coordPartial psi x j) K := by
    obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hK _ (hC a j).continuous
    exact (hb _ (hW a)).1.integrable_mul (hdt j)
  have hci (a j : Fin n) : IntegrableOn
      (fun x ↦ coordPartial (fun y ↦ C y a j) x l*V a x*coordPartial psi x j) K := by
    obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hK _
      (real_coordPartial_smooth _ (hC a j) l).continuous
    exact (hb _ (hV a)).1.integrable_mul (hdt j)
  have he (a j : Fin n) :
      (∫ x in K, C x a j*V a x*coordPartial (fun y ↦ coordPartial psi y l) x j) =
        -((∫ x in K, C x a j*W a x*coordPartial psi x j)+
          ∫ x in K, coordPartial (fun y ↦ C y a j) x l*V a x*coordPartial psi x j) := by
    have h := ((hprod a j).2.2 _ (hd j) (hdc j) (hds j)).2.2
    simp_rw [real_coordPartial_commute psi hp _ l j] at h
    rw [h]
    congr 1
    simp_rw [add_mul]
    exact integral_add (hi a j) (hci a j)
  have hde (j : Fin n) :
      (∫ x in K, D j x*coordPartial (fun y ↦ coordPartial psi y l) x j) =
        -(∫ x in K, E j x*coordPartial psi x j) := by
    have h := hDE j _ (hd j) (hdc j) (hds j)
    simpa only [real_coordPartial_commute psi hp _ l j] using h
  have hcomb (j : Fin n) :
      IntegrableOn (fun x ↦ (realWeakGradientCommutator C V l j x+E j x)*coordPartial psi x j) K ∧
      (∫ x in K, (realWeakGradientCommutator C V l j x+E j x)*coordPartial psi x j) =
        (∑ a, ∫ x in K, coordPartial (fun y ↦ C y a j) x l*V a x*coordPartial psi x j)+
          ∫ x in K, E j x*coordPartial psi x j := by
    simp only [realWeakGradientCommutator,add_mul,Finset.sum_mul]
    have hsum := integrable_finsetSum Finset.univ (fun a _ ↦ hci a j)
    have hei : IntegrableOn (fun x ↦ E j x*coordPartial psi x j) K := (hE j).integrable_mul (hdt j)
    exact ⟨hsum.add hei,by
      rw [integral_add hsum hei,
        integral_finsetSum Finset.univ (fun a _ ↦ hci a j)]⟩
  refine ⟨hi,hG.integrable_mul ht,fun j ↦ (hcomb j).1,?_⟩
  have h := heq _ (hd l) (hdc l) (hds l)
  simp_rw [he,hde,hFG psi hp hc hs,Finset.sum_neg_distrib,Finset.sum_add_distrib] at h
  simp_rw [(hcomb _).2,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun j a ↦ ∫ x in K,
    coordPartial (fun y ↦ C y a j) x l*V a x*coordPartial psi x j)]
  linarith only [h]

end
end Yau

end OAI
