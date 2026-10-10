import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.EuclideanPairDirection
import OAI.MeasureTheory.FalconerCompletion.Graphs.ProfileChildCard

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def farChildMaximumND {n : ℕ}
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1))))
    (a : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
    (v M : ℝ) (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))) : ℝ≥0∞ :=
  (P.sup fun p => positiveDistanceCountND
    ((gridPairMeasureND ρ a p).restrict {x | euclideanPairDirectionND x∈U x}) (n+1) v a M) ⊔
  (Q.sup fun q => positiveDistanceCountND
    ((gridPairMeasureND κ a q).restrict {x | euclideanPairDirectionND x∈W x}) (n+1) v a M)

lemma farChildMaximumND_ne_top {n : ℕ}
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (a : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
    (v M : ℝ) (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))) :
    farChildMaximumND ρ κ a P Q v M U W ≠ ⊤ := by
  unfold farChildMaximumND
  apply ne_of_lt
  rw [sup_lt_iff, Finset.sup_lt_iff, Finset.sup_lt_iff]
  · exact ⟨fun p _ => (positiveDistanceCountND_ne_top _ _ _ _ _).lt_top,
      fun p _ => (positiveDistanceCountND_ne_top _ _ _ _ _).lt_top⟩
  · exact bot_lt_top
  · exact bot_lt_top

theorem euclidean_far_finite_sumND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ : ℝ} (hθ : 0<θ) (B T : ℝ) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))),
      ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (a : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
        (X Y : Set (EuclideanSpace ℝ (Fin (n+1))))
        (v M A : ℝ) (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      0<M → 1≤A → A≤R^2 →
      (∀ p∈P, ambientGridCell a p.1⊆X ∧ ambientGridCell a p.2⊆X) →
      (∀ q∈Q, ambientGridCell a q.1⊆Y ∧ ambientGridCell a q.2⊆Y) →
      MeasurableSet {x | euclideanPairDirectionND x∈U x} →
      MeasurableSet {x | euclideanPairDirectionND x∈W x} →
      (∀ p∈P, ∀ᵐ x ∂gridPairMeasureND ρ a p,
        (2:ℝ)^(-(a:ℝ))/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (b x) ∧
        (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*A^j)) →
      (∀ q∈Q, ∀ᵐ x ∂gridPairMeasureND κ a q,
        (2:ℝ)^(-(a:ℝ))/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (c x) ∧
        (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*A^j)) →
      R^B*‖∑ pq∈P.product Q, ∫ x, (∫ u : ℝ, (Ψ u:ℂ)*
        sphereAxisIntegralND (((2:ℝ)^v*dist x.1.1 x.1.2)*u) (euclideanPairDirectionND x.1) (b x.1)*
          conj (sphereAxisIntegralND (((2:ℝ)^v*dist x.2.1 x.2.2)*u) (euclideanPairDirectionND x.2) (c x.2)))
        ∂(gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2)‖ ≤
        (R^B*H*(2:ℝ)^(-(n:ℝ)*(v-a)))*
          (binKernelConstant.toReal*(M^4*(2:ℝ)^(-(v-a)))*
            ((P.product Q).card:ℝ)*(farChildMaximumND ρ κ a P Q v M U W).toReal)+
        (ρ X).toReal^2*(κ Y).toReal^2*R^(-T) := by
  obtain ⟨J,H,hH,hint⟩ := euclidean_far_integratedND (n := n) hΨ hs C hC hθ B T
  refine ⟨J,H,hH,?_⟩
  filter_upwards [hint,eventually_gt_atTop (0:ℝ)] with R hint hR
  intro ρ κ _ _ a P Q X Y v M A b c U W hM hA hAup hPx hQy hU hW hb hc
  let D := (farChildMaximumND ρ κ a P Q v M U W).toReal
  have hD := farChildMaximumND_ne_top ρ κ a P Q v M U W
  let L := R^B*H*(2:ℝ)^(-(n:ℝ)*(v-a))*(binKernelConstant.toReal*(M^4*(2:ℝ)^(-(v-a))))
  have hL : 0≤L := by dsimp [L]; positivity
  let G := fun x : ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))) =>
    ∫ u : ℝ, (Ψ u:ℂ)*
      sphereAxisIntegralND (((2:ℝ)^v*dist x.1.1 x.1.2)*u) (euclideanPairDirectionND x.1) (b x.1)*
        conj (sphereAxisIntegralND (((2:ℝ)^v*dist x.2.1 x.2.2)*u) (euclideanPairDirectionND x.2) (c x.2))
  have hpq (p) (hp : p∈P) (q) (hq : q∈Q) :
      R^B*‖∫ x, G x ∂(gridPairMeasureND ρ a p).prod (gridPairMeasureND κ a q)‖ ≤
      L*D+((gridPairMeasureND ρ a p).prod (gridPairMeasureND κ a q)).real univ*R^(-T) := by
    have hh := hint (gridPairMeasureND ρ a p) (gridPairMeasureND κ a q)
      v a M A b c U W hM hA hAup hU hW (hb p hp) (hc q hq)
    apply hh.trans
    apply add_le_add _ le_rfl
    have hm : max
        (positiveDistanceCountND ((gridPairMeasureND ρ a p).restrict {x | euclideanPairDirectionND x∈U x}) (n+1) v a M).toReal
        (positiveDistanceCountND ((gridPairMeasureND κ a q).restrict {x | euclideanPairDirectionND x∈W x}) (n+1) v a M).toReal ≤ D := by
      apply max_le
      · apply ENNReal.toReal_mono hD
        unfold farChildMaximumND
        apply le_sup_of_le_left
        exact Finset.le_sup (f := fun p => positiveDistanceCountND
          ((gridPairMeasureND ρ a p).restrict {x | euclideanPairDirectionND x∈U x}) (n+1) v a M) hp
      · apply ENNReal.toReal_mono hD
        unfold farChildMaximumND
        apply le_sup_of_le_right
        exact Finset.le_sup (f := fun q => positiveDistanceCountND
          ((gridPairMeasureND κ a q).restrict {x | euclideanPairDirectionND x∈W x}) (n+1) v a M) hq
    simpa only [L,mul_assoc] using mul_le_mul_of_nonneg_left hm hL
  calc
    _ ≤ R^B*∑ pq∈P.product Q, ‖∫ x, G x ∂(gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.rpow_nonneg hR.le _)
    _ = ∑ pq∈P.product Q, R^B*‖∫ x, G x ∂(gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2)‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ pq∈P.product Q, (L*D+((gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2)).real univ*R^(-T)) := by
      apply Finset.sum_le_sum
      intro pq hpq'
      exact hpq pq.1 (Finset.mem_product.mp hpq').1 pq.2 (Finset.mem_product.mp hpq').2
    _ = ((P.product Q).card:ℝ)*(L*D)+
        (∑ pq∈P.product Q, ((gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2)).real univ)*R^(-T) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_mul]
    _ ≤ ((P.product Q).card:ℝ)*(L*D)+(ρ X).toReal^2*(κ Y).toReal^2*R^(-T) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (gridPairMeasureND_quadruple_mass ρ κ a P Q X Y hPx hQy) (show 0≤R^(-T) by positivity))
    _ = _ := by dsimp [L,D]; ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
