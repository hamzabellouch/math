import Mathlib
import OAI.Probability.LogConcave.Sampling.FinsetSumSum
import OAI.Probability.LogConcave.JetEstimates.CompLinear

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma spatialSquared_coordinateLift {S : Type} [Fintype S] {d D : ℕ}
    (e : Fin d ↪ Fin D) (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (j : ℕ) (y : Point D) :
    spatialSquared (arrayCoordinateLift e ι F) j y=
      spatialSquared F j (coordinateProjection e y) := by
  unfold spatialSquared
  rw [spatialTensor_coordinateLift e ι F hF _ (fun k => List.mem_finRange k) y,squared_zeroExtend]

lemma arrayCoordinateLift_polySmooth {S : Type} {d D : ℕ}
    (e : Fin d ↪ Fin D) (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (c : S → Fin D) :
    PolySmooth (arrayCoordinateLift e ι F c) := by
  by_cases hc : c∈Set.range (slotEmbedding ι)
  · obtain ⟨a,rfl⟩ := hc
    change PolySmooth (fun y => zeroExtend (slotEmbedding ι) (fun a => F a (coordinateProjection e y)) (slotEmbedding ι a))
    simp only [zeroExtend_apply]
    exact (hF a).comp_linear _
  · have he : arrayCoordinateLift e ι F c=fun _ => 0 := by
      funext y; exact zeroExtend_out _ _ hc
    rw [he]
    exact PolySmooth.const 0

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma spatialSquared_reindex {S T : Type} [Fintype S] [Fintype T] {d j : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (e : S ≃ T) (y : Point d) :
    spatialSquared (fun c => F (c ∘ e)) j y=spatialSquared F j y := by
  have he : spatialTensor (fun c => F (c ∘ e)) (List.finRange j) y=
      fun c => spatialTensor F (List.finRange j) y (c ∘ (Equiv.sumCongr (Equiv.refl (Fin j)) e)) := by
    funext c
    symm
    exact spatialTensor_relabel F hF e (Equiv.refl _) _ _ (by simp) y c
  unfold spatialSquared
  rw [he]
  exact squared_reindex _ _

lemma spatialEnergy_reindex {S T : Type} [Fintype S] [Fintype T] {d j : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (e : S ≃ T) (μ : Measure (Point d)) :
    spatialEnergy (fun c => F (c ∘ e)) j μ=spatialEnergy F j μ := by
  unfold spatialEnergy
  congr 1
  funext y
  exact spatialSquared_reindex F hF e y

def tensorGrad {S : Type} {d : ℕ} (F : (S → Fin d) → Point d → ℝ)
    (c : S ⊕ Unit → Fin d) : Point d → ℝ :=
  directional (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ()))) (F (fun s => c (Sum.inl s)))

lemma tensorGrad_polySmooth {S : Type} {d : ℕ} (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (c : S ⊕ Unit → Fin d) : PolySmooth (tensorGrad F c) :=
  (hF _).directional _

def gradSpatialSlots (K S : Type) : ((K ⊕ Unit) ⊕ S) ≃ K ⊕ (S ⊕ Unit) where
  toFun := Sum.elim (Sum.elim Sum.inl (fun u => Sum.inr (Sum.inr u))) (fun s => Sum.inr (Sum.inl s))
  invFun := Sum.elim (fun k => Sum.inl (Sum.inl k)) (Sum.elim Sum.inr (fun u => Sum.inl (Sum.inr u)))
  left_inv a := by rcases a with (a | a) | a <;> rfl
  right_inv a := by rcases a with a | (a | a) <;> rfl

lemma spatialTensor_grad {S K : Type} {d : ℕ} (F : (S → Fin d) → Point d → ℝ)
    (l : List K) (y : Point d) (c : K ⊕ (S ⊕ Unit) → Fin d) :
    spatialTensor (tensorGrad F) l y c=
      spatialTensor F (l.map Sum.inl++([()] : List Unit).map Sum.inr) y (c ∘ gradSpatialSlots K S) := by
  unfold spatialTensor tensorGrad
  rw [JetCalculus.jet_append,JetCalculus.jet_map,JetCalculus.jet_map]
  rfl

lemma spatialSquared_grad {S : Type} [Fintype S] {d j : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (y : Point d) :
    spatialSquared (tensorGrad F) j y=spatialSquared F (j+1) y := by
  unfold spatialSquared
  have he : spatialTensor (tensorGrad F) (List.finRange j) y=
      fun c => spatialTensor F ((List.finRange j).map Sum.inl++([()] : List Unit).map Sum.inr) y
        (c ∘ gradSpatialSlots (Fin j) S) := funext (spatialTensor_grad F _ y)
  rw [he,squared_reindex]
  have hh := spatialSquared_full F hF ((List.finRange j).map Sum.inl++([()] : List Unit).map Sum.inr)
    (JetCalculus.nodup_sum_append (List.nodup_finRange _) (by simp))
    (by intro k; cases k <;> simp) y
  have hc : Fintype.card (Fin j ⊕ Unit)=j+1 := by simp
  simp only [Fintype.card_eq_nat_card] at hh hc
  rw [hc] at hh
  exact hh

lemma spatialEnergy_grad {S : Type} [Fintype S] {d j : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (μ : Measure (Point d)) :
    spatialEnergy (tensorGrad F) j μ=spatialEnergy F (j+1) μ := by
  unfold spatialEnergy
  congr 1
  funext y
  exact spatialSquared_grad F hF y

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

def lieInside {S : Type} {d : ℕ} (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (c : S ⊕ Unit → Fin d) (y : Point d) : ℝ :=
  singleContract (fun a => A a y) (fun a => tensorGrad F a y) (c ∘ Equiv.sumComm Unit S)

def tensorLie {S : Type} {d : ℕ} (H : Point d → ℝ)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (c : S → Fin d) : Point d → ℝ :=
  tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ) (fun z => lieInside A F (Sum.elim c (fun _ => z)))

lemma lieInside_polySmooth {S : Type} {d : ℕ} (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (c : S ⊕ Unit → Fin d) : PolySmooth (lieInside A F c) :=
  singleContract_polySmooth A (tensorGrad F) hA (tensorGrad_polySmooth F hF) _

lemma tensorLie_polySmooth {S : Type} {d : ℕ} {H : Point d → ℝ} (hH : PolySmooth H)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c)) (c : S → Fin d) : PolySmooth (tensorLie H A F c) :=
  tensorAdjoint_polySmooth hH (lieInside A F) (lieInside_polySmooth A F hA hF) c

def productEnergyBudget (C E : ℕ → ℝ) (j : ℕ) : ℝ :=
  2^j*∑s∈(Finset.univ : Finset (Fin j)).powerset,(C s.card)^2*E (j-s.card+1)

def adjointEnergyBudget (K : ℝ) (C E : ℕ → ℝ) (j : ℕ) : ℝ :=
  2*(E (j+1)+K*E j+2^j*∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
    (C s.card)^2*E (j-s.card))

lemma productEnergyBudget_nonneg {C E : ℕ → ℝ} (hE : ∀j,0 ≤ E j) (j : ℕ) :
    0 ≤ productEnergyBudget C E j :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun s _ => mul_nonneg (sq_nonneg _) (hE _)))

lemma productEnergyBudget_mono (C : ℕ → ℝ) {E G : ℕ → ℝ} (j : ℕ)
    (h : ∀k,0<k → k ≤ j+1 → E k ≤ G k) : productEnergyBudget C E j ≤ productEnergyBudget C G j := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left (h _ (by omega) (by omega)) (sq_nonneg _)

lemma adjointEnergyBudget_mono {K : ℝ} (hK : 0 ≤ K) (C : ℕ → ℝ) {E G : ℕ → ℝ} (j : ℕ)
    (h : ∀k ≤ j+1,E k ≤ G k) : adjointEnergyBudget K C E j ≤ adjointEnergyBudget K C G j := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add
  · exact add_le_add (h _ le_rfl) (mul_le_mul_of_nonneg_left (h _ (by omega)) hK)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h _ (by omega)) (sq_nonneg _))

lemma lieInside_energy {S : Type} [Fintype S] {d j : ℕ}
    {H : Point d → ℝ} (hH : Continuous H) (ht : HasGaussianLowerTail H)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c)) (C : ℕ → ℝ)
    (hb : ∀k ≤ j,∀y,AllSplitBound (spatialTensor A (List.finRange k) y) (C k)) :
    spatialEnergy (lieInside A F) j (gibbs H) ≤ productEnergyBudget C (fun k => spatialEnergy F k (gibbs H)) j := by
  have hg := tensorGrad_polySmooth F hF
  have hh := spatialEnergy_contract hH ht A (tensorGrad F) hA hg C hb
  have he := spatialEnergy_reindex (j:=j) (fun c y => singleContract (fun a => A a y) (fun a => tensorGrad F a y) c)
    (fun c => (singleContract_polySmooth A (tensorGrad F) hA hg c).smooth) (Equiv.sumComm Unit S) (gibbs H)
  change spatialEnergy (lieInside A F) j (gibbs H)=_ at he
  rw [he]
  simp_rw [spatialEnergy_grad F (fun c => (hF c).smooth)] at hh
  exact hh

lemma tensorLie_energy {S : Type} [Fintype S] {d j : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c)) (C D : ℕ → ℝ)
    (hb : ∀k ≤ j+1,∀y,AllSplitBound (spatialTensor A (List.finRange k) y) (C k))
    (hs : ∀k,0<k → k ≤ j → ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange k) y) (D k)) :
    spatialEnergy (tensorLie H A F) j (gibbs H) ≤
      adjointEnergyBudget K D (productEnergyBudget C (fun k => spatialEnergy F k (gibbs H))) j := by
  have he := spatialEnergy_adjoint hH ht hL (lieInside A F) (lieInside_polySmooth A F hA hF) D hs
  apply he.trans
  exact adjointEnergyBudget_mono K.2 D j (fun k hk =>
    lieInside_energy hH.smooth.continuous ht A F hA hF C (fun i hi => hb i (hi.trans hk)))

end LogConcaveSampling

end

end

end

end OAI
