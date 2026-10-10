import Mathlib
import OAI.Probability.LogConcave.Sampling.AnalyticBase
import OAI.Probability.LogConcave.JetEstimates.Squared

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma finset_sum_le_sum_of_eq {α : Type} (s t : Finset α) (f g : α → ℝ)
    (he : s=t) (h : ∀a∈s,f a ≤ g a) : (∑a∈s,f a) ≤ ∑a∈t,g a := by
  subst t
  exact Finset.sum_le_sum h

lemma adjointCommutator_squared {S : Type} [Fintype S] {d j : ℕ}
    {H : Point d → ℝ} (hH : ContDiff ℝ (⊤:ℕ∞) H)
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (y : Point d) (M : ℕ → ℝ)
    (hM : ∀e,0<e → e ≤ j → AllSplitBound (spatialTensor (scoreField H) (List.finRange e) y) (M e)) :
    squared (adjointCommutator H F (List.finRange j) y) ≤
      2^j*∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
        (M s.card)^2*spatialSquared F (j-s.card) y := by
  let : DecidableEq (Fin j) := Classical.decEq _
  have heq : (List.finRange j).toFinset=(Finset.univ : Finset (Fin j)) := by ext k; simp
  unfold adjointCommutator
  rw [heq]
  apply (squared_sum _ _).trans
  have hc : (((Finset.univ : Finset (Fin j)).powerset.erase ∅).card : ℝ) ≤ 2^j := by
    exact_mod_cast (Finset.card_erase_le.trans_eq (by simp :
      (Finset.univ : Finset (Fin j)).powerset.card=2^j))
  apply (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun s _ => squared_nonneg _))).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply finset_sum_le_sum_of_eq
  · ext s; simp
  intro s hs
  have hs0 : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hs).1
  let : Nonempty {k // k∈s} := ⟨⟨hs0.choose,hs0.choose_spec⟩⟩
  have hh := scoreField_arbitrary_allSplit hH (selectList (fun k => k∈s) (List.finRange j))
    (selectList_nodup _ (List.nodup_finRange _)) (selectList_full _ (by simp)) y (M s.card)
    (by
      have hc : Fintype.card {k : Fin j // k∈s}=s.card := Fintype.card_of_subtype s (fun _ => Iff.rfl)
      rw [hc]
      exact hM s.card hs0.card_pos ((Finset.card_le_univ s).trans_eq (Fintype.card_fin j)))
  rw [squared_reindex]
  have hb := spatialContractTerm_squared (fun k => k∈s) (scoreField H) F hF _ (List.nodup_finRange _) (by simp) y hh
  have hc : Fintype.card {k : Fin j // k∉s}=j-s.card := by
    rw [Fintype.card_subtype_compl]
    have hs' : Fintype.card {k : Fin j // k∈s}=s.card := Fintype.card_of_subtype s (fun _ => Iff.rfl)
    rw [hs',Fintype.card_fin]
  simp only [Fintype.card_eq_nat_card] at hb hc
  rw [hc] at hb
  exact hb

lemma tensorAdjoint_polySmooth {S : Type} {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (a : S → Fin d) : PolySmooth
      (tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ) (fun z => F (Sum.elim a (fun _ => z)))) :=
  hH.tensorAdjoint (fun _ => hF _) _

lemma spatialEnergy_adjoint {d j : ℕ} {S : Type} [Fintype S]
    {H : Point d → ℝ} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (M : ℕ → ℝ)
    (hM : ∀e,0<e → e ≤ j → ∀y, AllSplitBound (spatialTensor (scoreField H) (List.finRange e) y) (M e)) :
    spatialEnergy (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => F (Sum.elim a (fun _ => z)))) j (gibbs H) ≤
      2*(spatialEnergy F (j+1) (gibbs H)+(K:ℝ)*spatialEnergy F j (gibbs H)+
        2^j*∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
          (M s.card)^2*spatialEnergy F (j-s.card) (gibbs H)) := by
  have hlead : Integrable (fun y => squared (spatialAdjointLeading H F (List.finRange j) y)) (gibbs H) :=
    integrable_finsetSum _ (fun c _ =>
      (hH.tensorAdjoint (fun z => spatialInside_polySmooth F hF _ c z) _).sq.integrable hH.smooth.continuous ht)
  have hf k := (spatialSquared_polySmooth F hF k).integrable hH.smooth.continuous ht
  have hsum := (integrable_finsetSum ((Finset.univ : Finset (Fin j)).powerset.erase ∅)
    (fun s _ => (hf (j-s.card)).const_mul ((M s.card)^2))).const_mul ((2:ℝ)^j)
  have hbase := (spatialSquared_polySmooth _ (tensorAdjoint_polySmooth hH F hF) j).integrable hH.smooth.continuous ht
  have hp (y : Point d) : spatialSquared (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => F (Sum.elim a (fun _ => z)))) j y ≤
      2*(squared (spatialAdjointLeading H F (List.finRange j) y)+
        2^j * ∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
          (M s.card)^2*spatialSquared F (j-s.card) y) := by
    unfold spatialSquared
    rw [spatialTensor_adjoint_sum hH F hF _ (List.nodup_finRange _) y]
    apply (squared_add _ _).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply add_le_add le_rfl
    exact adjointCommutator_squared hH.smooth F (fun c => (hF c).smooth) y M (fun e he hj => hM e he hj y)
  have hh := integral_mono hbase ((hlead.add hsum).const_mul 2) hp
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add hlead hsum,integral_const_mul,
    integral_finsetSum _ (fun s _ => (hf (j-s.card)).const_mul ((M s.card)^2))] at hh
  simp only [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add
    (spatialAdjointLeading_energy hH ht hL F hF) le_rfl) (by norm_num))

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open TensorEnergy
open scoped Classical

lemma spatialTensor_finRange_of_arrayBound {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (y : Point d) {B : ℝ}
    (hb : AllSplitBound (arrayTensor (iteratedFDeriv ℝ n g y)) B) :
    AllSplitBound (spatialTensor (fun c z => g z c) (List.finRange n) y) B := by
  rw [spatialTensor_eq_arrayTensor hg y]
  exact hb.reindex (Equiv.sumComm S (Fin n))
end LogConcaveSampling

end

end

end

end OAI
