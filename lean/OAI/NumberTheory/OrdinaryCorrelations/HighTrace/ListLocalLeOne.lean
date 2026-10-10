import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AbsPrimeMeanLe
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ListSupport

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.FiniteIntegration OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ : ℕ}

lemma listLocal_le_one (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (a : ZMod (p : ℕ)) : listLocal w 𝔏 p a ≤ 1 := by
  unfold listLocal
  split_ifs <;> norm_num

lemma abs_localWithList_le_center (w : ClosedLine h ℓ)
    (𝔏 : List (AttachedSpec w D L)) (p : S.Index) (hp : ¬S.IsCore p)
    (a : ZMod (p : ℕ)) :
    |localWithList w 𝔏 p a| ≤ |centerPrimeFactor w.departures w.label a| := by
  rw [localWithList, abs_mul, abs_of_nonneg (listLocal_nonneg w 𝔏 p a),
    center_primeFactor_eq S w p hp a]
  exact mul_le_of_le_one_right (abs_nonneg _) (listLocal_le_one w 𝔏 p a)

lemma free_center_abs_mean_le (w : ClosedLine h ℓ)
    (𝔏 : List (AttachedSpec w D L)) (p : S.FreeCenterIndex w)
    (e : Fin ℓ) (he : (p.val.val : ℕ) ∣ w.label e) (k : ℕ)
    (hk : k ≤ departureCount w.departures
      (activeResidue w.departures e : ZMod (p.val.val : ℕ))) :
    |avg (localWithList w 𝔏 p.val.val)| ≤
      (betaZ ^ k + theta) / (p.val.val : ℝ) := by
  calc
    _ ≤ avg (fun a => |localWithList w 𝔏 p.val.val a|) := abs_avg_le _
    _ ≤ avg (fun a => |centerPrimeFactor w.departures w.label a|) :=
      avg_mono (abs_localWithList_le_center w 𝔏 p.val.val p.property)
    _ = primeMean (fun a : ZMod (p.val.val : ℕ) =>
        |centerPrimeFactor w.departures w.label a|) := by
      simp only [avg, primeMean, ZMod.card]
    _ ≤ _ := singleton_abs_mean_le w.departures w.label e
      (unique_occurrence_of_free w p.val.val p.val.property e he) k hk

theorem nongood_free_center_mean (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (p : S.FreeCenterIndex w)
    (e : Fin ℓ) (he : (p.val.val : ℕ) ∣ w.label e) :
    |avg (localWithList w 𝔏 p.val.val)| ≤
      (betaZ ^ (w.children (w.offset e.castSucc) +
        w.children (w.offset e.succ)) + theta) / (p.val.val : ℝ) := by
  exact free_center_abs_mean_le w 𝔏 p e he _
    (w.departureCount_ge_endpoint_children hh e he)

theorem tagged_free_center_mean (w : ClosedLine h ℓ)
    (𝔏 : List (AttachedSpec w D L)) (p : S.FreeCenterIndex w)
    (e : Fin ℓ) (he : (p.val.val : ℕ) ∣ w.label e) :
    |avg (localWithList w 𝔏 p.val.val)| ≤ 2 / (p.val.val : ℝ) := by
  apply (free_center_abs_mean_le w 𝔏 p e he 0 (Nat.zero_le _)).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  norm_num

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
