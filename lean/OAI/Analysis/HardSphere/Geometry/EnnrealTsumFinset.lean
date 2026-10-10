import Mathlib
import OAI.Analysis.HardSphere.Geometry.TorusBall

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice
open scoped ENNReal

lemma ennreal_tsum_finset {ι α : Type*} (S : Finset ι) (f : α → ι → ℝ≥0∞) :
    (∑' n, ∑ i∈S, f n i) = ∑ i∈S, ∑' n, f n i := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi, ENNReal.tsum_add, ih]

lemma cardinal_weight_sum {V : Type*} [DecidableEq V] (S : Finset (Finset V))
    (hS : ∀ F∈S, F.Nonempty) (t : ℝ≥0∞) :
    (∑ F∈S, t^F.card) = ∑' m : ℕ, ((S.filter (fun F ↦ F.card=m+1)).card:ℝ≥0∞)*t^(m+1) := by
  have hsingle (F : Finset V) (hF : F∈S) :
      (∑' m : ℕ, if F.card=m+1 then t^(m+1) else 0)=t^F.card := by
    have hpos := Finset.card_pos.mpr (hS F hF)
    rw [tsum_eq_single (F.card-1) (by intro m hm; exact ite_eq_right (by omega))]
    have he : F.card-1+1=F.card := by omega
    simp [he]
  have he (m : ℕ) :
      ((S.filter (fun F ↦ F.card=m+1)).card:ℝ≥0∞)*t^(m+1) =
      ∑ F∈S, if F.card=m+1 then t^(m+1) else 0 := by
    rw [← Finset.sum_filter]
    simp
  simp_rw [he]
  rw [ennreal_tsum_finset]
  exact Finset.sum_congr rfl fun F hF ↦ (hsingle F hF).symm

theorem contact_candidate_potential {K n : ℕ} [NeZero K] (a : ℕ) (hnK : 2*n≤K)
    (U U' : Fin (n+1) → Vertex) (b : ℤ)
    (hfirst : ∀ i, U i 0=b+i.val) (hfirst' : ∀ i, U' i 0=b+i.val)
    (hspeed : ∀ i j k, |U' i k-U' j k|≤3*|(i.val:ℤ)-j.val|)
    (Γ Γ' : Finset (DiscreteTorus K))
    (hcover : ∀ x∈Γ, ∃ i, torusNear K 3 (torusProjection K (U i)) x)
    (hcover' : ∀ x∈Γ', ∃ i, torusNear K 3 (torusProjection K (U' i)) x)
    (t : ℝ≥0∞) :
    (∑ F∈candidateSets (torusRangeGraph K a),
      if torusContact a F Γ ∧ torusContact a F Γ' then t^F.card else 0) ≤
      ∑ i : Fin (n+1), ∑' m : ℕ,
        if torusNear K ((12*a+24)*(m+1)) (torusProjection K (U i)) (torusProjection K (U' i))
        then ((((2*(a+3)+1)^3*2^((2*a+1)^3):ℕ):ℝ≥0∞)*t)^(m+1) else 0 := by
  let S := (candidateSets (torusRangeGraph K a)).filter
    (fun F ↦ torusContact a F Γ ∧ torusContact a F Γ')
  have hS : ∀ F∈S, F.Nonempty := fun F hF ↦ candidate_nonempty _ (Finset.mem_filter.mp hF).1
  rw [← Finset.sum_filter]
  change (∑ F∈S, t^F.card)≤_
  rw [cardinal_weight_sum S hS t]
  rw [← ennreal_tsum_finset]
  apply ENNReal.tsum_le_tsum
  intro m
  have hcard := contact_candidates_card a hnK U U' b hfirst hfirst' hspeed Γ Γ' hcover hcover' (m+1) (by omega)
  have he : S.filter (fun F ↦ F.card=m+1) =
      (candidateSets (torusRangeGraph K a)).filter
      (fun F ↦ F.card=m+1 ∧ torusContact a F Γ ∧ torusContact a F Γ') := by
    ext F; simp only [S,Finset.mem_filter]; tauto
  rw [he]
  calc
    _ ≤ (((((2*(a+3)+1)^3*2^((2*a+1)^3))^(m+1))*
      (Finset.univ.filter (fun i ↦ torusNear K ((12*a+24)*(m+1))
        (torusProjection K (U i)) (torusProjection K (U' i)))).card : ℕ):ℝ≥0∞)*t^(m+1) := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast hcard
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,Nat.cast_mul,Nat.cast_pow,mul_pow]
      ring

end HardSphere.Lattice

open scoped ENNReal NNReal

end

end OAI
