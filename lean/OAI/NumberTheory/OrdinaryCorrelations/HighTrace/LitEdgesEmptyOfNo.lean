import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ChargedCorrectionSum
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SubtreeUnionWeightNonneg

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma litEdges_empty_of_no_tree (w : ClosedLine h ℓ) (p : S.Index)
    (hnot : ∀ i ∈ w.treeSteps, ¬(p : ℕ) ∣ w.label i) (a : ZMod (p : ℕ)) :
    litEdges w p a = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hi' := (mem_filter.mp (mem_filter.mp hi).1)
  exact hnot i hi'.1 hi'.2

theorem charged_prime_le_background (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hU : U ⊆ goodOrigins w) (p : S.Index)
    (hnot : ∀ i ∈ w.treeSteps, ¬(p : ℕ) ∣ w.label i) (a : ZMod (p : ℕ)) :
    |S.primeFactor w p a| * allPrimeCharges w U p a ≤ backgroundMultiplier w U p a := by
  have hoc : (∏ i ∈ w.treeSteps, |S.occurrenceFactor w p i a|) = 1 := by
    apply prod_eq_one
    intro i hi
    simp only [occurrenceFactor, ite_eq_right (hnot i hi), abs_one]
  have htop : NoComponentTop w U p ∅ := by
    intro hc i hi he
    simp [edgeVertices] at he
  calc
    _ ≤ _ := charged_prime_le_tree w U p a
    _ = (∏ i ∈ w.treeSteps, S.beta p ^
        (if a + (w.offset i.castSucc : ZMod (p : ℕ)) = 0 then (1 : ℕ) else 0)) *
        ∏ i ∈ incomingCharges w U, S.primeCharge p (w.label i) (w.offset i.succ) a := by
      rw [hoc, one_mul]
    _ ≤ (∏ i ∈ w.treeSteps, S.beta p ^
        (if a + (w.offset i.castSucc : ZMod (p : ℕ)) = 0 then (1 : ℕ) else 0)) *
        ∏ v ∈ treeVertices w, isolatedCharge w U p ∅ a v :=
      mul_le_mul_of_nonneg_left (incoming_charges_le_vertices w U hU p ∅ htop a)
        (prod_nonneg (fun _ _ => pow_nonneg (beta_nonneg p) _))
    _ = _ := by
      rw [tree_normalization, ← prod_mul_distrib]
      apply prod_congr rfl
      intro v hv
      by_cases ha : a + (v : ZMod (p : ℕ)) = 0
      · simp [isolatedCharge, edgeVertices, ha]
      · simp [isolatedCharge, ha]

lemma listLocal_has_residue (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (hp : (p : ℕ) ∈ listSupport w 𝔏) :
    ∃ v : ℤ, ∀ a : ZMod (p : ℕ), listLocal w 𝔏 p a ≤ activity (p : ℕ) a v := by
  obtain ⟨s,hs,hp⟩ := mem_biUnion.mp hp
  have hsL : s ∈ 𝔏 := List.mem_toFinset.mp hs
  rcases mem_insert.mp hp with hp | hp
  · refine ⟨s.vertex,?_⟩
    intro a
    unfold listLocal
    split_ifs with ht
    · rw [activity, ite_eq_left ((ht s hsL).1 hp)]
    · exact activity_nonneg p a _
  · obtain ⟨i,hi,hpi⟩ := mem_biUnion.mp hp
    refine ⟨s.vertex + s.spec.offset i.castSucc,?_⟩
    intro a
    unfold listLocal
    split_ifs with ht
    · rw [activity, ite_eq_left ((ht s hsL).2 i (Nat.mem_primeFactors.mp hpi).2.1)]
    · exact activity_nonneg p a _

theorem list_no_tree_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (p : S.Index)
    (hnot : ∀ i ∈ w.treeSteps, ¬(p : ℕ) ∣ w.label i)
    (hlist : (p : ℕ) ∈ listSupport w 𝔏) :
    avg (fun a => |localWithList w 𝔏 p a| * allPrimeCharges w U p a) ≤ (p : ℝ)⁻¹ := by
  obtain ⟨v,hv⟩ := listLocal_has_residue w 𝔏 p hlist
  calc
    _ ≤ avg (fun a : ZMod (p : ℕ) => activity (p : ℕ) a v) := by
      apply avg_mono
      intro a
      calc
        _ = (|S.primeFactor w p a| * allPrimeCharges w U p a) * listLocal w 𝔏 p a := by
          rw [localWithList, abs_mul, abs_of_nonneg (listLocal_nonneg w 𝔏 p a)]
          ring
        _ ≤ backgroundMultiplier w U p a * listLocal w 𝔏 p a :=
          mul_le_mul_of_nonneg_right (charged_prime_le_background w U hU p hnot a)
            (listLocal_nonneg w 𝔏 p a)
        _ ≤ 1 * activity (p : ℕ) a v :=
          mul_le_mul (backgroundMultiplier_bounds w U
            (fun u hu => (good_origin_data w (hU hu)).2.2.1) p a).2
            (hv a) (listLocal_nonneg w 𝔏 p a) zero_le_one
        _ = _ := one_mul _
    _ = _ := activity_mean p v

theorem background_kernel_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (p : S.Index)
    (hnot : ∀ i ∈ w.treeSteps, ¬(p : ℕ) ∣ w.label i)
    (hinj : Set.InjOn (fun v : ℤ => (v : ZMod (p : ℕ))) (treeVertices w)) :
    avg (fun a => |localWithList w 𝔏 p a| * allPrimeCharges w U p a) ≤
      Real.exp (-(treeDefect w p -
        (if S.IsCore p then betaC * (Real.exp kappa - 1) * U.card else 0)) / (p : ℝ)) := by
  calc
    _ ≤ avg (backgroundMultiplier w U p) :=
      avg_mono (fun a => (charged_local_le w 𝔏 U p a).trans
        (charged_prime_le_background w U hU p hnot a))
    _ ≤ _ := background_mean_le_exp w U (fun v hv => (good_origin_data w (hU hv)).1)
      (fun v hv => (good_origin_data w (hU hv)).2.2.1) p hinj

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
