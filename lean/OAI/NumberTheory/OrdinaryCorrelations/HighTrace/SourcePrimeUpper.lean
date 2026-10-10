import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceWitnessMajorant
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LinePrimeMemFullUsed
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Ordered
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UnselectedCard

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SignedTrace
open Finset Classical Filter
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ n : ℕ}

lemma source_prime_upper (B : ℝ) (hB : 1 ≤ B) (p : (sourceSystem B).Index) :
    (p:ℝ) ≤ Real.exp B := by
  rcases mem_union.mp p.property with hp|hp
  · exact (by exact_mod_cast (mem_Icc.mp (mem_filter.mp hp).1).2 :
      (p:ℝ) ≤ (⌊Real.exp B⌋₊:ℝ)).trans (Nat.floor_le (Real.exp_pos _).le)
  · have hb : B^(1-SourcePrimeBands.eta) ≤ B :=
      Real.rpow_le_self_of_one_le hB (by norm_num [SourcePrimeBands.eta,SourcePrimeBands.epsilon])
    exact ((by exact_mod_cast (mem_Icc.mp (mem_filter.mp hp).1).2 :
      (p:ℝ) ≤ (⌊Real.exp (B^(1-SourcePrimeBands.eta))⌋₊:ℝ)).trans
        (Nat.floor_le (Real.exp_pos _).le)).trans (Real.exp_le_exp.mpr hb)

namespace PrivateFamily
variable {w : ClosedLine h ℓ} (F : PrivateFamily w D L n)

theorem used_fiber_sum_le (hl : ∀ i, w.label i ∈ D.members)
    (l : List (AttachedSpec w D L)) (c : Case) (A : Finset (Fin n)) (t : ∀ j : A, F.Test j.val)
    (ht : ∀ j, (t j).Valid) (hinj : Function.Injective (fun j => (t j).selected))
    (hfuture : ∀ i j : A, c.Precedes i.val j.val → ((t j).selected:ℕ) ∉ (t i).support)
    (hB : 0 ≤ B) (P : ℝ) (hP : 0 < P) (hS : ∀ p : S.Index, P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp B) :
    (∑ x : F.used l → S.Index,
      (F.usedTestSystem hl l c A t ht hinj hfuture).fiberWeight P (testSize B C₀ h ℓ L)
        (fun p => (x p:ℕ))) ≤
      (∑ p ∈ S.primes, (p:ℝ)⁻¹)^((F.used l).card-A.card) *
        (max (testSize B C₀ h ℓ L/(P*Real.log 2)) ((2+B)/P))^A.card := by
  have hb := (F.usedTestSystem hl l c A t ht hinj hfuture).fiber_sum_le S.primes P B
    (testSize B C₀ h ℓ L) hP hB (testSize_nonneg ..)
    (fun p hp => ⟨S.prime_mem p hp,(hS ⟨p,hp⟩).1,(hS ⟨p,hp⟩).2⟩)
  rw [unselected_card,Fintype.card_coe] at hb
  exact hb
end PrivateFamily

theorem source_crude_witness_fiber (h : ℕ) (hh : 0 < h) (τ C₀ : ℝ) (hτ : τ < 2) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (w : ClosedLine h (sourceLength B)) (_hl : ∀ i, w.label i ∈ D.members)
      (l : List (AttachedSpec w D (pathLength B)))
      (F : PrivateFamily w D (pathLength B) (listCutoff B)),
      JointlyRealizable w (l++List.ofFn F.witness) →
      ∃ (k : ℕ) (e : Fin k ↪ F.used l)
        (d : TriangularExpressions e ((sourceLength B+pathLength B)+pathLength B)),
        B^(2*epsilon) ≤ (k:ℝ) ∧
        d.Admissible (sourceMinPrime B) (PrivateFamily.testSize B C₀ h (sourceLength B) (pathLength B))
          (fun p => (p.val:ℕ)) ∧
        (∑ x : F.used l → (sourceSystem B).Index,
          d.fiberWeight (sourceMinPrime B) (PrivateFamily.testSize B C₀ h (sourceLength B) (pathLength B))
            (fun p => (x p:ℕ))) ≤
          (∑ p ∈ (sourceSystem B).primes, (p:ℝ)⁻¹)^((F.used l).card-k) *
            (max (PrivateFamily.testSize B C₀ h (sourceLength B) (pathLength B)/(sourceMinPrime B*Real.log 2))
              ((2+B)/sourceMinPrime B))^k := by
  filter_upwards [source_crude_witness_tests h hh τ C₀ hτ,eventually_ge_atTop (1:ℝ)] with B hb hB
  intro D w hl l F hj
  obtain ⟨c,A,t,hcard,ht,hinj,hfuture,hnd,_⟩ := hb D w l F hj
  obtain ⟨r,hr⟩ := hj
  have hq (i) (p) : (F.witness i).spec.ResidueTest p (F.witness i).vertex (r p) :=
    hr (F.witness i) (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)) p
  exact ⟨A.card,F.usedEmbedding l c A t ht hinj,F.usedTestSystem hl l c A t ht hinj hfuture,
    hcard,F.usedTestSystem_admissible hl l c A t ht hinj hfuture hnd (by linarith)
      (sourceMinPrime B) (fun p => (source_prime_lower B hB p).le) (source_prime_upper B hB) r hq,
    F.used_fiber_sum_le hl l c A t ht hinj hfuture (by linarith) (sourceMinPrime B)
      (Real.exp_pos _) (fun p => ⟨(source_prime_lower B hB p).le,source_prime_upper B hB p⟩)⟩

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
