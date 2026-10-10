import OAI.NumberTheory.Jacobsthal.Paths.TagCutoffSeparation
import OAI.NumberTheory.Jacobsthal.Sieve.TagCRTPeriodicity

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve
open scoped BigOperators
open Erdos970Dependency.SiegelWalfisz
attribute [local instance] Classical.propDecidable

lemma mem_AP_canonical (R V : ℝ) (M a p : ℕ) (ha : a<M) :
    p∈intervalPrimes R V M (a:ℤ) ↔ p∈intervalPrimes R V 1 0 ∧ p%M=a := by
  simp only [mem_intervalPrimes,Int.natCast_modEq_iff,Nat.ModEq,Nat.mod_eq_of_lt ha]
  have h1 : Int.ModEq (1:ℤ) (p:ℤ) 0 := by simp [Int.ModEq]
  simpa only [Nat.cast_one,h1,and_true] using (show
    (p.Prime ∧ R<(p:ℝ) ∧ (p:ℝ)≤R+V ∧ p%M=a) ↔
      (p.Prime ∧ R<(p:ℝ) ∧ (p:ℝ)≤R+V) ∧ p%M=a by tauto)

noncomputable def intersectionPrimes (R V : ℝ) (Q : ℕ) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) : Finset ℕ :=
  (intervalPrimes R V 1 0).filter (fun p => p%Q∈A ∧ ∀ t∈T,(p:ZMod t)=rho t)

theorem intersectionPrimes_eq_biUnion (R V : ℝ) (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) :
    intersectionPrimes R V Q T A rho=
      (intersectionResidues Q T A rho hT hQT).biUnion
        (fun a => intervalPrimes R V (Q*(∏ t∈T,t)) (a:ℤ)) := by
  ext p
  rw [intersectionPrimes,Finset.mem_filter,Finset.mem_biUnion]
  have hM : 0 < Q*(∏ t∈T,t) := Nat.mul_pos hQ (Finset.prod_pos (fun t ht => (hT t ht).pos))
  constructor
  · rintro ⟨hp,h⟩
    refine ⟨p%(Q*(∏ t∈T,t)),(mod_mem_intersectionResidues Q hQ T A rho hT hQT hA p).mpr h,?_⟩
    exact (mem_AP_canonical R V _ _ p (Nat.mod_lt p hM)).mpr ⟨hp,rfl⟩
  · rintro ⟨a,ha,hp⟩
    have har := ((mem_intersectionResidues Q hQ T A rho hT hQT hA a).mp ha).1
    obtain ⟨hp,he⟩ := (mem_AP_canonical R V _ a p har).mp hp
    refine ⟨hp,(mod_mem_intersectionResidues Q hQ T A rho hT hQT hA p).mp ?_⟩
    rw [he]
    exact ha

lemma intersection_AP_disjoint (R V : ℝ) (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) :
    ((intersectionResidues Q T A rho hT hQT : Finset ℕ) : Set ℕ).Pairwise (fun a b =>
      Disjoint (intervalPrimes R V (Q*(∏ t∈T,t)) (a:ℤ))
        (intervalPrimes R V (Q*(∏ t∈T,t)) (b:ℤ))) := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro p hpa hpb
  have har := ((mem_intersectionResidues Q hQ T A rho hT hQT hA a).mp ha).1
  have hbr := ((mem_intersectionResidues Q hQ T A rho hT hQT hA b).mp hb).1
  exact hab (((mem_AP_canonical R V _ a p har).mp hpa).2.symm.trans
    ((mem_AP_canonical R V _ b p hbr).mp hpb).2)

theorem intersectionPrimes_card (R V : ℝ) (Q : ℕ) (hQ : 0 < Q) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) (hT : ∀ t∈T,t.Prime) (hQT : ∀ t∈T,Q.Coprime t)
    (hA : ∀ a∈A,a<Q) :
    (intersectionPrimes R V Q T A rho).card=
      ∑ a∈intersectionResidues Q T A rho hT hQT,(intervalPrimes R V (Q*(∏ t∈T,t)) (a:ℤ)).card := by
  rw [intersectionPrimes_eq_biUnion R V Q hQ T A rho hT hQT hA]
  exact Finset.card_biUnion (intersection_AP_disjoint R V Q hQ T A rho hT hQT hA)

end ErdosStoppedTagSieve


end Erdos970

end OAI
