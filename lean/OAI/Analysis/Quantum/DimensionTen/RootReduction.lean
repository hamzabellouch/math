import Mathlib

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma prod_roots_eq_prod_rootSet {K : Type*} [Field K] (f : K[X])
    (hm : f.Monic) (hs : f.Separable) (hsp : f.Splits) :
    f = ∏ x : f.rootSet K, (X - C (x : K)) := by
  classical
  conv_lhs => rw [hsp.eq_prod_roots_of_monic hm]
  have hroot : f.rootSet K = (f.roots.toFinset : Set K) := by
    simp only [rootSet_def, aroots_def, Algebra.algebraMap_self, map_id]
  have hfin : (f.rootSet K).toFinset = f.roots.toFinset := by
    ext x
    simp only [Set.mem_toFinset, hroot, Finset.mem_coe]
  rw [Finset.prod_set_coe (f := fun x : K => X - C x) (f.rootSet K), hfin]
  change _ = (f.roots.toFinset).prod _
  have hnodup := nodup_roots hs
  change _ = (f.roots.toFinset.val.map (fun x => X - C x)).prod
  simp only [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]

lemma map_eq_prod_rootSet {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (f : R[X]) (hm : f.Monic) (hs : (f.map (algebraMap R K)).Separable)
    (hsp : (f.map (algebraMap R K)).Splits) :
    f.map (algebraMap R K) = ∏ x : f.rootSet K, (X - C (x : K)) := by
  classical
  conv_lhs => rw [hsp.eq_prod_roots_of_monic (hm.map _)]
  have hroot : f.rootSet K = ((f.map (algebraMap R K)).roots.toFinset : Set K) := by
    simp only [rootSet_def, aroots_def]
  have hfin : (f.rootSet K).toFinset = (f.map (algebraMap R K)).roots.toFinset := by
    ext x
    simp only [Set.mem_toFinset, hroot, Finset.mem_coe]
  rw [Finset.prod_set_coe (f := fun x : K => X - C x) (f.rootSet K), hfin]
  change _ = ((f.map (algebraMap R K)).roots.toFinset.val.map (fun x => X - C x)).prod
  simp only [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (nodup_roots hs)]


def rootInteger {K : Type*} [Field K] [CharZero K] (f : ℤ[X]) (hm : f.Monic)
    (x : f.rootSet K) : 𝓞 K :=
  ⟨x, ⟨f, hm, (mem_rootSet.mp x.property).2⟩⟩

@[simp] lemma rootInteger_coe {K : Type*} [Field K] [CharZero K] (f : ℤ[X]) (hm : f.Monic)
    (x : f.rootSet K) : (rootInteger f hm x : K) = x := rfl

lemma map_eq_prod_rootInteger {K : Type*} [Field K] [CharZero K]
    (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hsp : (f.map (algebraMap ℤ K)).Splits) :
    f.map (algebraMap ℤ (𝓞 K)) = ∏ x : f.rootSet K, (X - C (rootInteger f hm x)) := by
  classical
  apply Polynomial.map_injective _ (RingOfIntegers.coe_injective (K := K))
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ (𝓞 K) K]
  exact map_eq_prod_rootSet f hm hs hsp

lemma reduction_factorization {K k : Type*} [Field K] [CharZero K] [Field k]
    (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hsp : (f.map (algebraMap ℤ K)).Splits) (ρ : 𝓞 K →+* k) :
    f.map (Int.castRingHom k) = ∏ x : f.rootSet K, (X - C (ρ (rootInteger f hm x))) := by
  classical
  simpa only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_map, RingHom.eq_intCast'] using
      congrArg (Polynomial.map ρ) (map_eq_prod_rootInteger f hm hs hsp)

lemma reduction_injective {K k : Type*} [Field K] [CharZero K] [Field k]
    (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hsp : (f.map (algebraMap ℤ K)).Splits) (ρ : 𝓞 K →+* k)
    (hred : (f.map (Int.castRingHom k)).Separable) :
    Function.Injective (fun x : f.rootSet K => ρ (rootInteger f hm x)) := by
  rw [reduction_factorization f hm hs hsp ρ] at hred
  exact hred.injective_of_prod_X_sub_C

end DimensionTen

end
end

end OAI
