import OAI.Analysis.Quantum.DimensionTen.Mod41Result
import OAI.Analysis.Quantum.DimensionTen.ModularPermutations

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma reduction_eq_131 {k : Type*} [Field k] [CharP k 131]
    (f : ℤ[X]) (h : f.map (Int.castRingHom (ZMod 131)) = Mod131.f X) :
    f.map (Int.castRingHom k) = Mod131.f X := by
  let φ := ZMod.castHom (dvd_refl 131) k
  have hmap : map φ (Mod131.f X) = Mod131.f X := by
    change mapRingHom φ (Mod131.f X) = _
    exact (Mod131.map_f (mapRingHom φ) X).trans (congrArg Mod131.f (map_X φ))
  have := congrArg (map φ) h
  rw [map_map] at this
  have he : φ.comp (Int.castRingHom (ZMod _)) = Int.castRingHom k := RingHom.eq_intCast' _
  rw [he] at this
  exact this.trans hmap

lemma reduction_eq_139 {k : Type*} [Field k] [CharP k 139]
    (f : ℤ[X]) (h : f.map (Int.castRingHom (ZMod 139)) = Mod139.f X) :
    f.map (Int.castRingHom k) = Mod139.f X := by
  let φ := ZMod.castHom (dvd_refl 139) k
  have hmap : map φ (Mod139.f X) = Mod139.f X := by
    change mapRingHom φ (Mod139.f X) = _
    exact (Mod139.map_f (mapRingHom φ) X).trans (congrArg Mod139.f (map_X φ))
  have := congrArg (map φ) h
  rw [map_map] at this
  have he : φ.comp (Int.castRingHom (ZMod _)) = Int.castRingHom k := RingHom.eq_intCast' _
  rw [he] at this
  exact this.trans hmap

lemma irr_rational_of_mod41 (f : ℤ[X]) (hm : f.Monic)
    (h : f.map (Int.castRingHom (ZMod 41)) = Mod41.f X) :
    Irreducible (f.map (algebraMap ℤ ℚ)) := by
  apply hm.irreducible_iff_irreducible_map_fraction_map.mp
  apply Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 41)) f hm
  rw [h]
  exact Mod41.irreducible_f

lemma roots_card_int {K : Type*} [Field K] [CharZero K]
    (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hp : (f.map (algebraMap ℤ K)).Splits) : Fintype.card (f.rootSet K) = f.natDegree := by
  classical
  have h := congrArg natDegree (map_eq_prod_rootSet f hm hs hp)
  rw [hm.natDegree_map, natDegree_prod _ _ (fun i _ => X_sub_C_ne_zero _)] at h
  simpa using h.symm

section Roots
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [DecidableEq K]
variable (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hp : (f.map (algebraMap ℤ K)).Splits)
    (hc : Fintype.card (f.rootSet K) = 20)

include hm hs hp hc in
lemma exists_swap_of_mod131
    (h131 : f.map (Int.castRingHom (ZMod 131)) = Mod131.f X) :
    ∃ σ : Gal(K/ℚ), (MulAction.toPerm (σ ^ 17) : Equiv.Perm (f.rootSet K)).IsSwap := by
  classical
  let : Fact (Nat.Prime 131) := ⟨by decide⟩
  obtain ⟨P, hP, hOver, σ, hσ⟩ := numberField_frobenius K 131
  let := hP
  let := hOver
  let k := 𝓞 K ⧸ P
  let : Field k := Ideal.Quotient.field P
  let : CharP k 131 := quotient_charP 131 P
  let ρ := Ideal.Quotient.mk P
  let r : f.rootSet K → k := fun x => ρ (rootInteger f hm x)
  let π : Equiv.Perm (f.rootSet K) := MulAction.toPerm σ
  have hred := reduction_eq_131 (k := k) f h131
  have hsep : (f.map (Int.castRingHom k)).Separable := by
    rw [hred]; exact Mod131.separable_f
  have hinj : Function.Injective r := reduction_injective f hm hs hp ρ hsep
  have hfact : f.map (Int.castRingHom k) = ∏ i, (X - C (r i)) :=
    reduction_factorization f hm hs hp ρ
  have h18 : Fintype.card {i : f.rootSet K // (π ^ 17) i = i} = 18 :=
    fixed_mod131 r hinj π (hred ▸ hfact) (fun i => root_reduction_frobenius f hm 131 P σ hσ i)
  refine ⟨σ, ?_⟩
  have ht := swap_of_card_fixed hc (π ^ 17) h18
  simpa only [π, ← MulAction.toPermHom_apply, ← map_pow] using ht

include hm hs hp hc in
lemma exists_nineteen_cycle_of_mod139
    (h139 : f.map (Int.castRingHom (ZMod 139)) = Mod139.f X) :
    ∃ σ : Gal(K/ℚ), (MulAction.toPerm σ : Equiv.Perm (f.rootSet K)).IsCycle ∧
      (MulAction.toPerm σ : Equiv.Perm (f.rootSet K)).support.card = 19 := by
  classical
  let : Fact (Nat.Prime 139) := ⟨by decide⟩
  obtain ⟨P, hP, hOver, σ, hσ⟩ := numberField_frobenius K 139
  let := hP
  let := hOver
  let k := 𝓞 K ⧸ P
  let : Field k := Ideal.Quotient.field P
  let : CharP k 139 := quotient_charP 139 P
  let ρ := Ideal.Quotient.mk P
  let r : f.rootSet K → k := fun x => ρ (rootInteger f hm x)
  let π : Equiv.Perm (f.rootSet K) := MulAction.toPerm σ
  have hred := reduction_eq_139 (k := k) f h139
  have hsep : (f.map (Int.castRingHom k)).Separable := by
    rw [hred]; exact Mod139.separable_f
  have hinj : Function.Injective r := reduction_injective f hm hs hp ρ hsep
  have hfact : Mod139.f X = ∏ i, (X - C (r i)) :=
    hred ▸ reduction_factorization f hm hs hp ρ
  have hfrob (i : f.rootSet K) : r (π i) = r i ^ 139 :=
    root_reduction_frobenius f hm 139 P σ hσ i
  have h1 : Fintype.card {i : f.rootSet K // π i = i} = 1 := by
    simpa only [pow_one] using fixed_mod139 r hinj π hfact hfrob
  exact ⟨σ, cycle_of_pow_eq_one_card_fixed hc π (pow_mod139 r hinj π hfact hfrob) h1⟩

include hm in
omit [IsGalois ℚ K] [DecidableEq K] in
lemma root_minpoly (hirr : Irreducible (f.map (algebraMap ℤ ℚ))) (x : f.rootSet K) :
    minpoly ℚ (x : K) = f.map (algebraMap ℤ ℚ) := by
  have hx : (aeval (x : K)) (f.map (algebraMap ℤ ℚ)) = 0 := by
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq ℤ ℚ K]
    exact (mem_rootSet.mp x.property).2
  have he := minpoly.eq_of_irreducible hirr hx
  simpa only [(hm.map (algebraMap ℤ ℚ)).leadingCoeff, inv_one, C_1, mul_one] using he.symm

include hm in
omit [DecidableEq K] in
lemma root_action_pretransitive (hirr : Irreducible (f.map (algebraMap ℤ ℚ))) :
    MulAction.IsPretransitive Gal(K/ℚ) (f.rootSet K) := by
  constructor
  intro x y
  have hh : minpoly ℚ (y : K) = minpoly ℚ (x : K) :=
    (root_minpoly f hm hirr y).trans (root_minpoly f hm hirr x).symm
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit K).mp hh
  exact ⟨σ, Subtype.ext hσ⟩

include hm hs hp hc in
lemma root_action_full_symmetric
    (h41 : f.map (Int.castRingHom (ZMod 41)) = Mod41.f X)
    (h131 : f.map (Int.castRingHom (ZMod 131)) = Mod131.f X)
    (h139 : f.map (Int.castRingHom (ZMod 139)) = Mod139.f X) :
    Function.Surjective (MulAction.toPermHom Gal(K/ℚ) (f.rootSet K)) := by
  classical
  let φ := MulAction.toPermHom Gal(K/ℚ) (f.rootSet K)
  let H := φ.range
  let : MulAction.IsPretransitive Gal(K/ℚ) (f.rootSet K) :=
    root_action_pretransitive f hm (irr_rational_of_mod41 f hm h41)
  let : MulAction.IsPretransitive H (f.rootSet K) := by
    constructor
    intro a b
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (M := Gal(K/ℚ)) a b
    exact ⟨⟨φ σ, ⟨σ, rfl⟩⟩, hσ⟩
  obtain ⟨σ, hσ, hcσ⟩ := exists_nineteen_cycle_of_mod139 f hm hs hp hc h139
  obtain ⟨τ, hτ⟩ := exists_swap_of_mod131 f hm hs hp hc h131
  have htop : H = ⊤ := full_symmetric_of_nineteen_cycle H hc (φ σ) ⟨σ, rfl⟩ hσ hcσ
    (φ (τ ^ 17)) ⟨τ ^ 17, rfl⟩ hτ
  exact MonoidHom.range_eq_top.mp htop

end Roots
end DimensionTen

end
end

end OAI
