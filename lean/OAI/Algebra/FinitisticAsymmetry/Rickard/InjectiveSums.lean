import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard
universe u v
variable {R : Type u} [Ring R] {ι : Type v}
variable (Q : ι → Type u) [∀ i, AddCommGroup (Q i)] [∀ i, Module R (Q i)]

lemma finite_support_map (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (g : M →ₗ[R] Π₀ i, Q i) : ∃ s : Finset ι, ∀ x i, i ∉ s → g x i = 0 := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let s := Finset.univ.biUnion (fun j : Fin n => (g (f (Pi.single j 1))).support)
  refine ⟨s, ?_⟩
  intro x i hi
  obtain ⟨v, rfl⟩ := hf x
  have hv : ∑ j : Fin n, v j • Pi.single j (1 : R) = v := by
    ext j
    simp [Pi.single_apply, smul_eq_mul]
  have hz (j : Fin n) : (g (f (Pi.single j 1))) i = 0 := by
    apply DFinsupp.notMem_support_iff.mp
    intro h
    apply hi
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, h⟩
  rw [← hv, map_sum, map_sum]
  change (DFinsupp.lapply (R := R) i) (∑ j, g (f (v j • Pi.single j 1))) = 0
  rw [map_sum]
  simp only [map_smul, DFinsupp.lapply_apply, hz, smul_zero, Finset.sum_const_zero]

lemma dfinsupp_injective [IsNoetherianRing R] [∀ i, Module.Injective R (Q i)] :
    Module.Injective R (Π₀ i, Q i) := by
  classical
  apply Module.Baer.injective
  intro I g
  obtain ⟨s, hs⟩ := finite_support_map Q I g
  have he (i : ι) : ∃ f : R →ₗ[R] Q i, ∀ (x : R) (hx : x ∈ I),
      f x = g ⟨x,hx⟩ i :=
    Module.Baer.of_injective (inferInstance : Module.Injective R (Q i)) I
      ((DFinsupp.lapply i).comp g)
  choose f hf using he
  refine ⟨∑ i ∈ s, (DFinsupp.lsingle i).comp (f i), ?_⟩
  intro x hx
  apply DFinsupp.ext
  intro j
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, DFinsupp.lsingle_apply]
  by_cases hj : j ∈ s
  · simpa [DFinsupp.single_apply, hj] using hf j x hx
  · simp [DFinsupp.single_apply, hj, hs _ _ hj]

lemma dfinsupp_injective_object [IsNoetherianRing R]
    (hQ : ∀ i, Injective (ModuleCat.of R (Q i))) :
    Injective (ModuleCat.of R (Π₀ i, Q i)) := by
  let (index : ι) : Module.Injective R (Q index) :=
    (Module.injective_iff_injective_object R (Q index)).mpr (hQ index)
  let := dfinsupp_injective (R := R) Q
  exact Module.injective_object_of_injective_module R _

lemma prod_injective (M N : Type u) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Injective R M] [Module.Injective R N] :
    Module.Injective R (M × N) := by
  constructor
  intro X Y _ _ _ _ f hf g
  obtain ⟨a, ha⟩ := Module.Injective.out f hf ((LinearMap.fst R M N).comp g)
  obtain ⟨b, hb⟩ := Module.Injective.out f hf ((LinearMap.snd R M N).comp g)
  exact ⟨a.prod b, fun x => Prod.ext (ha x) (hb x)⟩

end LittleFinitistic.Rickard

end

end OAI
