import Mathlib

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.IteratedSubdivision

section Linear

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

def eventuallyIn (s : Module.End R M) (P : Submodule R M) : Submodule R M where
  carrier := {x | ∃ N : ℕ, ∀ n, N ≤ n → (s ^ n) x ∈ P}
  zero_mem' := ⟨0, fun n _ => by simp⟩
  add_mem' := by
    rintro x y ⟨N, hN⟩ ⟨K, hK⟩
    refine ⟨max N K, fun n hn => ?_⟩
    simpa only [map_add] using P.add_mem
      (hN n ((le_max_left N K).trans hn))
      (hK n ((le_max_right N K).trans hn))
  smul_mem' := by
    rintro a x ⟨N, hN⟩
    exact ⟨N, fun n hn => by simpa only [map_smul] using P.smul_mem a (hN n hn)⟩

theorem pow_mem_of_mem (s : Module.End R M) (P : Submodule R M)
    (hP : ∀ x ∈ P, s x ∈ P) {x : M} (hx : x ∈ P) (n : ℕ) :
    (s ^ n) x ∈ P := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa only [pow_succ', Module.End.mul_apply] using hP ((s ^ n) x) ih

theorem mem_eventuallyIn_of_pow_mem (s : Module.End R M) (P : Submodule R M)
    (hP : ∀ x ∈ P, s x ∈ P) {x : M} {N : ℕ} (hx : (s ^ N) x ∈ P) :
    x ∈ eventuallyIn s P := by
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm N k]
  simpa only [pow_add, Module.End.mul_apply] using
    pow_mem_of_mem s P hP hx k

theorem finsupp_eventuallyIn {ι : Type*}
    (s : Module.End R (ι →₀ R)) (P : Submodule R (ι →₀ R))
    (hgen : ∀ i, Finsupp.single i 1 ∈ eventuallyIn s P)
    (c : ι →₀ R) : c ∈ eventuallyIn s P := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => exact (eventuallyIn s P).zero_mem
  | add f g hf hg => exact (eventuallyIn s P).add_mem hf hg
  | single i a =>
    simpa using (eventuallyIn s P).smul_mem a (hgen i)

theorem finsupp_exists_uniform_iteration {ι : Type*}
    (s : Module.End R (ι →₀ R)) (P : Submodule R (ι →₀ R))
    (hP : ∀ x ∈ P, s x ∈ P)
    (hgen : ∀ i, ∃ N : ℕ, (s ^ N) (Finsupp.single i 1) ∈ P)
    (c : ι →₀ R) : ∃ N : ℕ, ∀ n, N ≤ n → (s ^ n) c ∈ P := by
  apply finsupp_eventuallyIn s P _ c
  intro i
  obtain ⟨N, hN⟩ := hgen i
  exact mem_eventuallyIn_of_pow_mem s P hP hN

theorem finite_family_uniform_iteration {ι : Type*} (t : Finset ι)
    (s : Module.End R M) (P : Submodule R M) (z : ι → M)
    (hz : ∀ i ∈ t, z i ∈ eventuallyIn s P) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ i ∈ t, (s ^ n) (z i) ∈ P := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i t hi ih =>
    obtain ⟨N, hN⟩ := hz i (Finset.mem_insert_self i t)
    obtain ⟨K, hK⟩ := ih (fun j hj => hz j (Finset.mem_insert_of_mem hj))
    refine ⟨max N K, fun n hn j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hN n ((le_max_left N K).trans hn)
    · exact hK n ((le_max_right N K).trans hn) j hj

end Linear

section ChainHomotopy

variable {V : Type*} [Category V] [Preadditive V]
variable {ι : Type*} {c : ComplexShape ι} {C : HomologicalComplex V c}

def chainIterate (s : C ⟶ C) : ℕ → (C ⟶ C)
  | 0 => 𝟙 C
  | n + 1 => chainIterate s n ≫ s

def iterateHomotopy {s : C ⟶ C} (h : Homotopy s (𝟙 C)) :
    (n : ℕ) → Homotopy (chainIterate s n) (𝟙 C)
  | 0 => Homotopy.refl _
  | n + 1 => (h.compLeftId (chainIterate s n)).trans (iterateHomotopy h n)

theorem iterateHomotopy_hom {s : C ⟶ C} (h : Homotopy s (𝟙 C))
    (n : ℕ) (i j : ι) :
    (iterateHomotopy h n).hom i j =
      ∑ k ∈ Finset.range n, (chainIterate s k).f i ≫ h.hom i j := by
  induction n with
  | zero => simp [iterateHomotopy]
  | succ n ih =>
    simp [iterateHomotopy, Homotopy.compLeftId, ih, Finset.sum_range_succ,
      add_comm]

theorem chainIterate_eq_pow (s : C ⟶ C) (n : ℕ) :
    chainIterate s n = End.asHom ((End.of s) ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [chainIterate, ih, pow_succ', End.mul_def]

theorem homologyMap_chainIterate {s : C ⟶ C} (h : Homotopy s (𝟙 C))
    (n : ℕ) (i : ι) [C.HasHomology i] :
    HomologicalComplex.homologyMap (chainIterate s n) i = 𝟙 (C.homology i) := by
  rw [(iterateHomotopy h n).homologyMap_eq, HomologicalComplex.homologyMap_id]

end ChainHomotopy

section Support

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
variable {C : HomologicalComplex (ModuleCat R) c}

theorem chainIterate_f_hom (s : C ⟶ C) (n : ℕ) (i : ι) :
    ((chainIterate s n).f i).hom = ((s.f i).hom ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext x
    simp only [chainIterate, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, ih, pow_succ', Module.End.mul_apply]

theorem chainIterate_preserves (s : C ⟶ C) (P : ∀ i, Submodule R (C.X i))
    (hs : ∀ i x, x ∈ P i → (s.f i).hom x ∈ P i)
    (n : ℕ) (i : ι) {x : C.X i} (hx : x ∈ P i) :
    ((chainIterate s n).f i).hom x ∈ P i := by
  rw [chainIterate_f_hom]
  exact pow_mem_of_mem _ _ (hs i) hx n

theorem iterateHomotopy_preserves {s : C ⟶ C} (h : Homotopy s (𝟙 C))
    (P : ∀ i, Submodule R (C.X i))
    (hs : ∀ i x, x ∈ P i → (s.f i).hom x ∈ P i)
    (hh : ∀ i j x, x ∈ P i → (h.hom i j).hom x ∈ P j)
    (n : ℕ) (i j : ι) {x : C.X i} (hx : x ∈ P i) :
    ((iterateHomotopy h n).hom i j).hom x ∈ P j := by
  rw [iterateHomotopy_hom, ModuleCat.hom_sum, LinearMap.sum_apply]
  apply (P j).sum_mem
  intro k _
  change (h.hom i j).hom (((chainIterate s k).f i).hom x) ∈ P j
  exact hh i j _ (chainIterate_preserves s P hs k i hx)

end Support

end Problem340.IteratedSubdivision

end

end OAI
