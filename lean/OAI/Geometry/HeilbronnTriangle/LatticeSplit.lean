import Mathlib

namespace OAI

namespace Problem355.LatticeSplit
open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def kernelProdEquiv (f : M →ₗ[R] R) (u : M) (hu : f u = 1) :
    M ≃ₗ[R] (LinearMap.ker f) × R where
  toFun x := (⟨x - f x • u, by simp [LinearMap.mem_ker, hu]⟩, f x)
  invFun p := (p.1 : M) + p.2 • u
  left_inv x := sub_add_cancel x (f x • u)
  right_inv p := by
    rcases p with ⟨⟨w, hw⟩, t⟩
    have hw' : f w = 0 := hw
    ext <;> simp [hw', hu]
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - f (x + y) • u = (x - f x • u) + (y - f y • u)
      simp only [map_add, add_smul]
      abel
    · exact f.map_add x y
  map_smul' a x := by
    ext <;> simp [smul_sub, smul_smul]

@[simp] theorem kernelProdEquiv_snd (f : M →ₗ[R] R) (u : M) (hu : f u = 1)
    (x : M) : (kernelProdEquiv f u hu x).2 = f x := rfl

@[simp] theorem kernelProdEquiv_fst_coe (f : M →ₗ[R] R) (u : M) (hu : f u = 1)
    (x : M) : ((kernelProdEquiv f u hu x).1 : M) = x - f x • u := rfl

@[simp] theorem kernelProdEquiv_symm_apply (f : M →ₗ[R] R) (u : M)
    (hu : f u = 1) (p : LinearMap.ker f × R) :
    (kernelProdEquiv f u hu).symm p = (p.1 : M) + p.2 • u := rfl

theorem existsUnique_kernel_component (f : M →ₗ[R] R) (u : M) (hu : f u = 1)
    (x : M) : ∃! w : LinearMap.ker f, x = (w : M) + f x • u := by
  refine ⟨(kernelProdEquiv f u hu x).1, ?_, ?_⟩
  · simp
  · intro w hw
    apply Subtype.ext
    change (w : M) = x - f x • u
    exact eq_sub_iff_add_eq.mpr hw.symm

noncomputable def extendKernelBasis {ι : Type*} (f : M →ₗ[R] R) (u : M) (hu : f u = 1)
    (b : Basis ι R (LinearMap.ker f)) : Basis (ι ⊕ Unit) R M :=
  (b.prod (Basis.singleton Unit R)).map (kernelProdEquiv f u hu).symm

@[simp] theorem extendKernelBasis_inl {ι : Type*} (f : M →ₗ[R] R)
    (u : M) (hu : f u = 1) (b : Basis ι R (LinearMap.ker f)) (i : ι) :
    extendKernelBasis f u hu b (Sum.inl i) = (b i : M) := by
  simp [extendKernelBasis]

@[simp] theorem extendKernelBasis_inr {ι : Type*} (f : M →ₗ[R] R)
    (u : M) (hu : f u = 1) (b : Basis ι R (LinearMap.ker f)) (i : Unit) :
    extendKernelBasis f u hu b (Sum.inr i) = u := by
  simp [extendKernelBasis]

@[simp] theorem extendKernelBasis_repr_inr {ι : Type*} (f : M →ₗ[R] R)
    (u : M) (hu : f u = 1) (b : Basis ι R (LinearMap.ker f))
    (x : M) (i : Unit) :
    (extendKernelBasis f u hu b).repr x (Sum.inr i) = f x := by
  simp [extendKernelBasis]

def restrictedKernelEquiv (L : Submodule R M) (f : M →ₗ[R] R) :
    LinearMap.ker (f.comp L.subtype) ≃ₗ[R] ↥(L ⊓ LinearMap.ker f) where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictedKernelEquiv_apply_coe
    (L : Submodule R M) (f : M →ₗ[R] R)
    (x : LinearMap.ker (f.comp L.subtype)) :
    (restrictedKernelEquiv L f x : M) = x.1 := rfl

variable {A : Type*} [AddCommGroup A]

def divideIntFunctional (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hdiv : ∀ x, g ∣ f x) :
    A →ₗ[ℤ] ℤ where
  toFun x := f x / g
  map_add' x y := by
    simp only [map_add]
    exact Int.add_ediv_of_dvd_left (hdiv x)
  map_smul' a x := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    exact Int.mul_ediv_assoc a (hdiv x)

@[simp] theorem divideIntFunctional_apply (f : A →ₗ[ℤ] ℤ) (g : ℤ)
    (hdiv : ∀ x, g ∣ f x) (x : A) :
    divideIntFunctional f g hdiv x = f x / g := rfl

theorem ker_divideIntFunctional (f : A →ₗ[ℤ] ℤ) (g : ℤ)
    (hdiv : ∀ x, g ∣ f x) :
    LinearMap.ker (divideIntFunctional f g hdiv) = LinearMap.ker f := by
  ext x
  simp only [LinearMap.mem_ker, divideIntFunctional_apply]
  constructor
  · intro hx
    have h := Int.ediv_mul_cancel (hdiv x)
    rw [hx, zero_mul] at h
    exact h.symm
  · intro hx
    simp [hx]

def integerKernelProdEquiv (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0)
    (hdiv : ∀ x, g ∣ f x) (u : A) (hu : f u = g) :
    A ≃ₗ[ℤ] (LinearMap.ker f) × ℤ where
  toFun x := (⟨x - (f x / g) • u, by
    simp only [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, hu]
    exact sub_eq_zero.mpr (Int.ediv_mul_cancel (hdiv x)).symm⟩, f x / g)
  invFun p := (p.1 : A) + p.2 • u
  left_inv x := sub_add_cancel x ((f x / g) • u)
  right_inv p := by
    rcases p with ⟨⟨w, hw⟩, t⟩
    have hw' : f w = 0 := hw
    have ht : f (w + t • u) / g = t := by
      simp only [map_add, map_smul, hw', hu, smul_eq_mul, zero_add]
      rw [mul_comm, Int.mul_ediv_cancel_left _ hg]
    apply Prod.ext
    · apply Subtype.ext
      change w + t • u - (f (w + t • u) / g) • u = w
      rw [ht]
      abel
    · exact ht
  map_add' x y := by
    have h := (divideIntFunctional f g hdiv).map_add x y
    change (f (x + y) / g) = (f x / g) + (f y / g) at h
    apply Prod.ext
    · apply Subtype.ext
      change x + y - (f (x + y) / g) • u =
        (x - (f x / g) • u) + (y - (f y / g) • u)
      rw [h, add_smul]
      abel
    · exact h
  map_smul' a x := by
    have h := (divideIntFunctional f g hdiv).map_smul a x
    change (f (a • x) / g) = a * (f x / g) at h
    apply Prod.ext
    · apply Subtype.ext
      change a • x - (f (a • x) / g) • u = a • (x - (f x / g) • u)
      rw [h, smul_sub, smul_smul]
    · exact h

@[simp] theorem integerKernelProdEquiv_snd
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (x : A) :
    (integerKernelProdEquiv f g hg hdiv u hu x).2 = f x / g := rfl

@[simp] theorem integerKernelProdEquiv_fst_coe
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (x : A) :
    ((integerKernelProdEquiv f g hg hdiv u hu x).1 : A) = x - (f x / g) • u := rfl

@[simp] theorem integerKernelProdEquiv_symm_apply
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (p : LinearMap.ker f × ℤ) :
    (integerKernelProdEquiv f g hg hdiv u hu).symm p = (p.1 : A) + p.2 • u := rfl

noncomputable def extendIntegerKernelBasis {ι : Type*}
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (b : Basis ι ℤ (LinearMap.ker f)) :
    Basis (ι ⊕ Unit) ℤ A :=
  (b.prod (Basis.singleton Unit ℤ)).map (integerKernelProdEquiv f g hg hdiv u hu).symm

@[simp] theorem extendIntegerKernelBasis_inl {ι : Type*}
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (b : Basis ι ℤ (LinearMap.ker f)) (i : ι) :
    extendIntegerKernelBasis f g hg hdiv u hu b (Sum.inl i) = (b i : A) := by
  simp [extendIntegerKernelBasis]

@[simp] theorem extendIntegerKernelBasis_inr {ι : Type*}
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (b : Basis ι ℤ (LinearMap.ker f)) (i : Unit) :
    extendIntegerKernelBasis f g hg hdiv u hu b (Sum.inr i) = u := by
  simp [extendIntegerKernelBasis]

@[simp] theorem extendIntegerKernelBasis_repr_inr {ι : Type*}
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (b : Basis ι ℤ (LinearMap.ker f))
    (x : A) (i : Unit) :
    (extendIntegerKernelBasis f g hg hdiv u hu b).repr x (Sum.inr i) = f x / g := by
  simp [extendIntegerKernelBasis]

theorem exists_positive_image_generator (f : A →ₗ[ℤ] ℤ) (hf : f ≠ 0) :
    ∃ g : ℤ, 0 < g ∧ (∀ x, g ∣ f x) ∧ ∃ u : A, f u = g := by
  let g := Submodule.IsPrincipal.generator (LinearMap.range f)
  have hdiv : ∀ x, g ∣ f x := fun x =>
    (Submodule.IsPrincipal.mem_iff_generator_dvd (LinearMap.range f)).mp ⟨x, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, f u = g := Submodule.IsPrincipal.generator_mem (LinearMap.range f)
  have hg : g ≠ 0 := by
    intro hg
    apply hf
    ext x
    have h := hdiv x
    simpa [hg] using h
  by_cases hpos : 0 < g
  · exact ⟨g, hpos, hdiv, u, hu⟩
  · refine ⟨-g, by omega, ?_, -u, ?_⟩
    · intro x
      simpa only [neg_dvd] using hdiv x
    · simp [hu]

theorem finrank_kernel_add_one [Module.Free ℤ A] [Module.Finite ℤ A]
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) :
    Module.finrank ℤ (LinearMap.ker f) + 1 = Module.finrank ℤ A := by
  have h := (integerKernelProdEquiv f g hg hdiv u hu).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_self] using h.symm

noncomputable def integerKernelBasisFin [Module.Free ℤ A] [Module.Finite ℤ A]
    (f : A →ₗ[ℤ] ℤ) (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : A) (hu : f u = g) (n : ℕ) (hdim : Module.finrank ℤ A = n + 1) :
    Basis (Fin n) ℤ (LinearMap.ker f) := by
  apply Module.finBasisOfFinrankEq
  have h := finrank_kernel_add_one f g hg hdiv u hu
  omega

theorem finrank_kernel_add_one_of_ne_zero [Module.Free ℤ A] [Module.Finite ℤ A]
    (f : A →ₗ[ℤ] ℤ) (hf : f ≠ 0) :
    Module.finrank ℤ (LinearMap.ker f) + 1 = Module.finrank ℤ A := by
  obtain ⟨g, hg, hdiv, u, hu⟩ := exists_positive_image_generator f hf
  exact finrank_kernel_add_one f g (ne_of_gt hg) hdiv u hu

theorem exists_plane_kernel_basis (f : (Fin 3 → ℤ) →ₗ[ℤ] ℤ) (hf : f ≠ 0) :
    Nonempty (Basis (Fin 2) ℤ (LinearMap.ker f)) := by
  obtain ⟨g, hg, hdiv, u, hu⟩ := exists_positive_image_generator f hf
  exact ⟨integerKernelBasisFin f g (ne_of_gt hg) hdiv u hu 2 (by simp)⟩

theorem finrank_eq_of_scalar_containment [Module.Free ℤ A] [Module.Finite ℤ A]
    (L : Submodule ℤ A) (E : ℤ) (hE : E ≠ 0) (hEL : ∀ x : A, E • x ∈ L) :
    Module.finrank ℤ L = Module.finrank ℤ A := by
  let j : A →ₗ[ℤ] L := (LinearMap.lsmul ℤ A E).codRestrict L hEL
  have hj : Function.Injective j := by
    intro x y h
    apply LinearMap.lsmul_injective hE
    exact congrArg Subtype.val h
  exact le_antisymm L.finrank_le (LinearMap.finrank_le_finrank_of_injective hj)

theorem index_ne_zero_of_scalar_containment [Module.Free ℤ A] [Module.Finite ℤ A]
    (L : Submodule ℤ A) (E : ℤ) (hE : E ≠ 0) (hEL : ∀ x : A, E • x ∈ L) :
    L.toAddSubgroup.index ≠ 0 := by
  let := L.finiteQuotientOfFreeOfRankEq (finrank_eq_of_scalar_containment L E hE hEL)
  change Nat.card (A ⧸ L) ≠ 0
  exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩

theorem exists_restricted_image_generator
    (L : Submodule ℤ A) (E : ℤ) (hE : E ≠ 0) (hEL : ∀ x : A, E • x ∈ L)
    (f : A →ₗ[ℤ] ℤ) (z : A) (hz : f z = 1) :
    ∃ g : ℤ, 0 < g ∧ g ∣ E ∧ (∀ v : L, g ∣ f v) ∧ ∃ u : L, f u = g := by
  let fr : L →ₗ[ℤ] ℤ := f.comp L.subtype
  let w : L := ⟨E • z, hEL z⟩
  have hw : fr w = E := by
    change f (E • z) = E
    simp [hz]
  have hf : fr ≠ 0 := by
    intro h
    apply hE
    simpa only [hw, LinearMap.zero_apply] using LinearMap.congr_fun h w
  obtain ⟨g, hg, hdiv, u, hu⟩ := exists_positive_image_generator fr hf
  refine ⟨g, hg, ?_, hdiv, u, hu⟩
  simpa only [hw] using hdiv w

theorem exists_restricted_kernel_basis [Module.Free ℤ A] [Module.Finite ℤ A]
    (L : Submodule ℤ A) (E : ℤ) (hE : E ≠ 0) (hEL : ∀ x : A, E • x ∈ L)
    (f : A →ₗ[ℤ] ℤ) (z : A) (hz : f z = 1)
    (n : ℕ) (hdim : Module.finrank ℤ A = n + 1) :
    Nonempty (Basis (Fin n) ℤ (LinearMap.ker (f.comp L.subtype))) := by
  obtain ⟨g, hg, _, hdiv, u, hu⟩ := exists_restricted_image_generator L E hE hEL f z hz
  exact ⟨integerKernelBasisFin (f.comp L.subtype) g (ne_of_gt hg) hdiv u hu n
    ((finrank_eq_of_scalar_containment L E hE hEL).trans hdim)⟩

end Problem355.LatticeSplit

end OAI
