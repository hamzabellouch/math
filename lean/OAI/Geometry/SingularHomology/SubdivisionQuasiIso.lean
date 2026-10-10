import OAI.Geometry.SingularHomology.HomologyCycle

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SubdivisionComparison

variable {R : Type*} [Ring R]

theorem exists_cycle_representative (S : ShortComplex (ModuleCat R))
    (v : S.homology) :
    ∃ z : S.X₂, ∃ hz : S.g.hom z = 0, moduleHomologyClass S z hz = v := by
  obtain ⟨z, hz⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective
    (S.moduleCatHomologyIso.toLinearEquiv v)
  refine ⟨z.1, z.2, ?_⟩
  apply S.moduleCatHomologyIso.toLinearEquiv.injective
  unfold moduleHomologyClass
  erw [LinearEquiv.apply_symm_apply]
  change (LinearMap.range S.moduleCatToCycles).mkQ z = _
  exact hz

theorem map_cycle {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (z : S.X₂) (hz : S.g.hom z = 0) : T.g.hom (φ.τ₂.hom z) = 0 := by
  have h := congrArg (fun k : S.X₂ ⟶ T.X₃ => k.hom z) φ.comm₂₃
  change T.g.hom (φ.τ₂.hom z) = φ.τ₃.hom (S.g.hom z) at h
  simpa only [hz, map_zero] using h

theorem reflect_cycle {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (hφ : Function.Injective φ.τ₃.hom) (z : S.X₂)
    (hz : T.g.hom (φ.τ₂.hom z) = 0) : S.g.hom z = 0 := by
  apply hφ
  have h := congrArg (fun k : S.X₂ ⟶ T.X₃ => k.hom z) φ.comm₂₃
  change T.g.hom (φ.τ₂.hom z) = φ.τ₃.hom (S.g.hom z) at h
  simpa only [map_zero] using h.symm.trans hz

theorem class_map_eq_class {S : ShortComplex (ModuleCat R)} (s : S ⟶ S)
    (hs : ShortComplex.homologyMap s = 𝟙 S.homology)
    (z : S.X₂) (hz : S.g.hom z = 0) :
    moduleHomologyClass S (s.τ₂.hom z) (map_cycle s z hz) =
      moduleHomologyClass S z hz := by
  rw [← moduleHomologyClass_map s z hz (map_cycle s z hz), hs]
  rfl

theorem homologyMap_bijective_of_eventual_range
    {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (hinj₂ : Function.Injective φ.τ₂.hom)
    (hinj₃ : Function.Injective φ.τ₃.hom)
    (s : ℕ → (T ⟶ T)) (t : ℕ → (S ⟶ S))
    (hcomm : ∀ k, φ ≫ s k = t k ≫ φ)
    (hs : ∀ k, ShortComplex.homologyMap (s k) = 𝟙 T.homology)
    (ht : ∀ k, ShortComplex.homologyMap (t k) = 𝟙 S.homology)
    (hsmall₁ : ∀ y : T.X₁, ∃ k, ∃ x : S.X₁,
      (s k).τ₁.hom y = φ.τ₁.hom x)
    (hsmall₂ : ∀ y : T.X₂, ∃ k, ∃ x : S.X₂,
      (s k).τ₂.hom y = φ.τ₂.hom x) :
    Function.Bijective (ShortComplex.homologyMap φ).hom := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    obtain ⟨z, hz, rfl⟩ := exists_cycle_representative S v
    rw [moduleHomologyClass_map φ z hz (map_cycle φ z hz)] at hv
    obtain ⟨y, hy⟩ := (moduleHomologyClass_eq_zero_iff T
      (φ.τ₂.hom z) (map_cycle φ z hz)).mp hv
    obtain ⟨k, x, hx⟩ := hsmall₁ y
    have hb : S.f.hom x = (t k).τ₂.hom z := by
      apply hinj₂
      have hφ := congrArg (fun f : S.X₁ ⟶ T.X₂ => f.hom x) φ.comm₁₂
      have hs' := congrArg (fun f : T.X₁ ⟶ T.X₂ => f.hom y) (s k).comm₁₂
      have hc := congrArg (fun f : S ⟶ T => f.τ₂.hom z) (hcomm k)
      change T.f.hom (φ.τ₁.hom x) = φ.τ₂.hom (S.f.hom x) at hφ
      change T.f.hom ((s k).τ₁.hom y) = (s k).τ₂.hom (T.f.hom y) at hs'
      change (s k).τ₂.hom (φ.τ₂.hom z) = φ.τ₂.hom ((t k).τ₂.hom z) at hc
      calc
        φ.τ₂.hom (S.f.hom x) = T.f.hom (φ.τ₁.hom x) := hφ.symm
        _ = T.f.hom ((s k).τ₁.hom y) := congrArg T.f.hom hx.symm
        _ = (s k).τ₂.hom (T.f.hom y) := hs'
        _ = (s k).τ₂.hom (φ.τ₂.hom z) := congrArg (s k).τ₂.hom hy
        _ = φ.τ₂.hom ((t k).τ₂.hom z) := hc
    have hzero := (moduleHomologyClass_eq_zero_iff S
      ((t k).τ₂.hom z) (map_cycle (t k) z hz)).mpr ⟨x, hb⟩
    rw [class_map_eq_class (t k) (ht k) z hz] at hzero
    exact hzero
  · intro v
    obtain ⟨z, hz, rfl⟩ := exists_cycle_representative T v
    obtain ⟨k, x, hx⟩ := hsmall₂ z
    have hφx : T.g.hom (φ.τ₂.hom x) = 0 := by
      rw [← hx]
      exact map_cycle (s k) z hz
    have hxc : S.g.hom x = 0 := reflect_cycle φ hinj₃ x hφx
    refine ⟨moduleHomologyClass S x hxc, ?_⟩
    rw [moduleHomologyClass_map φ x hxc hφx]
    have hclass := class_map_eq_class (s k) (hs k) z hz
    simpa only [hx] using hclass

section Complexes

variable {ι : Type*} {c : ComplexShape ι}
  {C D : HomologicalComplex (ModuleCat R) c}

theorem quasiIso_of_eventual_range
    (φ : C ⟶ D) (hinj : ∀ n, Function.Injective (φ.f n).hom)
    (s : ℕ → (D ⟶ D)) (t : ℕ → (C ⟶ C))
    (hcomm : ∀ k, φ ≫ s k = t k ≫ φ)
    (hs : ∀ k n, HomologicalComplex.homologyMap (s k) n = 𝟙 (D.homology n))
    (ht : ∀ k n, HomologicalComplex.homologyMap (t k) n = 𝟙 (C.homology n))
    (hsmall : ∀ n (y : D.X n), ∃ k, ∃ x : C.X n,
      ((s k).f n).hom y = (φ.f n).hom x) : QuasiIso φ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  let F := HomologicalComplex.shortComplexFunctor (ModuleCat R) c n
  apply homologyMap_bijective_of_eventual_range (F.map φ)
    (hinj n) (hinj (c.next n)) (fun k => F.map (s k)) (fun k => F.map (t k))
  · intro k
    simpa only [Functor.map_comp] using congrArg F.map (hcomm k)
  · exact fun k => hs k n
  · exact fun k => ht k n
  · exact hsmall (c.prev n)
  · exact hsmall n

theorem quasiIso_of_homotopy_eventual_range
    (φ : C ⟶ D) (hinj : ∀ n, Function.Injective (φ.f n).hom)
    (s : ℕ → (D ⟶ D)) (t : ℕ → (C ⟶ C))
    (hcomm : ∀ k, φ ≫ s k = t k ≫ φ)
    (hs : ∀ k, Homotopy (s k) (𝟙 D))
    (ht : ∀ k, Homotopy (t k) (𝟙 C))
    (hsmall : ∀ n (y : D.X n), ∃ k, ∃ x : C.X n,
      ((s k).f n).hom y = (φ.f n).hom x) : QuasiIso φ := by
  apply quasiIso_of_eventual_range φ hinj s t hcomm
  · intro k n
    exact ((hs k).homologyMap_eq n).trans (HomologicalComplex.homologyMap_id D n)
  · intro k n
    exact ((ht k).homologyMap_eq n).trans (HomologicalComplex.homologyMap_id C n)
  · exact hsmall

theorem intertwines_pow (φ : C ⟶ D) (s : End D) (t : End C)
    (hcomm : φ ≫ s = t ≫ φ) (k : ℕ) :
    φ ≫ (s ^ k).asHom = (t ^ k).asHom ≫ φ := by
  induction k with
  | zero => simp
  | succ k hk =>
    simp only [pow_succ, End.mul_def, End.asHom]
    rw [← Category.assoc, hcomm, Category.assoc, hk, Category.assoc]

theorem homologyMap_pow_eq_id (s : End C) (hs : Homotopy s (𝟙 C))
    (k : ℕ) (n : ι) :
    HomologicalComplex.homologyMap (s ^ k).asHom n = 𝟙 (C.homology n) := by
  have hs' := (hs.homologyMap_eq n).trans (HomologicalComplex.homologyMap_id C n)
  induction k with
  | zero => simpa only [pow_zero, End.one_def] using HomologicalComplex.homologyMap_id C n
  | succ k hk =>
    simp only [pow_succ, End.mul_def, End.asHom,
      HomologicalComplex.homologyMap_comp, hs', hk, Category.id_comp]

theorem quasiIso_of_eventual_iterate_range
    (φ : C ⟶ D) (hinj : ∀ n, Function.Injective (φ.f n).hom)
    (s : End D) (t : End C) (hcomm : φ ≫ s = t ≫ φ)
    (hs : Homotopy s (𝟙 D)) (ht : Homotopy t (𝟙 C))
    (hsmall : ∀ n (y : D.X n), ∃ k, ∃ x : C.X n,
      ((s ^ k).asHom.f n).hom y = (φ.f n).hom x) : QuasiIso φ := by
  exact quasiIso_of_eventual_range φ hinj
    (fun k => (s ^ k).asHom) (fun k => (t ^ k).asHom)
    (intertwines_pow φ s t hcomm)
    (homologyMap_pow_eq_id s hs) (homologyMap_pow_eq_id t ht) hsmall

end Complexes

end Problem340.SubdivisionComparison

end

end OAI
