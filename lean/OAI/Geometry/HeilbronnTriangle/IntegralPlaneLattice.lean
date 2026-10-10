import Mathlib

namespace OAI


noncomputable section

namespace Problem355.IntegralPlaneLattice

open Module Matrix

abbrev Ambient := EuclideanSpace ℝ (Fin 3)

def stdBasis : Basis (Fin 3) ℝ Ambient := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

def standardLattice : Submodule ℤ Ambient := Submodule.span ℤ (Set.range stdBasis)

instance : DiscreteTopology standardLattice := by
  unfold standardLattice
  infer_instance

def castVec (x : Fin 3 → ℤ) : Ambient := WithLp.toLp 2 (fun i => (x i : ℝ))

@[simp] lemma castVec_apply (x : Fin 3 → ℤ) (i : Fin 3) : castVec x i = (x i : ℝ) := rfl

lemma stdBasis_repr (v : Ambient) (i : Fin 3) : stdBasis.repr v i = v i := rfl

lemma mem_standardLattice (v : Ambient) :
    v ∈ standardLattice ↔ ∀ i, ∃ z : ℤ, (z : ℝ) = v i := by
  change v ∈ Submodule.span ℤ (Set.range stdBasis) ↔ _
  rw [stdBasis.mem_span_iff_repr_mem ℤ v]
  simp [stdBasis_repr]

lemma castVec_mem (x : Fin 3 → ℤ) : castVec x ∈ standardLattice :=
  (mem_standardLattice _).mpr (fun i => ⟨x i, rfl⟩)

def realDot (x : Fin 3 → ℤ) : Ambient →ₗ[ℝ] ℝ where
  toFun v := ∑ i, (x i : ℝ) * v i
  map_add' v w := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' t v := by simp [Finset.mul_sum, mul_left_comm]

@[simp] lemma realDot_apply (x : Fin 3 → ℤ) (v : Ambient) :
    realDot x v = ∑ i, (x i : ℝ) * v i := rfl

@[simp] lemma realDot_castVec (x z : Fin 3 → ℤ) :
    realDot x (castVec z) = (x ⬝ᵥ z : ℤ) := by
  simp [realDot, castVec, dotProduct]

def plane (x : Fin 3 → ℤ) : Submodule ℝ Ambient := (realDot x).ker

def lattice (x : Fin 3 → ℤ) : Submodule ℤ (plane x) :=
  standardLattice.comap ((plane x).subtype.restrictScalars ℤ)

instance lattice_discrete (x : Fin 3 → ℤ) : DiscreteTopology (lattice x) := by
  let : DiscreteTopology (standardLattice : Set Ambient) :=
    inferInstanceAs (DiscreteTopology standardLattice)
  exact DiscreteTopology.preimage_of_continuous_injective (standardLattice : Set Ambient)
    (LinearMap.continuous_of_finiteDimensional (plane x).subtype) (Submodule.injective_subtype _)

lemma realDot_stdBasis (x : Fin 3 → ℤ) (i : Fin 3) : realDot x (stdBasis i) = (x i : ℝ) := by
  simp [realDot, stdBasis, EuclideanSpace.basisFun_apply]

def projection (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) : Ambient →ₗ[ℝ] plane x :=
  (LinearMap.id - (realDot x).smulRight (castVec z)).codRestrict (plane x) (by
    intro v
    change realDot x (v - realDot x v • castVec z) = 0
    rw [map_sub, map_smul, realDot_castVec, hz]
    simp)

lemma projection_apply (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) (v : Ambient) :
    (projection x z hz v : Ambient) = v - realDot x v • castVec z := rfl

lemma projection_on_plane (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) (v : plane x) :
    projection x z hz v = v := by
  apply Subtype.ext
  change (v : Ambient) - realDot x v • castVec z = v
  have hv : realDot x v = 0 := v.property
  simp [hv]

lemma projection_basis_mem (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) (i : Fin 3) :
    projection x z hz (stdBasis i) ∈ lattice x := by
  change stdBasis i - realDot x (stdBasis i) • castVec z ∈ standardLattice
  rw [realDot_stdBasis]
  apply standardLattice.sub_mem
  · exact Submodule.subset_span ⟨i, rfl⟩
  · rw [Int.cast_smul_eq_zsmul ℝ]
    exact standardLattice.smul_mem _ (castVec_mem z)

lemma lattice_spans (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) :
    Submodule.span ℝ (lattice x : Set (plane x)) = ⊤ := by
  apply top_unique
  intro v hv
  rw [← projection_on_plane x z hz v, ← stdBasis.sum_repr (v : Ambient), map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (projection_basis_mem x z hz i))

lemma isZLattice (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) : IsZLattice ℝ (lattice x) :=
  ⟨lattice_spans x z hz⟩

lemma plane_finrank (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) :
    finrank ℝ (plane x) = 2 := by
  have hn : realDot x ≠ 0 := by
    intro h
    have he := LinearMap.congr_fun h (castVec z)
    change realDot x (castVec z) = 0 at he
    rw [realDot_castVec, hz] at he
    norm_num at he
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  change finrank ℝ (plane x) + 1 = finrank ℝ Ambient at h
  norm_num [Ambient] at h
  omega

lemma lattice_finrank (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) :
    finrank ℤ (lattice x) = 2 := by
  let := isZLattice x z hz
  rw [ZLattice.rank ℝ (lattice x), plane_finrank x z hz]

def basis (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) : Basis (Fin 2) ℤ (lattice x) := by
  letI := isZLattice x z hz
  exact (Module.finBasis ℤ (lattice x)).reindex (finCongr (lattice_finrank x z hz))

def integerDot (x : Fin 3 → ℤ) : (Fin 3 → ℤ) →ₗ[ℤ] ℤ where
  toFun v := x ⬝ᵥ v
  map_add' v w := by simp [dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' t v := by simp [dotProduct, Finset.mul_sum, mul_left_comm]

def integerPlane (x : Fin 3 → ℤ) : Submodule ℤ (Fin 3 → ℤ) := (integerDot x).ker

def kernelMap (x : Fin 3 → ℤ) : integerPlane x →ₗ[ℤ] lattice x where
  toFun v := ⟨⟨castVec v, by
    change realDot x (castVec v) = 0
    rw [realDot_castVec]
    have hv : x ⬝ᵥ (v : Fin 3 → ℤ) = 0 := v.property
    exact_mod_cast hv⟩, castVec_mem v⟩
  map_add' v w := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    simp [castVec]
  map_smul' t v := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    simp [castVec]

lemma kernelMap_injective (x : Fin 3 → ℤ) : Function.Injective (kernelMap x) := by
  intro u v h
  apply Subtype.ext
  funext i
  have he := congrArg (fun w : lattice x => ((w : plane x) : Ambient) i) h
  change (u.val i : ℝ) = (v.val i : ℝ) at he
  exact_mod_cast he

lemma kernelMap_surjective (x : Fin 3 → ℤ) : Function.Surjective (kernelMap x) := by
  intro y
  have hy : ((y : plane x) : Ambient) ∈ standardLattice := y.property
  choose z hz using (mem_standardLattice _).mp hy
  have he : castVec z = ((y : plane x) : Ambient) := by
    ext i
    exact hz i
  have hzker : z ∈ integerPlane x := by
    have hyker : realDot x ((y : plane x) : Ambient) = 0 := (y : plane x).property
    rw [← he, realDot_castVec] at hyker
    change x ⬝ᵥ z = 0
    exact_mod_cast hyker
  refine ⟨⟨z, hzker⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact he

def kernelEquiv (x : Fin 3 → ℤ) : integerPlane x ≃ₗ[ℤ] lattice x :=
  LinearEquiv.ofBijective (kernelMap x) ⟨kernelMap_injective x, kernelMap_surjective x⟩

def integerBasis (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) :
    Basis (Fin 2) ℤ (integerPlane x) := (basis x z hz).map (kernelEquiv x).symm

def castLinear : (Fin 3 → ℤ) →ₗ[ℤ] Ambient where
  toFun := castVec
  map_add' v w := by ext i; simp [castVec]
  map_smul' t v := by ext i; simp [castVec]

def realLattice (L : Submodule ℤ (Fin 3 → ℤ)) : Submodule ℤ Ambient := L.map castLinear

lemma realLattice_le_standard (L : Submodule ℤ (Fin 3 → ℤ)) :
    realLattice L ≤ standardLattice := by
  rintro y ⟨v, hv, rfl⟩
  exact castVec_mem v

instance realLattice_discrete (L : Submodule ℤ (Fin 3 → ℤ)) :
    DiscreteTopology (realLattice L) := by
  exact DiscreteTopology.of_subset (inferInstanceAs (DiscreteTopology standardLattice))
    (realLattice_le_standard L)

def latticeIn (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    Submodule ℤ (plane x) := (realLattice L).comap ((plane x).subtype.restrictScalars ℤ)

instance latticeIn_discrete (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    DiscreteTopology (latticeIn x L) := by
  let : DiscreteTopology (realLattice L : Set Ambient) :=
    inferInstanceAs (DiscreteTopology (realLattice L))
  exact DiscreteTopology.preimage_of_continuous_injective (realLattice L : Set Ambient)
    (LinearMap.continuous_of_finiteDimensional (plane x).subtype) (Submodule.injective_subtype _)

lemma latticeIn_spans (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
    Submodule.span ℝ (latticeIn x L : Set (plane x)) = ⊤ := by
  apply top_unique
  rw [← lattice_spans x z hz]
  apply Submodule.span_le.mpr
  intro v hv
  obtain ⟨u, hu⟩ := kernelMap_surjective x ⟨v, hv⟩
  have hm : E • v ∈ latticeIn x L := by
    change (E • (v : Ambient)) ∈ realLattice L
    refine ⟨E • u.val, hL u.val, ?_⟩
    rw [map_smul]
    have he := congrArg (fun w : lattice x => ((w : plane x) : Ambient)) hu
    change castVec u.val = (v : Ambient) at he
    exact congrArg (fun a : Ambient => E • a) he
  have hs : (E : ℝ) • v ∈ Submodule.span ℝ (latticeIn x L : Set (plane x)) := by
    rw [Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.subset_span hm
  exact (Submodule.smul_mem_iff _ (by exact_mod_cast hE : (E : ℝ) ≠ 0)).mp hs

lemma latticeIn_isZLattice (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) : IsZLattice ℝ (latticeIn x L) :=
  ⟨latticeIn_spans x z hz L E hE hL⟩

lemma latticeIn_finrank (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) : finrank ℤ (latticeIn x L) = 2 := by
  let := latticeIn_isZLattice x z hz L E hE hL
  rw [ZLattice.rank ℝ (latticeIn x L), plane_finrank x z hz]

def basisIn (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) : Basis (Fin 2) ℤ (latticeIn x L) := by
  letI := latticeIn_isZLattice x z hz L E hE hL
  exact (Module.finBasis ℤ (latticeIn x L)).reindex
    (finCongr (latticeIn_finrank x z hz L E hE hL))

def integerPlaneIn (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    Submodule ℤ (Fin 3 → ℤ) := L ⊓ integerPlane x

def kernelMapIn (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    integerPlaneIn x L →ₗ[ℤ] latticeIn x L where
  toFun v := ⟨⟨castVec v, by
    change realDot x (castVec v) = 0
    rw [realDot_castVec]
    have hv : x ⬝ᵥ (v : Fin 3 → ℤ) = 0 := v.property.2
    exact_mod_cast hv⟩, ⟨v.val, v.property.1, rfl⟩⟩
  map_add' v w := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    simp [castVec]
  map_smul' t v := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    simp [castVec]

lemma kernelMapIn_injective (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    Function.Injective (kernelMapIn x L) := by
  intro u v h
  apply Subtype.ext
  funext i
  have he := congrArg (fun w : latticeIn x L => ((w : plane x) : Ambient) i) h
  change (u.val i : ℝ) = (v.val i : ℝ) at he
  exact_mod_cast he

lemma kernelMapIn_surjective (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    Function.Surjective (kernelMapIn x L) := by
  intro y
  obtain ⟨v, hv, he⟩ := y.property
  have hvker : v ∈ integerPlane x := by
    have hyker : realDot x ((y : plane x) : Ambient) = 0 := (y : plane x).property
    change castVec v = ((y : plane x) : Ambient) at he
    rw [← he, realDot_castVec] at hyker
    change x ⬝ᵥ v = 0
    exact_mod_cast hyker
  refine ⟨⟨v, hv, hvker⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact he

def kernelEquivIn (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    integerPlaneIn x L ≃ₗ[ℤ] latticeIn x L :=
  LinearEquiv.ofBijective (kernelMapIn x L)
    ⟨kernelMapIn_injective x L, kernelMapIn_surjective x L⟩

def integerBasisIn (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
    Basis (Fin 2) ℤ (integerPlaneIn x L) :=
  (basisIn x z hz L E hE hL).map (kernelEquivIn x L).symm

lemma cast_integerBasisIn (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) (i : Fin 2) :
    castVec (integerBasisIn x z hz L E hE hL i : Fin 3 → ℤ) =
      ((basisIn x z hz L E hE hL i : plane x) : Ambient) := by
  exact congrArg (fun w : latticeIn x L => ((w : plane x) : Ambient))
    ((kernelEquivIn x L).apply_symm_apply (basisIn x z hz L E hE hL i))

end Problem355.IntegralPlaneLattice

end

end OAI
