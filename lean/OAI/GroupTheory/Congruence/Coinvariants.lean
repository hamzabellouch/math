import OAI.Combinatorics.Coboundary.Cosets
import OAI.GroupTheory.Congruence.Transfer

namespace OAI

noncomputable section

/-!
Simplicial group actions, permutation modules, coset sums, and chain coinvariants.
-/

section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.InfiniteChains
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def rawMap (f : V ↪ W) : (Finset V →₀ k) →ₗ[k] (Finset W →₀ k) :=
  Finsupp.lmapDomain k k (Finset.map f)

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma rawMap_single (f : V ↪ W) (s : Finset V) (r : k) :
    rawMap f (Finsupp.single s r) = Finsupp.single (s.map f) r :=
  Finsupp.mapDomain_single

lemma rawMap_boundary (f : V ↪ W) :
    (rawMap f).comp rawBoundary = rawBoundary.comp (rawMap f) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, rawBoundary_single,
    map_sum, rawMap_single, Finset.sum_map]
  simp only [Finset.map_erase]

namespace Complex
variable (X : CoboundaryExpanders.InfiniteChains.Complex V) (Y : CoboundaryExpanders.InfiniteChains.Complex W) (f : V ↪ W)
  (hf : ∀ s ∈ X.faces, s.map f ∈ Y.faces)

def mapFace (n : ℕ) (s : X.Face n) : Y.Face n :=
  ⟨s.val.map f, hf s.val s.property.1, by rw [Finset.card_map]; exact s.property.2⟩

def map (n : ℕ) : X.Chains n →ₗ[k] Y.Chains n :=
  Finsupp.lmapDomain k k (X.mapFace Y f hf n)

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma map_single (n : ℕ) (s : X.Face n) (r : k) :
    X.map Y f hf n (Finsupp.single s r) = Finsupp.single (X.mapFace Y f hf n s) r :=
  Finsupp.mapDomain_single

omit [DecidableEq V] [DecidableEq W] in
lemma embed_map (n : ℕ) :
    (Y.embed n).comp (X.map Y f hf n) = (rawMap f).comp (X.embed n) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, map_single,
    embed_single, rawMap_single]
  rfl

lemma map_boundary (n : ℕ) :
    (X.map Y f hf n).comp (X.boundary n) =
      (Y.boundary n).comp (X.map Y f hf (n+1)) := by
  apply LinearMap.ext
  intro c
  apply Y.embed_injective n
  change (Y.embed n).comp (X.map Y f hf n) (X.boundary n c) =
    (Y.embed n).comp (Y.boundary n) (X.map Y f hf (n+1) c)
  rw [embed_map, embed_boundary]
  change rawMap f ((X.embed n).comp (X.boundary n) c) =
    rawBoundary ((Y.embed (n+1)).comp (X.map Y f hf (n+1)) c)
  rw [embed_boundary, embed_map]
  exact LinearMap.congr_fun (rawMap_boundary f) (X.embed (n+1) c)

end Complex
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.FinsuppPermutation
open CategoryTheory
variable (k G A : Type) [CommRing k] [Group G] [MulAction G A]

def ρ : Representation k G (A →₀ k) where
  toFun g := Finsupp.lmapDomain k k (g • ·)
  map_one' := by
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext
    intro r
    simp
  map_mul' g h := by
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext
    intro r
    simp [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, mul_smul]

@[simp] lemma ρ_single (g : G) (a : A) (r : k) :
    ρ k G A g (Finsupp.single a r) = Finsupp.single (g • a) r :=
  Finsupp.mapDomain_single

abbrev rep : Rep k G := Rep.of (ρ k G A)

def coeffIso : Rep.ofMulAction k G A ≅ rep k G A :=
  Rep.mkIso { MonoidAlgebra.coeffLinearEquiv k with
    isIntertwining' := by
      intro g
      apply MonoidAlgebra.lhom_ext'
      intro a
      apply LinearMap.ext
      intro r
      simp [ρ_single] }

end CoboundaryExpanders.FinsuppPermutation

namespace CoboundaryExpanders.InfiniteChains.Complex
open CategoryTheory
variable {V G : Type} [DecidableEq V] [Group G] [MulAction G V] (X : CoboundaryExpanders.InfiniteChains.Complex V)

def Invariant : Prop :=
  ∀ (g : G) (s : Finset V), s ∈ X.faces → s.map (MulAction.toPerm g).toEmbedding ∈ X.faces

variable [Fact (X.Invariant (G := G))]

instance faceMulAction (n : ℕ) : MulAction G (X.Face n) where
  smul g s := X.mapFace X (MulAction.toPerm g).toEmbedding (Fact.out (p := X.Invariant (G := G)) g) n s
  one_smul s := by
    apply Subtype.ext
    change s.val.map (MulAction.toPerm (1 : G)).toEmbedding = s.val
    ext v
    simp
  mul_smul g h s := by
    apply Subtype.ext
    change s.val.map (MulAction.toPerm (g*h)).toEmbedding =
      (s.val.map (MulAction.toPerm h).toEmbedding).map (MulAction.toPerm g).toEmbedding
    rw [Finset.map_map]
    congr 1
    ext v
    exact mul_smul g h v

omit [DecidableEq V] in
@[simp] lemma smul_face_val (g : G) (n : ℕ) (s : X.Face n) :
    (g • s).val = s.val.map (MulAction.toPerm g).toEmbedding := rfl

abbrev chainsRep (n : ℕ) : Rep k G := FinsuppPermutation.rep k G (X.Face n)

def boundaryRep (n : ℕ) : X.chainsRep (G := G) (n+1) ⟶ X.chainsRep (G := G) n :=
  Rep.ofHom ⟨X.boundary n, by
    intro g
    exact (X.map_boundary X (MulAction.toPerm g).toEmbedding (Fact.out (p := X.Invariant (G := G)) g) n).symm⟩

@[simp] lemma boundaryRep_squared (n : ℕ) :
    X.boundaryRep (G := G) (n+1) ≫ X.boundaryRep (G := G) n = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact X.boundary_squared n

def repComplex : ChainComplex (Rep k G) ℕ :=
  ChainComplex.of (fun n => X.chainsRep (G := G) (n+1))
    (fun n => X.boundaryRep (G := G) (n+1))
    (fun n => X.boundaryRep_squared (G := G) (n+1))

@[simp] lemma repComplex_d (n : ℕ) :
    X.repComplex.d (n+1) n = X.boundaryRep (G := G) (n+1) := by
  simp [repComplex, ChainComplex.of_d]

def augmentationRep : X.chainsRep (G := G) 1 ⟶ Rep.trivial k G k :=
  Rep.ofHom ⟨X.sumCoefficients 1, by
    intro g
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro r
    simp [FinsuppPermutation.ρ_single]⟩

@[simp] lemma augmentationRep_boundary :
    X.boundaryRep (G := G) 1 ≫ X.augmentationRep (G := G) = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact X.augmentation_boundary

lemma repComplex_exactAt (n : ℕ) (h : X.chainComplex.ExactAt (n+1)) :
    (X.repComplex (G := G)).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)] at h ⊢
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k))).mp
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  have hh := (ShortComplex.moduleCat_exact_iff _).mp h
  change ∀ c, X.repComplex.d (n+1) n c = 0 → ∃ b, X.repComplex.d (n+2) (n+1) b = c
  change ∀ c, X.chainComplex.d (n+1) n c = 0 → ∃ b, X.chainComplex.d (n+2) (n+1) b = c at hh
  simp only [repComplex_d, chainComplex_d] at hh ⊢
  exact hh

lemma augmentationRep_exact (h : Function.Exact (X.boundary 1) (X.sumCoefficients 1)) :
    (ShortComplex.mk (X.boundaryRep (G := G) 1) X.augmentationRep X.augmentationRep_boundary).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k))).mp
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  exact fun c hc => (h c).mp hc

omit [DecidableEq V] in
lemma augmentationRep_epi [Nonempty (X.Face 1)] : Epi (X.augmentationRep (G := G)) := by
  apply (Rep.epi_iff_surjective _).mpr
  intro r
  let s : X.Face 1 := Classical.choice inferInstance
  exact ⟨Finsupp.single s r, X.sumCoefficients_single 1 s r⟩

end CoboundaryExpanders.InfiniteChains.Complex

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

instance vertexMulAction : MulAction G (Vertex H) where
  smul g x := ⟨x.1, g • x.2⟩
  one_smul x := congrArg (Sigma.mk x.1) (one_smul G x.2)
  mul_smul g h x := congrArg (Sigma.mk x.1) (mul_smul g h x.2)

omit [DecidableEq I] in
@[simp] lemma map_face (g h : G) (A : Finset I) :
    (face H h A).map (MulAction.toPerm g).toEmbedding = face H (g*h) A := by
  rw [Finset.map_eq_image, face, Finset.image_image]
  rfl

lemma types_card {σ : Finset (Vertex H)} (hσ : IsFace H σ) :
    (types H σ).card = σ.card := by
  obtain ⟨g,A,rfl⟩ := hσ
  simp

instance complexInvariant : Fact ((complex H).Invariant (G := G)) := ⟨by
  rintro g σ ⟨h,A,rfl⟩
  rw [map_face]
  exact ⟨g*h,A,rfl⟩⟩

abbrev Types (n : ℕ) := {A : Finset I // A.card = n}
abbrev Basis (n : ℕ) := (A : Types (I := I) n) × G ⧸ stabilizer H A.val

instance basisMulAction (n : ℕ) : MulAction G (Basis H n) where
  smul g x := ⟨x.1, g • x.2⟩
  one_smul x := congrArg (Sigma.mk x.1) (one_smul G x.2)
  mul_smul g h x := congrArg (Sigma.mk x.1) (mul_smul g h x.2)

def gradedFace (n : ℕ) (x : Basis H n) : (complex H).Face n :=
  let q := quotientFace H x.1.val x.2
  ⟨q.val, q.property.1, by
    have hh := types_card H q.property.1
    rw [q.property.2] at hh
    exact hh.symm.trans x.1.property⟩

lemma gradedFace_bijective (n : ℕ) : Function.Bijective (gradedFace H n) := by
  constructor
  · rintro ⟨A,x⟩ ⟨B,y⟩ he
    have ht : A.val = B.val := by
      have hh := congrArg (fun s : (complex H).Face n => types H s.val) he
      exact (quotientFace H A.val x).property.2.symm.trans
        (hh.trans (quotientFace H B.val y).property.2)
    have hAB : A=B := Subtype.ext ht
    subst B
    congr 1
    apply (quotientFace_bijective H A.val).1
    have hv := congrArg (fun z : (complex H).Face n => z.val) he
    exact Subtype.ext hv
  · rintro ⟨σ,hσ,hc⟩
    obtain ⟨g,A,rfl⟩ := hσ
    have hA : A.card = n := by simpa using hc
    exact ⟨⟨⟨A,hA⟩,QuotientGroup.mk g⟩,rfl⟩

def gradedEquiv (n : ℕ) : Basis H n ≃ (complex H).Face n :=
  Equiv.ofBijective (gradedFace H n) (gradedFace_bijective H n)

@[simp] lemma gradedFace_mk (n : ℕ) (A : Types (I := I) n) (g : G) :
    (gradedFace H n ⟨A,QuotientGroup.mk g⟩).val = face H g A.val := rfl

lemma gradedFace_smul (n : ℕ) (g : G) (x : Basis H n) :
    gradedFace H n (g • x) = g • gradedFace H n x := by
  rcases x with ⟨A,x⟩
  induction x using Quotient.inductionOn with | h h =>
  apply Subtype.ext
  change face H (g*h) A.val = (face H h A.val).map (MulAction.toPerm g).toEmbedding
  exact (map_face H g h A.val).symm

end CoboundaryExpanders.TypedCosetFaces

end

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra

namespace CoboundaryExpanders.CosetModules

section
universe u
variable {k G : Type u} [Field k] [Group G]

abbrev permutation (H : Subgroup G) : Rep k G := Rep.ofMulAction k G (G ⧸ H)

def orbitVector (H : Subgroup G) (A : Rep k G) (x : A)
    (hx : ∀ h : H, A.ρ h x = x) : G ⧸ H → A :=
  Quotient.lift (fun g : G => A.ρ g x) (by
    intro a b hab
    have hh : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have he := hx ⟨a⁻¹ * b, hh⟩
    have hm := congrArg (A.ρ a) he
    simpa only [Subtype.coe_mk, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel_left] using hm.symm)

@[simp] theorem orbitVector_mk (H : Subgroup G) (A : Rep k G) (x : A)
    (hx : ∀ h : H, A.ρ h x = x) (g : G) :
    orbitVector H A x hx (QuotientGroup.mk g) = A.ρ g x := rfl

theorem orbitVector_smul (H : Subgroup G) (A : Rep k G) (x : A)
    (hx : ∀ h : H, A.ρ h x = x) (g : G) (q : G ⧸ H) :
    orbitVector H A x hx (g • q) = A.ρ g (orbitVector H A x hx q) := by
  induction q using Quotient.inductionOn with | h a =>
    change A.ρ (g * a) x = A.ρ g (A.ρ a x)
    rw [map_mul, Module.End.mul_apply]

def extend (H : Subgroup G) (A : Rep k G) (x : A)
    (hx : ∀ h : H, A.ρ h x = x) : permutation (k := k) H ⟶ A :=
  Rep.ofHom ⟨(Finsupp.linearCombination k (orbitVector H A x hx)).comp (MonoidAlgebra.coeffLinearEquiv k).toLinearMap, by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply,
      Representation.ofMulAction_single]
    change (Finsupp.linearCombination k (orbitVector H A x hx)) (Finsupp.single (g • q) r) =
      A.ρ g ((Finsupp.linearCombination k (orbitVector H A x hx)) (Finsupp.single q r))
    simp only [Finsupp.linearCombination_single, map_smul, orbitVector_smul]⟩

@[simp] theorem extend_single (H : Subgroup G) (A : Rep k G) (x : A)
    (hx : ∀ h : H, A.ρ h x = x) (a : G) (r : k) :
    extend H A x hx (MonoidAlgebra.single (QuotientGroup.mk a) r) = r • A.ρ a x := by
  change (Finsupp.linearCombination k (orbitVector H A x hx))
    (Finsupp.single (QuotientGroup.mk a) r) = _
  rw [Finsupp.linearCombination_single, orbitVector_mk]

def base (H : Subgroup G) : Rep.trivial k H k ⟶ Rep.res H.subtype (permutation (k := k) H) :=
  Rep.ofHom ⟨MonoidAlgebra.lsingle (QuotientGroup.mk (1 : G)), by
    intro h
    apply LinearMap.ext
    intro r
    change MonoidAlgebra.single (QuotientGroup.mk (1 : G)) r =
      (Representation.ofMulAction k G (G ⧸ H)) h (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) r)
    rw [Representation.ofMulAction_single]
    congr 1
    change (QuotientGroup.mk (1 : G) : G ⧸ H) = QuotientGroup.mk (h.val * 1)
    simp only [mul_one]
    apply Quotient.sound
    simpa only [QuotientGroup.leftRel_apply, inv_one, one_mul] using h.property⟩

theorem projective_permutation (H : Subgroup G) [Projective (Rep.trivial k H k)] :
    Projective (permutation (k := k) H) where
  factors {E X} f e he := by
    let f₀ : Rep.trivial k H k ⟶ Rep.res H.subtype X :=
      base H ≫ (Rep.resFunctor (k := k) H.subtype).map f
    let e₀ : Rep.res H.subtype E ⟶ Rep.res H.subtype X :=
      (Rep.resFunctor (k := k) H.subtype).map e
    have : Epi e₀ := by
      apply (Rep.epi_iff_surjective e₀).mpr
      exact (Rep.epi_iff_surjective e).mp he
    let l := Projective.factorThru f₀ e₀
    let x : E := l 1
    have hx : ∀ h : H, E.ρ h x = x := by
      intro h
      have hh := Rep.hom_comm_apply l h 1
      simpa [x] using hh.symm
    refine ⟨extend H E x hx, ?_⟩
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro r
    induction q using Quotient.inductionOn with | h a =>
      have hbase : e x = f (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) (1 : k)) := by
        have hh := congrArg (fun z => z 1) (Projective.factorThru_comp f₀ e₀)
        exact hh
      change e (extend H E x hx (MonoidAlgebra.single (QuotientGroup.mk a) r)) =
        f (MonoidAlgebra.single (QuotientGroup.mk a) r)
      rw [extend_single, map_smul, Rep.hom_comm_apply, hbase]
      have hf := Rep.hom_comm_apply f a (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) (1 : k))
      rw [← hf]
      simp only [Representation.ofMulAction_single]
      change r • f (MonoidAlgebra.single (QuotientGroup.mk (a * 1)) 1) = _
      rw [mul_one, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

theorem projective_permutation_of_invertible_order (H : Subgroup G)
    [Finite H] [NeZero (Nat.card H : k)] : Projective (permutation (k := k) H) := by
  let A := Rep.trivial k H k
  let M := Rep.toModuleMonoidAlgebra.obj A
  let : Module.Projective (MonoidAlgebra k H) M :=
    Module.projective_of_isSemisimpleRing _ _
  have : Projective M := inferInstance
  have : Projective A :=
    Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective A
      (inferInstance : Projective M)
  exact projective_permutation H

end

theorem projective_permutation_of_odd_order {G : Type} [Group G]
    (H : Subgroup G) [Finite H] (hH : Odd (Nat.card H)) :
    Projective (permutation (k := ZMod 2) H) := by
  have hc : (Nat.card H : ZMod 2) = 1 := by
    rcases hH with ⟨r, hr⟩
    rw [hr]
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp [Nat.cast_add, Nat.cast_mul, htwo]
  let : NeZero (Nat.card H : ZMod 2) := ⟨by rw [hc]; exact one_ne_zero⟩
  exact projective_permutation_of_invertible_order H
end CoboundaryExpanders.CosetModules

namespace CoboundaryExpanders.CosetSums
variable {k G I : Type} [Field k] [Group G] (H : I → Subgroup G)
abbrev Basis := (i : I) × G ⧸ H i
instance : MulAction G (Basis H) where
  smul g x := ⟨x.1, g • x.2⟩
  one_smul x := congrArg (Sigma.mk x.1) (one_smul G x.2)
  mul_smul g h x := congrArg (Sigma.mk x.1) (mul_smul g h x.2)
abbrev permutation : Rep k G := Rep.ofMulAction k G (Basis H)

def inclusion (i : I) : CosetModules.permutation (k := k) (H i) ⟶ permutation (k := k) H :=
  Rep.ofHom ⟨(Finsupp.linearCombination k (fun q : G ⧸ H i =>
    MonoidAlgebra.single (⟨i,q⟩ : Basis H) (1 : k))).comp
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap, by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply,
      Representation.ofMulAction_single]
    change Finsupp.linearCombination _ _ (Finsupp.single (g • q) r) =
      (Representation.ofMulAction k G (Basis H)) g
        (Finsupp.linearCombination _ _ (Finsupp.single q r))
    simp [Representation.ofMulAction_single]
    rfl⟩

@[simp] theorem inclusion_single (i : I) (q : G ⧸ H i) (r : k) :
    inclusion (k := k) H i (MonoidAlgebra.single q r) =
      MonoidAlgebra.single (⟨i,q⟩ : Basis H) r := by
  change Finsupp.linearCombination _ _ (Finsupp.single q r) = _
  simp

def descend (A : Rep k G) (f : ∀ i, CosetModules.permutation (k := k) (H i) ⟶ A) :
    permutation (k := k) H ⟶ A :=
  Rep.ofHom ⟨(Finsupp.linearCombination k (fun x : Basis H =>
    f x.1 (MonoidAlgebra.single x.2 (1 : k)))).comp
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap, by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply,
      Representation.ofMulAction_single]
    change Finsupp.linearCombination _ _ (Finsupp.single (g • x) r) =
      A.ρ g (Finsupp.linearCombination _ _ (Finsupp.single x r))
    simp only [Finsupp.linearCombination_single, map_smul]
    congr 1
    change (f x.1).hom (MonoidAlgebra.single (g • x.2) (1 : k)) =
      A.ρ g ((f x.1).hom (MonoidAlgebra.single x.2 (1 : k)))
    have hh := Rep.hom_comm_apply (f x.1) g (MonoidAlgebra.single x.2 (1 : k))
    rw [Representation.ofMulAction_single] at hh
    exact hh⟩

@[simp] theorem descend_single (A : Rep k G)
    (f : ∀ i, CosetModules.permutation (k := k) (H i) ⟶ A)
    (x : Basis H) (r : k) :
    descend H A f (MonoidAlgebra.single x r) = f x.1 (MonoidAlgebra.single x.2 r) := by
  change Finsupp.linearCombination _ _ (Finsupp.single x r) = _
  simp [← map_smul]

theorem projective [∀ i, Projective (CosetModules.permutation (k := k) (H i))] :
    Projective (permutation (k := k) H) where
  factors {E X} f e he := by
    let l := fun i => Projective.factorThru (inclusion H i ≫ f) e
    refine ⟨descend H E l, ?_⟩
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro r
    change e (descend H E l (MonoidAlgebra.single x r)) = f (MonoidAlgebra.single x r)
    rw [descend_single]
    have hh := congrArg (fun z => z (MonoidAlgebra.single x.2 r))
      (Projective.factorThru_comp (inclusion H x.1 ≫ f) e)
    change e (l x.1 (MonoidAlgebra.single x.2 r)) =
      f (inclusion H x.1 (MonoidAlgebra.single x.2 r)) at hh
    exact hh.trans (congrArg (fun z => f z) (inclusion_single H x.1 x.2 r))

theorem projective_of_odd_order [∀ i, Finite (H i)] (hH : ∀ i, Odd (Nat.card (H i))) :
    Projective (permutation (k := ZMod 2) H) := by
  let _ : ∀ i, Projective (CosetModules.permutation (k := ZMod 2) (H i)) :=
    fun i => CosetModules.projective_permutation_of_odd_order (H i) (hH i)
  exact projective H
end CoboundaryExpanders.CosetSums

namespace CoboundaryExpanders.TypedCosetFaces

section
open CategoryTheory
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

def chainsIso (n : ℕ) :
    CosetSums.permutation (k := ZMod 2) (fun A : Types (I := I) n => stabilizer H A.val) ≅
      (complex H).chainsRep (G := G) n :=
  FinsuppPermutation.coeffIso _ _ _ ≪≫ Rep.mkIso {
    (Finsupp.domLCongr (gradedEquiv H n) : _ ≃ₗ[ZMod 2] _) with
    isIntertwining' := by
      intro g
      apply Finsupp.lhom_ext'
      intro x
      apply LinearMap.ext
      intro r
      change (Finsupp.domLCongr (gradedEquiv H n) : _ ≃ₗ[ZMod 2] _)
        (FinsuppPermutation.ρ (ZMod 2) G _ g (Finsupp.single x r)) =
        FinsuppPermutation.ρ (ZMod 2) G _ g
          ((Finsupp.domLCongr (gradedEquiv H n) : _ ≃ₗ[ZMod 2] _) (Finsupp.single x r))
      simp only [FinsuppPermutation.ρ_single, Finsupp.domLCongr_single]
      exact congrArg (fun s => Finsupp.single s r) (gradedFace_smul H n g x) }

omit [DecidableEq I] in
lemma stabilizer_le (A : Finset I) {i : I} (hi : i ∈ A) : stabilizer H A ≤ H i :=
  fun _ hg => (mem_stabilizer H A _).mp hg i hi

omit [DecidableEq I] in
lemma stabilizer_finite [∀ i, Finite (H i)] (A : Finset I) (hA : A.Nonempty) :
    Finite (stabilizer H A) := by
  obtain ⟨i,hi⟩ := hA
  exact Finite.of_injective (Subgroup.inclusion (stabilizer_le H A hi))
    (Subgroup.inclusion_injective _)

omit [DecidableEq I] in
lemma stabilizer_odd (hH : ∀ i, Odd (Nat.card (H i))) (A : Finset I) (hA : A.Nonempty) :
    Odd (Nat.card (stabilizer H A)) := by
  obtain ⟨i,hi⟩ := hA
  exact (hH i).of_dvd_nat (Subgroup.card_dvd_of_le (stabilizer_le H A hi))

theorem projective_chains [∀ i, Finite (H i)] (hH : ∀ i, Odd (Nat.card (H i))) (j : ℕ) :
    Projective (((complex H).repComplex (G := G)).X j) := by
  let _ : ∀ A : Types (I := I) (j+1), Finite (stabilizer H A.val) :=
    fun A => stabilizer_finite H A.val (Finset.card_pos.mp (by omega))
  have hp := CosetSums.projective_of_odd_order
    (fun A : Types (I := I) (j+1) => stabilizer H A.val)
    (fun A => stabilizer_odd H hH A.val (Finset.card_pos.mp (by omega)))
  exact Projective.of_iso (chainsIso H (j+1)) hp

end

open InfiniteChains
open CategoryTheory
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

abbrev Simplex := CoboundaryExpanders.InfiniteChains.Complex.full I

def typeFace (n : ℕ) (s : (complex H).Face n) : (Simplex (I := I)).Face n :=
  ⟨types H s.val, Set.mem_univ _, (types_card H s.property.1).trans s.property.2⟩

def baseFace (n : ℕ) (A : (Simplex (I := I)).Face n) : (complex H).Face n :=
  ⟨face H 1 A.val, ⟨1,A.val,rfl⟩, by simp [A.property.2]⟩

@[simp] lemma typeFace_baseFace (n : ℕ) (A : (Simplex (I := I)).Face n) :
    typeFace H n (baseFace H n A) = A := Subtype.ext (types_face H 1 A.val)

@[simp] lemma typeFace_smul (n : ℕ) (g : G) (s : (complex H).Face n) :
    typeFace H n (g • s) = typeFace H n s := by
  obtain ⟨g',A,hA⟩ := s.property.1
  apply Subtype.ext
  change types H (s.val.map (MulAction.toPerm g).toEmbedding) = types H s.val
  rw [← hA, map_face, types_face, types_face]

lemma face_orbit_base (n : ℕ) (s : (complex H).Face n) :
    ∃ g : G, g • baseFace H n (typeFace H n s) = s := by
  obtain ⟨g,A,hA⟩ := s.property.1
  refine ⟨g, Subtype.ext ?_⟩
  change (face H 1 (types H s.val)).map (MulAction.toPerm g).toEmbedding = s.val
  rw [map_face, mul_one, ← hA, types_face]

def typeMap (n : ℕ) : (complex H).Chains n →ₗ[k] (Simplex (I := I)).Chains n :=
  Finsupp.lmapDomain k k (typeFace H n)

@[simp] lemma typeMap_single (n : ℕ) (s : (complex H).Face n) (r : k) :
    typeMap H n (Finsupp.single s r) = Finsupp.single (typeFace H n s) r :=
  Finsupp.mapDomain_single

lemma typeMap_invariant (n : ℕ) (g : G) :
    (typeMap H n).comp (((complex H).chainsRep (G := G) n).ρ g) = typeMap H n := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp [FinsuppPermutation.ρ_single]

abbrev CoinvariantChains (n : ℕ) := ((complex H).chainsRep (G := G) n).ρ.Coinvariants

def toTypes (n : ℕ) : CoinvariantChains H n →ₗ[k] (Simplex (I := I)).Chains n :=
  Representation.Coinvariants.lift _ (typeMap H n) (typeMap_invariant H n)

@[simp] lemma toTypes_single (n : ℕ) (s : (complex H).Face n) (r : k) :
    toTypes H n (Representation.Coinvariants.mk (FinsuppPermutation.ρ k G ((complex H).Face n)) (Finsupp.single s r)) =
      Finsupp.single (typeFace H n s) r := typeMap_single H n s r

def fromTypes (n : ℕ) : (Simplex (I := I)).Chains n →ₗ[k] CoinvariantChains H n :=
  Finsupp.linearCombination k (fun A =>
    Representation.Coinvariants.mk (FinsuppPermutation.ρ k G ((complex H).Face n)) (Finsupp.single (baseFace H n A) 1))

@[simp] lemma fromTypes_single (n : ℕ) (A : (Simplex (I := I)).Face n) (r : k) :
    fromTypes H n (Finsupp.single A r) =
      Representation.Coinvariants.mk (FinsuppPermutation.ρ k G ((complex H).Face n)) (Finsupp.single (baseFace H n A) r) := by
  simp [fromTypes, ← map_smul]

lemma fromTypes_toTypes (n : ℕ) : (fromTypes H n).comp (toTypes H n) = LinearMap.id := by
  apply Representation.Coinvariants.hom_ext
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  change fromTypes H n (typeMap H n (Finsupp.single s r)) =
    Representation.Coinvariants.mk (FinsuppPermutation.ρ k G ((complex H).Face n))
      (Finsupp.single s r)
  rw [typeMap_single, fromTypes_single]
  obtain ⟨g,hg⟩ := face_orbit_base H n s
  have hh := (Representation.Coinvariants.mk_self_apply
    (FinsuppPermutation.ρ k G ((complex H).Face n)) g
    (Finsupp.single (baseFace H n (typeFace H n s)) r)).symm
  simpa only [FinsuppPermutation.ρ_single, hg] using hh

lemma toTypes_fromTypes (n : ℕ) : (toTypes H n).comp (fromTypes H n) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro A
  apply LinearMap.ext
  intro r
  simp

def typesEquiv (n : ℕ) : CoinvariantChains H n ≃ₗ[k] (Simplex (I := I)).Chains n :=
  LinearEquiv.ofLinearMap (toTypes H n) (fromTypes H n)
    (toTypes_fromTypes H n) (fromTypes_toTypes H n)

lemma types_erase_vertex (g : G) (A : Finset I) (i : I) :
    types H ((face H g A).erase (vertex H g i)) = A.erase i := by
  rw [face, ← Finset.image_erase (vertex_injective H g)]
  exact types_face H g (A.erase i)

lemma typeMap_boundary (n : ℕ) :
    (typeMap H n).comp ((complex H).boundary n) =
      (Simplex (I := I)).boundary n ∘ₗ typeMap H (n+1) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  apply (Simplex (I := I)).embed_injective n
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, CoboundaryExpanders.InfiniteChains.Complex.boundary_single,
    map_sum, typeMap_single, CoboundaryExpanders.InfiniteChains.Complex.embed_single]
  change (∑ v : ↥s.val, Finsupp.single (types H (s.val.erase v.val)) r) =
    ∑ i : ↥(types H s.val), Finsupp.single ((types H s.val).erase i.val) r
  rw [Finset.sum_coe_sort s.val (fun v => Finsupp.single (types H (s.val.erase v)) r),
    Finset.sum_coe_sort (types H s.val) (fun i => Finsupp.single ((types H s.val).erase i) r)]
  obtain ⟨g,A,hA⟩ := s.property.1
  rw [← hA, types_face]
  change (∑ i ∈ A.image (vertex H g),
    Finsupp.single (types H ((face H g A).erase i)) r) = _
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [types_erase_vertex]
  · exact fun _ _ _ _ he => vertex_injective H g he

def coinvariantBoundary (n : ℕ) : CoinvariantChains H (n+1) →ₗ[k] CoinvariantChains H n :=
  Representation.Coinvariants.map _ _ ((complex H).boundaryRep (G := G) n).hom

lemma toTypes_boundary (n : ℕ) :
    (toTypes H n).comp (coinvariantBoundary H n) =
      (Simplex (I := I)).boundary n ∘ₗ toTypes H (n+1) := by
  apply Representation.Coinvariants.hom_ext
  exact typeMap_boundary H n

abbrev coinvariantComplex : ChainComplex (ModuleCat k) ℕ :=
  ((Rep.coinvariantsFunctor k G).mapHomologicalComplex _).obj ((complex H).repComplex (G := G))

def coinvariantSimplexIso : coinvariantComplex H ≅ (Simplex (I := I)).chainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (typesEquiv H (j+1)).toModuleIso) (by
      intro i j hij
      have he : i=j+1 := by simpa using hij.symm
      subst i
      apply ModuleCat.hom_ext
      change ((Simplex (I := I)).chainComplex.d (j+1) j).hom.comp (toTypes H (j+2)) = _
      rw [CoboundaryExpanders.InfiniteChains.Complex.chainComplex_d]
      change (Simplex (I := I)).boundary (j+1) ∘ₗ toTypes H (j+2) =
        (toTypes H (j+1)).comp
          (Representation.Coinvariants.map _ _ (((complex H).repComplex (G := G)).d (j+1) j).hom)
      rw [CoboundaryExpanders.InfiniteChains.Complex.repComplex_d]
      exact (toTypes_boundary H (j+1)).symm)

theorem coinvariant_homology_isZero [Nonempty I] (j : ℕ) :
    Limits.IsZero ((coinvariantComplex H).homology (j+1)) := by
  let a : I := Classical.choice inferInstance
  have hz := (Simplex (I := I)).chainComplex_homology_isZero_of_cone a
    (CoboundaryExpanders.InfiniteChains.Complex.full_isConePoint a) j
  exact hz.of_iso ((HomologicalComplex.homologyFunctor _ _ (j+1)).mapIso
    (coinvariantSimplexIso H))

end CoboundaryExpanders.TypedCosetFaces

end

end OAI
