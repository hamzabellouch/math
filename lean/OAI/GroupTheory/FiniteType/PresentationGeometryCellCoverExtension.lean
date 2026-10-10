import Mathlib
import OAI.GroupTheory.FiniteType.FiberCoreMap

namespace OAI

noncomputable section

section
open Set Function Topology
open Set Function
open scoped unitInterval
open scoped unitInterval
open Set
open Set Topology unitInterval
namespace PresentationGeometry.CellCoverExtension
open Set Cells Metric
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k d : ℕ} (f : C(boundary k d,X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k d,Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

lemma oldLift_isEmbedding : IsEmbedding (oldLift f b Z pot s hs hpot) :=
  FiberCoreMap.isEmbedding Z (coveringCore f b Z pot s hs hpot)
    ⟨Adjunction.old f,Adjunction.continuous_old f⟩ Sum.inl
    (fun i x hx => (mem_coveringCore_old f b Z pot s hs hpot i x).mpr hx)
    (fun i j x _ q => coveringCore_old_coordChange f b Z pot s hs hpot i j x q)
    (Adjunction.old_isClosedEmbedding (boundary_closed k d) f).isEmbedding

lemma range_oldLift : Set.range (oldLift f b Z pot s hs hpot) =
    (coveringCore f b Z pot s hs hpot).proj ⁻¹' Set.range (Adjunction.old f) := by
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨Z.proj a,rfl⟩
  · rintro ⟨x,hx⟩
    obtain ⟨a,ha⟩ := (oldLift_fiber_bijective f b Z pot s hs hpot x).2 ⟨z,hx.symm⟩
    exact ⟨a.1,congrArg Subtype.val ha⟩

def boundarySlice (i : Fin k) : C(SphereCover.Sphere (Fin d → ℝ),boundary k d) :=
  ⟨fun v => ⟨(i,⟨v.1,sphere_subset_closedBall v.2⟩),v.2⟩,
    (continuous_const.prodMk (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩

def sphereInDisk : C(SphereCover.Sphere (Fin d → ℝ),Disk d) :=
  ⟨fun v => ⟨v.1,sphere_subset_closedBall v.2⟩,continuous_subtype_val.subtype_mk _⟩

def attachedDisk (i : Fin k) : C(Disk d,Cells.Space f) :=
  ⟨fun v => Adjunction.disk f (i,v),
    (Adjunction.continuous_disk f).comp (continuous_const.prodMk continuous_id)⟩

omit [T2Space X] [CompactSpace X] in
@[simp] lemma attachedDisk_boundary (i : Fin k) (v : SphereCover.Sphere (Fin d → ℝ)) :
    attachedDisk f i (sphereInDisk v) = Adjunction.old f (f (boundarySlice i v)) :=
  Adjunction.disk_boundary f (boundarySlice i v)

lemma attaching_lift_nullhomotopic {n : ℕ} (hd : d = n+3) (i : Fin k) :
    ∃ z : (coveringCore f b Z pot s hs hpot).TotalSpace,
      ((oldLift f b Z pot s hs hpot).comp (s.comp (boundarySlice i))).Homotopic
        (ContinuousMap.const _ z) := by
  subst d
  let : SimplyConnectedSpace (SphereCover.Sphere (Fin (n+3) → ℝ)) :=
    SphereCover.normed_simplyConnected n (by simp)
  let : ContractibleSpace (Disk (n+3)) := Metric.contractibleSpace_closedBall (by norm_num)
  exact CoveringCellGeometry.boundary_nullhomotopic
    (coveringCore_isCoveringMap f b Z pot s hs hpot) (attachedDisk f i) sphereInDisk
    ((oldLift f b Z pot s hs hpot).comp (s.comp (boundarySlice i)))
    (by
      funext v
      exact (congrArg (Adjunction.old f) (hs (boundarySlice i v))).trans
        (attachedDisk_boundary f i v).symm)
    (Classical.arbitrary _)

end PresentationGeometry.CellCoverExtension

end

open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace AffineChains
section

def vertices (V : Type) : SSet where
  obj n := Fin (n.unop.len+1) → V
  map f := ↾fun v => v ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev chains (V : Type) := (vertices V).chainComplex (ModuleCat.of ℤ ℤ)

variable {V W : Type}

def generator {n : ℕ} (v : Fin (n+1) → V) : ModuleCat.of ℤ ℤ ⟶ (chains V).X n :=
  (vertices V).ιChainComplex v

lemma generator_boundary {n : ℕ} (v : Fin (n+2) → V) :
    generator v ≫ (chains V).d (n+1) n =
      ∑ i : Fin (n+2), (-1:ℤ)^i.val • generator (v ∘ i.succAbove) := by
  exact SSet.ιChainComplex_d (R := ModuleCat.of ℤ ℤ) (X := vertices V) v

def desc {n : ℕ} {A : ModuleCat ℤ} (b : (Fin (n+1) → V) → (ModuleCat.of ℤ ℤ ⟶ A)) :
    (chains V).X n ⟶ A := Sigma.desc b

@[reassoc (attr := simp)] lemma generator_desc {n : ℕ} {A : ModuleCat ℤ}
    (b : (Fin (n+1) → V) → (ModuleCat.of ℤ ℤ ⟶ A)) (v : Fin (n+1) → V) :
    generator v ≫ desc b = b v := by
  exact Sigma.ι_comp_desc _ _

lemma hom_ext {n : ℕ} {A : ModuleCat ℤ} {f g : (chains V).X n ⟶ A}
    (h : ∀ v : Fin (n+1) → V, generator v ≫ f = generator v ≫ g) : f = g :=
  SSet.chainComplex_hom_ext h

def verticesMap (f : V → W) : vertices V ⟶ vertices W where
  app _ := ↾fun v => f ∘ v
  naturality _ _ _ := rfl

def map (f : V → W) : chains V ⟶ chains W :=
  SSet.chainComplexMap (verticesMap f) (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)] lemma generator_map {n : ℕ} (v : Fin (n+1) → V) (f : V → W) :
    generator v ≫ (map f).f n = generator (f ∘ v) := by
  exact SSet.ι_chainComplexMap_f (vertices V) (vertices W) (verticesMap f) (ModuleCat.of ℤ ℤ) v

def cone (x : V) (n : ℕ) : (chains V).X n ⟶ (chains V).X (n+1) :=
  desc (fun v => generator (Fin.cons x v))

@[reassoc (attr := simp)] lemma generator_cone {n : ℕ} (v : Fin (n+1) → V) (x : V) :
    generator v ≫ cone x n = generator (Fin.cons x v) := generator_desc _ _

lemma cons_face_zero {n : ℕ} (v : Fin (n+1) → V) (x : V) :
    Fin.cons x v ∘ (0 : Fin (n+2)).succAbove = v := by
  funext i
  simp

lemma cons_face_succ {n : ℕ} (v : Fin (n+2) → V) (x : V) (i : Fin (n+2)) :
    Fin.cons x v ∘ i.succ.succAbove = Fin.cons x (v ∘ i.succAbove) := by
  funext j
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp

lemma cone_boundary_zero (x : V) :
    cone x 0 ≫ (chains V).d 1 0 = 𝟙 _ - (map (fun _ : V => x)).f 0 := by
  apply hom_ext
  intro v
  simp only [← Category.assoc,generator_cone,generator_boundary,
    Preadditive.comp_sub,Category.comp_id,generator_map]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_smul,cons_face_zero,Fin.sum_univ_one,
    Fin.val_succ,Fin.val_zero,zero_add,pow_one,neg_smul,one_smul]
  rw [sub_eq_add_neg]
  congr 2
  apply congrArg generator
  funext i
  fin_cases i
  simp

lemma cone_boundary_succ (x : V) (n : ℕ) :
    cone x (n+1) ≫ (chains V).d (n+2) (n+1) =
      𝟙 _ - (chains V).d (n+1) n ≫ cone x n := by
  apply hom_ext
  intro v
  simp only [← Category.assoc,generator_cone,generator_boundary,
    Preadditive.comp_sub,Category.comp_id,Preadditive.sum_comp,Preadditive.zsmul_comp]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_smul,cons_face_zero,Fin.val_succ,pow_succ,
    mul_neg_one,neg_smul,cons_face_succ]
  rw [Finset.sum_neg_distrib]
  exact sub_eq_add_neg _ _ |>.symm

end

section
open CategoryTheory AlgebraicTopology Limits
variable {V : Type}

lemma boundary_constant (x : V) :
    (chains V).d 1 0 ≫ (map (fun _ : V => x)).f 0 = 0 := by
  apply hom_ext
  intro v
  rw [← Category.assoc,generator_boundary]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,generator_map,comp_zero]
  change (∑ i : Fin 2, (-1:ℤ)^i.val • generator (fun _ : Fin 1 => x)) = 0
  simp [Fin.sum_univ_two]

variable (b : ∀ {n : ℕ}, (Fin (n+1) → V) → V)

def subdiv (b : ∀ {n : ℕ}, (Fin (n+1) → V) → V) (n : ℕ) : (chains V).X n ⟶ (chains V).X n :=
  match n with
  | 0 => 𝟙 _
  | n+1 => desc (fun v => generator v ≫ (chains V).d (n+1) n ≫ subdiv b n ≫ cone (b v) n)

@[simp] lemma subdiv_zero : subdiv b (V := V) 0 = 𝟙 _ := rfl

@[reassoc (attr := simp)] lemma generator_subdiv_succ {n : ℕ} (v : Fin (n+2) → V) :
    generator v ≫ subdiv b (n+1) =
      generator v ≫ (chains V).d (n+1) n ≫ subdiv b n ≫ cone (b v) n :=
  generator_desc _ _

lemma subdiv_comm (n : ℕ) :
    subdiv b (V := V) (n+1) ≫ (chains V).d (n+1) n =
      (chains V).d (n+1) n ≫ subdiv b n := by
  induction n with
  | zero =>
    apply hom_ext
    intro v
    rw [← Category.assoc,generator_subdiv_succ]
    simp only [subdiv_zero,Category.id_comp,Category.comp_id,Category.assoc]
    rw [cone_boundary_zero,Preadditive.comp_sub,Category.comp_id]
    rw [boundary_constant,sub_zero]
  | succ n ih =>
    apply hom_ext
    intro v
    rw [← Category.assoc,generator_subdiv_succ]
    simp only [Category.assoc]
    rw [cone_boundary_succ,Preadditive.comp_sub,Category.comp_id]
    rw [← Category.assoc (subdiv b (n+1)),ih]
    simp only [Preadditive.comp_sub,Category.assoc]
    rw [← Category.assoc ((chains V).d (n+2) (n+1))]
    simp only [HomologicalComplex.d_comp_d,zero_comp,comp_zero,sub_zero]

def subdivision : chains V ⟶ chains V :=
  ChainComplex.ofHom (subdiv b) (subdiv_comm b)

def prism (b : ∀ {n : ℕ}, (Fin (n+1) → V) → V) (n : ℕ) : (chains V).X n ⟶ (chains V).X (n+1) :=
  match n with
  | 0 => 0
  | n+1 => desc (fun v =>
      (generator v - generator v ≫ subdiv b (n+1) -
        generator v ≫ (chains V).d (n+1) n ≫ prism b n) ≫ cone (b v) (n+1))

@[simp] lemma prism_zero : prism b (V := V) 0 = 0 := rfl

@[reassoc (attr := simp)] lemma generator_prism_succ {n : ℕ} (v : Fin (n+2) → V) :
    generator v ≫ prism b (n+1) =
      (generator v - generator v ≫ subdiv b (n+1) -
        generator v ≫ (chains V).d (n+1) n ≫ prism b n) ≫ cone (b v) (n+1) :=
  generator_desc _ _

lemma prism_boundary (n : ℕ) :
    prism b (V := V) (n+1) ≫ (chains V).d (n+2) (n+1) =
      𝟙 _ - subdiv b (n+1) - (chains V).d (n+1) n ≫ prism b n := by
  induction n with
  | zero =>
    apply hom_ext
    intro v
    rw [← Category.assoc,generator_prism_succ,Category.assoc,cone_boundary_succ]
    simp only [prism_zero,comp_zero,sub_zero,Preadditive.comp_sub,Category.comp_id]
    rw [← Category.assoc,Preadditive.sub_comp,Category.assoc,subdiv_comm,
      subdiv_zero,Category.comp_id,sub_self,zero_comp,sub_zero]
  | succ n ih =>
    apply hom_ext
    intro v
    rw [← Category.assoc,generator_prism_succ,Category.assoc,cone_boundary_succ]
    simp only [Preadditive.comp_sub,Category.comp_id]
    have hz : (generator v - generator v ≫ subdiv b (n+2) -
        generator v ≫ (chains V).d (n+2) (n+1) ≫ prism b (n+1)) ≫
          (chains V).d (n+2) (n+1) = 0 := by
      simp only [Preadditive.sub_comp,Category.assoc]
      rw [subdiv_comm,ih]
      simp only [Preadditive.comp_sub,Category.comp_id]
      rw [← Category.assoc ((chains V).d (n+2) (n+1))]
      simp only [HomologicalComplex.d_comp_d,zero_comp,comp_zero,sub_zero,sub_self]
    have hz' := congrArg (fun k => k ≫ cone (b v) (n+1)) hz
    simp only [Category.assoc,zero_comp] at hz'
    try simp only [Category.assoc]
    rw [hz',sub_zero]

end

open CategoryTheory AlgebraicTopology Limits
variable {V W : Type}

lemma map_cone (f : V → W) (x : V) (n : ℕ) :
    (map f).f n ≫ cone (f x) n = cone x n ≫ (map f).f (n+1) := by
  apply hom_ext
  intro v
  simp only [← Category.assoc,generator_map,generator_cone]
  congr 1
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

variable (b : ∀ {n : ℕ}, (Fin (n+1) → V) → V)
  (c : ∀ {n : ℕ}, (Fin (n+1) → W) → W) (f : V → W)
  (hf : ∀ {n : ℕ} (v : Fin (n+1) → V), f (b v) = c (f ∘ v))

include hf
lemma subdiv_map (n : ℕ) :
    subdiv b n ≫ (map f).f n = (map f).f n ≫ subdiv c n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply hom_ext
    intro v
    rw [← Category.assoc,generator_subdiv_succ]
    simp only [Category.assoc]
    rw [← map_cone,← Category.assoc (subdiv b n),ih]
    simp only [Category.assoc]
    rw [← Category.assoc ((chains V).d (n+1) n),← (map f).comm]
    simp only [Category.assoc]
    simp only [generator_map_assoc,generator_subdiv_succ,hf]

lemma prism_map (n : ℕ) :
    prism b n ≫ (map f).f (n+1) = (map f).f n ≫ prism c n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply hom_ext
    intro v
    rw [← Category.assoc,generator_prism_succ]
    simp only [Category.assoc]
    rw [← map_cone,← Category.assoc]
    have inner : (generator v - generator v ≫ subdiv b (n+1) -
        generator v ≫ (chains V).d (n+1) n ≫ prism b n) ≫ (map f).f (n+1) =
        generator (f ∘ v) - generator (f ∘ v) ≫ subdiv c (n+1) -
          generator (f ∘ v) ≫ (chains W).d (n+1) n ≫ prism c n := by
      simp only [Preadditive.sub_comp,Category.assoc]
      rw [subdiv_map b c f hf,ih]
      rw [← Category.assoc ((chains V).d (n+1) n),← (map f).comm]
      simp only [Category.assoc,generator_map,generator_map_assoc]
    rw [inner,hf]
    rw [generator_map_assoc,generator_prism_succ]

end AffineChains

end

end OAI
