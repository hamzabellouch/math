import OAI.GroupTheory.UniversalGroup.CellularApproximation

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Simplicial
open Set Metric Topology BigOperators
open scoped Classical
universe u v
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

def restrict (S : Finset V) : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ K ∧ s ⊆ S}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨(K.isRelLowerSet_faces hs.1).1,fun t hts ht =>
      ⟨K.isRelLowerSet_faces.mem_of_le hs.1 hts ht,hts.trans hs.2⟩⟩

lemma restrict_le (S : Finset V) : restrict K S ≤ K := fun _ h => h.1
instance finiteFace_restrict (S : Finset V) : Finite (Face (restrict K S)) := by
  let f : Face (restrict K S) → {s : Finset V // s ∈ S.powerset} :=
    fun s => ⟨s.1,Finset.mem_powerset.mpr s.2.2⟩
  apply Finite.of_injective f
  intro a b h
  have hh := congrArg (fun z : {s : Finset V // s ∈ S.powerset} => z.1) h
  exact Subtype.ext hh

def restrictInclusion (S : Finset V) : C(Space (restrict K S),Space K) :=
  ⟨inclusion (restrict K S) K (fun _ h => restrict_le K S h),continuous_inclusion _ _ _⟩

lemma compactMap_finiteRestriction {A : Type v} [TopologicalSpace A] [CompactSpace A] (f : C(A,Space K)) :
    ∃ S : Finset V, ∃ F : C(A,Space (restrict K S)), (restrictInclusion K S).comp F = f := by
  obtain ⟨S,hS⟩ := compact_bounded_vertices K (isCompact_range f.continuous)
  let F : A → Space (restrict K S) := fun a =>
    ⟨(f a).1,(f a).2.1,(f a).2.2.1,(f a).2.2.2,hS (f a) (mem_range_self a)⟩
  have hc : Continuous F := (inclusion_closedEmbedding (restrict K S) K
    (fun _ h => restrict_le K S h)).isEmbedding.continuous_iff.mpr f.continuous
  exact ⟨S,⟨F,hc⟩,rfl⟩

end UniversalFInfinity.Simplicial

namespace UniversalFInfinity.Milnor

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy
universe u v w
variable (G : Type u) [Group G] (N : Type v) [DecidableEq N] [Nontrivial N]
variable (A : Type w) [Group A]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

abbrev StagePi (S : Shapes G) := HomotopyGroup N (Simplicial.Space (stage G S)) (stagePoint G S)
abbrev StageValues (S : Shapes G) := A →* StagePi G N S

def valueHom (S T : Shapes G) (h : S ⊆ T) : StageValues G N A S →* StageValues G N A T where
  toFun f := (stageHom G N S T h).comp f
  map_one' := by ext; rfl
  map_mul' f g := by ext a; exact (stageHom G N S T h).map_mul (f a) (g a)

instance : DirectedSystem (StageValues G N A) (fun S T h => valueHom G N A S T h) where
  map_self _ f := by ext a; exact DirectedSystem.map_self (f := fun _ _ h => stageHom G N _ _ h) (f a)
  map_map _ _ _ h₁ h₂ f := by ext a; exact DirectedSystem.map_map (f := fun _ _ h => stageHom G N _ _ h) h₁ h₂ (f a)

abbrev ControlledValues := DirectLimit (StageValues G N A) (valueHom G N A)

def value (S : Shapes G) (f : StageValues G N A S) : ControlledValues G N A := Quotient.mk _ ⟨S,f⟩

lemma value_eq_of_le (S T : Shapes G) (h : S ⊆ T) (f : StageValues G N A S) :
    value G N A S f = value G N A T ((stageHom G N S T h).comp f) := DirectLimit.eq_of_le ⟨S,f⟩ T h

lemma value_eq_one_iff (S : Shapes G) (f : StageValues G N A S) :
    value G N A S f = 1 ↔ ∃ T, ∃ h : S ⊆ T, (stageHom G N S T h).comp f = 1 :=
  DirectLimit.exists_eq_one (f := valueHom G N A) ⟨S,f⟩

lemma value_mul (S : Shapes G) (f g : StageValues G N A S) :
    value G N A S (f*g) = value G N A S f * value G N A S g :=
  (DirectLimit.mul_def (f := valueHom G N A) S f g).symm
end

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy unitInterval
universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (N : Type w) [DecidableEq N] [Nontrivial N]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

variable (φ : G →* H) (α : ℕ → ℕ) (S : Shapes G) (T : Shapes H)
variable (hv : ∀ s : Face (stage G S), faceImage φ α s.1 ∈ stage H T)

def stageMap : C(Simplicial.Space (stage G S), Simplicial.Space (stage H T)) :=
  mapC _ _ (vertexMap φ α) hv

lemma stageMap_point (hα : α 0 = 0) : stageMap φ α S T hv (stagePoint G S) = stagePoint H T := by
  apply Subtype.ext
  change (Finsupp.single (0,(1:G)) (1:ℝ)).mapDomain (vertexMap φ α) = Finsupp.single (0,1) 1
  rw [Finsupp.mapDomain_single]
  congr 1
  exact Prod.ext hα φ.map_one

variable (hα : α 0 = 0)
def stageMapHom : StagePi G N S →* StagePi H N T :=
  HomotopyFunctor.mapHom (stageMap φ α S T hv) (stageMap_point φ α S T hv hα)
def stageMapValue : ControlledValues H N (StagePi G N S) :=
  value H N _ T (stageMapHom N φ α S T hv hα)

lemma stageMapValue_congrTarget (U : Shapes H)
    (hu : ∀ s : Face (stage G S), faceImage φ α s.1 ∈ stage H U) :
    stageMapValue N φ α S T hv hα = stageMapValue N φ α S U hu hα := by
  apply Quotient.sound
  refine ⟨T ∪ U,Finset.subset_union_left,Finset.subset_union_right,?_⟩
  apply MonoidHom.ext
  intro a
  induction a using Quotient.inductionOn with | h p =>
  apply congrArg Quotient.mk'
  apply Subtype.ext
  ext z
  rfl

lemma stageMapValue_eq_of_homotopy (ψ : G →* H) (β : ℕ → ℕ)
    (hw : ∀ s : Face (stage G S), faceImage ψ β s.1 ∈ stage H T) (hβ : β 0 = 0)
    (F : (stageMap φ α S T hv).Homotopy (stageMap ψ β S T hw))
    (hF : ∀ t, F (t,stagePoint G S) = stagePoint H T) :
    stageMapValue N φ α S T hv hα = stageMapValue N ψ β S T hw hβ := by
  apply congrArg (value H N _ T)
  ext a
  exact HomotopyFunctor.map_eq_of_homotopy _ _ _ _ F hF a

lemma image_stage_valid (hαi : Function.Injective α) (s : Face (stage G S)) :
    faceImage φ α s.1 ∈ stage H (imageShapes φ α (basedShapes G S)) :=
  orbitSpan_mono (Finset.subset_insert _ _) (faceImage_controlled φ α hαi (basedShapes G S) s)

def mapValue (hαi : Function.Injective α) : ControlledValues H N (StagePi G N S) :=
  stageMapValue N φ α S _ (image_stage_valid φ α S hαi) hα

lemma mapValue_eq (hαi : Function.Injective α) :
    mapValue N φ α S hα hαi = stageMapValue N φ α S T hv hα :=
  stageMapValue_congrTarget N φ α S _ _ hα T hv
end

open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy unitInterval
universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (N : Type w) [DecidableEq N] [Nontrivial N]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

variable (φ : G →* H) (S : Shapes G) (α β : ℕ → ℕ)
variable (hα : Function.Injective α) (hβ : Function.Injective β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
include hα hα0 in
lemma relayerStageLeftValid (s : Face (stage G S)) :
    faceImage φ α s.1 ∈ stage H (relayerTarget φ (basedShapes G S) α β) :=
  orbitSpan_mono (Finset.subset_insert _ _) (relayerLeftMapValid φ (basedShapes G S) α β hα hα0 s)
include hβ hβ0 in
lemma relayerStageRightValid (s : Face (stage G S)) :
    faceImage φ β s.1 ∈ stage H (relayerTarget φ (basedShapes G S) α β) :=
  orbitSpan_mono (Finset.subset_insert _ _) (relayerRightMapValid φ (basedShapes G S) α β hβ hβ0 s)

def relayerToStage : C(Simplicial.Space (orbitSpan (relayerTarget φ (basedShapes G S) α β)),
    Simplicial.Space (stage H (relayerTarget φ (basedShapes G S) α β))) :=
  ⟨inclusion _ _ (fun _ hs => orbitSpan_mono (Finset.subset_insert _ _) hs),continuous_inclusion _ _ _⟩

def relayerStageHomotopy :
    (stageMap φ α S _ (relayerStageLeftValid φ S α β hα hα0)).Homotopy
      (stageMap φ β S _ (relayerStageRightValid φ S α β hβ hβ0)) :=
  (ContinuousMap.Homotopy.refl (relayerToStage φ S α β)).comp
    (relayerHomotopy φ (basedShapes G S) α β hα hβ hα0 hβ0)

lemma relayerStageHomotopy_fixed (t : I) :
    relayerStageHomotopy φ S α β hα hβ hα0 hβ0 (t,stagePoint G S) =
      stagePoint H (relayerTarget φ (basedShapes G S) α β) := by
  change relayerToStage φ S α β (relayerHomotopy φ (basedShapes G S) α β hα hβ hα0 hβ0 (t,stagePoint G S)) = _
  rw [relayerHomotopy_fixed φ (basedShapes G S) α β hα hβ hα0 hβ0 (stagePoint G S) 1 rfl]
  exact stageMap_point φ α S _ (relayerStageLeftValid φ S α β hα hα0) hα0

lemma mapValue_relayer : mapValue N φ α S hα0 hα = mapValue N φ β S hβ0 hβ := by
  rw [mapValue_eq N φ α S _ (relayerStageLeftValid φ S α β hα hα0) hα0 hα,
    mapValue_eq N φ β S _ (relayerStageRightValid φ S α β hβ hβ0) hβ0 hβ]
  exact stageMapValue_eq_of_homotopy N φ α S _ _ hα0 φ β _ hβ0
    (relayerStageHomotopy φ S α β hα hβ hα0 hβ0) (relayerStageHomotopy_fixed φ S α β hα hβ hα0 hβ0)
end UniversalFInfinity.Milnor

namespace UniversalFInfinity.Simplicial

section
open Set Metric Topology BigOperators
open scoped Classical Topology.Homotopy
universe u v
variable {V : Type u} (K : PreAbstractSimplicialComplex V)
variable {N : Type v} [Nonempty N] {x : Space K}

lemma loop_finite_restriction (p : GenLoop N (Space K) x) :
    ∃ S : Finset V, ∃ y : Space (restrict K S),
      ∃ hy : restrictInclusion K S y = x,
      ∃ q : GenLoop N (Space (restrict K S)) y,
        HomotopyFunctor.loopMap (restrictInclusion K S) hy q = p := by
  obtain ⟨S,F,hF⟩ := compactMap_finiteRestriction K p.1
  let z : N → unitInterval := fun _ => 0
  have hz : z ∈ Cube.boundary N := ⟨Classical.arbitrary N,Or.inl rfl⟩
  have hy : restrictInclusion K S (F z) = x :=
    (ContinuousMap.congr_fun hF z).trans (GenLoop.boundary p z hz)
  let q : GenLoop N (Space (restrict K S)) (F z) := ⟨F,by
    intro t ht
    apply inclusion_injective (restrict K S) K (fun _ h => restrict_le K S h)
    exact (ContinuousMap.congr_fun hF t).trans ((GenLoop.boundary p t ht).trans hy.symm)⟩
  refine ⟨S,F z,hy,q,?_⟩
  apply Subtype.ext
  exact hF
end

section
open Set Metric Topology BigOperators
open scoped Classical
universe u v w
variable {V : Type u} {W : Type v} {U : Type w}

def tensor (x : V →₀ ℝ) (y : W →₀ ℝ) : V × W →₀ ℝ :=
  Finsupp.onFinset (x.support ×ˢ y.support) (fun p => x p.1 * y p.2) (by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hp),
      Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hp)⟩)

lemma tensor_apply (x : V →₀ ℝ) (y : W →₀ ℝ) (p : V × W) : tensor x y p = x p.1*y p.2 := rfl
lemma tensor_support (x : V →₀ ℝ) (y : W →₀ ℝ) :
    (tensor x y).support = x.support ×ˢ y.support := by
  ext p
  simp only [Finsupp.mem_support_iff,tensor_apply,Finset.mem_product,mul_ne_zero_iff]
lemma tensor_sum (x : V →₀ ℝ) (y : W →₀ ℝ) :
    (tensor x y).sum (fun _ r => r) = x.sum (fun _ r => r)*y.sum (fun _ r => r) := by
  rw [Finsupp.sum,tensor_support,Finset.sum_product]
  simp only [tensor_apply,Finsupp.sum,← Finset.mul_sum,← Finset.sum_mul]

variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (M : PreAbstractSimplicialComplex U)
variable (p : V × W → U) (hp : ∀ s : Face K, ∀ t : Face L, (s.1 ×ˢ t.1).image p ∈ M)

def pairMap (x : Space K) (y : Space L) : Space M := by
  let z := (tensor x.1 y.1).mapDomain p
  have hz : z.sum (fun _ r => r) = 1 := by
    rw [push_sum,tensor_sum,x.2.2.1,y.2.2.1,mul_one]
  refine ⟨z,?_,hz,?_⟩
  · exact push_nonneg p _ (fun a => mul_nonneg (x.2.1 a.1) (y.2.1 a.2))
  · apply M.isRelLowerSet_faces.mem_of_le (hp ⟨x.1.support,x.2.2.2⟩ ⟨y.1.support,y.2.2.2⟩)
    · exact Finsupp.mapDomain_support.trans (by rw [tensor_support])
    · exact support_nonempty hz

lemma pairMap_support (x : Space K) (y : Space L) :
    (pairMap K L M p hp x y).1.support ⊆ (x.1.support ×ˢ y.1.support).image p := by
  exact Finsupp.mapDomain_support.trans (by rw [tensor_support])

lemma continuous_pairMap_faces (s : Face K) (t : Face L) :
    Continuous (fun q : SimplexDisk.Simplex s.1 × SimplexDisk.Simplex t.1 =>
      pairMap K L M p hp (faceMap K s q.1) (faceMap L t q.2)) := by
  apply continuous_of_support_subset M _ ⟨(s.1 ×ˢ t.1).image p,hp s t⟩
  · intro q
    exact (pairMap_support K L M p hp _ _).trans
      (Finset.image_subset_image (Finset.product_subset_product (weight_support_subset _ _) (weight_support_subset _ _)))
  · intro b
    have he : (fun q : SimplexDisk.Simplex s.1 × SimplexDisk.Simplex t.1 =>
        (pairMap K L M p hp (faceMap K s q.1) (faceMap L t q.2)).1 b) =
        fun q => ∑ a : s.1, ∑ c : t.1, if p (a.1,c.1) = b then q.1.1 a * q.2.1 c else 0 := by
      funext q
      change ((tensor (weight s.1 q.1) (weight t.1 q.2)).mapDomain p) b = _
      rw [push_apply p _ (s.1 ×ˢ t.1) (by rw [tensor_support]; exact Finset.product_subset_product (weight_support_subset _ _) (weight_support_subset _ _)),Finset.sum_product]
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro c _
      simp only [tensor_apply,weight_apply]
    rw [he]
    apply continuous_finsetSum
    intro a _
    apply continuous_finsetSum
    intro c _
    split_ifs
    · exact (((continuous_apply a).comp continuous_subtype_val).comp continuous_fst).mul
        (((continuous_apply c).comp continuous_subtype_val).comp continuous_snd)
    · exact continuous_const

instance [Finite (Face K)] : CompactSpace (Space K) := by
  have hc : IsCompact (⋃ s : Face K, Set.range (faceMap K s)) :=
    isCompact_iUnion (fun s => isCompact_range (continuous_faceMap K s))
  have he : (⋃ s : Face K, Set.range (faceMap K s)) = Set.univ := by
    ext x
    simp only [mem_iUnion,mem_univ,iff_true]
    exact ⟨⟨x.1.support,x.2.2.2⟩,coordinates K _ x (Finset.Subset.refl _),faceMap_coordinates K _ _ _⟩
  exact ⟨he ▸ hc⟩

lemma continuous_prod_faces_iff [Finite (Face K)] {Y : Type*} [TopologicalSpace Y]
    (f : Space K × Space L → Y) : Continuous f ↔
    ∀ s : Face K, ∀ t : Face L, Continuous (fun q : SimplexDisk.Simplex s.1 × SimplexDisk.Simplex t.1 =>
      f (faceMap K s q.1,faceMap L t q.2)) := by
  constructor
  · intro hf s t
    exact hf.comp (((continuous_faceMap K s).comp continuous_fst).prodMk ((continuous_faceMap L t).comp continuous_snd))
  · intro hf
    rw [continuous_prod_iff]
    intro t
    have hc : Continuous (fun q : SimplexDisk.Simplex t.1 × Space K => f (q.2,faceMap L t q.1)) := by
      rw [continuous_prod_iff]
      intro s
      exact (hf s t).comp continuous_swap
    exact hc.comp continuous_swap

lemma continuous_pairMap [Finite (Face K)] : Continuous (fun q : Space K × Space L => pairMap K L M p hp q.1 q.2) :=
  (continuous_prod_faces_iff K L _).mpr (continuous_pairMap_faces K L M p hp)

def pairMapC [Finite (Face K)] : C(Space K × Space L,Space M) :=
  ⟨fun q => pairMap K L M p hp q.1 q.2,continuous_pairMap K L M p hp⟩
end

section
open Set Metric Topology BigOperators
open scoped Classical unitInterval
universe u v
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (f g : C(Space K,Space L)) (c : Face K → Face L)
variable (hf : ∀ s : Face K, ∀ x : Space K, x.1.support ⊆ s.1 → (f x).1.support ⊆ (c s).1)
variable (hg : ∀ s : Face K, ∀ x : Space K, x.1.support ⊆ s.1 → (g x).1.support ⊆ (c s).1)

def carrierBlend (t : I) (x : Space K) : Space L :=
  blend L (c ⟨x.1.support,x.2.2.2⟩) (f x) (g x)
    (hf _ x (Finset.Subset.refl _)) (hg _ x (Finset.Subset.refl _)) t

lemma continuous_carrierBlend : Continuous (fun p : I × Space K => carrierBlend K L f g c hf hg p.1 p.2) := by
  rw [continuous_prod_iff]
  intro s
  apply continuous_of_support_subset L _ (c s)
  · intro p
    exact (blend_support _ _ p.1).trans (Finset.union_subset
      (hf s _ (weight_support_subset _ _)) (hg s _ (weight_support_subset _ _)))
  · intro b
    change Continuous (fun p : I × SimplexDisk.Simplex s.1 =>
      (1-(p.1:ℝ)) * (f (faceMap K s p.2)).1 b + (p.1:ℝ) * (g (faceMap K s p.2)).1 b)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_eval L b).comp (f.continuous.comp ((continuous_faceMap K s).comp continuous_snd)))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_eval L b).comp (g.continuous.comp ((continuous_faceMap K s).comp continuous_snd))))

def carrierHomotopy : f.Homotopy g where
  toFun p := carrierBlend K L f g c hf hg p.1 p.2
  continuous_toFun := continuous_carrierBlend K L f g c hf hg
  map_zero_left _ := blend_zero L _ _ _ _ _
  map_one_left _ := blend_one L _ _ _ _ _

lemma carrierHomotopy_fixed (x : Space K) (h : f x = g x) (t : I) :
    carrierHomotopy K L f g c hf hg (t,x) = f x := by
  apply Subtype.ext
  change (1-(t:ℝ)) • (f x).1 + (t:ℝ) • (g x).1 = (f x).1
  rw [←h,←add_smul,sub_add_cancel,one_smul]
end

section
open Set Metric Topology BigOperators
open scoped Classical unitInterval
universe u v
variable {V : Type u} {W : Type v}

lemma tensor_single (v : V) (w : W) (a b : ℝ) :
    tensor (Finsupp.single v a) (Finsupp.single w b) = Finsupp.single (v,w) (a*b) := by
  ext p
  simp only [tensor_apply,Finsupp.single_apply]
  by_cases hv : v = p.1 <;> by_cases hw : w = p.2
  · have h : (v,w) = p := Prod.ext hv hw
    simp only [ite_eq_left hv,ite_eq_left hw,ite_eq_left h]
  · have h : (v,w) ≠ p := fun h => hw (congrArg Prod.snd h)
    simp only [ite_eq_left hv,ite_eq_right hw,ite_eq_right h,mul_zero]
  · have h : (v,w) ≠ p := fun h => hv (congrArg Prod.fst h)
    simp only [ite_eq_right hv,ite_eq_left hw,ite_eq_right h,zero_mul]
  · have h : (v,w) ≠ p := fun h => hv (congrArg Prod.fst h)
    simp only [ite_eq_right hv,ite_eq_right hw,ite_eq_right h,zero_mul]

variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (p : V × V → W) (hp : ∀ s t : Face K, (s.1 ×ˢ t.1).image p ∈ L)

include hp in
lemma diagonal_face (s : Face K) : s.1.image (fun v => p (v,v)) ∈ L := by
  apply L.isRelLowerSet_faces.mem_of_le (hp s s) _ ((K.isRelLowerSet_faces s.2).1.image _)
  intro z hz
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨(v,v),Finset.mem_product.mpr ⟨hv,hv⟩,rfl⟩

variable [Finite (Face K)]
def productDiagonal : C(Space K,Space L) :=
  (pairMapC K K L p hp).comp ((ContinuousMap.id _).prodMk (ContinuousMap.id _))
def vertexDiagonal : C(Space K,Space L) := mapC K L (fun v => p (v,v)) (diagonal_face K L p hp)

def diagonalCarrier (s : Face K) : Face L := ⟨(s.1 ×ˢ s.1).image p,hp s s⟩
lemma productDiagonal_carried (s : Face K) (x : Space K) (hx : x.1.support ⊆ s.1) :
    (productDiagonal K L p hp x).1.support ⊆ (diagonalCarrier K L p hp s).1 :=
  (pairMap_support K K L p hp x x).trans (Finset.image_subset_image (Finset.product_subset_product hx hx))
omit [Finite (Face K)] in
lemma vertexDiagonal_carried (s : Face K) (x : Space K) (hx : x.1.support ⊆ s.1) :
    (vertexDiagonal K L p hp x).1.support ⊆ (diagonalCarrier K L p hp s).1 := by
  apply (map_support K L (fun v => p (v,v)) (diagonal_face K L p hp) x).trans
  intro z hz
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨(v,v),Finset.mem_product.mpr ⟨hx hv,hx hv⟩,rfl⟩

def diagonalHomotopy : (productDiagonal K L p hp).Homotopy (vertexDiagonal K L p hp) :=
  carrierHomotopy K L _ _ (diagonalCarrier K L p hp)
    (productDiagonal_carried K L p hp) (vertexDiagonal_carried K L p hp)

omit [Finite (Face K)] in
lemma pairMap_pure {M : PreAbstractSimplicialComplex V} (q : V × V → W)
    (hq : ∀ s : Face K, ∀ t : Face M, (s.1 ×ˢ t.1).image q ∈ L)
    (x : Space K) (y : Space M) (v w : V)
    (hx : x.1 = Finsupp.single v 1) (hy : y.1 = Finsupp.single w 1) :
    (pairMap K M L q hq x y).1 = Finsupp.single (q (v,w)) 1 := by
  change (tensor x.1 y.1).mapDomain q = _
  rw [hx,hy,tensor_single,Finsupp.mapDomain_single,one_mul]

lemma diagonalHomotopy_fixed (x : Space K) (v : V) (hx : x.1 = Finsupp.single v 1) (t : I) :
    diagonalHomotopy K L p hp (t,x) = vertexDiagonal K L p hp x := by
  have h : productDiagonal K L p hp x = vertexDiagonal K L p hp x := by
    apply Subtype.ext
    rw [show (productDiagonal K L p hp x).1 = Finsupp.single (p (v,v)) 1 from
      pairMap_pure K L p hp x x v v hx hx]
    change Finsupp.single (p (v,v)) 1 = x.1.mapDomain (fun v => p (v,v))
    rw [hx,Finsupp.mapDomain_single]
  exact (carrierHomotopy_fixed K L _ _ _ _ _ x h t).trans h
end

open Set Metric Topology BigOperators
open scoped Classical
universe u v w
variable {V : Type u} {W : Type v} {U : Type w}
lemma tensor_single_right_push (x : V →₀ ℝ) (w : W) (p : V × W → U) :
    (tensor x (Finsupp.single w 1)).mapDomain p = x.mapDomain (fun v => p (v,w)) := by
  ext b
  rw [push_apply p _ (x.support ×ˢ {w}) (by
    rw [tensor_support]
    exact Finset.product_subset_product (Finset.Subset.refl _) Finsupp.support_single_subset)]
  rw [push_apply (fun v => p (v,w)) x x.support (Finset.Subset.refl _),Finset.sum_product]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Finset.sum_singleton,tensor_apply,Finsupp.single_eq_same,mul_one]
lemma tensor_single_left_push (v : V) (y : W →₀ ℝ) (p : V × W → U) :
    (tensor (Finsupp.single v 1) y).mapDomain p = y.mapDomain (fun w => p (v,w)) := by
  ext b
  rw [push_apply p _ ({v} ×ˢ y.support) (by
    rw [tensor_support]
    exact Finset.product_subset_product Finsupp.support_single_subset (Finset.Subset.refl _))]
  rw [push_apply (fun w => p (v,w)) y y.support (Finset.Subset.refl _),Finset.sum_product,Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro w _
  simp only [tensor_apply,Finsupp.single_eq_same,one_mul]
end UniversalFInfinity.Simplicial

end

end OAI
