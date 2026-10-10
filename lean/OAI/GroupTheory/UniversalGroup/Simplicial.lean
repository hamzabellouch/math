import OAI.GroupTheory.UniversalGroup.SimplexDisk

namespace OAI

noncomputable section

open Set Metric Topology BigOperators

namespace UniversalFInfinity.Simplicial

section
universe u v
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

def Space := {w : V →₀ ℝ | (∀ v, 0 ≤ w v) ∧ w.sum (fun _ r => r) = 1 ∧ w.support ∈ K}
abbrev Face := {s : Finset V // s ∈ K}

lemma support_nonempty {w : V →₀ ℝ} (h : w.sum (fun _ r => r) = 1) : w.support.Nonempty := by
  classical
  by_contra hn
  have hz : w = 0 := by
    apply Finsupp.support_eq_empty.mp
    exact Finset.not_nonempty_iff_eq_empty.mp hn
  simp [hz] at h

lemma face_nonempty (s : Face K) : s.1.Nonempty := (K.isRelLowerSet_faces s.2).1

noncomputable def weight (s : Finset V) (x : SimplexDisk.Simplex s) : V →₀ ℝ :=
  Finsupp.embDomain (Function.Embedding.subtype (· ∈ s)) (Finsupp.equivFunOnFinite.symm x.1)

lemma weight_apply (s : Finset V) (x : SimplexDisk.Simplex s) (v : s) :
    weight s x v = x.1 v := by
  exact Finsupp.embDomain_apply_self _ _ _

lemma weight_apply_not (s : Finset V) (x : SimplexDisk.Simplex s) {v : V} (hv : v ∉ s) :
    weight s x v = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨w,hw⟩
  exact hv (hw ▸ w.2)

lemma weight_nonneg (s : Finset V) (x : SimplexDisk.Simplex s) (v : V) : 0 ≤ weight s x v := by
  classical
  by_cases hv : v ∈ s
  · exact (weight_apply s x ⟨v,hv⟩) ▸ x.2.1 ⟨v,hv⟩
  · rw [weight_apply_not _ _ hv]

lemma weight_sum (s : Finset V) (x : SimplexDisk.Simplex s) : (weight s x).sum (fun _ r => r) = 1 := by
  rw [weight,Finsupp.sum_embDomain,Finsupp.sum_fintype _ _ (fun _ => rfl)]
  exact x.2.2

lemma weight_support_subset (s : Finset V) (x : SimplexDisk.Simplex s) : (weight s x).support ⊆ s := by
  classical
  intro v hv
  by_contra hn
  exact Finsupp.mem_support_iff.mp hv (weight_apply_not _ _ hn)

noncomputable def faceMap (s : Face K) (x : SimplexDisk.Simplex s.1) : Space K :=
  ⟨weight s.1 x,weight_nonneg _ _,weight_sum _ _,
    K.isRelLowerSet_faces.mem_of_le s.2 (weight_support_subset _ _) (support_nonempty (weight_sum _ _))⟩

noncomputable def quotient (x : Σ s : Face K, SimplexDisk.Simplex s.1) : Space K := faceMap K x.1 x.2

instance : TopologicalSpace (Space K) := TopologicalSpace.coinduced (quotient K) inferInstance

lemma continuous_iff {Y : Type v} [TopologicalSpace Y] (f : Space K → Y) :
    Continuous f ↔ ∀ s : Face K, Continuous (f ∘ faceMap K s) := by
  rw [continuous_coinduced_dom]
  exact continuous_sigma_iff

lemma continuous_faceMap (s : Face K) : Continuous (faceMap K s) :=
  (continuous_coinduced_rng : Continuous (quotient K)).comp (continuous_sigmaMk (i := s))

lemma continuous_eval (v : V) : Continuous (fun x : Space K => x.1 v) := by
  classical
  rw [continuous_iff]
  intro s
  by_cases hv : v ∈ s.1
  · have he : (fun x : Space K => x.1 v) ∘ faceMap K s = (fun x : SimplexDisk.Simplex s.1 => x.1 ⟨v,hv⟩) := by
      funext x
      exact weight_apply s.1 x ⟨v,hv⟩
    rw [he]
    exact (continuous_apply (⟨v,hv⟩ : s.1)).comp continuous_subtype_val
  · have he : (fun x : Space K => x.1 v) ∘ faceMap K s = (fun _ => (0:ℝ)) := by
      funext x
      exact weight_apply_not _ _ hv
    rw [he]
    exact continuous_const

instance : T2Space (Space K) :=
  T2Space.of_injective_continuous (f := fun x : Space K => (x.1 : V → ℝ))
    (fun _ _ h => Subtype.ext (Finsupp.ext fun v => congrFun h v))
    (continuous_pi fun v => continuous_eval K v)

lemma faceMap_injective (s : Face K) : Function.Injective (faceMap K s) := by
  intro x y h
  apply Subtype.ext
  funext v
  have hh := congrArg (fun p : Space K => p.1 v) h
  exact (weight_apply _ _ _).symm.trans (hh.trans (weight_apply _ _ _))

lemma faceMap_closedEmbedding (s : Face K) : IsClosedEmbedding (faceMap K s) :=
  (continuous_faceMap K s).isClosedEmbedding (faceMap_injective K s)

noncomputable def coordinates (s : Finset V) (x : Space K) (h : x.1.support ⊆ s) : SimplexDisk.Simplex s := by
  refine ⟨fun v => x.1 v,fun v => x.2.1 _,?_⟩
  rw [Finset.sum_coe_sort]
  exact (x.1.sum_of_support_subset h _ (fun _ _ => rfl)).symm.trans x.2.2.1

lemma faceMap_coordinates (s : Face K) (x : Space K) (h : x.1.support ⊆ s.1) :
    faceMap K s (coordinates K s.1 x h) = x := by
  classical
  apply Subtype.ext
  ext v
  by_cases hv : v ∈ s.1
  · exact weight_apply _ _ ⟨v,hv⟩
  · change weight s.1 _ v = x.1 v
    rw [weight_apply_not _ _ hv,Finsupp.notMem_support_iff.mp (fun hh => hv (h hh))]

lemma range_faceMap (s : Face K) : Set.range (faceMap K s) = {x | x.1.support ⊆ s.1} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact weight_support_subset _ _
  · intro h
    exact ⟨coordinates K s.1 x h,faceMap_coordinates K s x h⟩

lemma quotient_surjective : Function.Surjective (quotient K) := by
  intro x
  exact ⟨⟨⟨x.1.support,x.2.2.2⟩,coordinates K x.1.support x (subset_refl _)⟩,
    faceMap_coordinates K ⟨x.1.support,x.2.2.2⟩ x (subset_refl _)⟩

lemma isClosed_iff (A : Set (Space K)) :
    IsClosed A ↔ ∀ s : Face K, IsClosed ((faceMap K s) ⁻¹' A) := by
  rw [isClosed_coinduced]
  exact isClosed_sigma_iff

lemma support_eq_iff (s : Face K) (x : SimplexDisk.Simplex s.1) :
    (faceMap K s x).1.support = s.1 ↔ ∀ v, 0 < x.1 v := by
  classical
  constructor
  · intro he v
    have hn : weight s.1 x v ≠ 0 := by
      apply Finsupp.mem_support_iff.mp
      change v.1 ∈ (faceMap K s x).1.support
      rw [he]
      exact v.2
    rw [weight_apply] at hn
    exact lt_of_le_of_ne (x.2.1 v) (Ne.symm hn)
  · intro hp
    apply Finset.Subset.antisymm (weight_support_subset _ _)
    intro v hv
    apply Finsupp.mem_support_iff.mpr
    rw [weight_apply _ _ ⟨v,hv⟩]
    exact ne_of_gt (hp ⟨v,hv⟩)

end

section
open Set Metric Topology BigOperators
open scoped Classical
universe u v w
variable {V : Type u} {W : Type v} {T : Type w}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

lemma continuous_of_support_subset [TopologicalSpace T] (f : T → Space K) (s : Face K)
    (hs : ∀ x, (f x).1.support ⊆ s.1) (hc : ∀ v, Continuous fun x => (f x).1 v) : Continuous f := by
  let c : T → SimplexDisk.Simplex s.1 := fun x => coordinates K s.1 (f x) (hs x)
  have hcc : Continuous c := (continuous_pi fun v : s.1 => hc v.1).subtype_mk _
  have he : f = (faceMap K s) ∘ c := by
    funext x
    exact (faceMap_coordinates K s (f x) (hs x)).symm
  rw [he]
  exact (continuous_faceMap K s).comp hcc

lemma push_apply (f : V → W) (w : V →₀ ℝ) (s : Finset V) (hs : w.support ⊆ s) (b : W) :
    (w.mapDomain f) b = ∑ a ∈ s, if f a = b then w a else 0 := by
  classical
  rw [Finsupp.mapDomain,Finsupp.sum_apply]
  rw [w.sum_of_support_subset hs]
  · apply Finset.sum_congr rfl
    intro a _
    simp only [Finsupp.single_apply]
  · intro a _
    simp

lemma push_nonneg (f : V → W) (w : V →₀ ℝ) (hw : ∀ v, 0 ≤ w v) (b : W) :
    0 ≤ (w.mapDomain f) b := by
  classical
  rw [push_apply f w w.support (Finset.Subset.refl _) b]
  exact Finset.sum_nonneg fun a _ => by split; exact hw a; exact le_rfl

lemma push_sum (f : V → W) (w : V →₀ ℝ) :
    (w.mapDomain f).sum (fun _ r => r) = w.sum (fun _ r => r) :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

def map (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (x : Space K) : Space L := by
  classical
  refine ⟨x.1.mapDomain f,push_nonneg f x.1 x.2.1,?_,?_⟩
  · rw [push_sum]; exact x.2.2.1
  · exact L.isRelLowerSet_faces.mem_of_le (hf ⟨x.1.support,x.2.2.2⟩) Finsupp.mapDomain_support
      (support_nonempty (by rw [push_sum]; exact x.2.2.1))

lemma map_support (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (x : Space K) :
    (map K L f hf x).1.support ⊆ x.1.support.image f := by
  classical
  exact Finsupp.mapDomain_support

lemma continuous_map (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) : Continuous (map K L f hf) := by
  classical
  rw [continuous_iff]
  intro s
  apply continuous_of_support_subset L _ ⟨s.1.image f,hf s⟩
  · intro x
    exact (map_support K L f hf _).trans (Finset.image_subset_image (weight_support_subset _ _))
  · intro b
    have he : (fun x : SimplexDisk.Simplex s.1 => ((map K L f hf ∘ faceMap K s) x).1 b) =
        fun x => ∑ a : s.1, if f a.1 = b then x.1 a else 0 := by
      funext x
      change (Finsupp.mapDomain f (weight s.1 x)) b = _
      rw [push_apply f _ s.1 (weight_support_subset _ _) b,← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro a _
      rw [weight_apply]
    rw [he]
    apply continuous_finsetSum
    intro a _
    split_ifs
    · exact (continuous_apply a).comp continuous_subtype_val
    · exact continuous_const

def mapC (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) : C(Space K,Space L) :=
  ⟨map K L f hf,continuous_map K L f hf⟩

lemma map_id (hf : ∀ s : Face K, s.1.image id ∈ K) (x : Space K) : map K K id hf x = x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_id

lemma map_comp {U : Type*} (M : PreAbstractSimplicialComplex U)
    (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L)
    (g : W → U) (hg : ∀ s : Face L, s.1.image g ∈ M)
    (hgf : ∀ s : Face K, s.1.image (g ∘ f) ∈ M) (x : Space K) :
    map L M g hg (map K L f hf x) = map K M (g ∘ f) hgf x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_comp.symm

lemma quotient_quotientMap : IsQuotientMap (quotient K) :=
  ⟨⟨rfl⟩,quotient_surjective K⟩

lemma continuous_prod_iff [TopologicalSpace T] [LocallyCompactSpace T]
    {Y : Type*} [TopologicalSpace Y] (f : T × Space K → Y) :
    Continuous f ↔ ∀ s : Face K, Continuous (fun p : T × SimplexDisk.Simplex s.1 => f (p.1,faceMap K s p.2)) := by
  constructor
  · intro hf s
    exact hf.comp (continuous_fst.prodMk ((continuous_faceMap K s).comp continuous_snd))
  · intro hf
    apply (quotient_quotientMap K).continuous_lift_prod_right
    rw [continuous_def]
    intro O hO
    have hp : (fun p : T × (Σ s : Face K, SimplexDisk.Simplex s.1) => f (p.1,quotient K p.2)) ⁻¹' O =
      ⋃ s : Face K, (fun p : T × SimplexDisk.Simplex s.1 => (p.1,⟨s,p.2⟩)) ''
        ((fun p : T × SimplexDisk.Simplex s.1 => f (p.1,faceMap K s p.2)) ⁻¹' O) := by
      ext p
      simp only [mem_preimage,mem_iUnion,mem_image]
      constructor
      · intro h
        exact ⟨p.2.1,⟨p.1,p.2.2⟩,h,rfl⟩
      · rintro ⟨s,p,h,rfl⟩
        exact h
    rw [hp]
    apply isOpen_iUnion
    intro s
    exact (IsOpenMap.id.prodMap isOpenMap_sigmaMk) _ ((hf s).isOpen_preimage O hO)

end

section
open Set Metric Topology BigOperators
open scoped Classical unitInterval
universe u v
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

def mass : (V →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.lsum ℝ fun _ => LinearMap.id
lemma mass_apply (w : V →₀ ℝ) : mass w = w.sum (fun _ r => r) := rfl

lemma blend_support (x y : V →₀ ℝ) (t : I) :
    ((1-(t:ℝ)) • x + (t:ℝ) • y).support ⊆ x.support ∪ y.support :=
  Finsupp.support_add.trans (Finset.union_subset_union Finsupp.support_smul Finsupp.support_smul)

def blend (s : Face K) (x y : Space K) (hx : x.1.support ⊆ s.1) (hy : y.1.support ⊆ s.1) (t : I) : Space K := by
  let w := (1-(t:ℝ)) • x.1 + (t:ℝ) • y.1
  have hw : w.sum (fun _ r => r) = 1 := by
    rw [← mass_apply]
    simp only [w,map_add,map_smul,mass_apply,x.2.2.1,y.2.2.1,smul_eq_mul,mul_one]
    ring
  refine ⟨w,?_,hw,?_⟩
  · intro v
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (x.2.1 v)) (mul_nonneg t.2.1 (y.2.1 v))
  · exact K.isRelLowerSet_faces.mem_of_le s.2
      ((blend_support x.1 y.1 t).trans (Finset.union_subset hx hy)) (support_nonempty hw)

lemma blend_zero (s : Face K) (x y : Space K) (hx : x.1.support ⊆ s.1) (hy : y.1.support ⊆ s.1) :
    blend K s x y hx hy 0 = x := by
  apply Subtype.ext
  simp [blend]
lemma blend_one (s : Face K) (x y : Space K) (hx : x.1.support ⊆ s.1) (hy : y.1.support ⊆ s.1) :
    blend K s x y hx hy 1 = y := by
  apply Subtype.ext
  simp [blend]
lemma blend_self (s : Face K) (x : Space K) (hx : x.1.support ⊆ s.1) (t : I) :
    blend K s x x hx hx t = x := by
  apply Subtype.ext
  change (1-(t:ℝ)) • x.1 + (t:ℝ) • x.1 = x.1
  rw [← add_smul,sub_add_cancel,one_smul]

variable (f g : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (hg : ∀ s : Face K, s.1.image g ∈ L)
variable (hfg : ∀ s : Face K, s.1.image f ∪ s.1.image g ∈ L)

def straight (t : I) (x : Space K) : Space L :=
  blend L ⟨x.1.support.image f ∪ x.1.support.image g,hfg ⟨x.1.support,x.2.2.2⟩⟩
    (map K L f hf x) (map K L g hg x)
    ((map_support K L f hf x).trans Finset.subset_union_left)
    ((map_support K L g hg x).trans Finset.subset_union_right) t

lemma continuous_straight : Continuous (fun p : I × Space K => straight K L f g hf hg hfg p.1 p.2) := by
  rw [continuous_prod_iff]
  intro s
  apply continuous_of_support_subset L _ ⟨s.1.image f ∪ s.1.image g,hfg s⟩
  · intro p
    exact (blend_support _ _ p.1).trans (Finset.union_subset_union
      ((map_support K L f hf _).trans (Finset.image_subset_image (weight_support_subset _ _)))
      ((map_support K L g hg _).trans (Finset.image_subset_image (weight_support_subset _ _))))
  · intro b
    change Continuous (fun p : I × SimplexDisk.Simplex s.1 =>
      (1-(p.1:ℝ)) * (map K L f hf (faceMap K s p.2)).1 b +
        (p.1:ℝ) * (map K L g hg (faceMap K s p.2)).1 b)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_eval L b).comp ((continuous_map K L f hf).comp ((continuous_faceMap K s).comp continuous_snd)))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_eval L b).comp ((continuous_map K L g hg).comp ((continuous_faceMap K s).comp continuous_snd))))

def straightHomotopy : (mapC K L f hf).Homotopy (mapC K L g hg) where
  toFun p := straight K L f g hf hg hfg p.1 p.2
  continuous_toFun := continuous_straight K L f g hf hg hfg
  map_zero_left _ := blend_zero L _ _ _ _ _
  map_one_left _ := blend_one L _ _ _ _ _

lemma straightHomotopy_fixed (x : Space K) (h : map K L f hf x = map K L g hg x) (t : I) :
    straightHomotopy K L f g hf hg hfg (t,x) = map K L f hf x := by
  apply Subtype.ext
  change (1-(t:ℝ)) • (map K L f hf x).1 + (t:ℝ) • (map K L g hg x).1 = (map K L f hf x).1
  rw [←h,←add_smul,sub_add_cancel,one_smul]
end
open Set Metric Topology BigOperators
open scoped Classical
universe u
variable {V : Type u} (K L : PreAbstractSimplicialComplex V) (hKL : ∀ s ∈ K, s ∈ L)

def inclusion (x : Space K) : Space L := ⟨x.1,x.2.1,x.2.2.1,hKL _ x.2.2.2⟩

lemma inclusion_injective : Function.Injective (inclusion K L hKL) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : Space L => z.1) h)

lemma inclusion_faceMap (s : Face K) (x : SimplexDisk.Simplex s.1) :
    inclusion K L hKL (faceMap K s x) = faceMap L ⟨s.1,hKL _ s.2⟩ x := rfl

lemma continuous_inclusion : Continuous (inclusion K L hKL) := by
  rw [continuous_iff]
  intro s
  exact continuous_faceMap L ⟨s.1,hKL _ s.2⟩

lemma inclusion_isClosedMap : IsClosedMap (inclusion K L hKL) := by
  intro A hA
  rw [isClosed_iff]
  intro s
  let T : Set (Face K) := {t | t.1 ⊆ s.1}
  have hT : T.Finite := by
    have hf := s.1.powerset.finite_toSet.preimage (Subtype.val_injective : Function.Injective (Subtype.val : Face K → Finset V)).injOn
    convert hf using 1
    ext t
    simp only [T,mem_ofPred_eq,mem_preimage,Finset.mem_coe,Finset.mem_powerset]
  have hc : IsClosed (⋃ t ∈ T, inclusion K L hKL '' (A ∩ Set.range (faceMap K t))) := by
    apply hT.isClosed_biUnion
    intro t _
    exact (((isCompact_range (continuous_faceMap K t)).inter_left hA).image
      (continuous_inclusion K L hKL)).isClosed
  have he : inclusion K L hKL '' A ∩ Set.range (faceMap L s) =
      ⋃ t ∈ T, inclusion K L hKL '' (A ∩ Set.range (faceMap K t)) := by
    ext x
    simp only [mem_inter_iff,mem_image,mem_iUnion]
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hs⟩
      rw [range_faceMap] at hs
      let t : Face K := ⟨y.1.support,y.2.2.2⟩
      refine ⟨t,hs,y,⟨hy,?_⟩,rfl⟩
      rw [range_faceMap]
      exact Finset.Subset.refl _
    · rintro ⟨t,ht,y,⟨hy,hyt⟩,rfl⟩
      refine ⟨⟨y,hy,rfl⟩,?_⟩
      rw [range_faceMap] at hyt ⊢
      exact hyt.trans (show t.1 ⊆ s.1 from ht)
  rw [←he] at hc
  have hp := hc.preimage (continuous_faceMap L s)
  simpa only [preimage_inter,preimage_range,inter_univ] using hp

lemma inclusion_closedEmbedding : IsClosedEmbedding (inclusion K L hKL) :=
  .of_continuous_injective_isClosedMap (continuous_inclusion K L hKL)
    (inclusion_injective K L hKL) (inclusion_isClosedMap K L hKL)
end UniversalFInfinity.Simplicial

end

end OAI
