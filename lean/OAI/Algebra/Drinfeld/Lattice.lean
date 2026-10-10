import OAI.Algebra.Drinfeld.Descent

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace LatticeDimension
open scoped TensorProduct
variable {ι F : Type*} [Field F]

theorem reduction_lift (E : Submodule ℚ (ι → ℚ))
    (hs : Function.Surjective (Int.cast : ℤ → F)) {v : ι → F}
    (hv : v∈reduction F E) : ∃ u : lattice E, (fun i => (u.val i : F))=v := by
  obtain ⟨w,rfl⟩ := hv
  induction w using TensorProduct.inductionOn with

  | tmul c u =>
    obtain ⟨z,rfl⟩ := hs c
    refine ⟨z • u,?_⟩
    ext i
    rw [scalarMap_tmul]
    simp only [Submodule.coe_smul,Pi.smul_apply,zsmul_eq_mul,Int.cast_mul]
    exact mul_comm _ _
  | add w w' hw hw' =>
    obtain ⟨u,hu⟩ := hw
    obtain ⟨u',hu'⟩ := hw'
    refine ⟨u+u',?_⟩
    rw [map_add,←hu,←hu']
    ext i
    simp

theorem reduction_lift_two (E : Submodule ℚ (ι → ℚ)) {v : ι → ZMod 2}
    (hv : v∈reduction (ZMod 2) E) : ∃ u : lattice E,(fun i => (u.val i : ZMod 2))=v := by
  apply reduction_lift E ?_ hv
  intro c
  exact ⟨c.val,by simp⟩
theorem reduction_mono {E E' : Submodule ℚ (ι → ℚ)} (h : E≤E') :
    reduction F E≤reduction F E' := by
  rintro v ⟨w,rfl⟩
  induction w using TensorProduct.inductionOn with

  | tmul c u =>
    refine ⟨c ⊗ₜ (⟨u.val,h u.property⟩ : lattice E'),?_⟩
    simp only [scalarMap_tmul]
  | add w w' hw hw' => simpa only [map_add] using (reduction F E').add_mem hw hw'
end LatticeDimension

namespace SaturatedSolutions
open AssociativeElimination UniversalEmbedding WordGrading
open ReducedDimension
abbrev K := ZMod 2
variable (n : ℕ) (E : Submodule ℚ (Wn n))

def image : Submodule ℚ (RationalBound.Words n → ℚ) := E.map (RationalBound.coordinates n)

theorem image_le : image n E≤RationalBound.image n := by
  rintro v ⟨p,_,rfl⟩
  exact ⟨p,rfl⟩

def reduction : Submodule K (solutions n) :=
  (LatticeDimension.reduction K (image n E)).comap (RationalBound.reducedCoordinates n)

theorem reduction_image_le (hn : 2<n) :
    LatticeDimension.reduction K (image n E)≤RationalBound.reducedImage n :=
  (LatticeDimension.reduction_mono (image_le n E)).trans (RationalBound.reduction_le n hn)

def coordReduction : reduction n E →ₗ[K] LatticeDimension.reduction K (image n E) :=
  ((RationalBound.reducedCoordinates n).comp (reduction n E).subtype).codRestrict _ (fun p => p.property)

theorem coordReduction_injective : Function.Injective (coordReduction n E) := by
  intro p q h
  apply Subtype.ext
  apply RationalBound.reducedCoordinates_injective n
  exact congrArg Subtype.val h

theorem coordReduction_surjective (hn : 2<n) : Function.Surjective (coordReduction n E) := by
  intro v
  obtain ⟨p,hp⟩ := reduction_image_le n E hn v.property
  let pR : reduction n E := ⟨p,by
    change RationalBound.reducedCoordinates n p∈LatticeDimension.reduction K (image n E)
    rw [hp]
    exact v.property⟩
  exact ⟨pR,Subtype.ext hp⟩

theorem finrank_reduction (hn : 2<n) : Module.finrank K (reduction n E)=Module.finrank ℚ E := by
  let eqv := LinearEquiv.ofBijective (coordReduction n E)
    ⟨coordReduction_injective n E,coordReduction_surjective n E hn⟩
  have he := eqv.finrank_eq
  rw [LatticeDimension.finrank_reduction] at he
  have hi : Function.Injective ((RationalBound.coordinates n).comp E.subtype) :=
    (RationalBound.coordinates_injective n).comp Subtype.val_injective
  have hq := (LinearEquiv.ofInjective _ hi).finrank_eq
  have hr : ((RationalBound.coordinates n).comp E.subtype).range=image n E := by
    rw [LinearMap.range_comp,Submodule.range_subtype]
    rfl
  rw [hr] at hq
  exact he.trans hq.symm

def filtration (hn : 1<n) (r : ℕ) : Submodule K (reduction n E) :=
  (ReducedDimension.filtration n hn r).comap (reduction n E).subtype

def inclusionFiltration (hn : 1<n) (r : ℕ) :
    filtration n E hn r →ₗ[K] ReducedDimension.filtration n hn r :=
  ((reduction n E).subtype.comp (filtration n E hn r).subtype).codRestrict _ (fun p => p.property)

def gradedMap (hn : 2<n) (r : ℕ) : filtration n E (by omega) r →ₗ[K] oddPiece n r :=
  (ReducedDimension.gradedMap n hn r).comp (inclusionFiltration n E (by omega) r)

theorem graded_kernel (hn : 2<n) (r : ℕ) (p : filtration n E (by omega) r)
    (hz : gradedMap n E hn r p=0) : p.val∈filtration n E (by omega) (r+1) :=
  ReducedDimension.graded_kernel n hn r (inclusionFiltration n E (by omega) r p) hz

theorem filtration_zero (hn : 1<n) : filtration n E hn 0=⊤ := by
  unfold filtration
  rw [ReducedDimension.filtration_zero,Submodule.comap_top]

theorem filtration_terminal (hn : 1<n) : filtration n E hn (n+1)=⊥ := by
  unfold filtration
  rw [ReducedDimension.filtration_terminal]
  exact LinearMap.ker_eq_bot_of_injective Subtype.val_injective

theorem graded_surjective (hn : 2<n) (he : Module.finrank ℚ E=Module.finrank ℚ (Fn n))
    (r : ℕ) (hr : r≤n) : Function.Surjective (gradedMap n E hn r) := by
  apply FiltrationDimension.surjective_of_equality (filtration n E (by omega))
    (gradedMap n E hn) (graded_kernel n E hn) (n+1) (filtration_terminal n E (by omega)) ?_ r (by omega)
  rw [filtration_zero,finrank_top,finrank_reduction n E hn,he]
  change Module.finrank ℚ (weightPiece oddWeight n)=_
  rw [LieGrading.weightPiece_eq,←LieDimension.finrank_homogeneous K oddWeight n,
    LieGrading.finrank_decomposition K oddWeight (fun _ => 1) n n (ReducedDimension.odd_length_bound n)]
  exact Fin.sum_univ_eq_sum_range (fun r => Module.finrank K (oddPiece n r)) (n+1)

theorem lattice_lift (u : LatticeDimension.lattice (image n E)) :
    ∃ q : LieGrading.homogeneousLie (R:=ℤ) RationalBound.wt n,
      LieDimension.coordinates ℤ RationalBound.wt n q=u.val ∧
      ∃ hq : (LieDimension.castHom (R:=ℚ) q).val∈Wn n,
        (⟨(LieDimension.castHom (R:=ℚ) q).val,hq⟩ : Wn n)∈E := by
  obtain ⟨p,hpE,hp⟩ := u.property
  have hu : u.val∈LatticeDimension.lattice (LieDimension.image ℚ RationalBound.wt n) :=
    ⟨RationalBound.toHom n p,hp⟩
  rw [LieDimension.lattice_image] at hu
  obtain ⟨q,hq⟩ := hu
  have heq : LieDimension.castHom (R:=ℚ) q=RationalBound.toHom n p := by
    apply LieDimension.coordinates_injective ℚ RationalBound.wt n
    ext w
    rw [LieDimension.coordinates_castHom]
    change ((LieDimension.coordinates ℤ RationalBound.wt n q) w : ℚ)=RationalBound.coordinates n p w
    rw [hq,congrFun hp w]
    rfl
  refine ⟨q,hq,?_,?_⟩
  · rw [heq]
    exact p.property
  · have hval : (LieDimension.castHom (R:=ℚ) q).val=p.val := congrArg Subtype.val heq
    have hsub : (⟨(LieDimension.castHom (R:=ℚ) q).val, by rw [heq]; exact p.property⟩ : Wn n)=p := Subtype.ext hval
    rw [hsub]
    exact hpE

theorem reduction_lift (hn : 2<n) (p : reduction n E) :
    ∃ q : LieGrading.homogeneousLie (R:=ℤ) RationalBound.wt n,
      (LieDimension.castHom (R:=K) q).val=p.val.val ∧
      ∃ hq : (LieDimension.castHom (R:=ℚ) q).val∈Wn n,
        (⟨(LieDimension.castHom (R:=ℚ) q).val,hq⟩ : Wn n)∈E := by
  obtain ⟨u,hu⟩ := LatticeDimension.reduction_lift_two (image n E) p.property
  obtain ⟨q,hq,hW,hE⟩ := lattice_lift n E u
  refine ⟨q,?_,hW,hE⟩
  let qS := RationalBound.reduceLattice n hn q hW.1
  have he : qS=p.val := by
    apply RationalBound.reducedCoordinates_injective n
    ext w
    change (LieDimension.coordinates K RationalBound.wt n (LieDimension.castHom q)) w=_
    rw [LieDimension.coordinates_castHom,hq]
    exact congrFun hu w
  exact congrArg Subtype.val he

end SaturatedSolutions

namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
variable {R α : Type*} [CommRing R]

theorem eval_homogeneous (wt : α → ℕ) (t : UniversalEmbedding.Tree α) :
    (t.eval : FreeLieAlgebra R α)∈homogeneousLie wt (treeDegree wt t) :=
  Submodule.subset_span ⟨t,rfl,rfl⟩

theorem piece_tree (wt : α → ℕ) (r : ℕ) (t : UniversalEmbedding.Tree α) :
    piece wt r (t.eval : FreeLieAlgebra R α)=if treeDegree wt t=r then t.eval else 0 :=
  piece_homogeneous (eval_homogeneous wt t) r

def biTreeSpan (wa wb : α → ℕ) (n r : ℕ) : Submodule R (FreeLieAlgebra R α) :=
  Submodule.span R {p | ∃ t : UniversalEmbedding.Tree α,treeDegree wa t=n ∧ treeDegree wb t=r ∧ t.eval=p}

theorem biTreeSpan_eq (wa wb : α → ℕ) (n r : ℕ) :
    biTreeSpan (R:=R) wa wb n r=biPiece wa wb n r := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨t,hn,hr,rfl⟩
    exact ⟨hn ▸ eval_homogeneous wa t,hr ▸ eval_homogeneous wb t⟩
  · intro p hp
    have he : piece wb r p=p := by rw [piece_homogeneous hp.2,ite_eq_left rfl]
    rw [←he]
    have hw : p∈homogeneousLie wa n := hp.1
    clear hp he
    induction hw using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨t,ht,rfl⟩ := hp
      rw [piece_tree]
      split_ifs with h
      · exact Submodule.subset_span ⟨t,ht,h,rfl⟩
      · exact Submodule.zero_mem _
    | zero =>
      have hz : piece wb r (0 : FreeLieAlgebra R α)=0 := (projection wb r).map_zero
      rw [hz]
      exact Submodule.zero_mem _
    | add p q _ _ hp hq => rw [piece_add]; exact Submodule.add_mem _ hp hq
    | smul c p _ hp => rw [piece_smul]; exact Submodule.smul_mem _ c hp

theorem treeDegree_pos {wt : α → ℕ} (h : ∀ a,0<wt a) (t : UniversalEmbedding.Tree α) : 0<treeDegree wt t := by
  induction t with
  | leaf a => simpa only [treeDegree_leaf] using h a
  | node t u ht hu => rw [treeDegree_node]; omega

theorem treeDegree_lower {wt : α → ℕ} {m : ℕ} (h : ∀ a,m≤wt a) (t : UniversalEmbedding.Tree α) : m≤treeDegree wt t := by
  induction t with
  | leaf a => simpa only [treeDegree_leaf] using h a
  | node t u ht hu => rw [treeDegree_node]; omega

theorem leaf_degree_le {wt : α → ℕ} {t : UniversalEmbedding.Tree α} {a : α}
    (ha : a∈t.leaves) : wt a≤treeDegree wt t := by
  induction t with
  | leaf b =>
    have hab : a=b := List.mem_singleton.mp ha
    simpa only [hab,treeDegree_leaf] using le_refl (wt b)
  | node t u ht hu =>
    rw [Tree.leaves,List.mem_append] at ha
    rw [treeDegree_node]
    rcases ha with h|h
    · exact (ht h).trans (Nat.le_add_right _ _)
    · exact (hu h).trans (Nat.le_add_left _ _)

theorem leaf_degree_lt {wt : α → ℕ} (hwt : ∀ a,0<wt a)
    {t : UniversalEmbedding.Tree α} (ht : 1<treeDegree (fun _ => 1) t)
    {a : α} (ha : a∈t.leaves) : wt a<treeDegree wt t := by
  cases t with
  | leaf b => simp only [treeDegree_leaf] at ht; omega
  | node t u =>
    rw [Tree.leaves,List.mem_append] at ha
    rw [treeDegree_node]
    rcases ha with h|h
    · have hle := leaf_degree_le (wt:=wt) h
      have hpos := treeDegree_pos hwt u
      omega
    · have hle := leaf_degree_le (wt:=wt) h
      have hpos := treeDegree_pos hwt t
      omega

end LieGrading

namespace NormalizedFamily
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open ImageBound LieGrading RowTwo RowKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing
abbrev K := ZMod 2

structure Data where
  active : ℕ → Prop
  value : ℕ → FreeLieAlgebra K Bool
  solution : ∀ n (p : FreeLieAlgebra K ℕ),p∈homogeneousLie oddWeight n →
    GenericIhara.evalIhara value p∈ReducedDimension.solutions n
  rep : ℕ → FreeLieAlgebra K Slot
  under_rep : ∀ k,under (rep k)=embed (value k)
  above_rep : ∀ k,active k → embed (rep k)∈above bCount 1
  leading_rep : ∀ k,active k → embed (leading 1 (rep k))=positiveInput (atom k)

variable (g : Data)

def treeSolution (t : UniversalEmbedding.Tree ℕ) : ReducedDimension.solutions (treeDegree oddWeight t) :=
  ⟨GenericIhara.evalIhara g.value t.eval,g.solution _ _ (eval_homogeneous oddWeight t)⟩

theorem treeWeight (t : UniversalEmbedding.Tree ℕ) : 2<treeDegree oddWeight t := by
  have h := treeDegree_lower (m:=3) (wt:=oddWeight) (by intro k; simp [oddWeight]) t
  omega

def treeRep (t : UniversalEmbedding.Tree ℕ) : FreeLieAlgebra K Slot :=
  ReducedDimension.representation (treeDegree oddWeight t) (by have := treeWeight t; omega) (treeSolution g t)

theorem under_treeRep (t : UniversalEmbedding.Tree ℕ) :
    under (treeRep g t)=embed (GenericIhara.evalIhara g.value t.eval) :=
  ReducedDimension.representation_under _ _ _

theorem treeRep_leaf (k : ℕ) : treeRep g (.leaf k)=g.rep k := by
  apply under_injective
  rw [under_treeRep,g.under_rep]
  simp only [Tree.eval,GenericIhara.evalIhara_of]

theorem treeRep_node (t u : UniversalEmbedding.Tree ℕ) :
    treeRep g (.node t u)=IharaLeading.iharaLie (treeRep g t) (treeRep g u) := by
  apply under_injective
  rw [under_treeRep,IharaLeading.actual_ihara_representation (under_treeRep g t) (under_treeRep g u)]
  simp only [Tree.eval,GenericIhara.evalIhara_lie]

theorem tree_leading (t : UniversalEmbedding.Tree ℕ)
    (hactive : ∀ k∈t.leaves,g.active k) :
    embed (treeRep g t)∈above bCount (treeDegree (fun _ => 1) t) ∧
    embed (leading (treeDegree (fun _ => 1) t) (treeRep g t))=positiveInput (embed (t.eval : FreeLieAlgebra K ℕ)) := by
  induction t with
  | leaf k =>
    rw [treeRep_leaf]
    simpa only [treeDegree_leaf,Tree.eval,AssociativeElimination.embed_of] using ⟨g.above_rep k (hactive k (by simp [Tree.leaves])),g.leading_rep k (hactive k (by simp [Tree.leaves]))⟩
  | node t u ht hu =>
    have ht := ht (fun k hk => hactive k (by simp only [Tree.leaves,List.mem_append]; exact Or.inl hk))
    have hu := hu (fun k hk => hactive k (by simp only [Tree.leaves,List.mem_append]; exact Or.inr hk))
    have hs := IharaLeading.actual_leading_ihara
      (ψ:=GenericIhara.evalIhara g.value t.eval) (φ:=GenericIhara.evalIhara g.value u.eval)
      (n:=treeDegree oddWeight t) (m:=treeDegree oddWeight u)
      (by have := treeWeight t; omega) (by have := treeWeight u; omega)
      (homogeneousLie_embed (ReducedDimension.solutions_hom (treeSolution g t)))
      (homogeneousLie_embed (ReducedDimension.solutions_hom (treeSolution g u)))
      (under_treeRep g t) (under_treeRep g u)
      (ReducedDimension.solutions_anti (treeSolution g t))
      (ReducedDimension.solutions_anti (treeSolution g u))
      (treeDegree_pos (wt:=fun _ : ℕ => 1) (by intro k; omega) t) (treeDegree_pos (wt:=fun _ : ℕ => 1) (by intro k; omega) u) ht.1 hu.1
    rw [treeRep_node,treeDegree_node,IharaLeading.embed_iharaLie]
    refine ⟨hs.1,?_⟩
    rw [embed_leading,IharaLeading.embed_iharaLie,hs.2,ht.2,hu.2]
    simp only [Tree.eval,LieHom.map_lie,EvenIndex.map_lie]

theorem bihomogeneous_leading {n r : ℕ} {p : FreeLieAlgebra K ℕ}
    (hp : p∈biPiece oddWeight (fun _ => 1) n r)
    (hactive : ∀ t : UniversalEmbedding.Tree ℕ,treeDegree oddWeight t=n →
      treeDegree (fun _ => 1) t=r → ∀ k∈t.leaves,g.active k) :
    ∃ q : FreeLieAlgebra K Slot,
      under q=embed (GenericIhara.evalIhara g.value p) ∧ embed q∈above bCount r ∧
      embed (leading r q)=positiveInput (embed p) := by
  rw [←biTreeSpan_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,hn,hr,rfl⟩ := hp
    have ht := tree_leading g t (hactive t hn hr)
    exact ⟨treeRep g t,under_treeRep g t,hr ▸ ht.1,hr ▸ ht.2⟩
  | zero => exact ⟨0,by simp,Submodule.zero_mem _,by simp only [embed_leading,map_zero]⟩
  | add p q _ _ hp hq =>
    obtain ⟨p',hp',hpr,hpl⟩ := hp
    obtain ⟨q',hq',hqr,hql⟩ := hq
    refine ⟨p'+q',by simp only [map_add,hp',hq'],?_,?_⟩
    · simpa only [map_add] using (above bCount r).add_mem hpr hqr
    · change embed (eraseLie (LieGrading.piece bCount r (p'+q')))=_
      rw [LieGrading.piece_add,map_add,map_add]
      change embed (leading r p')+embed (leading r q')=_
      rw [hpl,hql,map_add,map_add]
  | smul c p _ hp =>
    obtain ⟨p',hp',hpr,hpl⟩ := hp
    refine ⟨c • p',by simp only [map_smul,hp'],?_,?_⟩
    · simpa only [map_smul] using (above bCount r).smul_mem c hpr
    · change embed (eraseLie (LieGrading.piece bCount r (c • p')))=_
      rw [LieGrading.piece_smul,map_smul,map_smul]
      change c • embed (leading r p')=_
      rw [hpl,map_smul,map_smul]

end NormalizedFamily

namespace Triangular
variable {R : Type*} [Semiring R] {N : ℕ}
    {V : Fin N → Type*} [∀ i,AddCommGroup (V i)] [∀ i,Module R (V i)]
    {W : Type*} [AddCommMonoid W] [Module R W]
    {Z : Fin N → Type*} [∀ i,AddCommGroup (Z i)] [∀ i,Module R (Z i)]

def assemble (f : ∀ i,V i →ₗ[R] W) : (∀ i,V i) →ₗ[R] W :=
  ∑ i,(f i).comp (LinearMap.proj i)

theorem assemble_apply (f : ∀ i,V i →ₗ[R] W) (v : ∀ i,V i) : assemble f v=∑ i,f i (v i) := by
  simp [assemble]

theorem assemble_injective (f : ∀ i,V i →ₗ[R] W) (π : ∀ i,W →ₗ[R] Z i)
    (diag : ∀ i,Function.Injective ((π i).comp (f i)))
    (upper : ∀ i j,i < j → ∀ v,π i (f j v)=0) : Function.Injective (assemble f) := by
  classical
  intro v w hvw
  have aux : ∀ n (i : Fin N),i.val=n → v i=w i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      apply diag i
      change π i (f i (v i))=π i (f i (w i))
      have h := congrArg (π i) hvw
      simp only [assemble_apply,map_sum] at h
      have hv : (∑ j,π i (f j (v j))) =
          (∑ j∈(Finset.univ.filter (fun j => j < i)),π i (f j (v j))) + π i (f i (v i)) := by
        classical
        rw [←Finset.sum_filter_add_sum_filter_not (s:=Finset.univ) (p:=fun j => j < i)]
        congr 1
        apply Finset.sum_eq_single i
        · intro j hj hji
          have hle : i ≤ j := le_of_not_gt (Finset.mem_filter.mp hj).2
          exact upper i j (lt_of_le_of_ne hle (Ne.symm hji)) (v j)
        · simp
      have hw : (∑ j,π i (f j (w j))) =
          (∑ j∈(Finset.univ.filter (fun j => j < i)),π i (f j (w j))) + π i (f i (w i)) := by
        classical
        rw [←Finset.sum_filter_add_sum_filter_not (s:=Finset.univ) (p:=fun j => j < i)]
        congr 1
        apply Finset.sum_eq_single i
        · intro j hj hji
          have hle : i ≤ j := le_of_not_gt (Finset.mem_filter.mp hj).2
          exact upper i j (lt_of_le_of_ne hle (Ne.symm hji)) (w j)
        · simp
      have he : (∑ j∈(Finset.univ.filter (fun j => j < i)),π i (f j (v j))) =
          ∑ j∈(Finset.univ.filter (fun j => j < i)),π i (f j (w j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih j.val (by have hj' := (Finset.mem_filter.mp hj).2; change j.val < i.val at hj'; omega) j rfl]
      rw [hv,hw,he] at h
      exact add_left_cancel h
  funext i
  exact aux i.val i rfl

end Triangular

namespace NormalizedFamily

section
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open ImageBound LieGrading RowTwo RowKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing
variable (g : Data)

def valueMap (n : ℕ) : homogeneousLie (R:=K) oddWeight n →ₗ[K] ReducedDimension.solutions n :=
  ((GenericIhara.evalIhara g.value).comp (homogeneousLie oddWeight n).subtype).codRestrict _
    (fun p => g.solution n p.val p.property)

def repMap (n : ℕ) (hn : 1<n) : homogeneousLie (R:=K) oddWeight n →ₗ[K] FreeLieAlgebra K Slot :=
  (ReducedDimension.representationMap n hn).comp (valueMap g n)

def leadingLinear (r : ℕ) : FreeLieAlgebra K Slot →ₗ[K] A K Bool :=
  (OreShift.eraseShift 0).toLinearMap.comp ((WordGrading.piece bCount r).comp embed.toLinearMap)

theorem leadingLinear_apply (r : ℕ) (p : FreeLieAlgebra K Slot) :
    leadingLinear r p=embed (leading r p) := (embed_leading r p).symm

theorem repMap_bihomogeneous {n r : ℕ} (hn : 1<n) (p : biPiece (R:=K) oddWeight (fun _ => 1) n r)
    (hactive : ∀ t : UniversalEmbedding.Tree ℕ,treeDegree oddWeight t=n →
      treeDegree (fun _ => 1) t=r → ∀ k∈t.leaves,g.active k) :
    embed (repMap g n hn ⟨p.val,p.property.1⟩)∈above bCount r ∧
      leadingLinear r (repMap g n hn ⟨p.val,p.property.1⟩)=positiveInput (embed p.val) := by
  obtain ⟨q,hq,hqr,hql⟩ := bihomogeneous_leading g p.property hactive
  have he : repMap g n hn ⟨p.val,p.property.1⟩=q := by
    apply under_injective
    exact (ReducedDimension.representation_under n hn (valueMap g n ⟨p.val,p.property.1⟩)).trans hq.symm
  rw [he,leadingLinear_apply]
  exact ⟨hqr,hql⟩

def oldPiece (n r : ℕ) : Submodule K (FreeLieAlgebra K ℕ) :=
  if 1<r then biPiece oddWeight (fun _ => 1) n r else ⊥

theorem oldPiece_le (n r : ℕ) : oldPiece n r≤homogeneousLie oddWeight n := by
  unfold oldPiece
  split_ifs
  · exact inf_le_left
  · exact bot_le

instance finite_oldPiece (n r : ℕ) : Module.Finite K (oldPiece n r) :=
  Module.Finite.of_injective (Submodule.inclusion (oldPiece_le n r)) (Submodule.inclusion_injective _)

def oldMap (n r : ℕ) : oldPiece n r →ₗ[K] ReducedDimension.solutions n :=
  (valueMap g n).comp (Submodule.inclusion (oldPiece_le n r))

def solutionLeading (n : ℕ) (hn : 1<n) (r : ℕ) : ReducedDimension.solutions n →ₗ[K] A K Bool :=
  (leadingLinear r).comp (ReducedDimension.representationMap n hn)

theorem oldMap_leading {n r : ℕ} (hn : 1<n) (hr : 1<r)
    (ha : ∀ k,oddWeight k<n → g.active k) (p : oldPiece n r) :
    embed (ReducedDimension.representationMap n hn (oldMap g n r p))∈above bCount r ∧
      solutionLeading n hn r (oldMap g n r p)=positiveInput (embed p.val) := by
  have hp : p.val∈biPiece oddWeight (fun _ => 1) n r := by
    have h := p.property
    simpa only [oldPiece,ite_eq_left hr] using h
  exact repMap_bihomogeneous g hn ⟨p.val,hp⟩ (by
    intro t htn htr k hk
    apply ha k
    have hlt := leaf_degree_lt (wt:=oddWeight) (by intro k; simp [oddWeight]) (by omega : 1<treeDegree (fun _ => 1) t) hk
    simpa only [htn] using hlt)

theorem oldMap_low {n r : ℕ} (hr : ¬1<r) (p : oldPiece n r) : p=0 := by
  apply Subtype.ext
  change p.val=0
  have h := p.property
  simpa only [oldPiece,ite_eq_right hr,Submodule.mem_bot] using h

theorem old_assemble_injective (n : ℕ) (hn : 1<n) (ha : ∀ k,oddWeight k<n → g.active k) :
    Function.Injective (Triangular.assemble (fun r : Fin (n+1) => oldMap g n r.val)) := by
  apply Triangular.assemble_injective _ (fun r => solutionLeading n hn r.val)
  · intro r p q hpq
    by_cases hr : 1<r.val
    · have hp := (oldMap_leading g hn hr ha p).2
      have hq := (oldMap_leading g hn hr ha q).2
      apply Subtype.ext
      apply UniversalEmbedding.injective
      apply positiveInput_injective
      exact hp.symm.trans (hpq.trans hq)
    · rw [oldMap_low hr p,oldMap_low hr q]
  · intro r s hrs p
    by_cases hs : 1<s.val
    · have hp := (oldMap_leading g hn hs ha p).1
      change OreShift.eraseShift 0 (project (fun w => degree bCount w=r.val) (embed _))=0
      rw [project_eq_zero hp ?_,map_zero]
      intro w hw hwr
      change s.val≤degree bCount w at hw
      change degree bCount w=r.val at hwr
      have hrs' : r.val<s.val := hrs
      omega
    · rw [oldMap_low hs p,map_zero,map_zero]

end

open AssociativeElimination UniversalEmbedding WordGrading ImageBound LieGrading RowKernel

variable (g : Data)

def fullMap (n r : ℕ) : biPiece (R:=K) oddWeight (fun _ => 1) n r →ₗ[K] ReducedDimension.solutions n :=
  (valueMap g n).comp (Submodule.inclusion inf_le_left)

theorem fullMap_leading {n r : ℕ} (hn : 1<n) (ha : ∀ k,g.active k)
    (p : biPiece (R:=K) oddWeight (fun _ => 1) n r) :
    embed (ReducedDimension.representationMap n hn (fullMap g n r p))∈above bCount r ∧
      solutionLeading n hn r (fullMap g n r p)=positiveInput (embed p.val) :=
  repMap_bihomogeneous g hn p (by intros; apply ha)

theorem full_assemble_injective (n : ℕ) (hn : 1<n) (ha : ∀ k,g.active k) :
    Function.Injective (Triangular.assemble (fun r : Fin (n+1) => fullMap g n r.val)) := by
  apply Triangular.assemble_injective _ (fun r => solutionLeading n hn r.val)
  · intro r p q hpq
    apply Subtype.ext
    apply UniversalEmbedding.injective
    apply positiveInput_injective
    exact (fullMap_leading g hn ha p).2.symm.trans (hpq.trans (fullMap_leading g hn ha q).2)
  · intro r s hrs p
    have hp := (fullMap_leading g hn ha p).1
    change OreShift.eraseShift 0 (project (fun w => degree bCount w=r.val) (embed _))=0
    rw [project_eq_zero hp ?_,map_zero]
    intro w hw hwr
    change s.val≤degree bCount w at hw
    change degree bCount w=r.val at hwr
    have hrs' : r.val<s.val := hrs
    omega

theorem valueMap_injective (n : ℕ) (hn : 1<n) (ha : ∀ k,g.active k) :
    Function.Injective (valueMap g n) := by
  intro p q hpq
  have he (v : homogeneousLie (R:=K) oddWeight n) :
      Triangular.assemble (fun r : Fin (n+1) => fullMap g n r.val)
        (components oddWeight (fun _ => 1) n n v)=valueMap g n v := by
    have h := assemble_components oddWeight (fun _ => 1) n n (ReducedDimension.odd_length_bound n) v
    rw [Triangular.assemble_apply]
    calc
      _ = valueMap g n (assemble oddWeight (fun _ => 1) n n
          (components oddWeight (fun _ => 1) n n v)) := by
        change (∑ r : Fin (n+1),(valueMap g n) ⟨_,_⟩)=(valueMap g n) ⟨∑ r : Fin (n+1),_,_⟩
        rw [←map_sum]
        congr 1
        apply Subtype.ext
        simp only [Submodule.coe_sum]
        rfl
      _ = valueMap g n v := congrArg (valueMap g n) h
  have hc := full_assemble_injective g n hn ha ((he p).trans (hpq.trans (he q).symm))
  have h := congrArg (assemble oddWeight (fun _ => 1) n n) hc
  simpa only [assemble_components oddWeight (fun _ => 1) n n (ReducedDimension.odd_length_bound n)] using h

end NormalizedFamily

namespace GenericIhara
variable {R α : Type*} [CommRing R]

theorem cast_D (p q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=R) (D p q)=D (IntegralBaseChange.lie p) (IntegralBaseChange.lie q) := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [D]
  | ha q r hq hr => simp only [map_add,hq,hr]
  | hs c q hq =>
    change IntegralBaseChange.lie ((D p).toLinearMap (c • q)) =
      (D (IntegralBaseChange.lie p)).toLinearMap (IntegralBaseChange.lie (c • q))
    simp only [map_zsmul]
    exact congrArg (fun v => c • v) hq
  | hl q r hq hr => simp only [LieDerivation.apply_lie_eq_add,LieHom.map_lie,map_add,hq,hr]

theorem cast_ihara (p q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=R) (ihara p q)=ihara (IntegralBaseChange.lie p) (IntegralBaseChange.lie q) := by
  simp only [ihara,map_add,map_sub,LieHom.map_lie,cast_D]

theorem cast_evalIhara (f : α → FreeLieAlgebra ℤ Bool) (p : FreeLieAlgebra ℤ α) :
    IntegralBaseChange.lie (S:=R) (evalIhara f p)=
      evalIhara (fun a => IntegralBaseChange.lie (f a)) (IntegralBaseChange.lie p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp only [map_add,hp,hq]
  | hs c p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [evalIhara_lie,LieHom.map_lie,cast_ihara,hp,hq]

end GenericIhara

namespace IntegralFamily
open LieGrading AssociativeElimination UniversalEmbedding WordGrading
open scoped TensorProduct
abbrev K := ZMod 2

structure Values where
  space : Submodule ℚ L
  le_W : space≤W
  bracket : ∀ {p q},p∈space → q∈space → ihara p q∈space

variable (V : Values)

structure Family where
  value : ℕ → FreeLieAlgebra ℤ Bool
  homogeneous : ∀ k,value k∈homogeneousLie (fun _ => 1) (oddWeight k)
  member : ∀ k,IntegralBaseChange.lie (S:=ℚ) (value k)∈V.space

variable {V} (f : Family V)

def cast (R : Type*) [CommRing R] (k : ℕ) : FreeLieAlgebra R Bool :=
  IntegralBaseChange.lie (f.value k)

theorem cast_homogeneous (R : Type*) [CommRing R] (k : ℕ) :
    cast f R k∈homogeneousLie (fun _ => 1) (oddWeight k) :=
  (LieDimension.castHom (R:=R) ⟨f.value k,f.homogeneous k⟩).property

theorem rational_mem (p : FreeLieAlgebra ℚ ℕ) : GenericIhara.evalIhara (cast f ℚ) p∈V.space := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg k => simpa only [GenericIhara.evalIhara_of,cast] using f.member k
  | ha p q hp hq => rw [map_add]; exact V.space.add_mem hp hq
  | hs c p hp => rw [map_smul]; exact V.space.smul_mem c hp
  | hl p q hp hq => rw [GenericIhara.evalIhara_lie,GenericIhara.rational_ihara]; exact V.bracket hp hq

theorem eval_homogeneous (R : Type*) [CommRing R] {n : ℕ} {p : FreeLieAlgebra R ℕ}
    (hp : p∈homogeneousLie oddWeight n) :
    GenericIhara.evalIhara (cast f R) p∈homogeneousLie (fun _ => 1) n := by
  apply homogeneous_iff.mpr
  exact GenericIhara.evalIhara_homogeneous oddWeight _ (fun k => homogeneousLie_embed (cast_homogeneous f R k)) hp

theorem integral_eval_homogeneous {n : ℕ} {p : FreeLieAlgebra ℤ ℕ}
    (hp : p∈homogeneousLie oddWeight n) :
    GenericIhara.evalIhara f.value p∈homogeneousLie (fun _ => 1) n := by
  apply homogeneous_iff.mpr
  exact GenericIhara.evalIhara_homogeneous oddWeight _ (fun k => homogeneousLie_embed (f.homogeneous k)) hp

def piece (V : Values) (n : ℕ) : Submodule ℚ (Wn n) := V.space.comap (Wn n).subtype

theorem integral_reduction_mem {n : ℕ} (E : Submodule ℚ (Wn n))
    (q : homogeneousLie (R:=ℤ) RationalBound.wt n)
    (hW : (LieDimension.castHom (R:=ℚ) q).val∈Wn n)
    (hE : (⟨(LieDimension.castHom (R:=ℚ) q).val,hW⟩ : Wn n)∈E)
    (p : ReducedDimension.solutions n)
    (hp : (LieDimension.castHom (R:=K) q).val=p.val) :
    p∈SaturatedSolutions.reduction n E := by
  let u : LatticeDimension.lattice (SaturatedSolutions.image n E) :=
    ⟨LieDimension.coordinates ℤ RationalBound.wt n q,by
      refine ⟨⟨(LieDimension.castHom (R:=ℚ) q).val,hW⟩,hE,?_⟩
      ext w
      exact LieDimension.coordinates_castHom q w⟩
  refine ⟨(1 : K) ⊗ₜ[ℤ] u,?_⟩
  ext w
  rw [LatticeDimension.scalarMap_tmul]
  change (LieDimension.coordinates ℤ RationalBound.wt n q w : K)*1=(embed p.val).coeff w.val
  rw [mul_one,←LieDimension.coordinates_castHom,LieDimension.coordinates_apply,hp]

theorem tree_rational_W (t : UniversalEmbedding.Tree ℕ) :
    IntegralBaseChange.lie (S:=ℚ) (GenericIhara.evalIhara f.value (t.eval (R:=ℤ)))∈W := by
  rw [GenericIhara.cast_evalIhara,LieDimension.cast_eval]
  exact V.le_W (rational_mem f t.eval)

theorem reduced_solution {n : ℕ} {p : FreeLieAlgebra K ℕ}
    (hp : p∈homogeneousLie oddWeight n) :
    GenericIhara.evalIhara (cast f K) p∈ReducedDimension.solutions n := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,ht,rfl⟩ := hp
    have hn : 2<n := by
      have h := treeDegree_lower (m:=3) (wt:=oddWeight) (by intro k; simp [oddWeight]) t
      omega
    let q : homogeneousLie (R:=ℤ) RationalBound.wt n :=
      ⟨GenericIhara.evalIhara f.value t.eval,integral_eval_homogeneous f (ht ▸ LieGrading.eval_homogeneous oddWeight t)⟩
    have hq := (RationalBound.reduceLattice n hn q (tree_rational_W f t)).property
    change IntegralBaseChange.lie (S:=K) (GenericIhara.evalIhara f.value t.eval)∈_ at hq
    rwa [GenericIhara.cast_evalIhara,LieDimension.cast_eval] at hq
  | zero => simp
  | add p q _ _ hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | smul c p _ hp => rw [map_smul]; exact Submodule.smul_mem _ c hp

def reducedValue (n : ℕ) : homogeneousLie (R:=K) oddWeight n →ₗ[K] ReducedDimension.solutions n :=
  ((GenericIhara.evalIhara (cast f K)).comp (homogeneousLie oddWeight n).subtype).codRestrict _
    (fun p => reduced_solution f p.property)

theorem reduced_mem {n : ℕ} (p : homogeneousLie (R:=K) oddWeight n) :
    reducedValue f n p∈SaturatedSolutions.reduction n (piece V n) := by
  have ht : ∀ (t : UniversalEmbedding.Tree ℕ) (ht : treeDegree oddWeight t=n),
      reducedValue f n ⟨t.eval,ht ▸ LieGrading.eval_homogeneous oddWeight t⟩∈SaturatedSolutions.reduction n (piece V n) := by
    intro t ht
    let q : homogeneousLie (R:=ℤ) RationalBound.wt n :=
      ⟨GenericIhara.evalIhara f.value t.eval,integral_eval_homogeneous f (ht ▸ LieGrading.eval_homogeneous oddWeight t)⟩
    have he : (LieDimension.castHom (R:=ℚ) q).val=GenericIhara.evalIhara (cast f ℚ) t.eval := by
      exact (GenericIhara.cast_evalIhara f.value t.eval).trans (congrArg _ (LieDimension.cast_eval t))
    have hW : (LieDimension.castHom (R:=ℚ) q).val∈Wn n := by
      constructor
      · rw [he]; exact V.le_W (rational_mem f t.eval)
      · change _∈weightPiece RationalBound.wt n
        rw [weightPiece_eq]; exact (LieDimension.castHom (R:=ℚ) q).property
    apply integral_reduction_mem (piece V n) q hW ?_ _ ?_
    · change (LieDimension.castHom (R:=ℚ) q).val∈V.space
      rw [he]; exact rational_mem f t.eval
    · change IntegralBaseChange.lie (S:=K) (GenericIhara.evalIhara f.value t.eval)=_
      rw [GenericIhara.cast_evalIhara,LieDimension.cast_eval]
      rfl
  have hp := p.property
  change p.val∈homogeneousLie oddWeight n at hp
  have hh : ∀ v (hv : v∈homogeneousLie (R:=K) oddWeight n),
      reducedValue f n ⟨v,hv⟩∈SaturatedSolutions.reduction n (piece V n) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨t,htree,rfl⟩ := hv; exact ht t htree
    | zero =>
      change reducedValue f n 0∈_
      rw [map_zero]
      exact Submodule.zero_mem _
    | add v w hv hw hi hj =>
      change reducedValue f n (⟨v,hv⟩+⟨w,hw⟩)∈_
      rw [map_add]
      exact (SaturatedSolutions.reduction n (piece V n)).add_mem hi hj
    | smul c v hv hi =>
      change reducedValue f n (c • ⟨v,hv⟩)∈_
      rw [map_smul]
      exact (SaturatedSolutions.reduction n (piece V n)).smul_mem c hi
  exact hh p.val hp

end IntegralFamily

end DeligneDrinfeld

end

end OAI
