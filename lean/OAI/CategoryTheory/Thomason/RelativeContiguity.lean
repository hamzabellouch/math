import Mathlib
import OAI.CategoryTheory.Thomason.PosetalReduction
import OAI.CategoryTheory.Thomason.SimplicialApproximation

namespace OAI

/-! Relative Contiguity. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder

namespace Thomason.GeometricRecognition
open LastVertexProof KanLocal Subdivision Mesh Contiguity PolyPoint

lemma nerveOrderMap_id (P : Type u) [PartialOrder P] :
    nerveMap (OrderHom.id : P →o P).toFunctor = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  rfl

lemma nerveOrderMap_comp {P Q R : Type u} [PartialOrder P] [PartialOrder Q]
    [PartialOrder R] (f : Q →o R) (g : P →o Q) :
    nerveMap (f.comp g).toFunctor = nerveMap g.toFunctor ≫ nerveMap f.toFunctor :=
  by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    rfl

lemma chainLast_local (P : PartOrd.{u}) :
    Local (nerveMap (chainLast (X := P)).toFunctor) := by
  have he : (sdNerveIso (E := P)).hom ≫ nerveMap (chainLast (X := P)).toFunctor =
      lastVertex.app (nerve P) := lastVertex_nerve
  exact local_of_precomp _ _ (local_iso _) (he.symm ▸ lastVertex_local _)

lemma last_local (P : PartOrd.{u}) (n : ℕ) : Local (nerveMap (last P n).toFunctor) := by
  induction n with
  | zero =>
      change Local (nerveMap (OrderHom.id : P →o P).toFunctor)
      rw [nerveOrderMap_id]
      exact local_iso _
  | succ n ih =>
      have he : last P (n+1) = (last P n).comp (chainLast (X := level P n)) := by
        ext s
        apply le_antisymm
        · apply (last P n).monotone
          exact (chain_has_greatest s).choose_spec.2 _ (greatest_mem s)
        · apply (last P n).monotone
          exact le_greatest s _ (chainGreatest_mem s)
      rw [he,nerveOrderMap_comp]
      exact local_comp (chainLast_local _) ih

lemma orderMap_of_nerve {P Q : PartOrd.{u}} (f : nerve P ⟶ nerve Q) :
    ∃ a : P →o Q, nerveMap a.toFunctor = f := by
  let F : P ⥤ Q := (nerveFunctor.preimage (X := Cat.of P) (Y := Cat.of Q) f).toFunctor
  refine ⟨F.toOrderHom,?_⟩
  exact nerveFunctor.map_preimage (X := Cat.of P) (Y := Cat.of Q) f

lemma stage_unmate {A X : SSet.{u}} (n : ℕ) (t : A ⟶ exStage X (n+1)) :
    Homotopic (lastVertex.app A ≫ t ≫ exInfinityInclusion X (n+1))
      ((SSet.sdExAdjunction.homEquiv A (exStage X n)).symm t ≫
        exInfinityInclusion X n) := by
  let E := exInfinity X
  let : SSet.KanComplex E := exInfinity_kan X
  let : SSet.KanComplex (SSet.ex.obj E) := ex_kan E
  obtain ⟨H⟩ := homotopy_of_anodyne_eq (exComparison.app (exStage X n))
    (exComparison_anodyne _) (exInfinityInclusion X (n+1) ≫ exComparison.app E)
    (SSet.ex.map (exInfinityInclusion X n)) (by
      rw [← Category.assoc,exInfinityInclusion_step]
      exact exComparison.naturality (exInfinityInclusion X n))
  have h := homotopic_pre t (homotopic_of_homotopy H)
  have hm := unmate_homotopic h
  rw [← Category.assoc,← mate_lastVertex,Equiv.symm_apply_apply] at hm
  rw [SSet.sdExAdjunction.homEquiv_naturality_right_symm] at hm
  exact hm

lemma finite_stage_order_representative (Q : PartOrd.{u}) (n : ℕ) :
    ∀ (P : PartOrd.{u}) [Finite P] (t : nerve P ⟶ exStage (nerve Q) n),
      ∃ R : PartOrd.{u}, ∃ _ : Finite R, ∃ l : R →o P, ∃ b : R →o Q,
        Local (nerveMap l.toFunctor) ∧ Homotopic
          (nerveMap l.toFunctor ≫ t ≫ exInfinityInclusion (nerve Q) n)
          (nerveMap b.toFunctor ≫ exInfinityComparison (nerve Q)) := by
  induction n with
  | zero =>
      intro P hP t
      obtain ⟨b,hb⟩ := orderMap_of_nerve t
      refine ⟨P,hP,OrderHom.id,b,?_,?_⟩
      · rw [nerveOrderMap_id]
        exact local_iso _
      · simpa only [nerveOrderMap_id,hb,Category.id_comp,exInfinityComparison] using
          (homotopic_refl (t ≫ exInfinityComparison (nerve Q)))
  | succ n ih =>
      intro P hP t
      let F := PartOrd.of (NonemptyFiniteChains P)
      let t' := (sdNerveIso (E := P)).inv ≫
        (SSet.sdExAdjunction.homEquiv (nerve P) (exStage (nerve Q) n)).symm t
      obtain ⟨R,hR,l,b,hl,hb⟩ := ih F t'
      let q := chainLast (X := P)
      refine ⟨R,hR,q.comp l,b,?_,?_⟩
      · rw [nerveOrderMap_comp]
        exact local_comp hl (chainLast_local P)
      · have h := homotopic_pre (nerveMap l.toFunctor ≫ (sdNerveIso (E := P)).inv)
          (stage_unmate n t)
        have he : (sdNerveIso (E := P)).inv ≫ lastVertex.app (nerve P) =
            nerveMap q.toFunctor := by
          have hv : (sdNerveIso (E := P)).hom ≫ nerveMap q.toFunctor =
              lastVertex.app (nerve P) := lastVertex_nerve
          rw [← hv,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
        simp only [Category.assoc] at h
        rw [← Category.assoc (sdNerveIso (E := P)).inv,he] at h
        exact homotopic_trans (by simpa only [nerveOrderMap_comp,Category.assoc,t'] using h) hb

lemma finite_order_representative {K : SSet.{u}} [SSet.KanComplex K]
    (Q : PartOrd.{u}) (r : nerve Q ⟶ K) (e : exInfinity (nerve Q) ⟶ K)
    (he : KanHomotopy.IsHomotopyEquivalence e) (hre : exInfinityComparison (nerve Q) ≫ e = r)
    (P : PartOrd.{u}) [Finite P] (a : nerve P ⟶ K) :
    ∃ R : PartOrd.{u}, ∃ _ : Finite R, ∃ l : R →o P, ∃ b : R →o Q,
      Local (nerveMap l.toFunctor) ∧
        Homotopic (nerveMap l.toFunctor ≫ a) (nerveMap b.toFunctor ≫ r) := by
  obtain ⟨s,hs,ht⟩ := he
  let : PreservesFilteredColimitsOfSize.{0,0}
      (coyoneda.obj (Opposite.op (nerve P))) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨n,t,ht'⟩ := Limits.exists_hom_of_preservesColimit_coyoneda
    (colimit.isColimit (exSequence (nerve Q))) (a ≫ s)
  let stageLift : nerve P ⟶ exStage (nerve Q) n := t
  obtain ⟨R,hR,l,b,hl,hb⟩ := finite_stage_order_representative Q n P stageLift
  have h₁ := homotopic_post hb e
  have h₂ := homotopic_pre (nerveMap l.toFunctor ≫ a) ht
  have ht'' : stageLift ≫ exInfinityInclusion (nerve Q) n = a ≫ s := ht'
  simp only [Category.assoc,hre] at h₁
  rw [← Category.assoc stageLift,ht''] at h₁
  simp only [Category.assoc,Category.comp_id] at h₂
  exact ⟨R,hR,l,b,hl,homotopic_trans (homotopic_symm h₂) h₁⟩

lemma kan_poset_replacement_heq (K : SSet.{u}) [SSet.KanComplex K] :
    ∃ Q : PartOrd.{u}, ∃ r : nerve Q ⟶ K, ∃ e : exInfinity (nerve Q) ⟶ K,
      Local r ∧ exInfinityComparison (nerve Q) ≫ e = r ∧
        KanHomotopy.IsHomotopyEquivalence e := by
  obtain ⟨Q,r,hr,_⟩ := Posetal.kan_poset_replacement K
  obtain ⟨e,he⟩ := extend_anodyne (exInfinityComparison (nerve Q))
    (exInfinityComparison_anodyne _) r
  let : SSet.KanComplex (exInfinity (nerve Q)) := exInfinity_kan _
  exact ⟨Q,r,e,hr,he,kan_local_heq e (local_of_precomp _ _
    (local_anodyne _ (exInfinityComparison_anodyne _)) (he.symm ▸ hr))⟩
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.PolyPoint
variable {P : Type u} [PartialOrder P]

def restrict (B : Set P) (x : PolyPoint P) (hx : ∀ p ∈ x.weights.support, p ∈ B) :
    PolyPoint B where
  weights := x.weights.subtypeDomain (· ∈ B)
  nonneg p := x.nonneg p.val
  total := (Finsupp.sum_subtypeDomain_index hx).trans x.total
  chain := by
    intro a ha b hb hab
    have ha' : a.val ∈ x.weights.support := by
      simpa only [Finset.mem_coe,Finsupp.mem_support_iff,Finsupp.subtypeDomain_apply] using ha
    have hb' : b.val ∈ x.weights.support := by
      simpa only [Finset.mem_coe,Finsupp.mem_support_iff,Finsupp.subtypeDomain_apply] using hb
    exact x.chain.total ha' hb'

def inclusion (B : Set P) : B →o P := ⟨Subtype.val,fun _ _ h => h⟩

lemma map_subtype_restrict (B : Set P) (x : PolyPoint P) (hx) :
    map (inclusion B) (preservesChains_monotone (inclusion B)) (restrict B x hx) = x := by
  classical
  apply PolyPoint.ext
  change (x.weights.subtypeDomain (· ∈ B)).mapDomain Subtype.val = x.weights
  calc
    _ = (x.weights.subtypeDomain (· ∈ B)).embDomain (Function.Embedding.subtype (· ∈ B)) :=
      (Finsupp.embDomain_eq_mapDomain (Function.Embedding.subtype (· ∈ B)) _).symm
    _ = (x.weights.subtypeDomain (· ∈ B)).extendDomain :=
      (Finsupp.extendDomain_eq_embDomain_subtype _).symm
    _ = x.weights := Finsupp.extendDomain_subtypeDomain _ hx

lemma map_injective {Q : Type*} [PartialOrder Q] (f : P →o Q)
    (hf : Function.Injective f) : Function.Injective (map f (preservesChains_monotone f)) := by
  intro x y he
  exact PolyPoint.ext (Finsupp.mapDomain_injective hf (congrArg PolyPoint.weights he))

lemma map_subtype_support (B : Set P) (x : PolyPoint B) :
    ∀ p ∈ (map (inclusion B) (preservesChains_monotone (inclusion B)) x).weights.support, p ∈ B := by
  classical
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp (map_support _ _ x hp)
  exact q.property

lemma exists_of_support (B : Set P) (x : PolyPoint P) :
    (∃ y : PolyPoint B, map (inclusion B) (preservesChains_monotone (inclusion B)) y = x) ↔
      ∀ p ∈ x.weights.support, p ∈ B := by
  constructor
  · rintro ⟨y,rfl⟩
    exact map_subtype_support B y
  · intro hx
    exact ⟨restrict B x hx,map_subtype_restrict B x hx⟩
end Thomason.GeometricRecognition.PolyPoint

end

noncomputable section
universe u v w z
open CategoryTheory PartialOrder

namespace Thomason.GeometricRecognition
open PolyPoint Mesh Contiguity Subdivision

lemma chains_map_injective {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) :
    Function.Injective (NonemptyFiniteChains.orderHomMap f) := by
  classical
  intro s t h
  apply NonemptyFiniteChains.ext
  exact Finset.image_injective hf (congrArg NonemptyFiniteChains.finset h)

lemma greatest_map {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (s : NonemptyFiniteChains P) : greatest (s.map f) = f (greatest s) := by
  apply le_antisymm
  · obtain ⟨p,hp,he⟩ := (NonemptyFiniteChains.mem_map_iff s f _).mp (greatest_mem (s.map f))
    rw [← he]
    exact f.monotone (le_greatest s p hp)
  · exact le_greatest (s.map f) _
      ((NonemptyFiniteChains.mem_map_iff s f _).mpr ⟨greatest s,greatest_mem s,rfl⟩)

def levelMap {P Q : PartOrd.{u}} (f : P →o Q) :
    (n : ℕ) → level P n →o level Q n
  | 0 => f
  | n+1 => NonemptyFiniteChains.orderHomMap (levelMap f n)

lemma levelMap_injective {P Q : PartOrd.{u}} (f : P →o Q) (hf : Function.Injective f)
    (n : ℕ) : Function.Injective (levelMap f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact chains_map_injective (levelMap f n) ih

lemma last_natural {P Q : PartOrd.{u}} (f : P →o Q) (n : ℕ) :
    (last Q n).comp (levelMap f n) = f.comp (last P n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext s
    change last Q n (greatest (s.map (levelMap f n))) = f (last P n (greatest s))
    rw [greatest_map]
    exact DFunLike.congr_fun ih (greatest s)

lemma map_barycenter {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) (s : NonemptyFiniteChains P) :
    map f (preservesChains_monotone f) (barycenter s) = barycenter (s.map f) := by
  classical
  apply PolyPoint.ext
  simp only [PolyPoint.map,barycenter,NonemptyFiniteChains.map,Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single,Finset.card_image_of_injective _ hf]
  rw [Finset.sum_image]
  exact fun a _ b _ hab => hf hab

lemma barycentricLinear_natural {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) (w : NonemptyFiniteChains P →₀ ℝ) :
    barycentricLinear (w.mapDomain (NonemptyFiniteChains.orderHomMap f)) =
      (barycentricLinear w).mapDomain f := by
  classical
  induction w using Finsupp.induction with
  | zero => simp
  | @single_add a r w har hr ih =>
    rw [Finsupp.mapDomain_add,map_add,ih,map_add,Finsupp.mapDomain_add]
    congr 1
    rw [Finsupp.mapDomain_single]
    simp only [barycentricLinear,Finsupp.linearCombination_single,Finsupp.mapDomain_smul]
    exact congrArg (fun z : Q →₀ ℝ => r • z) (congrArg PolyPoint.weights (map_barycenter f hf a)).symm

lemma subdivide_natural {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) (x : PolyPoint (NonemptyFiniteChains P)) :
    subdivide (map (NonemptyFiniteChains.orderHomMap f)
      (preservesChains_monotone (NonemptyFiniteChains.orderHomMap f)) x) =
      map f (preservesChains_monotone f) (subdivide x) :=
  PolyPoint.ext (barycentricLinear_natural f hf x.weights)

lemma levelHomeomorph_natural {P Q : PartOrd.{u}} (f : P →o Q)
    (hf : Function.Injective f) (n : ℕ) (x : PolyPoint (level P n)) :
    levelHomeomorph Q n (map (levelMap f n) (preservesChains_monotone (levelMap f n)) x) =
      map f (preservesChains_monotone f) (levelHomeomorph P n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change levelHomeomorph Q n (subdivide (map (NonemptyFiniteChains.orderHomMap (levelMap f n))
      (preservesChains_monotone _) x)) = _
    rw [subdivide_natural (levelMap f n) (levelMap_injective f hf n)]
    exact ih (subdivide x)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open PolyPoint Mesh Contiguity Approximation

lemma last_affine_support (P : PartOrd.{u}) (n : ℕ) (x : PolyPoint (level P n)) :
    (affineMap (last P n) x).weights.support ⊆ (levelHomeomorph P n x).weights.support := by
  classical
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp (map_support (last P n) (preservesChains_monotone (last P n)) x hp)
  exact last_support P n x q hq

def lastBarycentricHomotopy (P : PartOrd.{u}) [Finite P] (n : ℕ) :
    (affineMap (last P n)).Homotopy
      ⟨levelHomeomorph P n,(levelHomeomorph P n).continuous⟩ := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  exact carrierHomotopy _ _ (fun x => (levelHomeomorph P n x).chain.mono (by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact last_affine_support P n x hp
    · exact hp))

lemma lastBarycentricHomotopy_support (P : PartOrd.{u}) [Finite P] (n : ℕ)
    (t : unitInterval) (x : PolyPoint (level P n)) :
    (lastBarycentricHomotopy P n (t,x)).weights.support ⊆
      (levelHomeomorph P n x).weights.support := by
  classical
  intro p hp
  change p ∈ ((1 - t.val) • (affineMap (last P n) x).weights +
    t.val • (levelHomeomorph P n x).weights).support at hp
  rcases Finset.mem_union.mp (Finsupp.support_add hp) with hp | hp
  · exact last_affine_support P n x (Finsupp.support_smul hp)
  · exact Finsupp.support_smul hp

lemma lastBarycentricHomotopy_pair (P : PartOrd.{u}) [Finite P] (B : Set P) (n : ℕ)
    (t : unitInterval) (x : PolyPoint (level (PartOrd.of B) n)) :
    ∃ y : PolyPoint B, map (inclusion B) (preservesChains_monotone (inclusion B)) y =
      lastBarycentricHomotopy P n (t,
        map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n)
          (preservesChains_monotone _) x) := by
  apply (exists_of_support B _).mpr
  intro p hp
  have hx := lastBarycentricHomotopy_support P n t _ hp
  rw [levelHomeomorph_natural _ Subtype.val_injective] at hx
  exact map_subtype_support B _ p hx
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Subdivision

lemma kan_square_relative_surjective {A₁ A₀ B₁ B₀ D : SSet.{u}}
    [SSet.KanComplex A₁] [SSet.KanComplex A₀] [SSet.KanComplex B₁] [SSet.KanComplex B₀]
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (w : a ≫ f₀ = f₁ ≫ b) (ha : simplicialFibrations a) (hb : simplicialFibrations b)
    (hf₁ : IsHomotopyEquivalence f₁) (hf₀ : IsHomotopyEquivalence f₀)
    (x₀ : D ⟶ A₀) (z : D ⟶ B₁) (hz : x₀ ≫ f₀ = z ≫ b) :
    ∃ x : D ⟶ A₁, ∃ H : SSet.Homotopy (x ≫ f₁) z,
      x ≫ a = x₀ ∧ H.h ≫ b = fst D Δ[1] ≫ x₀ ≫ f₀ := by
  let y : D ⟶ Matching f₀ b := pullback.lift (x₀ ≫ left f₀) z (by simpa using hz)
  let : HasLiftingProperty (initial.to D) (relative a b w) :=
    relative_rlp a b w ha hb hf₁ hf₀ _ (by infer_instance)
  let sq : CommSq (initial.to (MappingPath f₁)) (initial.to D) (relative a b w) y :=
    ⟨by simp⟩
  let l : D ⟶ MappingPath f₁ := sq.lift
  have hl : l ≫ map a b w = x₀ ≫ left f₀ := by
    have hh := congrArg (fun t => t ≫ pullback.fst (right f₀) b) sq.fac_right
    simp only [relative,y,Category.assoc,pullback.lift_fst] at hh
    exact hh
  have hr : l ≫ right f₁ = z := by
    have hh := congrArg (fun t => t ≫ pullback.snd (right f₀) b) sq.fac_right
    simp only [relative,y,Category.assoc,pullback.lift_snd] at hh
    exact hh
  let x : D ⟶ A₁ := l ≫ pullback.fst f₁ (eval₀ B₁)
  let t : D ⟶ Paths B₁ := l ≫ pullback.snd f₁ (eval₀ B₁)
  have ht₀ : t ≫ eval₀ B₁ = x ≫ f₁ := by
    dsimp only [t,x]
    simp only [Category.assoc,← pullback.condition]
  have ht₁ : t ≫ eval₁ B₁ = z := hr
  refine ⟨x,CoherentGluing.toHomotopy (uncurryR t)
    ((comp_eval₀ t).symm.trans ht₀) ((comp_eval₁ t).symm.trans ht₁), ?_, ?_⟩
  · have hh := congrArg (fun q => q ≫ pullback.fst f₀ (eval₀ B₀)) hl
    simpa only [Category.assoc,map_fst,left,pullback.lift_fst,Category.comp_id,x] using hh
  · change uncurryR t ≫ b = _
    rw [← uncurryR_post]
    have ht : t ≫ (ihom Δ[1]).map b = x₀ ≫ f₀ ≫ const B₀ := by
      have hh := congrArg (fun q => q ≫ pullback.snd f₀ (eval₀ B₀)) hl
      simpa only [Category.assoc,map_snd,left,pullback.lift_snd,t] using hh
    rw [ht]
    simp only [uncurryR_pre,const,uncurryR_curryR,whiskerRight_fst_assoc,
      whiskerRight_fst]

lemma pre_fibration {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (K : SSet.{u}) [SSet.KanComplex K] : simplicialFibrations ((pre i).app K) := by
  rw [show simplicialFibrations = SSet.modelCategoryQuillen.J.rlp from rfl,
    ← SSet.modelCategoryQuillen.fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
  infer_instance

lemma path_const_natural {A B : SSet.{u}} (f : A ⟶ B) :
    const A ≫ (ihom Δ[1]).map f = f ≫ const B := by
  apply uncurryR_injective
  rw [uncurryR_post]
  simp only [uncurryR_pre,const,uncurryR_curryR,whiskerRight_fst]

lemma endsMap_comp {A B C : SSet.{u}} (f g : A ⟶ B) (h : B ⟶ C) :
    SimplicialCylinder.endsMap f g ≫ h = SimplicialCylinder.endsMap (f ≫ h) (g ≫ h) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  cases x <;> rfl

lemma endsInclusion_comp {A B : SSet.{u}} (h : A ⊗ Δ[1] ⟶ B) :
    SimplicialCylinder.endsInclusion A ≫ h =
      SimplicialCylinder.endsMap (SSet.ι₀ ≫ h) (SSet.ι₁ ≫ h) := endsMap_comp _ _ _

lemma kan_square_relative_injective {A₁ A₀ B₁ B₀ D : SSet.{u}}
    [SSet.KanComplex A₁] [SSet.KanComplex A₀] [SSet.KanComplex B₁] [SSet.KanComplex B₀]
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (w : a ≫ f₀ = f₁ ≫ b) (ha : simplicialFibrations a) (hb : simplicialFibrations b)
    (hf₁ : IsHomotopyEquivalence f₁) (hf₀ : IsHomotopyEquivalence f₀)
    (x y : D ⟶ A₁) (z : D ⟶ A₀) (hx : x ≫ a = z) (hy : y ≫ a = z)
    (H : SSet.Homotopy (x ≫ f₁) (y ≫ f₁))
    (hH : H.h ≫ b = fst D Δ[1] ≫ z ≫ f₀) :
    ∃ G : SSet.Homotopy x y, G.h ≫ a = fst D Δ[1] ≫ z := by
  let t : D ⊗ Δ[1] ⟶ Matching f₀ b := pullback.lift
    (fst D Δ[1] ≫ z ≫ left f₀) H.h (by simpa only [Category.assoc,KanPath.fac] using hH.symm)
  let : HasLiftingProperty (SimplicialCylinder.endsInclusion D) (relative a b w) :=
    relative_rlp a b w ha hb hf₁ hf₀ _ (by infer_instance)
  have hl (v : D ⟶ A₁) : (v ≫ left f₁) ≫ map a b w = v ≫ a ≫ left f₀ := by
    apply pullback.hom_ext
    · simp only [Category.assoc,map_fst,left,pullback.lift_fst_assoc,pullback.lift_fst,
        Category.id_comp,Category.comp_id]
    · simp only [Category.assoc,map_snd,left,pullback.lift_snd_assoc,pullback.lift_snd,
        path_const_natural]
      rw [← Category.assoc f₁ b,← w]
      simp only [Category.assoc]
  let sq : CommSq (SimplicialCylinder.endsMap (x ≫ left f₁) (y ≫ left f₁))
      (SimplicialCylinder.endsInclusion D) (relative a b w) t := ⟨by
    apply pullback.hom_ext
    · simp only [relative,t,Category.assoc,pullback.lift_fst,endsMap_comp,endsInclusion_comp,
        SSet.ι₀_fst_assoc,SSet.ι₁_fst_assoc]
      congr 1
      · simpa only [Category.assoc,← hx] using hl x
      · simpa only [Category.assoc,← hy] using hl y
    · simp only [relative,t,Category.assoc,pullback.lift_snd,endsMap_comp,endsInclusion_comp,
        Category.assoc,KanPath.fac,H.h₀,H.h₁]⟩
  have h₀' : SSet.ι₀ ≫ sq.lift = x ≫ left f₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro d
    exact congrArg (fun h => h.app n (Sum.inl d)) sq.fac_left
  have h₁' : SSet.ι₁ ≫ sq.lift = y ≫ left f₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro d
    exact congrArg (fun h => h.app n (Sum.inr d)) sq.fac_left
  let g := sq.lift ≫ pullback.fst f₁ (eval₀ B₁)
  have h₀ : SSet.ι₀ ≫ g = x := by
    dsimp only [g]
    rw [← Category.assoc,h₀']
    simp only [Category.assoc,left,pullback.lift_fst,Category.comp_id]
  have h₁ : SSet.ι₁ ≫ g = y := by
    dsimp only [g]
    rw [← Category.assoc,h₁']
    simp only [Category.assoc,left,pullback.lift_fst,Category.comp_id]
  refine ⟨CoherentGluing.toHomotopy g h₀ h₁, ?_⟩
  have hh := congrArg (fun h => h ≫ pullback.fst (right f₀) b ≫
    pullback.fst f₀ (eval₀ B₀)) sq.fac_right
  change g ≫ a = _
  simpa only [relative,t,g,Category.assoc,pullback.lift_fst_assoc,pullback.lift_fst,
    map_fst,left,Category.comp_id] using hh
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.Contiguity
open PolyPoint Mesh Approximation
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
local instance relativeContiguityFixedDecidableEq : DecidableEq Q := Classical.decEq Q

def Fixed (B : Set P) (q : Q) (f : ChainMap P Q) : Prop := ∀ p ∈ B, f p = q

def FixedMap (B : Set P) (q : Q) := {f : ChainMap P Q // Fixed B q f}
def FixedContiguous {B : Set P} {q : Q} (f g : FixedMap B q) : Prop :=
  Contiguous f.val g.val

def fixedMapSetoid (B : Set P) (q : Q) : Setoid (FixedMap B q) where
  r := Relation.EqvGen FixedContiguous
  iseqv := ⟨fun _ => Relation.EqvGen.refl _,fun h => Relation.EqvGen.symm _ _ h,
    fun h h' => Relation.EqvGen.trans _ _ _ h h'⟩

def RelativeRelated (B : Set P) (q : Q) (f g : ChainMap P Q) : Prop :=
  ∃ hf : Fixed B q f, ∃ hg : Fixed B q g,
    Relation.EqvGen FixedContiguous (⟨f,hf⟩ : FixedMap B q) ⟨g,hg⟩

lemma fixed_of_carrier (B : Set P) (q : Q) (f : ChainMap P Q) (h : PolyPoint P → PolyPoint Q)
    (hf : ∀ x, ∀ p ∈ x.weights.support, f p ∈ (h x).weights.support)
    (hh : ∀ p ∈ B, h (vertex p) = vertex q) : Fixed B q f := by
  intro p hp
  have hm := hf (vertex p) p (by simp only [vertex_support,Finset.mem_singleton])
  rw [hh p hp,vertex_support,Finset.mem_singleton] at hm
  exact hm

def relativeVertices (P : PartOrd.{u}) (A : Set (PolyPoint P)) (n : ℕ) :
    Set (level P n) := {p | levelHomeomorph P n (vertex p) ∈ A}

theorem homotopy_relative_contiguity (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (H : C(unitInterval × PolyPoint P, PolyPoint Q))
    (A : Set (PolyPoint P)) (q : Q) (hA : ∀ t x, x ∈ A → H (t,x) = vertex q) :
    ∃ n : ℕ, ∃ f g : ChainMap (level P n) Q,
      RelativeRelated (relativeVertices P A n) q f g ∧
      (∀ x : PolyPoint (level P n), ∀ p ∈ x.weights.support,
        f p ∈ (H (0,levelHomeomorph P n x)).weights.support) ∧
      (∀ x : PolyPoint (level P n), ∀ p ∈ x.weights.support,
        g p ∈ (H (1,levelHomeomorph P n x)).weights.support) := by
  obtain ⟨n,δ,hδ,labels,hl⟩ := homotopy_star_labels P H
  have hs (t : unitInterval) := hl t t (by simpa using hδ)
  let f (t : unitInterval) : ChainMap (level P n) Q :=
    ⟨labels t,labels_preserve_chains P (fun x => H (t,x)) n (labels t) (hs t)⟩
  have fixed (t : unitInterval) : Fixed (relativeVertices P A n) q (f t) :=
    fixed_of_carrier _ q (f t) _ (hs t) (fun p hp => hA t _ hp)
  let fr (t : unitInterval) : FixedMap (relativeVertices P A n) q := ⟨f t,fixed t⟩
  let F (t : unitInterval) : Quotient (fixedMapSetoid (relativeVertices P A n) q) :=
    Quotient.mk _ (fr t)
  have hF : IsLocallyConstant F := by
    intro B
    rw [Metric.isOpen_iff]
    intro t ht
    refine ⟨δ,hδ,fun s hst => ?_⟩
    have he : F s = F t := Quotient.sound (Relation.EqvGen.rel _ _
      (show FixedContiguous (fr s) (fr t) from
        contiguous_of_carrier (f s) (f t) (fun x => H (t,levelHomeomorph P n x))
          (hl t s (by simpa only [Metric.mem_ball,dist_comm] using hst)) (hs t)))
    change F s ∈ B
    rw [he]
    exact ht
  have h01 : F 0 = F 1 := congrFun (hF.eq_const 1) 0
  exact ⟨n,f 0,f 1,⟨fixed 0,fixed 1,Quotient.exact h01⟩,hs 0,hs 1⟩

theorem homotopy_relative_subdivision_contiguity (P : PartOrd.{u}) [Fintype P]
    {Q : Type v} [PartialOrder Q] (f g : P →o Q)
    (H : (affineMap f).Homotopy (affineMap g))
    (A : Set (PolyPoint P)) (q : Q) (hA : ∀ t x, x ∈ A → H (t,x) = vertex q) :
    ∃ n : ℕ, RelativeRelated (relativeVertices P A n) q
      (toChainMap (f.comp (last P n))) (toChainMap (g.comp (last P n))) := by
  obtain ⟨n,a,b,⟨ha',hb',hab⟩,ha,hb⟩ := homotopy_relative_contiguity P H.toContinuousMap A q hA
  have hf (x : PolyPoint (level P n)) (p : level P n) (hp : p ∈ x.weights.support) :
      toChainMap (f.comp (last P n)) p ∈
        (H (0,levelHomeomorph P n x)).weights.support := by
    rw [H.apply_zero]
    exact map_support_image f (preservesChains_monotone f) _ _ (last_support P n x p hp)
  have hg (x : PolyPoint (level P n)) (p : level P n) (hp : p ∈ x.weights.support) :
      toChainMap (g.comp (last P n)) p ∈
        (H (1,levelHomeomorph P n x)).weights.support := by
    rw [H.apply_one]
    exact map_support_image g (preservesChains_monotone g) _ _ (last_support P n x p hp)
  have hfr := fixed_of_carrier (relativeVertices P A n) q _ _ hf (fun p hp => hA 0 _ hp)
  have hgr := fixed_of_carrier (relativeVertices P A n) q _ _ hg (fun p hp => hA 1 _ hp)
  refine ⟨n,hfr,hgr,Relation.EqvGen.trans _ (⟨a,ha'⟩ : FixedMap _ q) _ ?_
    (Relation.EqvGen.trans _ (⟨b,hb'⟩ : FixedMap _ q) _ hab ?_)⟩
  · exact Relation.EqvGen.rel _ _ (contiguous_of_carrier _ a _ hf ha)
  · exact Relation.EqvGen.rel _ _ (contiguous_of_carrier b _ _ hb hg)
end Thomason.GeometricRecognition.Contiguity

end

noncomputable section
universe u v w z
open PartialOrder CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition.Contiguity
open PolyPoint Mesh Approximation
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
local instance relativeContiguityFaceDecidableEq : DecidableEq Q := Classical.decEq Q

def relativeFaceSet (B : Set P) : Set (NonemptyFiniteChains P) := {s | ∀ p ∈ s.finset, p ∈ B}

def relativeFaceInclusion (B : Set P) : relativeFaceSet B →o NonemptyFiniteChains P :=
  ⟨Subtype.val,fun _ _ h => h⟩

lemma oriented_fixed (B : Set P) (q : Q) (f : ChainMap P Q) (hf : Fixed B q f)
    (s : relativeFaceSet B) : orientedMap f.toFun f.chains s.val = q := by
  obtain ⟨p,hp,he⟩ := orientedMap_mem f.toFun f.chains s.val
  exact he.trans (hf p (s.property p hp))

lemma upper_fixed (B : Set P) (q : Q) (f g : ChainMap P Q) (h : Contiguous f g)
    (hf : Fixed B q f) (hg : Fixed B q g) (s : relativeFaceSet B) : upperMap f g h s.val = q := by
  have hm := greatest_mem (unionChain f g h s.val)
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hm
    exact he.symm.trans (hf p (s.property p hp))
  · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hm
    exact he.symm.trans (hg p (s.property p hp))

def constantOrder (A : Type u) [PartialOrder A] (q : Q) : A →o Q := ⟨fun _ => q,fun _ _ _ => le_rfl⟩

def BasedHomotopy {A X Y : SSet.{u}} (i : A ⟶ X) (c : A ⟶ Y) (f g : X ⟶ Y) : Prop :=
  ∃ H : SSet.Homotopy f g, (i ▷ Δ[1]) ≫ H.h = fst _ _ ≫ c

def BasedRelated {A X Y : SSet.{u}} (i : A ⟶ X) (c : A ⟶ Y) (f g : X ⟶ Y) : Prop :=
  Relation.EqvGen (BasedHomotopy i c) f g

lemma orderHomotopy_fixed {A : Type u} [PartialOrder A] (i : A →o P)
    (f g : P →o Q) (h : ∀ p, f p ≤ g p) (q : Q)
    (hf : ∀ a, f (i a) = q) (hg : ∀ a, g (i a) = q) :
    (nerveMap i.toFunctor ▷ Δ[1]) ≫ (HornSubdivision.orderHomotopy f g h).h =
      fst _ _ ≫ nerveMap (constantOrder A q).toFunctor := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  exact CategoryTheory.Functor.ext (fun j => by
    change (if (SSet.stdSimplex.objEquiv x.2).toOrderHom j = 0
      then f (i (x.1.obj j)) else g (i (x.1.obj j))) = q
    split_ifs <;> [exact hf _; exact hg _])

lemma fixed_contiguous_nerve (B : Set P) (q : Q) (f g : FixedMap B q)
    (h : FixedContiguous f g) :
    BasedRelated (nerveMap (relativeFaceInclusion B).toFunctor)
      (nerveMap (constantOrder (relativeFaceSet B) q).toFunctor)
      (nerveMap (orientedMap f.val.toFun f.val.chains).toFunctor)
      (nerveMap (orientedMap g.val.toFun g.val.chains).toFunctor) := by
  refine Relation.EqvGen.trans _ (nerveMap (upperMap f.val g.val h).toFunctor) _ ?_ ?_
  · apply Relation.EqvGen.rel
    exact ⟨HornSubdivision.orderHomotopy _ _ (left_le_upper f.val g.val h),
      orderHomotopy_fixed _ _ _ _ q (oriented_fixed B q f.val f.property)
        (upper_fixed B q f.val g.val h f.property g.property)⟩
  · apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    exact ⟨HornSubdivision.orderHomotopy _ _ (right_le_upper f.val g.val h),
      orderHomotopy_fixed _ _ _ _ q (oriented_fixed B q g.val g.property)
        (upper_fixed B q f.val g.val h f.property g.property)⟩

lemma fixed_related_nerve (B : Set P) (q : Q) (f g : FixedMap B q)
    (h : Relation.EqvGen FixedContiguous f g) :
    BasedRelated (nerveMap (relativeFaceInclusion B).toFunctor)
      (nerveMap (constantOrder (relativeFaceSet B) q).toFunctor)
      (nerveMap (orientedMap f.val.toFun f.val.chains).toFunctor)
      (nerveMap (orientedMap g.val.toFun g.val.chains).toFunctor) := by
  induction h with
  | rel f g h => exact fixed_contiguous_nerve B q f g h
  | refl f => exact Relation.EqvGen.refl _
  | symm f g h ih => exact Relation.EqvGen.symm _ _ ih
  | trans f g h hfg hgh ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

lemma relative_related_nerve (B : Set P) (q : Q) (f g : ChainMap P Q)
    (h : RelativeRelated B q f g) :
    BasedRelated (nerveMap (relativeFaceInclusion B).toFunctor)
      (nerveMap (constantOrder (relativeFaceSet B) q).toFunctor)
      (nerveMap (orientedMap f.toFun f.chains).toFunctor)
      (nerveMap (orientedMap g.toFun g.chains).toFunctor) := by
  obtain ⟨hf,hg,h⟩ := h
  exact fixed_related_nerve B q ⟨f,hf⟩ ⟨g,hg⟩ h
end Thomason.GeometricRecognition.Contiguity

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Subdivision Contiguity

lemma uncurry_homotopy_restriction {A B D K : SSet.{u}} (i : B ⟶ A)
    {f g : D ⟶ (ihom A).obj K} (H : SSet.Homotopy f g) (c : D ⟶ (ihom B).obj K)
    (hh : H.h ≫ (pre i).app K = fst D Δ[1] ≫ c) :
    (i ▷ D) ▷ Δ[1] ≫ (uncurryHomotopy H).h = fst (B ⊗ D) Δ[1] ≫ uncurry c := by
  change (i ▷ D) ▷ Δ[1] ≫ (α_ A D Δ[1]).hom ≫ uncurry H.h = _
  rw [associator_naturality_left_assoc,← uncurry_pre_app,hh,uncurry_natural_left]
  rw [← Category.assoc]
  have hp : (α_ B D Δ[1]).hom ≫ B ◁ fst D Δ[1] = fst (B ⊗ D) Δ[1] := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [hp]

lemma curry_homotopy_restriction {A B D K : SSet.{u}} (i : B ⟶ A)
    {f g : A ⊗ D ⟶ K} (H : SSet.Homotopy f g) (c : B ⊗ D ⟶ K)
    (hh : (i ▷ D) ▷ Δ[1] ≫ H.h = fst (B ⊗ D) Δ[1] ≫ c) :
    (curryHomotopy H).h ≫ (pre i).app K = fst D Δ[1] ≫ curry c := by
  apply uncurry_injective
  change uncurry (curry ((α_ A D Δ[1]).inv ≫ H.h) ≫ (pre i).app K) = _
  rw [uncurry_pre_app,uncurry_curry,uncurry_natural_left,uncurry_curry]
  have hn : i ▷ (D ⊗ Δ[1]) ≫ (α_ A D Δ[1]).inv =
      (α_ B D Δ[1]).inv ≫ i ▷ D ▷ Δ[1] := by
    simp
  rw [← Category.assoc,hn,Category.assoc,hh,← Category.assoc]
  congr 1

lemma pair_local_surjective {A B A' B' D K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (j : B' ⟶ A') [Mono j]
    (f : A' ⟶ A) (g : B' ⟶ B) (w : j ≫ f = g ≫ i)
    (hf : Local f) (hg : Local g) (c : B ⊗ D ⟶ K) (a : A' ⊗ D ⟶ K)
    (ha : j ▷ D ≫ a = g ▷ D ≫ c) :
    ∃ b : A ⊗ D ⟶ K, ∃ H : SSet.Homotopy (f ▷ D ≫ b) a,
      i ▷ D ≫ b = c ∧ j ▷ D ▷ Δ[1] ≫ H.h = fst (B' ⊗ D) Δ[1] ≫ g ▷ D ≫ c := by
  have hs : (pre i).app K ≫ (pre g).app K = (pre f).app K ≫ (pre j).app K := by
    rw [← NatTrans.comp_app,← pre_map,← NatTrans.comp_app,← pre_map,w]
  have hc : curry c ≫ (pre g).app K = curry a ≫ (pre j).app K := by
    apply uncurry_injective
    simpa only [uncurry_pre_app,uncurry_curry] using ha.symm
  obtain ⟨x,H,hx,hH⟩ := kan_square_relative_surjective ((pre i).app K) ((pre j).app K)
    hs (pre_fibration i K) (pre_fibration j K) (hf K inferInstance) (hg K inferInstance)
    (curry c) (curry a) hc
  have hx' : i ▷ D ≫ uncurry x = c := by
    have hh := congrArg (fun z : D ⟶ (ihom B).obj K => uncurry z) hx
    simpa only [uncurry_pre_app,uncurry_curry] using hh
  have ht := uncurry_homotopy_restriction j H (curry c ≫ (pre g).app K) hH
  have hmap : uncurry (curry c ≫ (pre g).app K) = g ▷ D ≫ c := by
    rw [uncurry_pre_app,uncurry_curry]
  rw [hmap] at ht
  let G : SSet.Homotopy (f ▷ D ≫ uncurry x) a := CoherentGluing.toHomotopy
    (uncurryHomotopy H).h
    (by simpa only [uncurry_pre_app,uncurry_curry] using (uncurryHomotopy H).h₀)
    (by simpa only [uncurry_pre_app,uncurry_curry] using (uncurryHomotopy H).h₁)
  exact ⟨uncurry x,G,hx',ht⟩

lemma pair_local_injective {A B A' B' D K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (j : B' ⟶ A') [Mono j]
    (f : A' ⟶ A) (g : B' ⟶ B) (w : j ≫ f = g ≫ i)
    (hf : Local f) (hg : Local g) (c : B ⊗ D ⟶ K) (a b : A ⊗ D ⟶ K)
    (ha : i ▷ D ≫ a = c) (hb : i ▷ D ≫ b = c)
    (H : SSet.Homotopy (f ▷ D ≫ a) (f ▷ D ≫ b))
    (hH : j ▷ D ▷ Δ[1] ≫ H.h = fst (B' ⊗ D) Δ[1] ≫ g ▷ D ≫ c) :
    ∃ G : SSet.Homotopy a b, i ▷ D ▷ Δ[1] ≫ G.h = fst (B ⊗ D) Δ[1] ≫ c := by
  have hs : (pre i).app K ≫ (pre g).app K = (pre f).app K ≫ (pre j).app K := by
    rw [← NatTrans.comp_app,← pre_map,← NatTrans.comp_app,← pre_map,w]
  have hc (v : A ⊗ D ⟶ K) (hv : i ▷ D ≫ v = c) :
      curry v ≫ (pre i).app K = curry c := by
    apply uncurry_injective
    simpa only [uncurry_pre_app,uncurry_curry] using hv
  let H' : SSet.Homotopy (curry a ≫ (pre f).app K) (curry b ≫ (pre f).app K) :=
    CoherentGluing.toHomotopy (curryHomotopy H).h
      (by have hh := (curryHomotopy H).h₀
          simpa only [curry_pre_app] using hh)
      (by have hh := (curryHomotopy H).h₁
          simpa only [curry_pre_app] using hh)
  have hH' : H'.h ≫ (pre j).app K = fst D Δ[1] ≫ curry c ≫ (pre g).app K := by
    change (curryHomotopy H).h ≫ (pre j).app K = _
    simpa only [curry_pre_app,Category.assoc] using
      curry_homotopy_restriction j H (g ▷ D ≫ c) hH
  obtain ⟨G,hG⟩ := kan_square_relative_injective ((pre i).app K) ((pre j).app K)
    hs (pre_fibration i K) (pre_fibration j K) (hf K inferInstance) (hg K inferInstance)
    (curry a) (curry b) (curry c) (hc a ha) (hc b hb) H' hH'
  let G' : SSet.Homotopy a b := CoherentGluing.toHomotopy (uncurryHomotopy G).h
    (by simpa only [uncurry_curry] using (uncurryHomotopy G).h₀)
    (by simpa only [uncurry_curry] using (uncurryHomotopy G).h₁)
  refine ⟨G',?_⟩
  change i ▷ D ▷ Δ[1] ≫ (uncurryHomotopy G).h = _
  simpa only [uncurry_curry] using uncurry_homotopy_restriction i G (curry c) hG
end Thomason.GeometricRecognition

end

end OAI
