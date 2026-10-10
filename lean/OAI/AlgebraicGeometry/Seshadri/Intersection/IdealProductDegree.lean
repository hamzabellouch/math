import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.AmbientCurveDegree
import OAI.AlgebraicGeometry.Seshadri.Divisors.IdealSectionLifting

namespace OAI


                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma lift_of_local_module_lifts {M N P : X.Modules} (ι : N ⟶ P) [Mono ι]
    (s : M ⟶ P) (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ t : M.restrict U.ι ⟶ N.restrict U.ι,
        t ≫ (Scheme.Modules.restrictFunctor U.ι).map ι =
          (Scheme.Modules.restrictFunctor U.ι).map s) :
    ∃ t : M ⟶ N, t ≫ ι = s := by
  have hz : s ≫ cokernel.π ι = 0 := by
    apply MaximalSeshadri.ModuleLocal.eq_zero_of_local
    intro x
    obtain ⟨U,hx,t,ht⟩ := hs x
    refine ⟨U,hx,?_⟩
    rw [Functor.map_comp,← ht,Category.assoc,← Functor.map_comp,
      cokernel.condition,Functor.map_zero,comp_zero]
  exact ⟨Abelian.monoLift _ s hz,Abelian.monoLift_comp _ s hz⟩

lemma ideal_inclusion_lift (A B : LineBundle X) (a : A.sheaf ⟶ O X)
    (b : B.sheaf ⟶ O X) [Mono b]
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : A.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ f : B.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) a} ≤
        Ideal.span {affineMapCoefficient U f (Scheme.Modules.restrictUnitIso U.1.ι) b}) :
    ∃ φ : A.sheaf ⟶ B.sheaf, φ ≫ b = a := by
  apply lift_of_local_module_lifts b a
  intro x
  obtain ⟨U,hx,e,f,hh⟩ := h x
  have hm := hh (Ideal.subset_span (Set.mem_singleton
    (affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) a)))
  obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp hm
  obtain ⟨t,ht⟩ := framed_local_division f (Scheme.Modules.restrictUnitIso U.1.ι)
    ((Scheme.Modules.restrictFunctor U.1.ι).map b)
    (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map a) (by
      rw [Ideal.mem_span_singleton]
      refine ⟨U.1.topIso.inv c,?_⟩
      have H := congrArg U.1.topIso.inv hc
      simpa only [affineMapCoefficient,map_mul,U.1.topIso.hom_inv_id_apply,
        coefficient,Category.assoc] using H)
  refine ⟨U.1,hx,e.hom ≫ t,?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun morphism : O U.1.toScheme ⟶ (O X).restrict U.1.ι =>
      e.hom ≫ morphism) ht).trans (e.hom_inv_id_assoc _))

lemma ideal_inclusions_iso (A B : LineBundle X) (a : A.sheaf ⟶ O X)
    (b : B.sheaf ⟶ O X) [Mono a] [Mono b]
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : A.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ f : B.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) a} =
        Ideal.span {affineMapCoefficient U f (Scheme.Modules.restrictUnitIso U.1.ι) b}) :
    Nonempty (A.sheaf ≅ B.sheaf) := by
  obtain ⟨φ,hφ⟩ := ideal_inclusion_lift A B a b (fun x => by
    obtain ⟨U,hx,e,f,he⟩ := h x
    exact ⟨U,hx,e,f,he.le⟩)
  obtain ⟨ψ,hψ⟩ := ideal_inclusion_lift B A b a (fun x => by
    obtain ⟨U,hx,e,f,he⟩ := h x
    exact ⟨U,hx,f,e,he.ge⟩)
  exact ⟨⟨φ,ψ,by apply (cancel_mono a).mp; simp [Category.assoc,hφ,hψ],
    by apply (cancel_mono b).mp; simp [Category.assoc,hφ,hψ]⟩⟩

def finiteTensor : (n : ℕ) → (Fin n → LineBundle X) → LineBundle X
  | 0, _ => { sheaf := O X, locallyRankOne := fun x =>
      ⟨⊤,by trivial,⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩ }
  | n+1, J => (J 0).tensor (finiteTensor n (fun i => J i.succ))

def finiteTensorInclusion : (n : ℕ) → (J : Fin n → LineBundle X) →
    (∀ i, (J i).sheaf ⟶ O X) → ((finiteTensor n J).sheaf ⟶ O X)
  | 0, _, _ => 𝟙 _
  | n+1, J, a => tensorInclusion (J 0) (finiteTensor n (fun i => J i.succ)) (a 0) ≫
      finiteTensorInclusion n (fun i => J i.succ) (fun i => a i.succ)

lemma finiteTensorInclusion_mono (n : ℕ) (J : Fin n → LineBundle X)
    (a : ∀ i, (J i).sheaf ⟶ O X) (ha : ∀ i, Mono (a i)) :
    Mono (finiteTensorInclusion n J a) := by
  induction n with
  | zero => change Mono (𝟙 _); infer_instance
  | succ n ih =>
    exact mono_comp'
      (@tensorInclusion_mono X (J 0) (finiteTensor n (fun i => J i.succ)) (a 0) (ha 0))
      (ih (fun i => J i.succ) (fun i => a i.succ) (fun i => ha i.succ))

def finiteTensorFrame (U : X.Opens) : (n : ℕ) → (J : Fin n → LineBundle X) →
    (∀ i, (J i).sheaf.restrict U.ι ≅ O U.toScheme) →
    ((finiteTensor n J).sheaf.restrict U.ι ≅ O U.toScheme)
  | 0, _, _ => Scheme.Modules.restrictUnitIso U.ι
  | n+1, J, e => tensorFrame (J 0) (finiteTensor n (fun i => J i.succ)) U (e 0)
      (finiteTensorFrame U n (fun i => J i.succ) (fun i => e i.succ))

lemma finiteTensorInclusion_ideal (U : X.affineOpens) (n : ℕ) (J : Fin n → LineBundle X)
    (a : ∀ i, (J i).sheaf ⟶ O X)
    (e : ∀ i, (J i).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {affineMapCoefficient U (finiteTensorFrame U.1 n J e)
      (Scheme.Modules.restrictUnitIso U.1.ι) (finiteTensorInclusion n J a)} =
    ∏ i : Fin n, Ideal.span {affineMapCoefficient U (e i) (Scheme.Modules.restrictUnitIso U.1.ι) (a i)} := by
  let unitFrame : (O X).restrict U.1.ι ≅ O U.1.toScheme :=
    Scheme.Modules.restrictUnitIso U.1.ι
  change Ideal.span {affineMapCoefficient U (finiteTensorFrame U.1 n J e)
    unitFrame (finiteTensorInclusion n J a)} =
    ∏ i : Fin n, Ideal.span {affineMapCoefficient U (e i) unitFrame (a i)}
  induction n with
  | zero =>
    change Ideal.span {affineMapCoefficient U unitFrame unitFrame (𝟙 (O X))} = _
    have hidentity : affineMapCoefficient U unitFrame unitFrame (𝟙 (O X)) = 1 := by
      let restrictionFunctor : X.Modules ⥤ U.1.toScheme.Modules :=
        Scheme.Modules.restrictFunctor U.1.ι
      change U.1.topIso.hom (endValue
        (unitFrame.inv ≫ restrictionFunctor.map (𝟙 (O X)) ≫ unitFrame.hom)) = 1
      rw [restrictionFunctor.map_id,Category.id_comp,unitFrame.inv_hom_id,
        endValue_id,map_one]
    simp only [hidentity,Ideal.span_singleton_one,Fin.prod_univ_zero,Ideal.one_eq_top]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    change Ideal.span {affineMapCoefficient U (tensorFrame (J 0)
      (finiteTensor n (fun i => J i.succ)) U.1 (e 0)
      (finiteTensorFrame U.1 n (fun i => J i.succ) (fun i => e i.succ)))
      unitFrame (tensorInclusion (J 0) (finiteTensor n (fun i => J i.succ)) (a 0) ≫
        finiteTensorInclusion n (fun i => J i.succ) (fun i => a i.succ))} = _
    rw [affineMapCoefficient_comp U _
      (finiteTensorFrame U.1 n (fun i => J i.succ) (fun i => e i.succ)) unitFrame
      (tensorInclusion (J 0) (finiteTensor n (fun i => J i.succ)) (a 0))
      (finiteTensorInclusion n (fun i => J i.succ) (fun i => a i.succ)),
      ← Ideal.span_singleton_mul_span_singleton,ih]
    congr 1
    exact tensor_inclusion_ideal _ _ _ _ _ _

lemma finite_common_frames {α : Type} [Fintype α] (J : α → LineBundle X)
    (x : X) (W : X.Opens) (hxW : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      Nonempty (∀ i, (J i).sheaf.restrict U.1.ι ≅ O U.1.toScheme) := by
  classical
  choose V hx e using fun i => (J i).locallyRankOne x
  let V' := W ⊓ ⨅ i, V i
  have hx' : x ∈ V' := ⟨hxW,by rw [Opens.coe_iInf]; exact Set.mem_iInter.mpr hx⟩
  obtain ⟨U,hU,hxU,hUV⟩ := exists_isAffineOpen_mem_and_subset hx'
  refine ⟨⟨U,hU⟩,hxU,hUV.trans inf_le_left,⟨fun i =>
    frameOnSmaller (Classical.choice (e i)) U (hUV.trans (inf_le_right.trans (iInf_le V i)))⟩⟩

lemma idealSheaf_prod_ideal {α : Type*} (s : Finset α) (I : α → X.IdealSheafData)
    (U : X.affineOpens) : (∏ i ∈ s, I i).ideal U = ∏ i ∈ s, (I i).ideal U := by
  classical
  induction s using Finset.induction with
  | empty => simp [Scheme.IdealSheafData.ideal_top]
  | insert a s ha ih => simp only [Finset.prod_insert ha,Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply,ih]

lemma curveDegree_finiteTensor (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (n : ℕ) (J : Fin n → LineBundle S.scheme) (C : IntegralCurve S) :
    curveDegree S (finiteTensor n J) C = ∑ i, curveDegree S (J i) C := by
  induction n with
  | zero =>
    change curveDegree S (A.pow 0) C = _
    rw [curveDegree_pow S A hA]
    simp
  | succ n ih =>
    change curveDegree S ((J 0).tensor (finiteTensor n (fun i => J i.succ))) C = _
    rw [curveDegree_tensor S A hA,ih,Fin.sum_univ_succ]

theorem PointBlowup.total_ideal_degree (S : Surface) {r : ℕ} {p : Configuration S r}
    (B : PointBlowup S r p) (A : LineBundle B.surface.scheme) (hA : A.IsAmple)
    (J : LineBundle B.surface.scheme) (ι : J.sheaf ⟶ O B.surface.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) B.projection J ι)
    (C : IntegralCurve B.surface) :
    curveDegree B.surface J C = ∑ i,curveDegree B.surface (B.exceptionalIdeal i) C := by
  classical
  let T := finiteTensor r B.exceptionalIdeal
  let a := finiteTensorInclusion r B.exceptionalIdeal B.exceptionalInclusion
  let : Mono (C := B.surface.scheme.Modules) ι := hJ.1
  let : Mono (C := B.surface.scheme.Modules) a :=
    finiteTensorInclusion_mono r B.exceptionalIdeal B.exceptionalInclusion
    (fun i => (B.exceptionalPullback i).1)
  obtain ⟨e⟩ := ideal_inclusions_iso J T ι a (fun y => by
    obtain ⟨V,hV,hyV,-⟩ := exists_isAffineOpen_mem_and_subset
      (show B.projection y ∈ (⊤ : S.scheme.Opens) from trivial)
    let VV : S.scheme.affineOpens := ⟨V,hV⟩
    obtain ⟨W,hyW,⟨eW⟩⟩ := J.locallyRankOne y
    obtain ⟨U,hyU,hUW,⟨f⟩⟩ := finite_common_frames B.exceptionalIdeal y
      (W ⊓ B.projection ⁻¹ᵁ V) ⟨hyW,hyV⟩
    let eU := frameOnSmaller eW U.1 (hUW.trans inf_le_left)
    refine ⟨U,hyU,eU,finiteTensorFrame U.1 r B.exceptionalIdeal f,?_⟩
    refine (InvertibleLocal.pullback_frame_equation J ι hJ U VV
      (hUW.trans inf_le_right) eU).symm.trans ?_
    refine Eq.trans ?_ (finiteTensorInclusion_ideal U r B.exceptionalIdeal
      B.exceptionalInclusion f).symm
    change ((∏ i, (p.val i).left.ker).ideal VV).map _ = _
    rw [idealSheaf_prod_ideal,show Ideal.map _ (∏ i, (p.val i).left.ker.ideal VV) =
      ∏ i, Ideal.map _ ((p.val i).left.ker.ideal VV) from
        map_prod (Ideal.mapHom _) _ _]
    apply Finset.prod_congr rfl
    intro i hi
    exact InvertibleLocal.pullback_frame_equation _ _ (B.exceptionalPullback i) U VV
      (hUW.trans inf_le_right) (f i))
  have he : curveDegree B.surface J C = curveDegree B.surface T C := by
    unfold curveDegree
    rw [eulerCharacteristic_iso (C.embedding ≫ B.surface.structureMap)
      ((Scheme.Modules.pullback C.embedding).mapIso e) 1]
  rw [he]
  exact curveDegree_finiteTensor B.surface A hA r B.exceptionalIdeal C

end
end MaximalSeshadri.Geometry

end

end OAI
