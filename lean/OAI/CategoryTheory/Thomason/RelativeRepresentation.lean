import Mathlib
import OAI.CategoryTheory.Thomason.RelativeContiguity

namespace OAI

/-! Relative Representation. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Subdivision Contiguity

lemma pair_local_surjective_plain {A B A' B' K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (j : B' ⟶ A') [Mono j]
    (f : A' ⟶ A) (g : B' ⟶ B) (w : j ≫ f = g ≫ i)
    (hf : Local f) (hg : Local g) (c : B ⟶ K) (a : A' ⟶ K)
    (ha : j ≫ a = g ≫ c) :
    ∃ b : A ⟶ K, ∃ H : SSet.Homotopy (f ≫ b) a,
      i ≫ b = c ∧ (j ▷ Δ[1]) ≫ H.h = fst B' Δ[1] ≫ g ≫ c := by
  obtain ⟨b,H,hb,hH⟩ := pair_local_surjective i j f g w hf hg ((ρ_ B).hom ≫ c)
    ((ρ_ A').hom ≫ a) (by rw [rightUnitor_naturality_assoc,ha,rightUnitor_naturality_assoc])
  let b' : A ⟶ K := (ρ_ A).inv ≫ b
  let H' : SSet.Homotopy (f ≫ b') a := CoherentGluing.toHomotopy
    ((ρ_ A').inv ▷ Δ[1] ≫ H.h)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,b',Category.assoc,rightUnitor_inv_naturality_assoc] using
      (homotopy_pre (ρ_ A').inv H).h₀)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,b',Category.assoc,Iso.inv_hom_id_assoc] using
      (homotopy_pre (ρ_ A').inv H).h₁)
  refine ⟨b',H',?_,?_⟩
  · dsimp only [b']
    rw [rightUnitor_inv_naturality_assoc,hb,Iso.inv_hom_id_assoc]
  · change j ▷ Δ[1] ≫ (ρ_ A').inv ▷ Δ[1] ≫ H.h = _
    rw [← comp_whiskerRight_assoc,rightUnitor_inv_naturality,
      comp_whiskerRight_assoc,hH,whiskerRight_fst_assoc]
    simp only [rightUnitor_naturality_assoc,Iso.inv_hom_id_assoc]

lemma pair_local_injective_plain {A B A' B' K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (j : B' ⟶ A') [Mono j]
    (f : A' ⟶ A) (g : B' ⟶ B) (w : j ≫ f = g ≫ i)
    (hf : Local f) (hg : Local g) (c : B ⟶ K) (a b : A ⟶ K)
    (ha : i ≫ a = c) (hb : i ≫ b = c)
    (H : SSet.Homotopy (f ≫ a) (f ≫ b))
    (hH : j ▷ Δ[1] ≫ H.h = fst B' Δ[1] ≫ g ≫ c) :
    ∃ G : SSet.Homotopy a b, i ▷ Δ[1] ≫ G.h = fst B Δ[1] ≫ c := by
  let H' : SSet.Homotopy (f ▷ (𝟙_ SSet) ≫ (ρ_ A).hom ≫ a)
      (f ▷ (𝟙_ SSet) ≫ (ρ_ A).hom ≫ b) := CoherentGluing.toHomotopy
    ((ρ_ A').hom ▷ Δ[1] ≫ H.h)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,rightUnitor_naturality_assoc,Category.assoc] using
      (homotopy_pre (ρ_ A').hom H).h₀)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,rightUnitor_naturality_assoc,Category.assoc] using
      (homotopy_pre (ρ_ A').hom H).h₁)
  obtain ⟨G,hG⟩ := pair_local_injective i j f g w hf hg ((ρ_ B).hom ≫ c)
    ((ρ_ A).hom ≫ a) ((ρ_ A).hom ≫ b)
    (by rw [rightUnitor_naturality_assoc,ha])
    (by rw [rightUnitor_naturality_assoc,hb]) H' (by
      change j ▷ (𝟙_ SSet) ▷ Δ[1] ≫ (ρ_ A').hom ▷ Δ[1] ≫ H.h = _
      rw [← comp_whiskerRight_assoc,rightUnitor_naturality,
        comp_whiskerRight_assoc,hH,whiskerRight_fst_assoc]
      simp only [rightUnitor_naturality_assoc])
  let G' : SSet.Homotopy a b := CoherentGluing.toHomotopy
    ((ρ_ A).inv ▷ Δ[1] ≫ G.h)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,Category.assoc,Iso.inv_hom_id_assoc] using (homotopy_pre (ρ_ A).inv G).h₀)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,Category.assoc,Iso.inv_hom_id_assoc] using (homotopy_pre (ρ_ A).inv G).h₁)
  refine ⟨G',?_⟩
  change i ▷ Δ[1] ≫ (ρ_ A).inv ▷ Δ[1] ≫ G.h = _
  rw [← comp_whiskerRight_assoc,rightUnitor_inv_naturality,
    comp_whiskerRight_assoc,hG,whiskerRight_fst_assoc]
  simp only [Iso.inv_hom_id_assoc]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory PartialOrder Simplicial MonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open PolyPoint Mesh Approximation Contiguity LastVertexProof KanLocal

lemma vertex_injective {Q : Type u} [PartialOrder Q] :
    Function.Injective (@vertex Q _) := by
  classical
  intro a b h
  have hh := congrArg (fun x : PolyPoint Q => x.weights.support) h
  simpa only [vertex_support,Finset.singleton_inj] using hh

lemma nerveOrderMap_mono {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) : Mono (nerveMap f.toFunctor) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  intro x y h
  exact CategoryTheory.Functor.ext (fun i => hf (congrArg (fun z => z.obj i) h))

lemma pair_geometric_approximation (P : PartOrd.{u}) [Finite P] (B : Set P)
    {Q : Type u} [PartialOrder Q] (q : Q) (f : C(PolyPoint P,PolyPoint Q))
    (hf : ∀ x : PolyPoint B,
      f (map (inclusion B) (preservesChains_monotone (inclusion B)) x) = vertex q) :
    ∃ n : ℕ, ∃ a : level P n →o Q,
      ∃ H : (affineMap a).Homotopy
        (f.comp ⟨levelHomeomorph P n,(levelHomeomorph P n).continuous⟩),
        (a.comp (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n) =
          OrderHom.const _ q) ∧
        ∀ t x, H (t,map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n)
          (preservesChains_monotone _) x) = vertex q := by
  let : Fintype P := Fintype.ofFinite P
  obtain ⟨n,a,H,hc,hfixed⟩ := relative_approximation P f
  have hh (x : PolyPoint (level (PartOrd.of B) n)) (t : unitInterval) :
      H (t,map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n)
        (preservesChains_monotone _) x) = vertex q := by
    apply hfixed
    rw [levelHomeomorph_natural _ Subtype.val_injective]
    exact hf _
  refine ⟨n,a,H,?_,fun t x => hh x t⟩
  ext x
  apply vertex_injective
  change vertex (a ((levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n) x)) = vertex q
  have h := (H.apply_zero _).symm.trans (hh (vertex x) 0)
  simpa only [affineMap,ContinuousMap.coe_mk,map_vertex] using h

lemma descend_pair_approximation (P : PartOrd.{u}) (B : Set P) (n : ℕ)
    (K : SSet.{u}) [SSet.KanComplex K] (c : nerve B ⟶ K)
    (a : nerve (level P n) ⟶ K)
    (ha : nerveMap (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n).toFunctor ≫ a =
      nerveMap (last (PartOrd.of B) n).toFunctor ≫ c) :
    ∃ b : nerve P ⟶ K, ∃ H : SSet.Homotopy (nerveMap (last P n).toFunctor ≫ b) a,
      nerveMap (inclusion B).toFunctor ≫ b = c ∧
      (nerveMap (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n).toFunctor ▷ Δ[1]) ≫ H.h =
        CategoryTheory.CartesianMonoidalCategory.fst _ Δ[1] ≫
          nerveMap (last (PartOrd.of B) n).toFunctor ≫ c := by
  let := nerveOrderMap_mono (inclusion B) Subtype.val_injective
  let := nerveOrderMap_mono (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n)
    (levelMap_injective _ Subtype.val_injective n)
  apply pair_local_surjective_plain _ _ _ _ _ (last_local P n) (last_local (PartOrd.of B) n) c a ha
  rw [← nerveOrderMap_comp,← nerveOrderMap_comp,last_natural]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision

lemma unmate_homotopy_relative {A B K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] {f g : A ⟶ SSet.ex.obj K}
    (H : SSet.Homotopy f g) (hH : i ▷ Δ[1] ≫ H.h = fst B Δ[1] ≫ i ≫ g) :
    ∃ G : SSet.Homotopy ((SSet.sdExAdjunction.homEquiv A K).symm f)
      ((SSet.sdExAdjunction.homEquiv A K).symm g),
      SSet.sd.map i ▷ Δ[1] ≫ G.h = fst (SSet.sd.obj B) Δ[1] ≫
        SSet.sd.map i ≫ (SSet.sdExAdjunction.homEquiv A K).symm g := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i
    (SSet.stdSimplex.δ (n := 0) (0 : Fin 2))
  have hinl : s.inl ≫ s.ι = A ◁ SSet.stdSimplex.δ (n := 0) 0 := s.inl_ι
  have hinr : s.inr ≫ s.ι = i ▷ Δ[1] := s.inr_ι
  have heq : s.ι ≫ H.h = s.ι ≫ fst A Δ[1] ≫ g := by
    apply s.isPushout.hom_ext
    · rw [← Category.assoc,hinl,← Category.assoc,hinl]
      apply (cancel_epi (SimplicialCylinder.zeroFactorIso A).hom).mp
      rw [← Category.assoc,CoherentGluing.zeroFactor_one,H.h₁,
        ← Category.assoc,CoherentGluing.zeroFactor_one,SSet.ι₁_fst_assoc]
    · rw [← Category.assoc,hinr,← Category.assoc,hinr,hH,whiskerRight_fst_assoc]
  let h := (SSet.sdExAdjunction.homEquiv (A ⊗ Δ[1]) K).symm H.h
  let g' := (SSet.sdExAdjunction.homEquiv A K).symm g
  let p := SSet.sd.map (fst A Δ[1])
  have heq' : SSet.sd.map s.ι ≫ h = SSet.sd.map s.ι ≫ p ≫ g' := by
    dsimp only [h,p,g']
    rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm]
    exact (SSet.sdExAdjunction.homEquiv_naturality_left_symm
      (show s.pt ⟶ A ⊗ Δ[1] from s.ι) H.h).symm.trans
        ((congrArg (SSet.sdExAdjunction.homEquiv s.pt K).symm heq).trans
          (SSet.sdExAdjunction.homEquiv_naturality_left_symm
            (show s.pt ⟶ A ⊗ Δ[1] from s.ι) (fst A Δ[1] ≫ g)))
  obtain ⟨R,hR⟩ := homotopy_of_anodyne_eq_relative (SSet.sd.map s.ι)
    (HornSubdivision.sd_preserves_anodyne _
      (SSet.anodyneExtensions_pushoutObjObjι s (SimplicialCylinder.delta_one_anodyne 0)))
    h (p ≫ g') heq'
  have h₀ : SSet.sd.map (SSet.ι₀ (X := A)) ≫ h =
      (SSet.sdExAdjunction.homEquiv A K).symm f := by
    dsimp only [h]
    rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm,H.h₀]
  have hp : SSet.sd.map (SSet.ι₀ (X := A)) ≫ p = 𝟙 _ := by
    dsimp only [p]
    rw [← Functor.map_comp,SSet.ι₀_fst,CategoryTheory.Functor.map_id]
  let G := homotopy_pre (SSet.sd.map (SSet.ι₀ (X := A))) R
  let G' : SSet.Homotopy ((SSet.sdExAdjunction.homEquiv A K).symm f) g' :=
    CoherentGluing.toHomotopy G.h (by simpa only [h₀] using G.h₀)
      (by simpa only [← Category.assoc,hp,Category.id_comp] using G.h₁)
  refine ⟨G',?_⟩
  change SSet.sd.map i ▷ Δ[1] ≫ SSet.sd.map SSet.ι₀ ▷ Δ[1] ≫ R.h = _
  rw [← comp_whiskerRight_assoc,← Functor.map_comp,← SSet.ι₀_comp,← hinr,
    ← Category.assoc,Functor.map_comp,comp_whiskerRight_assoc,hR,whiskerRight_fst_assoc]
  rw [← Category.assoc (SSet.sd.map _) (SSet.sd.map _),← Functor.map_comp,
    Category.assoc,hinr,SSet.ι₀_comp,Functor.map_comp,Category.assoc,h₀]
  have hfg : i ≫ f = i ≫ g := by
    have hh := congrArg (fun t => SSet.ι₀ ≫ t) hH
    simpa only [SSet.ι₀_comp_assoc,H.h₀,SSet.ι₀_fst_assoc] using hh
  rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm,
    ← SSet.sdExAdjunction.homEquiv_naturality_left_symm,hfg]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision

lemma stage_unmate_boundary {A B X : SSet.{u}} (i : B ⟶ A) (n : ℕ)
    (t : A ⟶ exStage X (n+1)) (k : B ⟶ exStage X n)
    (ht : i ≫ t = k ≫ exComparison.app (exStage X n)) :
    SSet.sd.map i ≫ (SSet.sdExAdjunction.homEquiv A (exStage X n)).symm t =
      lastVertex.app B ≫ k := by
  rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm,ht,← mate_lastVertex,
    Equiv.symm_apply_apply]

lemma stage_unmate_relative {A B X : SSet.{u}} (i : B ⟶ A) [Mono i] (n : ℕ)
    (t : A ⟶ exStage X (n+1)) (k : B ⟶ exStage X n)
    (ht : i ≫ t = k ≫ exComparison.app (exStage X n)) :
    ∃ G : SSet.Homotopy (lastVertex.app A ≫ t ≫ exInfinityInclusion X (n+1))
      ((SSet.sdExAdjunction.homEquiv A (exStage X n)).symm t ≫ exInfinityInclusion X n),
      SSet.sd.map i ▷ Δ[1] ≫ G.h =
        fst (SSet.sd.obj B) Δ[1] ≫ lastVertex.app B ≫ k ≫ exInfinityInclusion X n := by
  let E := exInfinity X
  let : SSet.KanComplex E := exInfinity_kan X
  let : SSet.KanComplex (SSet.ex.obj E) := ex_kan E
  obtain ⟨H,hH⟩ := homotopy_of_anodyne_eq_relative (exComparison.app (exStage X n))
    (exComparison_anodyne _) (exInfinityInclusion X (n+1) ≫ exComparison.app E)
    (SSet.ex.map (exInfinityInclusion X n)) (by
      rw [← Category.assoc,exInfinityInclusion_step]
      exact exComparison.naturality (exInfinityInclusion X n))
  let F := homotopy_pre t H
  have hF : i ▷ Δ[1] ≫ F.h = fst B Δ[1] ≫ i ≫ t ≫ SSet.ex.map (exInfinityInclusion X n) := by
    change i ▷ Δ[1] ≫ t ▷ Δ[1] ≫ H.h = _
    rw [← comp_whiskerRight_assoc,ht,comp_whiskerRight_assoc,hH]
    change k ▷ Δ[1] ≫ fst (exStage X n) Δ[1] ≫ _ = _
    rw [whiskerRight_fst_assoc]
    rw [← Category.assoc (exComparison.app _) (exInfinityInclusion X (n+1)),
      exInfinityInclusion_step,← Category.assoc i t,ht]
    simp only [Category.assoc]
    rw [← exComparison.naturality]
    rfl
  obtain ⟨G,hG⟩ := unmate_homotopy_relative i F hF
  have hf : (SSet.sdExAdjunction.homEquiv A E).symm
      (t ≫ exInfinityInclusion X (n+1) ≫ exComparison.app E) =
      lastVertex.app A ≫ t ≫ exInfinityInclusion X (n+1) := by
    rw [← Category.assoc,← mate_lastVertex,Equiv.symm_apply_apply]
  have hg : (SSet.sdExAdjunction.homEquiv A E).symm
      (t ≫ SSet.ex.map (exInfinityInclusion X n)) =
      (SSet.sdExAdjunction.homEquiv A (exStage X n)).symm t ≫ exInfinityInclusion X n :=
    SSet.sdExAdjunction.homEquiv_naturality_right_symm t (exInfinityInclusion X n)
  let G' := CoherentGluing.toHomotopy G.h (G.h₀.trans hf) (G.h₁.trans hg)
  refine ⟨G',?_⟩
  change SSet.sd.map i ▷ Δ[1] ≫ G.h = _
  rw [hG,hg,← Category.assoc (SSet.sd.map i),stage_unmate_boundary i n t k ht]
  simp only [Category.assoc]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Contiguity HornSubdivision

lemma fill_rectangle_over {D E F : SSet.{u}} (p : E ⟶ F) (hp : simplicialFibrations p)
    {a b c d : D ⟶ E} (z : D ⟶ F) (bottom : SSet.Homotopy a b)
    (left : SSet.Homotopy a c) (right : SSet.Homotopy b d)
    (hbottom : bottom.h ≫ p = fst D Δ[1] ≫ z)
    (hleft : left.h ≫ p = fst D Δ[1] ≫ z)
    (hright : right.h ≫ p = fst D Δ[1] ≫ z) :
    ∃ G : SSet.Homotopy c d, G.h ≫ p = fst D Δ[1] ≫ z := by
  obtain ⟨Q,hQ,h₀,hpQ⟩ := cylinder_lift (SimplicialCylinder.endsInclusion D) p hp 1
    bottom.h (sides left.h right.h) (fst (D ⊗ Δ[1]) Δ[1] ≫ fst D Δ[1] ≫ z)
    (by rw [endpoint_sides,endpoint_zero,left.h₀,right.h₀,ends_pre,bottom.h₀,bottom.h₁])
    (by rw [endpoint_zero,SSet.ι₀_fst_assoc,hbottom])
    (by rw [ends_sides_post,hleft,hright]
        ext n x
        rcases x with ⟨x,t⟩
        cases x <;> rfl)
  refine ⟨CoherentGluing.toHomotopy (SSet.ι₁ ≫ Q)
    ((square_top_zero Q left.h right.h hQ).trans left.h₁)
    ((square_top_one Q left.h right.h hQ).trans right.h₁),?_⟩
  change (SSet.ι₁ ≫ Q) ≫ p = _
  rw [Category.assoc,hpQ,SSet.ι₁_fst_assoc]

lemma fill_rectangle_relative_tensor {A B D K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] {a b c d : A ⊗ D ⟶ K} (z : B ⊗ D ⟶ K)
    (bottom : SSet.Homotopy a b) (left : SSet.Homotopy a c) (right : SSet.Homotopy b d)
    (hbottom : i ▷ D ▷ Δ[1] ≫ bottom.h = fst (B ⊗ D) Δ[1] ≫ z)
    (hleft : i ▷ D ▷ Δ[1] ≫ left.h = fst (B ⊗ D) Δ[1] ≫ z)
    (hright : i ▷ D ▷ Δ[1] ≫ right.h = fst (B ⊗ D) Δ[1] ≫ z) :
    ∃ G : SSet.Homotopy c d, i ▷ D ▷ Δ[1] ≫ G.h = fst (B ⊗ D) Δ[1] ≫ z := by
  obtain ⟨G,hG⟩ := fill_rectangle_over ((pre i).app K) (pre_fibration i K)
    (curry z) (curryHomotopy bottom) (curryHomotopy left) (curryHomotopy right)
    (curry_homotopy_restriction i bottom z hbottom)
    (curry_homotopy_restriction i left z hleft)
    (curry_homotopy_restriction i right z hright)
  let H := uncurryHomotopy G
  let H' : SSet.Homotopy c d := CoherentGluing.toHomotopy H.h
    (by simpa only [uncurry_curry] using H.h₀)
    (by simpa only [uncurry_curry] using H.h₁)
  refine ⟨H',?_⟩
  change i ▷ D ▷ Δ[1] ≫ (uncurryHomotopy G).h = _
  simpa only [uncurry_curry] using uncurry_homotopy_restriction i G (curry z) hG

lemma fill_rectangle_relative {A B K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] {a b c d : A ⟶ K} (z : B ⟶ K)
    (bottom : SSet.Homotopy a b) (left : SSet.Homotopy a c) (right : SSet.Homotopy b d)
    (hbottom : i ▷ Δ[1] ≫ bottom.h = fst B Δ[1] ≫ z)
    (hleft : i ▷ Δ[1] ≫ left.h = fst B Δ[1] ≫ z)
    (hright : i ▷ Δ[1] ≫ right.h = fst B Δ[1] ≫ z) :
    ∃ G : SSet.Homotopy c d, i ▷ Δ[1] ≫ G.h = fst B Δ[1] ≫ z := by
  have hh {f g : A ⟶ K} (H : SSet.Homotopy f g)
      (hH : i ▷ Δ[1] ≫ H.h = fst B Δ[1] ≫ z) :
      i ▷ (𝟙_ SSet) ▷ Δ[1] ≫ (homotopy_pre (ρ_ A).hom H).h =
        fst (B ⊗ (𝟙_ SSet)) Δ[1] ≫ (ρ_ B).hom ≫ z := by
    change i ▷ (𝟙_ SSet) ▷ Δ[1] ≫ (ρ_ A).hom ▷ Δ[1] ≫ H.h = _
    rw [← comp_whiskerRight_assoc,rightUnitor_naturality,comp_whiskerRight_assoc,
      hH,whiskerRight_fst_assoc]
  obtain ⟨G,hG⟩ := fill_rectangle_relative_tensor i ((ρ_ B).hom ≫ z)
    (homotopy_pre (ρ_ A).hom bottom) (homotopy_pre (ρ_ A).hom left)
    (homotopy_pre (ρ_ A).hom right) (hh bottom hbottom) (hh left hleft) (hh right hright)
  let G' : SSet.Homotopy c d := CoherentGluing.toHomotopy
    ((ρ_ A).inv ▷ Δ[1] ≫ G.h)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,Category.assoc,Iso.inv_hom_id_assoc]
      using (homotopy_pre (ρ_ A).inv G).h₀)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,Category.assoc,Iso.inv_hom_id_assoc]
      using (homotopy_pre (ρ_ A).inv G).h₁)
  refine ⟨G',?_⟩
  change i ▷ Δ[1] ≫ (ρ_ A).inv ▷ Δ[1] ≫ G.h = _
  rw [← comp_whiskerRight_assoc,rightUnitor_inv_naturality,comp_whiskerRight_assoc,
    hG,whiskerRight_fst_assoc]
  simp only [Iso.inv_hom_id_assoc]

lemma based_homotopy_symm {A B K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (z : B ⟶ K) {a b : A ⟶ K}
    (H : BasedHomotopy i z a b) : BasedHomotopy i z b a := by
  obtain ⟨H,hH⟩ := H
  have ha : i ≫ a = z := by
    have hh := congrArg (fun q => SSet.ι₀ ≫ q) hH
    simpa only [SSet.ι₀_comp_assoc,H.h₀,SSet.ι₀_fst_assoc] using hh
  exact fill_rectangle_relative i z (refl a) H (refl a)
    (by change i ▷ Δ[1] ≫ fst A Δ[1] ≫ a = _; rw [whiskerRight_fst_assoc,ha]) hH
    (by change i ▷ Δ[1] ≫ fst A Δ[1] ≫ a = _; rw [whiskerRight_fst_assoc,ha])

lemma based_homotopy_trans {A B K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (z : B ⟶ K) {a b c : A ⟶ K}
    (H : BasedHomotopy i z a b) (H' : BasedHomotopy i z b c) : BasedHomotopy i z a c := by
  obtain ⟨H,hH⟩ := H
  obtain ⟨H',hH'⟩ := H'
  have ha : i ≫ a = z := by
    have hh := congrArg (fun q => SSet.ι₀ ≫ q) hH
    simpa only [SSet.ι₀_comp_assoc,H.h₀,SSet.ι₀_fst_assoc] using hh
  exact fill_rectangle_relative i z H (refl a) H' hH
    (by change i ▷ Δ[1] ≫ fst A Δ[1] ≫ a = _; rw [whiskerRight_fst_assoc,ha]) hH'
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh

lemma based_homotopy_refl {A B K : SSet.{u}} (i : B ⟶ A) (z : B ⟶ K)
    (a : A ⟶ K) (ha : i ≫ a = z) : BasedHomotopy i z a a := by
  refine ⟨refl a,?_⟩
  change i ▷ Δ[1] ≫ fst A Δ[1] ≫ a = _
  rw [whiskerRight_fst_assoc,ha]

lemma based_homotopy_pre {A B A' B' K : SSet.{u}}
    (i : B ⟶ A) (j : B' ⟶ A') (f : A' ⟶ A) (g : B' ⟶ B)
    (w : j ≫ f = g ≫ i) (z : B ⟶ K) {a b : A ⟶ K}
    (H : BasedHomotopy i z a b) : BasedHomotopy j (g ≫ z) (f ≫ a) (f ≫ b) := by
  obtain ⟨H,hH⟩ := H
  refine ⟨homotopy_pre f H,?_⟩
  change j ▷ Δ[1] ≫ f ▷ Δ[1] ≫ H.h = _
  rw [← comp_whiskerRight_assoc,w,comp_whiskerRight_assoc,hH,whiskerRight_fst_assoc]

lemma based_homotopy_post {A B K L : SSet.{u}} (i : B ⟶ A) (z : B ⟶ K)
    {a b : A ⟶ K} (H : BasedHomotopy i z a b) (f : K ⟶ L) :
    BasedHomotopy i (z ≫ f) (a ≫ f) (b ≫ f) := by
  obtain ⟨H,hH⟩ := H
  refine ⟨homotopy_post H f,?_⟩
  change i ▷ Δ[1] ≫ H.h ≫ f = _
  rw [← Category.assoc,hH,Category.assoc]

lemma constantOrder_comp {P Q R : Type u} [PartialOrder P] [PartialOrder Q]
    [PartialOrder R] (f : P →o Q) (r : R) :
    (constantOrder Q r).comp f = constantOrder P r := rfl

lemma nerve_constant_pre {P Q R : Type u} [PartialOrder P] [PartialOrder Q]
    [PartialOrder R] (f : P →o Q) (r : R) :
    nerveMap f.toFunctor ≫ nerveMap (constantOrder Q r).toFunctor =
      nerveMap (constantOrder P r).toFunctor := by
  rw [← nerveOrderMap_comp,constantOrder_comp]

lemma sdNerve_inv_natural {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P →o Q) :
    nerveMap (NonemptyFiniteChains.orderHomMap f).toFunctor ≫ (sdNerveIso (E := Q)).inv =
      (sdNerveIso (E := P)).inv ≫ SSet.sd.map (nerveMap f.toFunctor) := by
  apply (cancel_mono (sdNerveIso (E := Q)).hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  have hh := sdNerveMap_naturality f
  change SSet.sd.map (nerveMap f.toFunctor) ≫ (sdNerveIso (E := Q)).hom =
    (sdNerveIso (E := P)).hom ≫ nerveMap (NonemptyFiniteChains.orderHomMap f).toFunctor at hh
  rw [hh,Iso.inv_hom_id_assoc]

lemma sdNerve_inv_last (P : PartOrd.{u}) :
    (sdNerveIso (E := P)).inv ≫ lastVertex.app (nerve P) = nerveMap (chainLast (X := P)).toFunctor := by
  rw [← lastVertex_nerve]
  change (sdNerveIso (E := P)).inv ≫ (sdNerveIso (E := P)).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

lemma chainLast_natural {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P →o Q) :
    (chainLast (X := Q)).comp (NonemptyFiniteChains.orderHomMap f) =
      f.comp (chainLast (X := P)) := by
  have hc {T : Type u} [PartialOrder T] (s : NonemptyFiniteChains T) :
      chainLast s = greatest s := by
    apply le_antisymm
    · exact le_greatest s _ (chainGreatest_mem s)
    · exact (chain_has_greatest s).choose_spec.2 _ (greatest_mem s)
  ext s
  change chainLast (s.map f) = f (chainLast s)
  rw [hc,hc,greatest_map]

structure PairRefinement (P B : PartOrd.{u}) (i : B →o P) where
  R : PartOrd.{u}
  S : PartOrd.{u}
  finiteR : Finite R
  finiteS : Finite S
  j : S →o R
  injective : Function.Injective j
  l : R →o P
  k : S →o B
  square : l.comp j = i.comp k
  local_l : Local (nerveMap l.toFunctor)
  local_k : Local (nerveMap k.toFunctor)
  home : PolyPoint R ≃ₜ PolyPoint P
  homeB : PolyPoint S ≃ₜ PolyPoint B
  natural : ∀ x, home (map j (preservesChains_monotone j) x) =
    map i (preservesChains_monotone i) (homeB x)

attribute [instance] PairRefinement.finiteR PairRefinement.finiteS

def PairRefinement.identity (P B : PartOrd.{u}) [Finite P] [Finite B]
    (i : B →o P) (hi : Function.Injective i) : PairRefinement P B i where
  R := P
  S := B
  finiteR := inferInstance
  finiteS := inferInstance
  j := i
  injective := hi
  l := OrderHom.id
  k := OrderHom.id
  square := rfl
  local_l := by rw [nerveOrderMap_id]; exact local_iso _
  local_k := by rw [nerveOrderMap_id]; exact local_iso _
  home := Homeomorph.refl _
  homeB := Homeomorph.refl _
  natural := fun _ => rfl

def PairRefinement.prepend (P B : PartOrd.{u}) (i : B →o P)
    (hi : Function.Injective i)
    (d : PairRefinement (PartOrd.of (NonemptyFiniteChains P))
      (PartOrd.of (NonemptyFiniteChains B)) (NonemptyFiniteChains.orderHomMap i)) :
    PairRefinement P B i where
  R := d.R
  S := d.S
  finiteR := d.finiteR
  finiteS := d.finiteS
  j := d.j
  injective := d.injective
  l := (chainLast (X := P)).comp d.l
  k := (chainLast (X := B)).comp d.k
  square := by
    rw [OrderHom.comp_assoc,d.square,← OrderHom.comp_assoc,chainLast_natural,OrderHom.comp_assoc]
  local_l := by rw [nerveOrderMap_comp]; exact local_comp d.local_l (chainLast_local P)
  local_k := by rw [nerveOrderMap_comp]; exact local_comp d.local_k (chainLast_local B)
  home := d.home.trans subdivisionHomeomorph
  homeB := d.homeB.trans subdivisionHomeomorph
  natural := by
    intro x
    change subdivide (d.home (map d.j (preservesChains_monotone d.j) x)) = _
    rw [d.natural,subdivide_natural i hi]
    rfl

lemma exSequence_zero_succ (X : SSet.{u}) (n : ℕ) :
    (exSequence X).map (homOfLE (Nat.zero_le (n+1))) =
      (exSequence X).map (homOfLE (Nat.zero_le n)) ≫ exComparison.app (exStage X n) := by
  have h := (exSequence X).map_comp (homOfLE (Nat.zero_le n)) (homOfLE (Nat.le_succ n))
  erw [Functor.ofSequence_map_homOfLE_succ] at h
  exact h
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh

@[reassoc]
lemma exSequence_zero_inclusion (X : SSet.{u}) (n : ℕ) :
    (exSequence X).map (homOfLE (Nat.zero_le n)) ≫ exInfinityInclusion X n =
      exInfinityComparison X := colimit.w _ _

@[reassoc]
lemma nerve_constant_pre' {P Q R : Type u} [PartialOrder P] [PartialOrder Q]
    [PartialOrder R] (f : P →o Q) (r : R) :
    nerveMap f.toFunctor ≫ nerveMap (constantOrder Q r).toFunctor =
      nerveMap (constantOrder P r).toFunctor := nerve_constant_pre f r

lemma stage_order_pair_representative (Q : PartOrd.{u}) (q : Q) (n : ℕ) :
    ∀ (P B : PartOrd.{u}) [Finite P] [Finite B] (i : B →o P), Function.Injective i →
      ∀ (t : nerve P ⟶ exStage (nerve Q) n),
      nerveMap i.toFunctor ≫ t = nerveMap (constantOrder B q).toFunctor ≫
        (exSequence (nerve Q)).map (homOfLE (Nat.zero_le n)) →
    ∃ d : PairRefinement P B i, ∃ b : d.R →o Q,
      b.comp d.j = constantOrder d.S q ∧
      BasedHomotopy (nerveMap d.j.toFunctor)
        (nerveMap (constantOrder d.S q).toFunctor ≫ exInfinityComparison (nerve Q))
        (nerveMap d.l.toFunctor ≫ t ≫ exInfinityInclusion (nerve Q) n)
        (nerveMap b.toFunctor ≫ exInfinityComparison (nerve Q)) := by
  induction n with
  | zero =>
    intro P B hP hB i hi t ht
    obtain ⟨b,hb⟩ := orderMap_of_nerve t
    have hbc : b.comp i = constantOrder B q := by
      have ht' : nerveMap i.toFunctor ≫ t = nerveMap (constantOrder B q).toFunctor := by
        have h0 : (exSequence (nerve Q)).map (homOfLE (Nat.zero_le 0)) = 𝟙 (nerve Q) :=
          (exSequence (nerve Q)).map_id 0
        rw [h0] at ht
        exact ht.trans (Category.comp_id _)
      ext x
      have hh := congrArg (fun f : nerve B ⟶ nerve Q =>
        ((f.app (Opposite.op ⦋0⦌)) ((CategoryTheory.Functor.const (Fin 1)).obj x)).obj 0)
        (show nerveMap i.toFunctor ≫ nerveMap b.toFunctor = nerveMap (constantOrder B q).toFunctor from by simpa only [hb] using ht')
      exact hh
    refine ⟨PairRefinement.identity P B i hi,b,hbc,?_⟩
    change BasedHomotopy (nerveMap i.toFunctor) _
      (nerveMap (OrderHom.id : P →o P).toFunctor ≫ t ≫ _) _
    rw [nerveOrderMap_id,Category.id_comp,← hb]
    apply based_homotopy_refl
    rw [← Category.assoc,← nerveOrderMap_comp,hbc]
    rfl
  | succ n ih =>
    intro P B hP hB i hi t ht
    let F := PartOrd.of (NonemptyFiniteChains P)
    let G := PartOrd.of (NonemptyFiniteChains B)
    let j : G →o F := NonemptyFiniteChains.orderHomMap i
    let : Mono (nerveMap i.toFunctor) := nerveOrderMap_mono i hi
    let zeroInclusion : nerve Q ⟶ exStage (nerve Q) n :=
      (exSequence (nerve Q)).map (homOfLE (Nat.zero_le n))
    have zeroInclusion_eq : zeroInclusion ≫ exInfinityInclusion (nerve Q) n =
        exInfinityComparison (nerve Q) := exSequence_zero_inclusion (nerve Q) n
    let k : nerve B ⟶ exStage (nerve Q) n :=
      nerveMap (constantOrder B q).toFunctor ≫ zeroInclusion
    have ht' : nerveMap i.toFunctor ≫ t = k ≫ exComparison.app (exStage (nerve Q) n) := by
      rw [ht,exSequence_zero_succ]
      exact (Category.assoc (nerveMap (constantOrder B q).toFunctor) zeroInclusion
        (exComparison.app (exStage (nerve Q) n))).symm
    let t' := (sdNerveIso (E := P)).inv ≫
      (SSet.sdExAdjunction.homEquiv (nerve P) (exStage (nerve Q) n)).symm t
    have ht'' : nerveMap j.toFunctor ≫ t' = nerveMap (constantOrder G q).toFunctor ≫
        (exSequence (nerve Q)).map (homOfLE (Nat.zero_le n)) := by
      change nerveMap j.toFunctor ≫ t' = nerveMap (constantOrder G q).toFunctor ≫ zeroInclusion
      dsimp only [t',j]
      rw [← Category.assoc,sdNerve_inv_natural,Category.assoc,
        stage_unmate_boundary _ n t k ht',← Category.assoc,sdNerve_inv_last]
      dsimp only [k]
      rw [nerve_constant_pre'_assoc]
    obtain ⟨d,b,hb,Hb⟩ := ih F G j (chains_map_injective i hi) t' ht''
    let D := PairRefinement.prepend P B i hi d
    let : SSet.KanComplex (exInfinity (nerve Q)) := exInfinity_kan _
    let : Mono (nerveMap d.j.toFunctor) := nerveOrderMap_mono d.j d.injective
    refine ⟨D,b,hb,?_⟩
    obtain ⟨H,hH⟩ := stage_unmate_relative (nerveMap i.toFunctor) n t k ht'
    have HH : BasedHomotopy (SSet.sd.map (nerveMap i.toFunctor))
        (lastVertex.app (nerve B) ≫ k ≫ exInfinityInclusion (nerve Q) n)
        (lastVertex.app (nerve P) ≫ t ≫ exInfinityInclusion (nerve Q) (n+1))
        ((SSet.sdExAdjunction.homEquiv (nerve P) (exStage (nerve Q) n)).symm t ≫
          exInfinityInclusion (nerve Q) n) := ⟨H,hH⟩
    have H₀ := based_homotopy_pre _ (nerveMap j.toFunctor) (sdNerveIso (E := P)).inv
      (sdNerveIso (E := B)).inv (sdNerve_inv_natural i) _ HH
    simp only [← Category.assoc (sdNerveIso (E := P)).inv,
      ← Category.assoc (sdNerveIso (E := B)).inv,sdNerve_inv_last] at H₀
    have H₁ := based_homotopy_pre _ (nerveMap d.j.toFunctor)
      (nerveMap d.l.toFunctor) (nerveMap d.k.toFunctor)
      (by rw [← nerveOrderMap_comp,← nerveOrderMap_comp,d.square]) _ H₀
    have hz : nerveMap d.k.toFunctor ≫ (nerveMap (chainLast (X := B)).toFunctor ≫
        k ≫ exInfinityInclusion (nerve Q) n) =
        nerveMap (constantOrder d.S q).toFunctor ≫ exInfinityComparison (nerve Q) := by
      dsimp only [k]
      simp only [Category.assoc,nerve_constant_pre'_assoc,zeroInclusion_eq]
    rw [hz] at H₁
    have HH' : BasedHomotopy (nerveMap d.j.toFunctor)
        (nerveMap (constantOrder d.S q).toFunctor ≫ exInfinityComparison (nerve Q))
        (nerveMap ((chainLast (X := P)).comp d.l).toFunctor ≫
          t ≫ exInfinityInclusion (nerve Q) (n+1))
        (nerveMap d.l.toFunctor ≫ t' ≫ exInfinityInclusion (nerve Q) n) := by
      rw [nerveOrderMap_comp]
      simpa only [Category.assoc,t'] using H₁
    exact based_homotopy_trans (nerveMap d.j.toFunctor) _ HH' Hb

lemma finite_pair_order_representative {K : SSet.{u}} [SSet.KanComplex K]
    (Q : PartOrd.{u}) (q : Q) (r : nerve Q ⟶ K) (e : exInfinity (nerve Q) ⟶ K)
    (he : IsHomotopyEquivalence e) (hre : exInfinityComparison (nerve Q) ≫ e = r)
    (P B : PartOrd.{u}) [Finite P] [Finite B] (i : B →o P) (hi : Function.Injective i)
    (a : nerve P ⟶ K)
    (ha : nerveMap i.toFunctor ≫ a = nerveMap (constantOrder B q).toFunctor ≫ r) :
    ∃ d : PairRefinement P B i, ∃ b : d.R →o Q,
      b.comp d.j = constantOrder d.S q ∧
      BasedHomotopy (nerveMap d.j.toFunctor)
        (nerveMap (constantOrder d.S q).toFunctor ≫ r)
        (nerveMap d.l.toFunctor ≫ a) (nerveMap b.toFunctor ≫ r) := by
  let : Mono (nerveMap i.toFunctor) := nerveOrderMap_mono i hi
  let : SSet.KanComplex (exInfinity (nerve Q)) := exInfinity_kan _
  obtain ⟨g,H,hg,hH⟩ := relative_representative e he (nerveMap i.toFunctor)
    (nerveMap (constantOrder B q).toFunctor ≫ exInfinityComparison (nerve Q)) a
    (by simpa only [Category.assoc,hre] using ha)
  obtain ⟨n,t,ht,ht'⟩ := finite_relative_stage (nerveMap i.toFunctor)
    (nerveMap (constantOrder B q).toFunctor) g hg
  obtain ⟨d,b,hb,Hb⟩ := stage_order_pair_representative Q q n P B i hi t ht'
  let : Mono (nerveMap d.j.toFunctor) := nerveOrderMap_mono d.j d.injective
  have H₀ : BasedHomotopy (nerveMap i.toFunctor)
      (nerveMap (constantOrder B q).toFunctor ≫ r) (g ≫ e) a :=
    ⟨H,by simpa only [Category.assoc,hre] using hH⟩
  have H₁ := based_homotopy_pre _ (nerveMap d.j.toFunctor)
    (nerveMap d.l.toFunctor) (nerveMap d.k.toFunctor)
    (by rw [← nerveOrderMap_comp,← nerveOrderMap_comp,d.square]) _ H₀
  simp only [nerve_constant_pre'_assoc] at H₁
  have H₂ := based_homotopy_post _ _ Hb e
  simp only [Category.assoc,hre,ht] at H₂
  exact ⟨d,b,hb,based_homotopy_trans _ _ (based_homotopy_symm _ _ H₁) H₂⟩
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity HornSubdivision

lemma edge_homotopy_const {K : SSet.{u}} {x y : K _⦋0⦌} (e : K.Edge x y) :
    Nonempty (SSet.Homotopy (SSet.const (X := Δ[0]) x) (SSet.const y)) := by
  refine ⟨CoherentGluing.toHomotopy (snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm e.edge) ?_ ?_⟩
  · rw [SSet.ι₀_snd_assoc,← SSet.stdSimplex.δ_one_eq_const,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm,e.src_eq,SSet.yonedaEquiv_symm_zero]
  · rw [SSet.ι₁_snd_assoc,← SSet.stdSimplex.δ_zero_eq_const,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm,e.tgt_eq,SSet.yonedaEquiv_symm_zero]

lemma component_homotopic_const {K : SSet.{u}} {x y : K _⦋0⦌}
    (h : SSet.π₀.mk x = SSet.π₀.mk y) :
    Homotopic (SSet.const (X := Δ[0]) x) (SSet.const y) := by
  have h' := (SSet.π₀.mk_eq_mk_iff x y).mp h
  clear h
  induction h' with
  | rel _ _ h =>
    obtain ⟨e⟩ := h
    obtain ⟨H⟩ := edge_homotopy_const e
    exact Relation.EqvGen.rel _ _ ⟨H⟩
  | refl => exact homotopic_refl _
  | symm _ _ _ ih => exact homotopic_symm ih
  | trans _ _ _ _ _ ih ih' => exact homotopic_trans ih ih'

lemma homotopy_extension {A B K : SSet.{u}} [SSet.KanComplex K]
    (i : A ⟶ B) [Mono i] (f : B ⟶ K) {a : A ⟶ K}
    (H : SSet.Homotopy (i ≫ f) a) :
    ∃ g : B ⟶ K, ∃ G : SSet.Homotopy f g, i ≫ g = a ∧ i ▷ Δ[1] ≫ G.h = H.h := by
  have hp : simplicialFibrations (terminal.from K) := by
    change SSet.modelCategoryQuillen.J.rlp (terminal.from K)
    rw [← SSet.modelCategoryQuillen.fibrations_eq,← HomotopicalAlgebra.fibration_iff]
    infer_instance
  obtain ⟨Q,hQ,h₀,_⟩ := cylinder_lift i (terminal.from K) hp 1 f H.h (terminal.from _)
    (by rw [endpoint_zero,H.h₀]) (by subsingleton) (by subsingleton)
  refine ⟨SSet.ι₁ ≫ Q,CoherentGluing.toHomotopy Q ?_ rfl,?_,hQ⟩
  · simpa only [endpoint_zero] using h₀
  · rw [← SSet.ι₁_comp_assoc,hQ,H.h₁]

lemma point_mono {K : SSet.{u}} (x : K _⦋0⦌) : Mono (SSet.const (X := Δ[0]) x) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  intro a b _
  apply SSet.stdSimplex.ext
  intro j
  apply Fin.ext
  omega

lemma nerve_constant_vertex {Q B : Type u} [PartialOrder Q] [PartialOrder B]
    (v : (nerve Q) _⦋0⦌) :
    nerveMap (constantOrder B (v.obj 0)).toFunctor = SSet.const v := by
  ext n a j
  rfl

lemma pointed_kan_poset_replacement (K : SSet.{u}) [SSet.KanComplex K] (x : K _⦋0⦌) :
    ∃ Q : PartOrd.{u}, ∃ q : Q, ∃ r : nerve Q ⟶ K,
      Local r ∧ simplicialWeakEquivalences r ∧
      (∀ (B : Type u) [PartialOrder B], nerveMap (constantOrder B q).toFunctor ≫ r = SSet.const x) := by
  obtain ⟨Q,r,hr,hw⟩ := Posetal.kan_poset_replacement K
  obtain ⟨v,hv⟩ := (KanQuillen.map_components_bijective_of_weak r hw).2 (SSet.π₀.mk x)
  obtain ⟨v,rfl⟩ := SSet.π₀.mk_surjective v
  have h : SSet.π₀.mk (r.app _ v) = SSet.π₀.mk x := hv
  let i := SSet.const (X := Δ[0]) v
  let : Mono i := point_mono v
  obtain ⟨H⟩ := homotopy_of_homotopic (component_homotopic_const h)
  have H' : SSet.Homotopy (i ≫ r) (SSet.const x) := by
    simpa only [i,SSet.const_comp] using H
  obtain ⟨s,G,hs,_⟩ := homotopy_extension i r H'
  have hrs : Homotopic r s := Relation.EqvGen.rel _ _ ⟨G⟩
  have hlocal : Local s := local_homotopic hrs hr
  have hsx : s.app _ v = x := by
    have hh := congrArg SSet.yonedaEquiv hs
    simpa only [i,SSet.const_comp,SSet.yonedaEquiv_const] using hh
  refine ⟨Q,v.obj 0,s,hlocal,local_weak s hlocal,?_⟩
  intro B hB
  rw [nerve_constant_vertex,SSet.const_comp,hsx]

lemma pointed_kan_ex_replacement (K : SSet.{u}) [SSet.KanComplex K] (x : K _⦋0⦌) :
    ∃ Q : PartOrd.{u}, ∃ q : Q, ∃ r : nerve Q ⟶ K, ∃ e : Subdivision.exInfinity (nerve Q) ⟶ K,
      Subdivision.exInfinityComparison (nerve Q) ≫ e = r ∧
      simplicialWeakEquivalences r ∧ IsHomotopyEquivalence e ∧
      (∀ (B : Type u) [PartialOrder B], nerveMap (constantOrder B q).toFunctor ≫ r = SSet.const x) := by
  obtain ⟨Q,q,r,hr,hw,hx⟩ := pointed_kan_poset_replacement K x
  obtain ⟨e,he⟩ := extend_anodyne (Subdivision.exInfinityComparison (nerve Q))
    (Subdivision.exInfinityComparison_anodyne _) r
  have : SSet.KanComplex (Subdivision.exInfinity (nerve Q)) := Subdivision.exInfinity_kan _
  exact ⟨Q,q,r,e,he,hw,kan_local_heq e (local_of_precomp _ _
    (local_anodyne _ (Subdivision.exInfinityComparison_anodyne _)) (he.symm ▸ hr)),hx⟩
end Thomason.GeometricRecognition

end

end OAI
