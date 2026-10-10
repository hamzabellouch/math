import Mathlib.CategoryTheory.Idempotents.Biproducts
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.Abel

namespace OAI

namespace LittleFinitistic.OddDouble
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Preadditive CategoryTheory.Pretriangulated
open CategoryTheory.Idempotents

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]

noncomputable def sourceProjector (T : Triangle C) (u : T.obj₂ ⟶ T.obj₁) :=
  𝟙 T.obj₁ - T.mor₁ ≫ u

noncomputable def targetProjector (T : Triangle C) (u : T.obj₂ ⟶ T.obj₁) :=
  𝟙 T.obj₂ - u ≫ T.mor₁

variable (T : Triangle C) (u : T.obj₂ ⟶ T.obj₁)
variable (hu : T.mor₁ ≫ u ≫ T.mor₁ = T.mor₁)
include hu

theorem sourceProjector_idem : sourceProjector T u ≫ sourceProjector T u = sourceProjector T u := by
  unfold sourceProjector
  simp only [comp_sub,sub_comp,id_comp,comp_id,assoc,reassoc_of% hu]
  abel

theorem targetProjector_idem : targetProjector T u ≫ targetProjector T u = targetProjector T u := by
  unfold targetProjector
  simp only [comp_sub,sub_comp,id_comp,comp_id,assoc,hu]
  abel

theorem sourceProjector_comp : sourceProjector T u ≫ T.mor₁ = 0 := by
  simp only [sourceProjector,sub_comp,id_comp,assoc,hu,sub_self]

theorem comp_targetProjector : T.mor₁ ≫ targetProjector T u = 0 := by
  simp only [targetProjector,comp_sub,comp_id,hu,sub_self]

variable [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

local instance : HasFiniteBiproducts (Karoubi C) := Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi C) := hasBinaryBiproducts_of_finite_biproducts (Karoubi C)

variable (hT : T ∈ distTriang C)
include hT

omit hu in
theorem targetProjector_comp_second : targetProjector T u ≫ T.mor₂ = T.mor₂ := by
  simp only [targetProjector,sub_comp,id_comp,assoc,comp_distTriang_mor_zero₁₂ T hT,
    comp_zero,sub_zero]

omit hu in
theorem third_comp_sourceProjector :
    T.mor₃ ≫ (sourceProjector T u)⟦(1 : ℤ)⟧' = T.mor₃ := by
  simp only [sourceProjector,Functor.map_sub,Functor.map_comp,comp_sub,
    ← assoc,comp_distTriang_mor_zero₃₁ T hT,zero_comp,sub_zero]
  rw [(shiftFunctor C (1 : ℤ)).map_id,comp_id]

/-- Splitting data for the cone of a morphism admitting a generalized inverse.
These are the five biproduct equations in the idempotent completion. -/
theorem cone_splitting :
    ∃ (s : T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃) (t : T.obj₃ ⟶ T.obj₂),
      (sourceProjector T u)⟦(1 : ℤ)⟧' ≫ s = s ∧
      s ≫ T.mor₃ = (sourceProjector T u)⟦(1 : ℤ)⟧' ∧
      t ≫ targetProjector T u = t ∧
      T.mor₂ ≫ t = targetProjector T u ∧
      s ≫ t = 0 ∧
      t ≫ T.mor₂ + T.mor₃ ≫ s = 𝟙 T.obj₃ := by
  let p := sourceProjector T u
  let q := targetProjector T u
  have hp : p ≫ p = p := sourceProjector_idem T u hu
  have hq : q ≫ q = q := targetProjector_idem T u hu
  have hpf : p ≫ T.mor₁ = 0 := sourceProjector_comp T u hu
  have hfq : T.mor₁ ≫ q = 0 := comp_targetProjector T u hu
  have hqg : q ≫ T.mor₂ = T.mor₂ := targetProjector_comp_second T u hT
  have hhp : T.mor₃ ≫ p⟦(1 : ℤ)⟧' = T.mor₃ := third_comp_sourceProjector T u hT
  have hp1 : p⟦(1 : ℤ)⟧' ≫ p⟦(1 : ℤ)⟧' = p⟦(1 : ℤ)⟧' := by
    rw [← Functor.map_comp,hp]
  obtain ⟨s₀,hs₀⟩ := T.coyoneda_exact₁ hT (p⟦(1 : ℤ)⟧') (by
    rw [← Functor.map_comp,hpf,Functor.map_zero])
  let s := p⟦(1 : ℤ)⟧' ≫ s₀
  have hps : p⟦(1 : ℤ)⟧' ≫ s = s := by
    dsimp [s]; rw [← assoc,hp1]
  have hsh : s ≫ T.mor₃ = p⟦(1 : ℤ)⟧' := by
    dsimp [s]; rw [assoc,← hs₀,hp1]
  have hdelta : (𝟙 T.obj₃ - T.mor₃ ≫ s) ≫ T.mor₃ = 0 := by
    rw [sub_comp,id_comp,assoc,hsh,hhp,sub_self]
  obtain ⟨t₀,ht₀⟩ := T.coyoneda_exact₃ hT _ hdelta
  let t := t₀ ≫ q
  have htq : t ≫ q = t := by dsimp [t]; rw [assoc,hq]
  have htg : t ≫ T.mor₂ = 𝟙 T.obj₃ - T.mor₃ ≫ s := by
    dsimp [t]; rw [assoc,hqg,← ht₀]
  have hgt : T.mor₂ ≫ t = q := by
    have hz : (T.mor₂ ≫ t - q) ≫ T.mor₂ = 0 := by
      rw [sub_comp,assoc,htg,comp_sub,comp_id,← assoc,
        comp_distTriang_mor_zero₂₃ T hT,zero_comp,hqg,sub_zero,sub_self]
    obtain ⟨v,hv⟩ := T.coyoneda_exact₂ hT _ hz
    have he := congrArg (fun z => z ≫ q) hv
    simp only [sub_comp,assoc,htq,hq,hfq,comp_zero] at he
    exact sub_eq_zero.mp he
  have hst : s ≫ t = 0 := by
    have hz : (s ≫ t) ≫ T.mor₂ = 0 := by
      rw [assoc,htg,comp_sub,comp_id,← assoc,hsh,hps,sub_self]
    obtain ⟨v,hv⟩ := T.coyoneda_exact₂ hT _ hz
    have he := congrArg (fun z => z ≫ q) hv
    simpa only [assoc,htq,hfq,comp_zero] using he
  exact ⟨s,t,hps,hsh,htq,hgt,hst,by rw [htg,sub_add_cancel]⟩

noncomputable def formalKernel : Karoubi C where
  X := T.obj₁⟦(1 : ℤ)⟧
  p := (sourceProjector T u)⟦(1 : ℤ)⟧'
  idem := by rw [← Functor.map_comp,sourceProjector_idem T u hu]

noncomputable def formalCokernel : Karoubi C where
  X := T.obj₂
  p := targetProjector T u
  idem := targetProjector_idem T u hu

/-- The cone of a regular morphism is the direct sum of its formal cokernel
and the shifted formal kernel in the idempotent completion. -/
theorem regular_cone_iso :
    Nonempty ((toKaroubi C).obj T.obj₃ ≅ formalCokernel T u hu ⊞ formalKernel T u hu) := by
  obtain ⟨s,t,hps,hsh,htq,hgt,hst,htotal⟩ := cone_splitting T u hu hT
  let Q := formalCokernel T u hu
  let P := formalKernel T u hu
  let S := (toKaroubi C).obj T.obj₃
  let gi : Q ⟶ S := ⟨T.mor₂,by
    change targetProjector T u ≫ T.mor₂ ≫ 𝟙 _ = T.mor₂
    rw [comp_id,targetProjector_comp_second T u hT]⟩
  let tr : S ⟶ Q := ⟨t,by
    change 𝟙 _ ≫ t ≫ targetProjector T u = t
    rw [id_comp,htq]⟩
  let hr : S ⟶ P := ⟨T.mor₃,by
    change 𝟙 _ ≫ T.mor₃ ≫ (sourceProjector T u)⟦(1 : ℤ)⟧' = T.mor₃
    rw [id_comp,third_comp_sourceProjector T u hT]⟩
  let si : P ⟶ S := ⟨s,by
    change (sourceProjector T u)⟦(1 : ℤ)⟧' ≫ s ≫ 𝟙 _ = s
    rw [comp_id,hps]⟩
  let bc : BinaryBicone Q P :=
    { pt := S
      fst := tr
      snd := hr
      inl := gi
      inr := si
      inl_fst := by apply Karoubi.hom_ext; exact hgt
      inl_snd := by apply Karoubi.hom_ext; exact comp_distTriang_mor_zero₂₃ T hT
      inr_fst := by apply Karoubi.hom_ext; exact hst
      inr_snd := by apply Karoubi.hom_ext; exact hsh }
  have hb : bc.IsBilimit := isBinaryBilimitOfTotal bc (by
    apply Karoubi.hom_ext
    exact htotal)
  exact ⟨biprod.uniqueUpToIso Q P hb⟩

omit hu hT

noncomputable def formalShift (P : Karoubi C) (n : ℤ) : Karoubi C where
  X := P.X⟦n⟧
  p := P.p⟦n⟧'
  idem := by rw [← Functor.map_comp,P.idem]

/-- The first odd double is the cone of the complementary idempotent. -/
theorem odd_double_one (U : Karoubi C) :
    ∃ S : C, Nonempty ((toKaroubi C).obj S ≅ U ⊞ formalShift U 1) := by
  let f := 𝟙 U.X - U.p
  have hf : f ≫ f = f := by
    dsimp [f]
    simp only [comp_sub,sub_comp,id_comp,comp_id,U.idem]
    abel
  obtain ⟨S,g,h,hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  have hu : T.mor₁ ≫ f ≫ T.mor₁ = T.mor₁ := by change f ≫ f ≫ f = f; rw [hf,hf]
  have hq : formalCokernel T f hu = U := by
    refine Karoubi.ext (P := formalCokernel T f hu) (Q := U) rfl ?_
    change (𝟙 U.X - f ≫ f) ≫ 𝟙 U.X = 𝟙 U.X ≫ U.p
    rw [hf,comp_id,id_comp]
    dsimp [f]
    abel
  have hp : formalKernel T f hu = formalShift U 1 := by
    refine Karoubi.ext (P := formalKernel T f hu) (Q := formalShift U 1) rfl ?_
    change (𝟙 U.X - f ≫ f)⟦(1 : ℤ)⟧' ≫ 𝟙 _ = 𝟙 _ ≫ U.p⟦(1 : ℤ)⟧'
    rw [comp_id,id_comp,hf]
    congr 1
    dsimp [f]
    abel
  refine ⟨S,?_⟩
  have hc := regular_cone_iso T f hu hT
  rw [hq,hp] at hc
  exact hc

noncomputable def formalShiftFunctor (n : ℤ) : Karoubi C ⥤ Karoubi C where
  obj P := formalShift P n
  map {P Q} f := ⟨f.f⟦n⟧',by
    change P.p⟦n⟧' ≫ f.f⟦n⟧' ≫ Q.p⟦n⟧' = f.f⟦n⟧'
    simp only [← Functor.map_comp,f.comm]⟩
  map_id _ := by apply Karoubi.hom_ext; rfl
  map_comp _ _ := by apply Karoubi.hom_ext; exact Functor.map_comp _ _ _

instance (n : ℤ) : (formalShiftFunctor (C := C) n).Additive where
  map_add := by intros; apply Karoubi.hom_ext; exact Functor.map_add _

noncomputable def retractProjector {A P : Karoubi C} (i : P ⟶ A) (r : A ⟶ P)
    (hi : i ≫ r = 𝟙 P) : Karoubi C where
  X := A.X
  p := r.f ≫ i.f
  idem := by
    have h : i.f ≫ r.f = P.p := congrArg Karoubi.Hom.f hi
    calc
      (r.f ≫ i.f) ≫ (r.f ≫ i.f) = (r.f ≫ (i.f ≫ r.f)) ≫ i.f := by simp only [assoc]
      _ = (r.f ≫ P.p) ≫ i.f := by rw [h]
      _ = r.f ≫ i.f := by rw [Karoubi.comp_p]

noncomputable def retractProjectorIso {A P : Karoubi C} (i : P ⟶ A) (r : A ⟶ P)
    (hi : i ≫ r = 𝟙 P) : retractProjector i r hi ≅ P := by
  have h : i.f ≫ r.f = P.p := congrArg Karoubi.Hom.f hi
  exact
    { hom := ⟨r.f,by
        change (r.f ≫ i.f) ≫ r.f ≫ P.p = r.f
        simp only [assoc,h,Karoubi.comp_p]⟩
      inv := ⟨i.f,by
        change P.p ≫ i.f ≫ (r.f ≫ i.f) = i.f
        rw [← assoc,Karoubi.p_comp,← assoc,h,Karoubi.p_comp]⟩
      hom_inv_id := by apply Karoubi.hom_ext; rfl
      inv_hom_id := by apply Karoubi.hom_ext; exact h }

/-- The second cone realizes the third odd double, with three successive shifts. -/
theorem odd_double_three_nested (U : Karoubi C) :
    ∃ Z : C, Nonempty ((toKaroubi C).obj Z ≅
      U ⊞ formalShift (formalShift (formalShift U 1) 1) 1) := by
  classical
  obtain ⟨S,⟨e⟩⟩ := odd_double_one U
  let A := (toKaroubi C).obj S
  let F := formalShiftFunctor (C := C) 1
  let P := F.obj U
  let i₀ : U ⟶ A := biprod.inl ≫ e.inv
  let r₀ : A ⟶ U := e.hom ≫ biprod.fst
  let i₁ : P ⟶ A := biprod.inr ≫ e.inv
  let r₁ : A ⟶ P := e.hom ≫ biprod.snd
  have h₀ : i₀ ≫ r₀ = 𝟙 U := by simp only [i₀,r₀,assoc,Iso.inv_hom_id_assoc,biprod.inl_fst]
  have h₁ : i₁ ≫ r₁ = 𝟙 P := by
    change (biprod.inr ≫ e.inv) ≫ e.hom ≫ biprod.snd = 𝟙 (formalShift U 1)
    rw [assoc, e.inv_hom_id_assoc]
    exact biprod.inr_snd (X := U) (Y := formalShift U 1)
  have htotal : r₀ ≫ i₀ + r₁ ≫ i₁ = 𝟙 A := by
    change (e.hom ≫ biprod.fst) ≫ (biprod.inl ≫ e.inv) +
      (e.hom ≫ biprod.snd) ≫ (biprod.inr ≫ e.inv) = 𝟙 A
    calc
      _ = e.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ e.inv := by
        simp only [comp_add,add_comp,assoc]
      _ = 𝟙 A := by rw [biprod.total,id_comp,e.hom_inv_id]
  let δ : F.obj A ⟶ A := F.map r₀ ≫ i₁
  let γ : A ⟶ F.obj A := r₁ ≫ F.map i₀
  have hδγ : δ ≫ γ = F.map (r₀ ≫ i₀) := by
    dsimp only [δ,γ]
    rw [assoc,← assoc i₁ r₁,h₁,id_comp,← F.map_comp]
  have hγδ : γ ≫ δ = r₁ ≫ i₁ := by
    dsimp only [δ,γ]
    rw [assoc,← assoc (F.map i₀) (F.map r₀),← F.map_comp,h₀,F.map_id,id_comp]
  have hreg : δ ≫ γ ≫ δ = δ := by
    rw [← assoc,hδγ]
    dsimp only [δ]
    rw [F.map_comp,assoc,← assoc (F.map i₀) (F.map r₀),← F.map_comp,h₀,F.map_id,id_comp]
  obtain ⟨Z,g,h,hT⟩ := distinguished_cocone_triangle δ.f
  let T := Triangle.mk δ.f g h
  have hu : T.mor₁ ≫ γ.f ≫ T.mor₁ = T.mor₁ := congrArg Karoubi.Hom.f hreg
  have hq : formalCokernel T γ.f hu = retractProjector i₀ r₀ h₀ := by
    refine Karoubi.ext (P := formalCokernel T γ.f hu)
      (Q := retractProjector i₀ r₀ h₀) rfl ?_
    change (𝟙 A.X - γ.f ≫ δ.f) ≫ 𝟙 A.X = 𝟙 A.X ≫ (r₀.f ≫ i₀.f)
    rw [comp_id,id_comp]
    have he : 𝟙 A - γ ≫ δ = r₀ ≫ i₀ := by rw [hγδ,← htotal]; abel
    have he' := congrArg (Karoubi.inclusionHom A A) he
    rw [map_sub] at he'
    exact he'
  have h₁' : F.map (F.map i₁) ≫ F.map (F.map r₁) = 𝟙 (F.obj (F.obj P)) := by
    rw [← F.map_comp,← F.map_comp,h₁,F.map_id,F.map_id]
  have hp : formalKernel T γ.f hu =
      retractProjector (F.map (F.map i₁)) (F.map (F.map r₁)) h₁' := by
    refine Karoubi.ext (P := formalKernel T γ.f hu)
      (Q := retractProjector (F.map (F.map i₁)) (F.map (F.map r₁)) h₁') rfl ?_
    change (𝟙 (F.obj A).X - δ.f ≫ γ.f)⟦(1 : ℤ)⟧' ≫ 𝟙 _ =
      𝟙 _ ≫ ((F.map (F.map r₁)).f ≫ (F.map (F.map i₁)).f)
    rw [comp_id,id_comp]
    have he : 𝟙 (F.obj A) - δ ≫ γ = F.map (r₁ ≫ i₁) := by
      rw [hδγ,← F.map_id,← F.map_sub]
      congr 1
      rw [← htotal]
      abel
    have hA : (F.obj A).p = 𝟙 (F.obj A).X := (shiftFunctor C (1 : ℤ)).map_id S
    have he' := congrArg (Karoubi.inclusionHom (F.obj A) (F.obj A)) he
    rw [map_sub] at he'
    change (F.obj A).p - δ.f ≫ γ.f = (F.map (r₁ ≫ i₁)).f at he'
    rw [hA] at he'
    rw [he']
    change (shiftFunctor C (1 : ℤ)).map ((shiftFunctor C (1 : ℤ)).map (r₁.f ≫ i₁.f)) = _
    simp only [Functor.map_comp]
    rfl
  obtain ⟨econe⟩ := regular_cone_iso T γ.f hu hT
  rw [hq,hp] at econe
  refine ⟨Z,⟨econe ≪≫ biprod.mapIso (retractProjectorIso i₀ r₀ h₀)
    (retractProjectorIso (F.map (F.map i₁)) (F.map (F.map r₁)) h₁')⟩⟩

noncomputable def formalIso {P Q : Karoubi C} (e : P.X ≅ Q.X)
    (he : P.p ≫ e.hom = e.hom ≫ Q.p) : P ≅ Q := by
  have hi : Q.p ≫ e.inv = e.inv ≫ P.p := by
    apply (cancel_epi e.hom).mp
    rw [← assoc,← he,assoc,e.hom_inv_id,comp_id,e.hom_inv_id_assoc]
  exact
    { hom := ⟨P.p ≫ e.hom,by
        simp only [assoc,reassoc_of% he,he,Q.idem]⟩
      inv := ⟨Q.p ≫ e.inv,by
        simp only [assoc,reassoc_of% hi,hi,P.idem]⟩
      hom_inv_id := by
        apply Karoubi.hom_ext
        change (P.p ≫ e.hom) ≫ (Q.p ≫ e.inv) = P.p
        rw [assoc,hi,← assoc e.hom e.inv,e.hom_inv_id,id_comp,P.idem]
      inv_hom_id := by
        apply Karoubi.hom_ext
        change (Q.p ≫ e.inv) ≫ (P.p ≫ e.hom) = Q.p
        rw [assoc,he,← assoc e.inv e.hom,e.inv_hom_id,id_comp,Q.idem] }

noncomputable def formalShiftAdd (P : Karoubi C) (n m : ℤ) :
    formalShift (formalShift P n) m ≅ formalShift P (n+m) :=
  formalIso ((shiftFunctorAdd C n m).app P.X).symm
    ((shiftFunctorAdd C n m).inv.naturality P.p)

/-- Both odd doubles in the manuscript are represented by actual objects. -/
theorem odd_double_three (U : Karoubi C) :
    ∃ Z : C, Nonempty ((toKaroubi C).obj Z ≅ U ⊞ formalShift U 3) := by
  obtain ⟨Z,⟨e⟩⟩ := odd_double_three_nested U
  exact ⟨Z,⟨e ≪≫ biprod.mapIso (Iso.refl U)
    (formalShiftAdd (formalShift U 1) 1 1 ≪≫ formalShiftAdd U 1 2)⟩⟩
end LittleFinitistic.OddDouble

end OAI
