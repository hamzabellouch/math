import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.DoubleCoordinates
import OAI.GroupTheory.SimpleAmenable.Homology.RegularLiftFaces
import OAI.GroupTheory.SimpleAmenable.Simplicial.RegularBlockFaces

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularLabels
open FreeChains RegularCoordinates MonoidNerveCoordinates

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
@[reassoc] lemma totalInj_d_parts {n:ℕ} (s:DoubleCoordinates.Index P (n+1)) :
    totalInj F s ≫ ((RegularCoefficient.double F).total c).d (n+1) n =
      inj F s.2 ≫ (RegularCoefficient.double F).d₁ c s.1.val.1 s.1.val.2 n +
      inj F s.2 ≫ (RegularCoefficient.double F).d₂ c s.1.val.1 s.1.val.2 n := by
  dsimp only [totalInj]
  rw [Category.assoc,HomologicalComplex₂.total_d,Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁,HomologicalComplex₂.ι_D₂,Preadditive.comp_add]
@[reassoc] lemma totalInj_d_hor (h:ℕ) (y:Fin 0→P) (p:P) (x:Fin (h+1)→P) :
    totalInj F ⟨⟨(h+1,0),rfl⟩,y,p,x⟩ ≫ ((RegularCoefficient.double F).total c).d (h+1) h =
      ∑k:Fin (h+2),(-1:ℤ)^k.val • (F.map (arrow (faceWeight k x) p) ≫
        totalInj F ⟨⟨(h,0),rfl⟩,y,faceWeight k x*p,faceLabels k x⟩) := by
  rw [totalInj_d_parts]
  rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp)]
  rw [HomologicalComplex₂.d₁_eq _ _ (show c.Rel (h+1) h from rfl) 0 h rfl]
  simp only [comp_zero,add_zero,show c.ε₁ c c (h+1,0) = 1 from rfl,one_smul]
  change inj F (y,p,x) ≫ ((RegularCoefficient.double F).d (h+1) h).f 0 ≫
    (RegularCoefficient.double F).ιTotal c h 0 h rfl = _
  rw [inj_dH_assoc]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,Category.assoc,totalInj]
  rfl
@[reassoc] lemma totalInj_d_ver (v:ℕ) (y:Fin (v+1)→P) (p:P) (x:Fin 0→P) :
    totalInj F ⟨⟨(0,v+1),by omega⟩,y,p,x⟩ ≫ ((RegularCoefficient.double F).total c).d (v+1) v =
      ∑k:Fin (v+2),(-1:ℤ)^k.val • (F.map (arrow (faceWeight k y) p) ≫
        totalInj F ⟨⟨(0,v),by omega⟩,faceLabels k y,faceWeight k y*p,x⟩) := by
  rw [totalInj_d_parts]
  rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp)]
  rw [HomologicalComplex₂.d₂_eq _ _ 0 (show c.Rel (v+1) v from rfl) v (by change 0+v=v; omega)]
  simp only [comp_zero,zero_add,show c.ε₂ c c (0,v+1) = 1 from rfl,one_smul]
  change inj F (y,p,x) ≫ ((RegularCoefficient.double F).X 0).d (v+1) v ≫
    (RegularCoefficient.double F).ιTotal c 0 v v (by change 0+v=v; omega) = _
  rw [inj_dV_assoc]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,Category.assoc,totalInj]
@[reassoc] lemma totalInj_d_both (h v:ℕ) (y:Fin (v+1)→P) (p:P) (x:Fin (h+1)→P) :
    totalInj F ⟨⟨(h+1,v+1),by omega⟩,y,p,x⟩ ≫
      ((RegularCoefficient.double F).total c).d (h+v+2) (h+v+1) =
      (∑k:Fin (h+2),(-1:ℤ)^k.val • (F.map (arrow (faceWeight k x) p) ≫
        totalInj F ⟨⟨(h,v+1),by omega⟩,y,faceWeight k x*p,faceLabels k x⟩)) +
      (-1:ℤ)^(h+1) • (∑k:Fin (v+2),(-1:ℤ)^k.val • (F.map (arrow (faceWeight k y) p) ≫
        totalInj F ⟨⟨(h+1,v),by omega⟩,faceLabels k y,faceWeight k y*p,x⟩)) := by
  rw [totalInj_d_parts]
  rw [HomologicalComplex₂.d₁_eq _ _ (show c.Rel (h+1) h from rfl) (v+1) (h+v+1) (by change h+(v+1)=h+v+1; omega)]
  rw [HomologicalComplex₂.d₂_eq _ _ (h+1) (show c.Rel (v+1) v from rfl) (h+v+1) (by change (h+1)+v=h+v+1; omega)]
  simp only [show c.ε₁ c c (h+1,v+1) = 1 from rfl,one_smul]
  change inj F (y,p,x) ≫ ((RegularCoefficient.double F).d (h+1) h).f (v+1) ≫
      (RegularCoefficient.double F).ιTotal c h (v+1) (h+v+1) (by change h+(v+1)=h+v+1; omega) +
    inj F (y,p,x) ≫ ((ComplexShape.ε₂ c c c (h+1,v+1)) •
      (((RegularCoefficient.double F).X (h+1)).d (v+1) v ≫
        (RegularCoefficient.double F).ιTotal c (h+1) v (h+v+1) (by change (h+1)+v=h+v+1; omega))) = _
  rw [Units.smul_def]
  change _ + inj F (y,p,x) ≫ ((-1:ℤ)^(h+1) • _) = _
  rw [Preadditive.comp_zsmul,inj_dH_assoc,inj_dV_assoc]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,Category.assoc,totalInj]
end RegularLabels

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularLabels
open FreeChains RegularCoordinates MonoidNerveCoordinates

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
lemma totalInj_transport {h v n:ℕ} (hn:h+v=n) (y:Fin v→P) (x:Fin h→P) {p q:P} (e:p=q) :
    eqToHom (congrArg (fiber F) e) ≫ totalInj F ⟨⟨(h,v),hn⟩,y,q,x⟩ =
      totalInj F ⟨⟨(h,v),hn⟩,y,p,x⟩ := by
  subst q
  simp
@[reassoc] lemma one_totalInj {h v n:ℕ} (hn:h+v=n) (y:Fin v→P) (p:P) (x:Fin h→P) :
    F.map (arrow 1 p) ≫ totalInj F ⟨⟨(h,v),hn⟩,y,1*p,x⟩ =
      totalInj F ⟨⟨(h,v),hn⟩,y,p,x⟩ := by
  rw [arrow_one,eqToHom_map]
  exact totalInj_transport F hn y x (one_mul p).symm
end RegularLabels
namespace RegularFiniteFaces
open RegularLabels RegularCoordinates MonoidNerveCoordinates
variable {P:Type} [CommMonoid P]
@[simp] lemma labels1_0 (a:P) : faceLabels (0:Fin 2) ![a]=![] := by
  funext j
  fin_cases j
@[simp] lemma weight1_0 (a:P) : faceWeight (0:Fin 2) ![a]=1 := by
  simp [faceWeight]
@[simp] lemma labels1_1 (a:P) : faceLabels (1:Fin 2) ![a]=![] := by
  funext j
  fin_cases j
@[simp] lemma weight1_1 (a:P) : faceWeight (1:Fin 2) ![a]=a := by
  simp [faceWeight]
@[simp] lemma labels2_0 (a b:P) : faceLabels (0:Fin 3) ![a,b]=![b] := by
  funext j
  fin_cases j
  rfl
@[simp] lemma weight2_0 (a b:P) : faceWeight (0:Fin 3) ![a,b]=1 := by
  simp [faceWeight]
@[simp] lemma labels2_1 (a b:P) : faceLabels (1:Fin 3) ![a,b]=![(a*b)] := by
  funext j
  fin_cases j
  rfl
@[simp] lemma weight2_1 (a b:P) : faceWeight (1:Fin 3) ![a,b]=1 := by
  simp [faceWeight]
@[simp] lemma labels2_2 (a b:P) : faceLabels (2:Fin 3) ![a,b]=![a] := by
  funext j
  fin_cases j
  rfl
@[simp] lemma weight2_2 (a b:P) : faceWeight (2:Fin 3) ![a,b]=b := by
  simp [faceWeight]
@[simp] lemma labels3_0 (a b d:P) : faceLabels (0:Fin 4) ![a,b,d]=![b,d] := by
  funext j
  fin_cases j <;> rfl
@[simp] lemma weight3_0 (a b d:P) : faceWeight (0:Fin 4) ![a,b,d]=1 := by
  simp [faceWeight]
@[simp] lemma labels3_1 (a b d:P) : faceLabels (1:Fin 4) ![a,b,d]=![(a*b),d] := by
  funext j
  fin_cases j <;> rfl
@[simp] lemma weight3_1 (a b d:P) : faceWeight (1:Fin 4) ![a,b,d]=1 := by
  simp [faceWeight]
@[simp] lemma labels3_2 (a b d:P) : faceLabels (2:Fin 4) ![a,b,d]=![a,(b*d)] := by
  funext j
  fin_cases j <;> rfl
@[simp] lemma weight3_2 (a b d:P) : faceWeight (2:Fin 4) ![a,b,d]=1 := by
  simp [faceWeight]
@[simp] lemma labels3_3 (a b d:P) : faceLabels (3:Fin 4) ![a,b,d]=![a,b] := by
  funext j
  fin_cases j <;> rfl
@[simp] lemma weight3_3 (a b d:P) : faceWeight (3:Fin 4) ![a,b,d]=d := by
  simp [faceWeight]
end RegularFiniteFaces

end

section

namespace FilteredEdge
open FilteredFiniteness

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {D A B C : Type u} [AddCommGroup D] [Module R D]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
structure Data where
  s : D →ₗ[R] A
  d : A →ₗ[R] B
  e : B →ₗ[R] C
  ds : d.comp s = 0
  ed : e.comp d = 0
  FD : ℤ → Submodule R D
  FA : ℤ → Submodule R A
  FB : ℤ → Submodule R B
  FC : ℤ → Submodule R C
  monoA : Monotone FA
  monoB : Monotone FB
namespace Data
variable (K : Data (R:=R) (D:=D) (A:=A) (B:=B) (C:=C))
def current : FilteredFiniteness.Data (R:=R) (A:=A) (B:=B) (C:=C) :=
  ⟨K.d,K.e,K.ed,K.FA,K.FB,K.FC,K.monoB⟩
def previous : FilteredFiniteness.Data (R:=R) (A:=D) (B:=A) (C:=B) :=
  ⟨K.s,K.d,K.ds,K.FD,K.FA,K.FB,K.monoA⟩
variable (p : ℤ)
def inputs (k : ℤ) : Submodule R A := K.FA k ⊓ (K.FB p).comap K.d
def boundaryCycle (k : ℤ) : K.inputs p k →ₗ[R] K.current.Z₂ p :=
  (K.d.comp (K.inputs p k).subtype).codRestrict _ (fun x => by
    refine ⟨x.property.2,?_⟩
    change K.e (K.d x.val) ∈ K.FC (p-2)
    have he : K.e (K.d x.val)=0 := congrArg (fun f : A →ₗ[R] C => f x.val) K.ed
    rw [he]; exact Submodule.zero_mem _)
def boundaryMap (k : ℤ) : K.inputs p k →ₗ[R] K.current.E₂ p :=
  ((K.current.B₂ p).comap (K.current.Z₂ p).subtype).mkQ.comp (K.boundaryCycle p k)
def tower (k : ℤ) : Submodule R (K.current.E₂ p) := LinearMap.range (K.boundaryMap p k)
omit [IsNoetherianRing R] in
lemma tower_mono : Monotone (K.tower p) := by
  intro k l hkl y hy
  obtain ⟨x,rfl⟩ := hy
  exact ⟨⟨x.val, K.monoA hkl x.property.1,x.property.2⟩,rfl⟩
omit [IsNoetherianRing R] in
lemma tower_start : K.tower p (p+1)=⊥ := by
  apply le_antisymm _ bot_le
  rintro y ⟨x,rfl⟩
  apply (Submodule.mem_bot R).mpr
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change K.d x.val∈K.current.B₂ p
  exact (show (K.FA (p+1)).map K.d ⊓ K.FB p ≤ K.current.B₂ p from le_sup_right)
    ⟨⟨x.val,x.property.1,rfl⟩,x.property.2⟩
def inputLeading (k : ℤ) (hk : p≤k-2) : K.inputs p k →ₗ[R] K.previous.E₂ k :=
  ((K.previous.B₂ k).comap (K.previous.Z₂ k).subtype).mkQ.comp
    (((K.inputs p k).subtype).codRestrict _ (fun x =>
      ⟨x.property.1,K.monoB hk x.property.2⟩))
omit [IsNoetherianRing R] in
lemma lower_of_leading_zero (k : ℤ) (hk : p≤k-2) (x : K.inputs p k)
    (hx : K.inputLeading p k hk x=0) :
    K.boundaryMap p k x∈K.tower p (k-1) := by
  have hx' : x.val∈K.previous.B₂ k := (Submodule.Quotient.mk_eq_zero ((K.previous.B₂ k).comap (K.previous.Z₂ k).subtype)).mp hx
  obtain ⟨y,hy,z,hz,hyz⟩ := Submodule.mem_sup.mp hx'
  obtain ⟨w,hw,hwz⟩ := hz.1
  have hd : K.d z = 0 := by
    rw [←hwz]
    exact congrArg (fun f : D →ₗ[R] B => f w) K.ds
  have hxy : K.d y=K.d x.val := by
    rw [←hyz,map_add,hd,add_zero]
  refine ⟨⟨y,hy.1,?_⟩,?_⟩
  · change K.d y∈K.FB p
    rw [hxy]; exact x.property.2
  · change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    exact hxy
lemma finite_tower_step (k : ℤ) (hk : p≤k-2)
    [Module.Finite R (K.tower p (k-1))]
    [Module.Finite R (K.previous.E₂ k)] : Module.Finite R (K.tower p k) := by
  let S : Submodule R (K.tower p k) := (K.tower p (k-1)).submoduleOf (K.tower p k)
  have : Module.Finite R S := Module.Finite.equiv
    (Submodule.submoduleOfEquivOfLe (K.tower_mono p (by omega : k-1≤k))).symm
  let f : K.inputs p k →ₗ[R] K.tower p k ⧸ S :=
    S.mkQ.comp (K.boundaryMap p k).rangeRestrict
  have hf : Function.Surjective f := (Submodule.mkQ_surjective S).comp
    (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)
  have hker : LinearMap.ker (K.inputLeading p k hk) ≤ LinearMap.ker f := by
    intro x hx
    change f x=0
    apply (Submodule.Quotient.mk_eq_zero S).mpr
    exact K.lower_of_leading_zero p k hk x hx
  have : Module.Finite R (K.tower p k ⧸ S) :=
    finite_of_ker_le f (K.inputLeading p k hk) hf hker
  exact Module.Finite.of_submodule_quotient S
end Data
end FilteredEdge

end

end OAI
