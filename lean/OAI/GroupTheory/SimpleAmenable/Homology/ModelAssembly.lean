import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.DiagonalResolution

namespace OAI

section

open CategoryTheory Limits Opposite
namespace ModelAssembly

open DiagonalResolution
variable (X : Dᵒᵖ ⥤ Type)

abbrev projection : X.Elementsᵒᵖ ⥤ D := (Functor.Elements.π X).leftOp

noncomputable def assembly : (D ⥤ A) ⥤ A :=
  (Functor.whiskeringLeft _ _ _).obj (projection X) ⋙ colim

instance assembly_additive : (assembly X).Additive := by
  unfold assembly
  infer_instance

instance assembly_preservesColimits : PreservesColimitsOfSize.{0,0} (assembly X) := by
  unfold assembly
  infer_instance
noncomputable def freeCocone (d : D) : Cocone (projection X ⋙ free d) where
  pt := ∐ (fun _ : X.obj (op d) => Z)
  ι :=
    { app e := Sigma.desc (fun f : d ⟶ e.unop.1.unop =>
        Sigma.ι (fun _ : X.obj (op d) => Z) (X.map f.op e.unop.2))
      naturality e e' f := by
        apply Sigma.hom_ext
        intro g
        simp only [Functor.const_obj_obj,Functor.const_obj_map,Category.comp_id,
          Functor.comp_map,projection,Functor.leftOp_map,Functor.Elements.π_map,
          free,evaluationLeftAdjoint]
        simp only [← Category.assoc,Sigma.ι_comp_desc]
        congr 1
        change X.map (g ≫ f.unop.hom.unop).op e'.unop.2 = X.map g.op e.unop.2
        rw [op_comp, X.map_comp]
        change X.map g.op (X.map f.unop.hom e'.unop.2) = _
        rw [f.unop.map_val] }

noncomputable def forward (d : D) : (assembly X).obj (free d) ⟶ ∐ (fun _ : X.obj (op d) => Z) :=
  colimit.desc _ (freeCocone X d)

noncomputable def backward (d : D) : (∐ (fun _ : X.obj (op d) => Z)) ⟶ (assembly X).obj (free d) :=
  Sigma.desc (fun x => Sigma.ι (fun _ : d ⟶ d => Z) (𝟙 d) ≫
    colimit.ι (projection X ⋙ free d) (op (X.elementsMk (op d) x)))

@[reassoc (attr := simp)] lemma ι_to (d : D) (e : X.Elementsᵒᵖ) :
    colimit.ι (projection X ⋙ free d) e ≫ forward X d = (freeCocone X d).ι.app e := by
  apply colimit.ι_desc
lemma from_to (d : D) : backward X d ≫ forward X d = 𝟙 _ := by
  apply Sigma.hom_ext
  intro x
  dsimp only [backward]
  erw [Sigma.ι_comp_desc_assoc, Category.assoc, ι_to]
  change Sigma.ι (fun _ : d ⟶ d => Z) (𝟙 d) ≫ Sigma.desc
    (fun f : d ⟶ d => Sigma.ι (fun _ : X.obj (op d) => Z) (X.map f.op x)) = _
  simp
lemma to_from (d : D) : forward X d ≫ backward X d = 𝟙 _ := by
  apply colimit.hom_ext
  intro e
  apply Sigma.hom_ext
  intro f
  change Sigma.ι (fun _ : d ⟶ e.unop.1.unop => Z) f ≫
    colimit.ι (projection X ⋙ free d) e ≫ forward X d ≫ backward X d =
    Sigma.ι (fun _ : d ⟶ e.unop.1.unop => Z) f ≫ colimit.ι (projection X ⋙ free d) e ≫ 𝟙 _
  erw [← Category.assoc (colimit.ι (projection X ⋙ free d) e) (forward X d)
    (backward X d), ι_to]
  dsimp only [freeCocone]
  dsimp only [backward]
  erw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.comp_id]
  let k := (show e.unop ⟶ X.elementsMk (op d) (X.map f.op e.unop.2) from
    { hom := f.op, map_val := rfl }).op
  have h := congrArg (fun g => Sigma.ι (fun _ : d ⟶ d => Z) (𝟙 d) ≫ g)
    (colimit.w (projection X ⋙ free d) k)
  change Sigma.ι (fun _ : d ⟶ d => Z) (𝟙 d) ≫
    (Sigma.desc (fun g : d ⟶ d => Sigma.ι (fun _ : d ⟶ e.unop.1.unop => Z) (g ≫ f))) ≫
      colimit.ι (projection X ⋙ free d) e =
    Sigma.ι (fun _ : d ⟶ d => Z) (𝟙 d) ≫
      colimit.ι (projection X ⋙ free d) (op (X.elementsMk (op d) (X.map f.op e.unop.2))) at h
  erw [Sigma.ι_comp_desc_assoc, Category.id_comp] at h
  change _ = _ at h
  exact h.symm

noncomputable def freeIso (d : D) : (assembly X).obj (free d) ≅ ∐ (fun _ : X.obj (op d) => Z) where
  hom := forward X d
  inv := backward X d
  hom_inv_id := to_from X d
  inv_hom_id := from_to X d

end ModelAssembly

end

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalHomotopy

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]
abbrev c := ComplexShape.down ℕ
variable {K L : HomologicalComplex₂ C c c} {f g : K ⟶ L}

@[simp] lemma sign₁ (p q : ℕ) : ComplexShape.ε₁ c c c (p,q)=1 := rfl
@[simp] lemma sign₂ (p q : ℕ) : ComplexShape.ε₂ c c c (p,q)=(-1 : ℤˣ)^p := rfl
@[simp] lemma π_add (p q : ℕ) : ComplexShape.π c c c (p,q)=p+q := rfl

noncomputable def step (h : Homotopy f g) (n : ℕ) : (K.total c).X n ⟶ (L.total c).X (n+1) :=
  K.totalDesc (fun p q hpq => (h.hom p (p+1)).f q ≫ L.ιTotal c (p+1) q (n+1) (by
    dsimp at hpq ⊢; omega))

@[reassoc (attr := simp)] lemma ι_step (h : Homotopy f g) (p q n : ℕ) (hpq : p+q=n) :
    K.ιTotal c p q n hpq ≫ step h n =
      (h.hom p (p+1)).f q ≫ L.ιTotal c (p+1) q (n+1) (by dsimp; omega) := by
  apply ι_totalDesc

lemma ι_d₁_zero (q n : ℕ) : K.ιTotal c 0 q q (by simp) ≫ K.D₁ c q n=0 := by
  rw [ι_D₁]
  apply d₁_eq_zero
  simp [c]

lemma ι_d₂_zero (p n : ℕ) : K.ιTotal c p 0 p (by simp) ≫ K.D₂ c p n=0 := by
  rw [ι_D₂]
  apply d₂_eq_zero
  simp [c]

@[reassoc] lemma ι_d₁_succ (p q n : ℕ) (hpq : p+q=n) :
    K.ιTotal c (p+1) q (n+1) (by dsimp; omega) ≫ K.D₁ c (n+1) n =
      (K.d (p+1) p).f q ≫ K.ιTotal c p q n hpq := by
  rw [ι_D₁, d₁_eq K c (by rfl : c.Rel (p+1) p) q n hpq,sign₁,one_smul]

@[reassoc] lemma ι_d₂_succ (p q n : ℕ) (hpq : p+q=n) :
    K.ιTotal c p (q+1) (n+1) (by dsimp; omega) ≫ K.D₂ c (n+1) n =
      ((-1 : ℤˣ)^p) • ((K.X p).d (q+1) q ≫ K.ιTotal c p q n hpq) := by
  rw [ι_D₂,d₂_eq K c p (by rfl : c.Rel (q+1) q) n hpq,sign₂]

@[reassoc] lemma ι_d (p q n m : ℕ) (hpq : p+q=n) :
    K.ιTotal c p q n hpq ≫ (K.total c).d n m = K.d₁ c p q m+K.d₂ c p q m := by
  change _ ≫ (_+_)=_
  rw [Preadditive.comp_add,ι_D₁,ι_D₂]

omit [HasCoproducts C] in
lemma comm_zero (h : Homotopy f g) (q : ℕ) :
    (f.f 0).f q = (h.hom 0 1).f q ≫ (L.d 1 0).f q +(g.f 0).f q := by
  have e := congrArg (fun k : K.X 0 ⟶ L.X 0 => k.f q) (h.comm 0)
  simpa only [Homotopy.dNext_zero_chainComplex,Homotopy.prevD_chainComplex,
    zero_add, HomologicalComplex.comp_f,HomologicalComplex.add_f_apply] using e

omit [HasCoproducts C] in
lemma comm_succ (h : Homotopy f g) (p q : ℕ) :
    (f.f (p+1)).f q = (K.d (p+1) p).f q ≫ (h.hom p (p+1)).f q +
      (h.hom (p+1) (p+2)).f q ≫ (L.d (p+2) (p+1)).f q +(g.f (p+1)).f q := by
  have e := congrArg (fun k : K.X (p+1) ⟶ L.X (p+1) => k.f q) (h.comm (p+1))
  simpa only [Homotopy.dNext_succ_chainComplex,Homotopy.prevD_chainComplex,
    HomologicalComplex.comp_f,HomologicalComplex.add_f_apply] using e

noncomputable def hom (h : Homotopy f g) :
    ∀ n m, (K.total c).X n ⟶ (L.total c).X m :=
  fun n => Pi.single (n+1) (step h n)

@[simp] lemma hom_diag (h : Homotopy f g) (n : ℕ) : hom h n (n+1)=step h n := by
  simp [hom]

@[reassoc] lemma ι_d_rightZero (p : ℕ) :
    K.ιTotal c (p+1) 0 (p+1) (by simp) ≫ (K.total c).d (p+1) p =
      (K.d (p+1) p).f 0 ≫ K.ιTotal c p 0 p (by simp) := by
  rw [ι_d,d₁_eq K c (by rfl : c.Rel (p+1) p) 0 p (by simp),sign₁,one_smul,
    d₂_eq_zero K c (p+1) 0 p (by simp [c]),add_zero]

@[reassoc] lemma ι_d_leftZero (q : ℕ) :
    K.ιTotal c 0 (q+1) (q+1) (by simp) ≫ (K.total c).d (q+1) q =
      (K.X 0).d (q+1) q ≫ K.ιTotal c 0 q q (by simp) := by
  rw [ι_d,d₁_eq_zero K c 0 (q+1) q (by simp [c]),zero_add,
    d₂_eq K c 0 (by rfl : c.Rel (q+1) q) q (by simp),sign₂,pow_zero,one_smul]

@[reassoc] lemma ι_d_both (p q n : ℕ) (hpq : p+q+1=n) :
    K.ιTotal c (p+1) (q+1) (n+1) (by dsimp; omega) ≫ (K.total c).d (n+1) n =
      (K.d (p+1) p).f (q+1) ≫ K.ιTotal c p (q+1) n (by dsimp; omega) +
        ((-1 : ℤˣ)^(p+1)) • ((K.X (p+1)).d (q+1) q ≫ K.ιTotal c (p+1) q n (by dsimp; omega)) := by
  rw [ι_d,d₁_eq K c (by rfl : c.Rel (p+1) p) (q+1) n (by dsimp; omega),
    d₂_eq K c (p+1) (by rfl : c.Rel (q+1) q) n (by dsimp; omega),sign₁,one_smul,sign₂]

lemma total_comm_zero (h : Homotopy f g) :
    (total.map f c).f 0 = dNext 0 (hom h) + prevD 0 (hom h) +
      (total.map g c).f 0 := by
  rw [Homotopy.dNext_zero_chainComplex,Homotopy.prevD_chainComplex,hom_diag,zero_add]
  apply total.hom_ext
  intro p q hpq
  obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hpq
  simp only [Preadditive.comp_add,←Category.assoc,ι_step,ιTotal_map]
  rw [Category.assoc,ι_d_rightZero,←Category.assoc,comm_zero h 0,Preadditive.add_comp]

lemma neg_pow_smul_succ {A : Type*} [AddCommGroup A] (p : ℕ) (a : A) :
    ((-1 : ℤˣ)^(p+1)) • a = - (((-1 : ℤˣ)^p) • a) := by
  rw [pow_succ',mul_smul,Units.neg_smul,one_smul]

lemma total_comm_succ (h : Homotopy f g) (n : ℕ) :
    (total.map f c).f (n+1) = (K.total c).d (n+1) n ≫ step h n +
      step h (n+1) ≫ (L.total c).d (n+2) (n+1) + (total.map g c).f (n+1) := by
  apply total.hom_ext
  intro p q hpq
  change p+q=n+1 at hpq
  cases p with
  | zero =>
    cases q with
    | zero => omega
    | succ q =>
      have : q=n := by omega
      subst q
      simp only [Preadditive.comp_add,←Category.assoc,ι_d_leftZero,ι_step,ιTotal_map]
      simp only [Category.assoc,ι_step,ι_d_both 0 n (n+1) (by omega)]
      simp only [Preadditive.comp_add,Linear.comp_units_smul]
      rw [←Category.assoc, ←Category.assoc, ←(h.hom 0 1).comm]
      rw [comm_zero h (n+1),Preadditive.add_comp]
      simp only [Nat.zero_add, pow_one, Units.neg_smul, one_smul, Category.assoc]
      abel
  | succ p =>
    cases q with
    | zero =>
      have : p=n := by omega
      subst p
      simp only [Preadditive.comp_add,←Category.assoc,ι_d_rightZero,ι_step,ιTotal_map]
      simp only [Category.assoc,ι_step,ι_d_rightZero]
      rw [comm_succ h n 0]
      simp only [Preadditive.add_comp,Category.assoc]
    | succ q =>
      have hn : p+q+1=n := by omega
      simp only [Preadditive.comp_add,←Category.assoc,
        ι_d_both p q n hn,Preadditive.add_comp,Linear.units_smul_comp,
        ι_step,ιTotal_map]
      simp only [Category.assoc,ι_step,ι_d_both (p+1) q (n+1) (by omega)]
      simp only [Preadditive.comp_add,Linear.comp_units_smul]
      rw [←Category.assoc, ←Category.assoc, ←(h.hom (p+1) (p+2)).comm]
      rw [comm_succ h p (q+1)]
      simp only [Preadditive.add_comp,Category.assoc,neg_pow_smul_succ,neg_neg]
      abel

noncomputable def total (h : Homotopy f g) : Homotopy (total.map f c) (total.map g c) where
  hom := hom h
  zero i j hij := by
    have hne : i+1 ≠ j := by simpa [c,eq_comm] using hij
    exact Pi.single_eq_of_ne hne.symm _
  comm i := by
    cases i with
    | zero => exact total_comm_zero h
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex,Homotopy.prevD_chainComplex,hom_diag,hom_diag]
      exact total_comm_succ h n

end TotalHomotopy

end OAI
