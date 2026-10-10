import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ModelAssembly
import OAI.GroupTheory.SimpleAmenable.Homology.ConcreteHomology

namespace OAI

section

section
open CategoryTheory Limits HomologicalComplex
namespace ConeCoordinates

universe u
variable {R : Type u} [CommRing R]
open ConcreteHomology
variable {F G : CC (R:=R)} (φ : F ⟶ G)
lemma right_cycle (n : ℕ) (y : Cycles G n) :
    (C φ).d n (n-1) (right φ n y)=0 := by
  rw [d_right φ n (n-1),y.property,map_zero]
lemma fst_cycle (n : ℕ) (w : (C φ).X (n+1)) (y : G.X n)
    (hw : (C φ).d (n+1) n w=right φ n y) : F.d n (n-1) (fst φ n w)=0 := by
  cases n with
  | zero => rw [F.shape 0 (0-1) (by decide)]; rfl
  | succ n =>
    have h := congrArg (fst φ n) hw
    rw [d_fst φ n,fst_right φ n] at h
    exact neg_eq_zero.mp h
lemma surjective_of_cone_zero (n : ℕ) [Subsingleton (H (C φ) n)] :
    Function.Surjective ((functor n).map φ).hom := by
  intro z
  obtain ⟨y,rfl⟩ := π_surjective G n z
  let yc : Cycles (C φ) n := ⟨right φ n y,right_cycle φ n y⟩
  obtain ⟨w,hw⟩ := (π_eq_zero (C φ) n yc).mp (Subsingleton.elim _ _)
  change (C φ).X (n+1) at w
  have hw' : (C φ).d (n+1) n w=right φ n y := congrArg Subtype.val hw
  let x : Cycles F n := ⟨fst φ n w,fst_cycle φ n w y hw'⟩
  refine ⟨π F n x,?_⟩
  rw [map_π]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-snd φ (n+1) w,?_⟩
  apply Subtype.ext
  have hs := congrArg (snd φ n) hw'
  rw [d_snd φ n,snd_right φ n] at hs
  change G.d (n+1) n (-snd φ (n+1) w)=φ.f n x-y
  rw [map_neg]
  change -(G.d (n+1) n (snd φ (n+1) w))=φ.f n (fst φ n w)-y
  rw [←hs]
  abel
lemma injective_of_cone_zero (n : ℕ) [Subsingleton (H (C φ) (n+1))] :
    Function.Injective ((functor n).map φ).hom := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨x,rfl⟩ := π_surjective F n z
  have hz' : π G n (cyclesMap φ n x)=0 := by
    rw [←map_π]; exact hz
  obtain ⟨y,hy⟩ := (π_eq_zero G n _).mp hz'
  change G.X (n+1) at y
  have hy' : G.d (n+1) n y=φ.f n x := by
    have hh := congrArg Subtype.val hy
    change G.d (n+1) n y=(cyclesMap φ n x).val at hh
    rw [cyclesMap_val] at hh
    exact hh
  let w := left φ n x-right φ (n+1) y
  have hw : (C φ).d (n+1) n w=0 := by
    change (C φ).d (n+1) n (left φ n x-right φ (n+1) y)=0
    rw [map_sub,d_left_cycle φ n x,d_right φ (n+1) n,hy',sub_self]
  let wc : Cycles (C φ) (n+1) := ⟨w,hw⟩
  obtain ⟨a,ha⟩ := (π_eq_zero (C φ) (n+1) wc).mp (Subsingleton.elim _ _)
  change (C φ).X (n+2) at a
  have ha' : (C φ).d (n+2) (n+1) a=w := congrArg Subtype.val ha
  have hf := congrArg (fst φ n) ha'
  rw [d_fst φ n] at hf
  change -F.d (n+1) n (fst φ (n+1) a)=fst φ n (left φ n x-right φ (n+1) y) at hf
  rw [map_sub,fst_left φ n,fst_right φ n,sub_zero] at hf
  apply (Submodule.mem_bot R).mpr
  apply (π_eq_zero F n x).mpr
  refine ⟨-fst φ (n+1) a,?_⟩
  apply Subtype.ext
  change F.d (n+1) n (-fst φ (n+1) a)=x
  rw [map_neg]; exact hf
lemma cone_subsingleton_of_iso [IsIso φ] (n : ℕ) : Subsingleton (H (C φ) n) := by
  apply subsingleton_of_forall_eq 0
  intro z
  obtain ⟨x,rfl⟩ := π_surjective (C φ) n z
  apply (π_eq_zero (C φ) n x).mpr
  refine ⟨left φ n ((inv φ).f n (snd φ n x)),?_⟩
  apply Subtype.ext
  change (C φ).d (n+1) n (left φ n ((inv φ).f n (snd φ n x)))=x
  cases n with
  | zero =>
    rw [d_left_zero φ]
    have hi : φ.f 0 ((inv φ).f 0 (snd φ 0 x))=snd φ 0 x := by
      have h := congrArg (fun f : G ⟶ G => f.f 0 (snd φ 0 x)) (IsIso.inv_hom_id φ)
      exact h
    rw [hi]; exact decomp_zero φ x
  | succ n =>
    rw [d_left φ]
    apply ext φ
    · simp only [map_add,map_neg,fst_left φ n _,fst_right φ n _,add_zero]
      have hx : (C φ).d (n+1) n x=0 := x.property
      have hs := congrArg (snd φ n) hx
      rw [d_snd φ n,map_zero] at hs
      have hc := congrArg (fun f : G.X (n+1) ⟶ F.X n => f (snd φ (n+1) x))
        ((inv φ).comm (n+1) n)
      have hi : (inv φ).f n (φ.f n (fst φ n x))=fst φ n x := by
        exact congrArg (fun f : F ⟶ F => f.f n (fst φ n x)) (IsIso.hom_inv_id φ)
      have hs' := congrArg ((inv φ).f n) hs
      rw [map_add,hi,map_zero] at hs'
      change -(F.d (n+1) n ((inv φ).f (n+1) (snd φ (n+1) x)))=fst φ n x
      change F.d (n+1) n ((inv φ).f (n+1) (snd φ (n+1) x)) =
        (inv φ).f n (G.d (n+1) n (snd φ (n+1) x)) at hc
      rw [hc]
      exact (eq_neg_of_add_eq_zero_left hs').symm
    · simp only [map_add,map_neg,snd_left φ n _,snd_right φ (n+1) _,neg_zero,zero_add]
      exact congrArg (fun f : G ⟶ G => f.f (n+1) (snd φ (n+1) x)) (IsIso.inv_hom_id φ)
end ConeCoordinates

end

section
open CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalCone

universe u
variable {R : Type u} [CommRing R]
abbrev c := ComplexShape.down ℕ
variable {K L : HomologicalComplex₂ (ModuleCat.{u} R) c c} (φ : K ⟶ L)
noncomputable abbrev B : HomologicalComplex₂ (ModuleCat.{u} R) c c := homotopyCofiber φ
noncomputable abbrev f := total.map φ c
noncomputable abbrev inr := total.map (homotopyCofiber.inr φ) c
lemma total_zero {K L : HomologicalComplex₂ (ModuleCat.{u} R) c c} : total.map (0 : K ⟶ L) c=0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply total.hom_ext
  intro p q hpq
  simp only [ιTotal_map,HomologicalComplex.zero_f,zero_comp,comp_zero]
noncomputable def h : Homotopy (f φ ≫ inr φ) 0 := by
  let t := TotalHomotopy.total (homotopyCofiber.inrCompHomotopy φ (fun j => ⟨j+1,rfl⟩))
  exact {
    hom := t.hom
    zero := t.zero
    comm n := by
      simpa only [total.map_comp,total_zero] using t.comm n }
noncomputable def comparison : homotopyCofiber (f φ) ⟶ (B φ).total c :=
  homotopyCofiber.desc (f φ) (inr φ) (h φ)
@[reassoc] lemma right_comparison (n : ℕ) :
    homotopyCofiber.inrX (f φ) n ≫ (comparison φ).f n=(inr φ).f n :=
  homotopyCofiber.inrX_desc_f _ _ _ _
@[reassoc] lemma left_comparison (p q n : ℕ) (hpq : p+q=n) :
    K.ιTotal c p q n hpq ≫ homotopyCofiber.inlX (f φ) n (n+1) rfl ≫ (comparison φ).f (n+1)=
      (homotopyCofiber.inlX φ p (p+1) rfl).f q ≫
        (B φ).ιTotal c (p+1) q (n+1) (by dsimp;omega) := by
  have hn : c.Rel (n+1) n := rfl
  have hp : c.Rel (p+1) p := rfl
  change K.ιTotal c p q n hpq ≫ homotopyCofiber.inlX (f φ) n (n+1) hn ≫
    (comparison φ).f (n+1) = (homotopyCofiber.inlX φ p (p+1) hp).f q ≫
      (B φ).ιTotal c (p+1) q (n+1) _
  dsimp only [comparison]
  rw [homotopyCofiber.inlX_desc_f]
  change K.ιTotal c p q n hpq ≫
    TotalHomotopy.hom (homotopyCofiber.inrCompHomotopy φ (fun j => ⟨j+1,rfl⟩)) n (n+1)=_
  rw [TotalHomotopy.hom_diag,TotalHomotopy.ι_step,homotopyCofiber.inrCompHomotopy_hom]

noncomputable def inverseFZero : ((B φ).total c).X 0 ⟶ (homotopyCofiber (f φ)).X 0 :=
  (B φ).totalDesc (fun p q hpq => (homotopyCofiber.sndX φ p).f q ≫
    L.ιTotal c p q 0 hpq ≫ homotopyCofiber.inrX (f φ) 0)
noncomputable def inverseFSucc (n : ℕ) : ((B φ).total c).X (n+1) ⟶ (homotopyCofiber (f φ)).X (n+1) :=
  (B φ).totalDesc (fun p q hpq =>
    (if hp : p=0 then 0 else
      (homotopyCofiber.fstX φ p (p-1) (by change p-1+1=p;omega)).f q ≫
        K.ιTotal c (p-1) q n (by dsimp at hpq ⊢;omega) ≫
          homotopyCofiber.inlX (f φ) n (n+1) rfl) +
    (homotopyCofiber.sndX φ p).f q ≫ L.ιTotal c p q (n+1) hpq ≫
      homotopyCofiber.inrX (f φ) (n+1))
noncomputable def inverseF : ∀ n, ((B φ).total c).X n ⟶ (homotopyCofiber (f φ)).X n
  | 0 => inverseFZero φ
  | n+1 => inverseFSucc φ n
@[reassoc] lemma zero_inverse (q n : ℕ) (hq : q=n) :
    (B φ).ιTotal c 0 q n (by dsimp;omega) ≫ inverseF φ n =
      (homotopyCofiber.sndX φ 0).f q ≫ L.ιTotal c 0 q n (by dsimp;omega) ≫
        homotopyCofiber.inrX (f φ) n := by
  cases n with
  | zero => simp only [inverseF,inverseFZero,ι_totalDesc]
  | succ n =>
    simp only [inverseF,inverseFSucc,ι_totalDesc,dite_true,zero_add]
@[reassoc] lemma succ_inverse (p q n : ℕ) (hpq : p+q=n) :
    (B φ).ιTotal c (p+1) q (n+1) (by dsimp;omega) ≫ inverseF φ (n+1)=
      (homotopyCofiber.fstX φ (p+1) p rfl).f q ≫ K.ιTotal c p q n hpq ≫
        homotopyCofiber.inlX (f φ) n (n+1) rfl +
      (homotopyCofiber.sndX φ (p+1)).f q ≫ L.ιTotal c (p+1) q (n+1) (by dsimp;omega) ≫
        homotopyCofiber.inrX (f φ) (n+1) := by
  simp only [inverseF,inverseFSucc,ι_totalDesc,dite_eq_right (Nat.succ_ne_zero p),Nat.add_one_sub_one]
@[reassoc] lemma inr_snd (p q : ℕ) :
    (homotopyCofiber.inrX φ p).f q ≫ (homotopyCofiber.sndX φ p).f q = 𝟙 _ := by
  rw [←HomologicalComplex.comp_f,homotopyCofiber.inrX_sndX,HomologicalComplex.id_f]
@[reassoc] lemma inr_fst (p q : ℕ) :
    (homotopyCofiber.inrX φ (p+1)).f q ≫ (homotopyCofiber.fstX φ (p+1) p rfl).f q = 0 := by
  exact congrArg (fun morphism => morphism.f q) (homotopyCofiber.inrX_fstX φ (p+1) p rfl)
@[reassoc] lemma inl_snd (p q : ℕ) :
    (homotopyCofiber.inlX φ p (p+1) rfl).f q ≫ (homotopyCofiber.sndX φ (p+1)).f q = 0 := by
  exact congrArg (fun morphism => morphism.f q) (homotopyCofiber.inlX_sndX φ p (p+1) rfl)
@[reassoc] lemma inl_fst (p q : ℕ) :
    (homotopyCofiber.inlX φ p (p+1) rfl).f q ≫ (homotopyCofiber.fstX φ (p+1) p rfl).f q = 𝟙 _ := by
  exact congrArg (fun morphism => morphism.f q) (homotopyCofiber.inlX_fstX φ p (p+1) rfl)
lemma decomp (p q : ℕ) :
    (homotopyCofiber.fstX φ (p+1) p rfl).f q ≫ (homotopyCofiber.inlX φ p (p+1) rfl).f q +
      (homotopyCofiber.sndX φ (p+1)).f q ≫ (homotopyCofiber.inrX φ (p+1)).f q = 𝟙 _ := by
  have hrel : c.Rel (p+1) p := rfl
  have hh : homotopyCofiber.fstX φ (p+1) p hrel ≫ homotopyCofiber.inlX φ p (p+1) hrel +
      homotopyCofiber.sndX φ (p+1) ≫ homotopyCofiber.inrX φ (p+1) = 𝟙 _ := by
    apply homotopyCofiber.ext_from_X φ p (p+1) hrel <;> simp
  exact congrArg (fun h => h.f q) hh
lemma decomp_zero (q : ℕ) :
    (homotopyCofiber.sndX φ 0).f q ≫ (homotopyCofiber.inrX φ 0).f q = 𝟙 _ := by
  rw [←HomologicalComplex.comp_f,homotopyCofiber.sndX_inrX _ _ (by simp [c]),HomologicalComplex.id_f]
@[reassoc] lemma right_inverse (n : ℕ) :
    (inr φ).f n ≫ inverseF φ n = homotopyCofiber.inrX (f φ) n := by
  apply total.hom_ext
  intro p q hpq
  rw [ιTotal_map_assoc]
  change (homotopyCofiber.inrX φ p).f q ≫ (B φ).ιTotal c p q n hpq ≫ inverseF φ n = _
  cases p with
  | zero =>
    rw [zero_inverse φ q n (by simpa using hpq),inr_snd_assoc]
  | succ p =>
    obtain ⟨n,rfl⟩ : ∃ n',n=n'+1 := ⟨p+q,by dsimp at hpq;omega⟩
    rw [succ_inverse φ p q n (by dsimp at hpq;omega),Preadditive.comp_add,
      inr_fst_assoc,zero_comp,inr_snd_assoc,zero_add]
@[reassoc] lemma left_inverse (p q n : ℕ) (hpq : p+q=n) :
    (homotopyCofiber.inlX φ p (p+1) rfl).f q ≫
      (B φ).ιTotal c (p+1) q (n+1) (by dsimp;omega) ≫ inverseF φ (n+1) =
        K.ιTotal c p q n hpq ≫ homotopyCofiber.inlX (f φ) n (n+1) rfl := by
  rw [succ_inverse,Preadditive.comp_add,inl_fst_assoc,inl_snd_assoc,zero_comp,add_zero]
lemma comparison_inverse (n : ℕ) : (comparison φ).f n ≫ inverseF φ n=𝟙 _ := by
  cases n with
  | zero =>
    apply homotopyCofiber.ext_from_X' (f φ) 0 (by simp [c])
    rw [←Category.assoc,right_comparison,right_inverse]
    simp
  | succ n =>
    apply homotopyCofiber.ext_from_X (f φ) n (n+1) rfl
    · apply total.hom_ext
      intro p q hpq
      rw [left_comparison_assoc φ p q n hpq,left_inverse φ p q n hpq]
      simp
    · rw [←Category.assoc,right_comparison,right_inverse]
      simp
lemma inverse_comparison (n : ℕ) : inverseF φ n ≫ (comparison φ).f n=𝟙 _ := by
  apply total.hom_ext
  intro p q hpq
  cases p with
  | zero =>
    rw [zero_inverse_assoc φ q n (by simpa using hpq),right_comparison,ιTotal_map]
    change (homotopyCofiber.sndX φ 0).f q ≫ (homotopyCofiber.inrX φ 0).f q ≫ _ = _
    rw [←Category.assoc,decomp_zero]
    simp
  | succ p =>
    obtain ⟨n,rfl⟩ : ∃ n',n=n'+1 := ⟨p+q,by dsimp at hpq;omega⟩
    rw [succ_inverse_assoc φ p q n (by dsimp at hpq;omega),Preadditive.add_comp]
    simp only [Category.assoc]
    rw [left_comparison,right_comparison,ιTotal_map]
    change (homotopyCofiber.fstX φ (p+1) p rfl).f q ≫
      (homotopyCofiber.inlX φ p (p+1) rfl).f q ≫ _ +
      (homotopyCofiber.sndX φ (p+1)).f q ≫ (homotopyCofiber.inrX φ (p+1)).f q ≫ _ = _
    simp only [←Category.assoc,←Preadditive.add_comp,decomp,Category.id_comp,Category.comp_id]
noncomputable def iso : homotopyCofiber (f φ) ≅ (B φ).total c := by
  haveI : ∀ n,IsIso ((comparison φ).f n) := fun n =>
    ⟨⟨inverseF φ n,comparison_inverse φ n,inverse_comparison φ n⟩⟩
  haveI : IsIso (comparison φ) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (comparison φ)
end TotalCone

end

end

end OAI
