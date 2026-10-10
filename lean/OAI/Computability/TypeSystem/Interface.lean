import OAI.Computability.TypeSystem.Candidates
import OAI.Computability.TypeSystem.Potential

namespace OAI

/-! The exact local obligations used when advancing a primary component.
This is an internal interface, not a hypothesis of the main PTS theorem. -/
namespace PureTypeSystem
universe u v

/-- Expected types include unsorted literal sorts (the regularity alternative). -/
def Expected {S : Type u} (P : Specification S) (Γ : List (Expr S)) (A : Expr S) : Prop :=
  (∃ s, A = .sort s) ∨ ∃ s, HasType P Γ A (.sort s)
namespace Expected
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {A D : Expr S}
theorem of_type {M : Expr S} (h : HasType P Γ M A) : Expected P Γ A := h.regularity
theorem sorted {s : S} (h : HasType P Γ A (.sort s)) : Expected P Γ A := .inr ⟨s,h⟩
theorem wn (hw : SystemWeaklyNormalizing P) (h : Expected P Γ A) : WeaklyNormalizing A := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact ⟨_,.refl,Normal.sort s⟩
  · exact h.weaklyNormalizing hw
theorem weaken {s : S} (h : Expected P Γ A) (hD : HasType P Γ D (.sort s)) :
    Expected P (D :: Γ) (A.rename Nat.succ) := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact .inl ⟨s,rfl⟩
  · exact .inr ⟨s,.weaken h hD⟩
end Expected

namespace Expr
variable {S : Type u}
def extend (σ : Nat → Expr S) (n : Expr S) : Nat → Expr S
  | 0 => n
  | i+1 => σ i
@[simp] theorem extend_zero (σ : Nat → Expr S) (n : Expr S) : extend σ n 0 = n := rfl
@[simp] theorem extend_succ (σ : Nat → Expr S) (n : Expr S) (i : Nat) : extend σ n (i+1) = σ i := rfl
@[simp] theorem subst_raise_extend (M n : Expr S) (σ : Nat → Expr S) :
    (M.rename Nat.succ).subst (extend σ n) = M.subst σ := by
  rw [subst_rename]; rfl
@[simp] theorem instantiate_extended (M n : Expr S) (σ : Nat → Expr S) :
    (M.subst (liftSub σ)).instantiate n = M.subst (extend σ n) := by
  rw [instantiate,subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact subst_lift_single (σ i) n
end Expr

/-- Ground=top has already been proved on U; U is predecessor closed and
contains every strict predecessor of the component currently processed. -/
structure Processed {S : Type u} {P : Specification S} (Ω : ContextTower P)
    (U C : Set (Set S)) : Prop where
  disjoint : Disjoint U C
  closed : ∀ {I J}, J ∈ U → Reach (PrimaryEdge P) I J → I ∈ U
  before : ∀ {I J}, J ∈ C → Reach (PrimaryEdge P) I J → I ∈ U ∨ I ∈ C
  invariant : ∀ {T}, Candidates.ActualType Ω T → Ω.profile T ∈ U →
    Candidates.Ground Ω T = Candidates.Top Ω T

/-- Environments carry arbitrary typed raw images. Extension collections are
nonempty, and retain old parameters. Product tests range over all listed
extensions; specialization can select the normal argument's tested payload. -/
structure ComponentInterface {S : Type u} {P : Specification S} (Ω : ContextTower P)
    (hw : SystemWeaklyNormalizing P) (C : Set (Set S)) where
  Env : List (Expr S) → Type v
  images : {Γ : List (Expr S)} → Env Γ → Nat → Expr S
  typed : ∀ {Γ} (e : Env Γ), Ω.TypedSubstitution Γ (images e)
  inhabit : ∀ {Γ} (σ : Nat → Expr S), Ω.TypedSubstitution Γ σ →
    ∃ e : Env Γ, images e = σ
  Ext : {Γ : List (Expr S)} → {D : Expr S} → Env Γ → Env (D :: Γ) → Expr S → Prop
  ext_images : ∀ {Γ D} {e : Env Γ} {e' : Env (D :: Γ)} {n}, Ext e e' n →
    images e' = Expr.extend (images e) n
  extend : ∀ {Γ D s} (e : Env Γ), HasType P Γ D (.sort s) → ∀ n,
    Ω.HasType n (D.subst (images e)) → ∃ e' : Env (D :: Γ), Ext e e' n
  R : {Γ : List (Expr S)} → Expr S → Env Γ → Set (Expr S)
  candidate : ∀ {Γ A} (e : Env Γ), Expected P Γ A →
    Candidates.IsCandidate Ω (A.subst (images e)).normalForm (R A e)
  conversion : ∀ {Γ A B} (e : Env Γ), Expected P Γ A → Expected P Γ B →
    Converts A B → R A e = R B e
  outside : ∀ {Γ A} (e : Env Γ), Expected P Γ A →
    (Profile P Γ A ∉ C ∨ Ω.profile (A.subst (images e)) ∉ C) →
    R A e = Candidates.Top Ω (A.subst (images e)).normalForm
  weakening : ∀ {Γ D A s} {e : Env Γ} {e' : Env (D :: Γ)} {n},
    HasType P Γ D (.sort s) → Expected P Γ A → Ext e e' n →
    R (A.rename Nat.succ) e' = R A e
  product_intro : ∀ {Γ D E s} (e : Env Γ), HasType P Γ (.pi D E) (.sort s) →
    Profile P Γ (.pi D E) ∈ C → Ω.profile ((Expr.pi D E).subst (images e)) ∈ C →
    ∀ h, h ∈ Candidates.Top Ω ((Expr.pi D E).subst (images e)).normalForm →
    (∀ n, n ∈ R D e → ∀ e' : Env (D :: Γ), Ext e e' n → Expr.app h n ∈ R E e') →
    h ∈ R (.pi D E) e
  specialization : ∀ {Γ D E s N} (e : Env Γ), HasType P Γ (.pi D E) (.sort s) →
    HasType P Γ N D → Profile P Γ (.pi D E) ∈ C →
    Ω.profile ((Expr.pi D E).subst (images e)) ∈ C →
    ∀ h, h ∈ R (.pi D E) e → N.subst (images e) ∈ R D e →
    Expr.app h (N.subst (images e)) ∈ R (E.instantiate N) e

namespace ComponentInterface
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

def Admissible {Γ : List (Expr S)} (e : J.Env Γ) : Prop :=
  ∀ i B, Lookup Γ i B →
    (Profile P Γ B ∈ C → J.images e i ∈ J.R B e) ∧
    (Profile P Γ B ∈ U → StronglyNormalizing (J.images e i)) ∧
    (Profile P Γ B ∉ U → Profile P Γ B ∉ C →
      J.images e i ∈ Ground Ω (B.subst (J.images e)).normalForm)

theorem admissible_extension {Γ : List (Expr S)} {D : Expr S} {s : S}
    {e : J.Env Γ} {e' : J.Env (D :: Γ)} {n : Expr S}
    (hD : HasType P Γ D (.sort s)) (he : J.Ext e e' n)
    (ha : J.Admissible (U := U) e)
    (hnC : Profile P Γ D ∈ C → n ∈ J.R D e)
    (hnU : Profile P Γ D ∈ U → StronglyNormalizing n)
    (hnG : Profile P Γ D ∉ U → Profile P Γ D ∉ C → n ∈ Ground Ω (D.subst (J.images e)).normalForm) :
    J.Admissible (U := U) e' := by
  intro i B hi
  cases hi with
  | zero =>
    have hp := Profile.weaken hw hD hD
    rw [hp,J.weakening hD (.sorted hD) he]
    simpa only [J.ext_images he,Expr.extend_zero,Expr.subst_raise_extend] using ⟨hnC,hnU,hnG⟩
  | succ D hi =>
    obtain ⟨t,hB⟩ := HasType.lookup_sorted hD.valid hi
    rw [Profile.weaken hw hB hD,J.weakening hD (.sorted hB) he]
    simpa only [J.ext_images he,Expr.extend_succ,Expr.subst_raise_extend] using ha _ _ hi

/-- Sending a binder to a fresh typed variable always preserves admissibility.
SN of that instance reflects back to the open substituted body by substitution
reflection, so no global renaming or reduction-height bound is needed. -/
theorem fresh_extension {Γ : List (Expr S)} {D : Expr S} {s : S}
    (e : J.Env Γ) (hD : HasType P Γ D (.sort s)) (ha : J.Admissible (U := U) e) :
    ∃ n, ∃ e' : J.Env (D :: Γ), J.Ext e e' (.var n) ∧ J.Admissible (U := U) e' := by
  have ht := ContextTower.HasType.subst hD (J.typed e)
  obtain ⟨n,_,hn⟩ := Ω.fresh_variable ht 0
  obtain ⟨e',he⟩ := J.extend e hD (.var n) hn
  have hng := var_ground n (hn.normalize_type hw)
  exact ⟨n,e',he,J.admissible_extension hD he ha
    (fun _ => (J.candidate e (.sorted hD)).lower hng)
    (fun _ => (Normal.var n).stronglyNormalizing) (fun _ _ => hng)⟩

end ComponentInterface

namespace Expected
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S}
theorem subst_wn (h : Expected P Γ A) (hw : SystemWeaklyNormalizing P)
    (hσ : Ω.TypedSubstitution Γ σ) : WeaklyNormalizing (A.subst σ) := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact ⟨_,.refl,Normal.sort s⟩
  · exact (ContextTower.HasType.subst h hσ).weaklyNormalizing hw

theorem actual (h : Expected P Γ A) (hw : SystemWeaklyNormalizing P)
    (hσ : Ω.TypedSubstitution Γ σ) : Candidates.ActualType Ω (A.subst σ).normalForm := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact .inr ⟨s,Expr.normalForm_of_normal (Normal.sort s)⟩
  · have ht := ContextTower.HasType.subst h hσ
    exact .inl ⟨(Expr.normalForm_spec (ht.weaklyNormalizing hw)).2, s, ht.normalForm hw⟩
end Expected

namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable (hw : SystemWeaklyNormalizing P)
include hw
theorem profile_subst_path {Γ : List (Expr S)} {T : Expr S} {s : S} {σ : Nat → Expr S}
    (ht : PureTypeSystem.HasType P Γ T (.sort s)) (hσ : Ω.TypedSubstitution Γ σ) :
    PositivePath (PrimaryEdge P) (Ω.profile (T.subst σ)) (Profile P Γ T) :=
  Profile.inclusion_path (Ω.profile_feasible hw (HasType.subst ht hσ))
    (Profile.feasible (ht.weaklyNormalizing hw) (Profile.nonempty_of_sorted hw ht))
    (Ω.profile_subst_growth hw ht hσ)

theorem profile_instantiate_product_path {D E n : Expr S} {s : S}
    (hp : Ω.HasType (.pi D E) (.sort s)) (hn : Ω.HasType n D) :
    PositivePath (PrimaryEdge P) (Ω.profile (E.instantiate n)) (Ω.profile (.pi D E)) := by
  obtain ⟨k,hp,hn⟩ := hp.common hn
  obtain ⟨a,b,c,_,hE,_,_⟩ := hp.generation_pi
  have hEn := hE.instantiate hn
  change PureTypeSystem.HasType P (Ω.context k)
    ((E.rename (Expr.liftRen (Expr.reverseIndex k))).instantiate (n.rename (Expr.reverseIndex k))) (.sort b) at hEn
  rw [Expr.instantiate_rename] at hEn
  rw [Ω.profile_at hw hEn,Ω.profile_at hw hp]
  simpa only [Expr.rename,Expr.instantiate_rename] using Profile.instantiate_product_path hw hp hn
end ContextTower

namespace Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable (hw : SystemWeaklyNormalizing P)
include hw
/-- G propagates through the normal form of a raw dependent product. -/
theorem ground_application_subst {Γ : List (Expr S)} {D E n h : Expr S} {s : S}
    {σ : Nat → Expr S} (hp : HasType P Γ (.pi D E) (.sort s))
    (hσ : Ω.TypedSubstitution Γ σ)
    (hh : h ∈ Ground Ω ((Expr.pi D E).subst σ).normalForm)
    (hn : n ∈ Top Ω (D.subst σ).normalForm) :
    Expr.app h n ∈ Ground Ω (E.subst (Expr.extend σ n)).normalForm := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hraw := ContextTower.HasType.subst hp hσ
  have hwraw := hraw.weaklyNormalizing hw
  change WeaklyNormalizing (.pi (D.subst σ) (E.subst (Expr.liftSub σ))) at hwraw
  have hrawD := ContextTower.HasType.subst hD hσ
  have hnr : Ω.HasType n (D.subst σ) := hn.1.conversion hrawD
    (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
  have hparts : WeaklyNormalizing (D.subst σ) ∧
      WeaklyNormalizing (E.subst (Expr.liftSub σ)) := by
    obtain ⟨normal, reduction, hnormal⟩ := hwraw
    obtain ⟨domain, body, rfl, hdomain, hbody⟩ := Reduces.pi_inv reduction
    exact ⟨⟨domain, hdomain, hnormal.pi_domain⟩, ⟨body, hbody, hnormal.pi_body⟩⟩
  have htarget : Ω.HasType (E.subst (Expr.extend σ n)) (.sort b) :=
    ContextTower.HasType.subst hE (hσ.cons hnr)
  have hnf : ((Expr.pi D E).subst σ).normalForm =
      .pi (D.subst σ).normalForm (E.subst (Expr.liftSub σ)).normalForm :=
    Expr.normalForm_pi hparts.1 hparts.2
  rw [hnf] at hh
  have hout := ground_application hw hh hn
  have hpN := hraw.normalForm hw
  rw [hnf] at hpN
  obtain ⟨t,ht⟩ := Ω.frame_target_sorted hpN hn.1
  have hr : Reduces (E.subst (Expr.extend σ n))
      ((E.subst (Expr.liftSub σ)).normalForm.instantiate n) := by
    rw [← Expr.instantiate_extended]
    exact (Expr.normalForm_spec hparts.2).1.subst (Expr.single n)
  have he := Expr.normalForm_converts (htarget.weaklyNormalizing hw)
    (ht.weaklyNormalizing hw) hr.converts
  rwa [he]
end Candidates

namespace Processed
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {U C : Set (Set S)} (H : Processed Ω U C) (hw : SystemWeaklyNormalizing P)
variable {Γ : List (Expr S)} {T : Expr S} {s : S} {σ : Nat → Expr S}
include H hw
theorem subst_closed (ht : HasType P Γ T (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hT : Profile P Γ T ∈ U) : Ω.profile (T.subst σ) ∈ U :=
  H.closed hT (Ω.profile_subst_path hw ht hσ).reach

theorem subst_before (ht : HasType P Γ T (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hT : Profile P Γ T ∈ C) : Ω.profile (T.subst σ) ∈ U ∨ Ω.profile (T.subst σ) ∈ C :=
  H.before hT (Ω.profile_subst_path hw ht hσ).reach

theorem top_ground_generic {e : Expr S}
    (ht : HasType P Γ T (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hT : Profile P Γ T ∈ U) (he : e ∈ Candidates.Top Ω (T.subst σ).normalForm) :
    e ∈ Candidates.Ground Ω (T.subst σ).normalForm := by
  rw [H.invariant ((Expected.sorted ht).actual hw hσ) (by
    rw [Ω.profile_normalForm]
    exact H.subst_closed hw ht hσ hT)]
  exact he
end Processed

namespace ComponentInterface
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

/-- The extra neutral invariant is exactly the G-prefix invariant in the
manuscript's spine argument. -/
def Transported {Γ : List (Expr S)} (M A : Expr S) (e : J.Env Γ) : Prop :=
  M.subst (J.images e) ∈ J.R A e ∧
    (Neutral M → Profile P Γ A ∉ C →
      M.subst (J.images e) ∈ Ground Ω (A.subst (J.images e)).normalForm)

namespace Transported
variable {J} {Γ : List (Expr S)} {M A B : Expr S} {e : J.Env Γ}
theorem sn (h : J.Transported M A e) (hA : Expected P Γ A) :
    StronglyNormalizing (M.subst (J.images e)) := (J.candidate e hA).upper h.1 |>.2

theorem convert (h : J.Transported M A e) (hA : Expected P Γ A)
    (hB : Expected P Γ B) (hc : Converts A B) : J.Transported M B e := by
  have hp := Profile.converts (P := P) (Γ := Γ) (hA.wn hw) (hB.wn hw) hc
  have he := Expr.normalForm_converts (hA.subst_wn hw (J.typed e))
    (hB.subst_wn hw (J.typed e)) (hc.subst (J.images e))
  refine ⟨?_,?_⟩
  · rw [← J.conversion e hA hB hc]; exact h.1
  · intro hn hout
    rw [← he]
    exact h.2 hn (hp ▸ hout)
end Transported

theorem transported_of_ground {Γ : List (Expr S)} {M A : Expr S} {e : J.Env Γ}
    (hA : Expected P Γ A) (hg : M.subst (J.images e) ∈ Ground Ω (A.subst (J.images e)).normalForm) :
    J.Transported M A e := ⟨(J.candidate e hA).lower hg,fun _ _ => hg⟩

theorem transported_at_sort {Γ : List (Expr S)} {M : Expr S} {e : J.Env Γ} {s : S}
    (ht : HasType P Γ M (.sort s)) (hs : StronglyNormalizing (M.subst (J.images e))) :
    J.Transported M (.sort s) e := by
  apply J.transported_of_ground (.inl ⟨s,rfl⟩)
  have hh : M.subst (J.images e) ∈ Top Ω (.sort s) :=
    ⟨ContextTower.HasType.subst ht (J.typed e),hs⟩
  simpa only [Expr.subst,Expr.normalForm_of_normal (Normal.sort s),sort_ground_eq_top] using hh

variable (H : Processed Ω U C)
include H

theorem transported_var {Γ : List (Expr S)} {A : Expr S} {i : Nat}
    (ht : HasType P Γ (.var i) A) (e : J.Env Γ) (ha : J.Admissible (U := U) e) :
    J.Transported (.var i) A e := by
  obtain ⟨B,hB,hc⟩ := ht.generation
  obtain ⟨s,hBs⟩ := HasType.lookup_sorted ht.valid hB
  have hea := Expected.of_type ht
  apply Transported.convert (A := B) (hA := .sorted hBs) (hB := hea) (hc := .symm _ _ hc)
  have hdr := ha i B hB
  by_cases hBU : Profile P Γ B ∈ U
  · apply J.transported_of_ground (.sorted hBs)
    exact H.top_ground_generic hw hBs (J.typed e) hBU
      ⟨(J.typed e i B hB).normalize_type hw,hdr.2.1 hBU⟩
  · by_cases hBC : Profile P Γ B ∈ C
    · exact ⟨hdr.1 hBC,fun _ hn => False.elim (hn hBC)⟩
    · exact J.transported_of_ground (.sorted hBs) (hdr.2.2 hBU hBC)

/-- Propagation for a neutral prefix. Unlike a candidate, G has application
closure; the processed invariant handles the sole transition out of C. -/
theorem transported_neutral_app {Γ : List (Expr S)} {f n D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hn : HasType P Γ n D)
    (hf : Neutral f) (e : J.Env Γ)
    (hfr : J.Transported f (.pi D E) e) (hnr : J.Transported n D e) :
    J.Transported (.app f n) (E.instantiate n) e := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hExpected := Expected.sorted (hE.instantiate hn)
  have hnt := (J.candidate e (.sorted hD)).upper hnr.1
  have hg (hfg : f.subst (J.images e) ∈ Ground Ω ((Expr.pi D E).subst (J.images e)).normalForm) :
      J.Transported (.app f n) (E.instantiate n) e := by
    apply J.transported_of_ground hExpected
    rw [← Expr.instantiate_subst,Expr.instantiate_extended]
    exact ground_application_subst hw hp (J.typed e) hfg hnt
  by_cases hK : Profile P Γ (.pi D E) ∈ C
  · by_cases hKa : Ω.profile ((Expr.pi D E).subst (J.images e)) ∈ C
    · have hr := J.specialization e hp hn hK hKa _ hfr.1 hnr.1
      refine ⟨hr,?_⟩
      intro _ ho
      have hL := H.before hK (Profile.instantiate_product_path hw hp hn).reach
      rcases hL with hLU | hLC
      · exact H.top_ground_generic hw (hE.instantiate hn) (J.typed e) hLU
          ((J.candidate e hExpected).upper hr)
      · exact False.elim (ho hLC)
    · apply hg
      have haK := (H.subst_before hw hp (J.typed e) hK).resolve_right hKa
      rw [H.invariant ((Expected.sorted hp).actual hw (J.typed e)) (by
        rwa [Ω.profile_normalForm])]
      exact (J.candidate e (.sorted hp)).upper hfr.1
  · exact hg (hfr.2 hf hK)

end ComponentInterface
end PureTypeSystem

namespace PureTypeSystem.Candidates
universe u
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable (hw : SystemWeaklyNormalizing P)
include hw

theorem application_subst_type {Γ : List (Expr S)} {D E n h : Expr S} {s : S}
    {σ : Nat → Expr S} (hp : HasType P Γ (.pi D E) (.sort s))
    (hσ : Ω.TypedSubstitution Γ σ)
    (hh : Ω.HasType h ((Expr.pi D E).subst σ).normalForm)
    (hn : Ω.HasType n (D.subst σ).normalForm) :
    Ω.HasType (.app h n) (E.subst (Expr.extend σ n)).normalForm := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hraw := ContextTower.HasType.subst hp hσ
  have hrawD := ContextTower.HasType.subst hD hσ
  have hhr := hh.conversion hraw
    (.symm _ _ (Expr.normalForm_spec (hraw.weaklyNormalizing hw)).1.converts)
  have hnr := hn.conversion hrawD
    (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
  have hout := (hhr.application hnr).normalize_type hw
  simpa only [Expr.instantiate_extended] using hout

def RawProduct (Ω : ContextTower P) (D E : Expr S) (σ : Nat → Expr S)
    (X : Set (Expr S)) (Y : Expr S → Bool → Set (Expr S)) : Set (Expr S) :=
  {h | h ∈ Top Ω ((Expr.pi D E).subst σ).normalForm ∧
    ∀ n ∈ X, ∀ b, Expr.app h n ∈ Y n b}

theorem rawProduct_candidate {Γ : List (Expr S)} {D E : Expr S} {s : S}
    {σ : Nat → Expr S} {X : Set (Expr S)} {Y : Expr S → Bool → Set (Expr S)}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hX : IsCandidate Ω (D.subst σ).normalForm X)
    (hY : ∀ n ∈ X, ∀ b, IsCandidate Ω (E.subst (Expr.extend σ n)).normalForm (Y n b)) :
    IsCandidate Ω ((Expr.pi D E).subst σ).normalForm (RawProduct Ω D E σ X Y) where
  lower := by
    intro h hh
    refine ⟨ground_le_top hh,?_⟩
    intro n hn b
    exact (hY n hn b).lower (ground_application_subst hw hp hσ hh (hX.upper hn))
  upper := fun _ hh => hh.1
  expansion := by
    intro D' m a ns ht hD hm ha hns hc
    refine ⟨⟨ht,StronglyNormalizing.head_expansion hD hm ha hns hc.1.2⟩,?_⟩
    intro n hn b
    have ht' := application_subst_type hw hp hσ ht (hX.upper hn).1
    have hsn : StronglyNormalizingArgs (ns ++ [n]) := by
      apply StronglyNormalizingArgs.of_forall
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hns.of_mem hx
      · exact (List.mem_singleton.mp hx).symm ▸ (hX.upper hn).2
    have hc' := hc.2 n hn b
    have ht'' : Ω.HasType ((Expr.app (.lam D' m) a).apps (ns ++ [n]))
        (E.subst (Expr.extend σ n)).normalForm := by
      simpa only [Expr.apps_append,Expr.apps] using ht'
    have hc'' : (m.instantiate a).apps (ns ++ [n]) ∈ Y n b := by
      simpa only [Expr.apps_append,Expr.apps] using hc'
    simpa only [Expr.apps_append,Expr.apps] using
      (hY n hn b).expansion D' m a (ns ++ [n]) ht'' hD hm ha hsn hc'' 
end PureTypeSystem.Candidates

end OAI
