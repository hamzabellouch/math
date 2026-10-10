import OAI.Computability.TypeSystem.Interface

namespace OAI

namespace PureTypeSystem

section
universe u v
namespace Neutral
variable {S : Type u} {M : Expr S} {ns : List (Expr S)}
theorem apps_head (h : Neutral (M.apps ns)) : Neutral M := by
  induction ns generalizing M with
  | nil => exact h
  | cons n ns ih =>
    have hh := ih h
    cases hh with
    | app hh => exact hh
end Neutral

namespace ComponentInterface
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

def Transports (M : Expr S) : Prop :=
  ∀ (Γ : List (Expr S)) A, HasType P Γ M A →
    ∀ e : J.Env Γ, J.Admissible (U := U) e → J.Transported M A e

/-- Reflection of the fresh-variable instance proves SN of the open body. -/
theorem open_sn {Γ : List (Expr S)} {D b B : Expr S} {s : S}
    (hb : HasType P (D :: Γ) b B) (hD : HasType P Γ D (.sort s))
    (ih : J.Transports (U := U) b) (e : J.Env Γ) (ha : J.Admissible (U := U) e) :
    StronglyNormalizing (b.subst (Expr.liftSub (J.images e))) := by
  obtain ⟨z,e',he',ha'⟩ := J.fresh_extension e hD ha
  have hsn := (ih _ _ hb e' ha').sn (.of_type hb)
  rw [J.ext_images he',← Expr.instantiate_extended] at hsn
  exact StronglyNormalizing.of_subst (Expr.single (.var z)) hsn

variable (H : Processed Ω U C)
include H

theorem transports_lam {Γ : List (Expr S)} {D b B : Expr S} {s : S}
    (hb : HasType P (D :: Γ) b B) (hp : HasType P Γ (.pi D B) (.sort s))
    (ihD : J.Transports (U := U) D) (ihb : J.Transports (U := U) b)
    (e : J.Env Γ) (ha : J.Admissible (U := U) e) :
    J.Transported (.lam D b) (.pi D B) e := by
  classical
  obtain ⟨a,c,d,hD,hB,_,_⟩ := hp.generation_pi
  have hDs := (ihD _ _ hD e ha).sn (.of_type hD)
  have hbs := J.open_sn hb hD ihb e ha
  have htop : (Expr.lam D b).subst (J.images e) ∈ Top Ω ((Expr.pi D B).subst (J.images e)).normalForm :=
    ⟨(ContextTower.HasType.subst (.abstraction hb hp) (J.typed e)).normalize_type hw,hDs.lam hbs⟩
  refine ⟨?_,fun hn => by cases hn⟩
  by_cases hK : Profile P Γ (.pi D B) ∈ C
  · by_cases hKa : Ω.profile ((Expr.pi D B).subst (J.images e)) ∈ C
    · apply J.product_intro e hp hK hKa _ htop
      intro n hn e' he
      have hnt := (J.candidate e (.sorted hD)).upper hn
      have hDomain := ContextTower.HasType.subst hD (J.typed e)
      have hnr := hnt.1.conversion hDomain
        (.symm _ _ (Expr.normalForm_spec (hDomain.weaklyNormalizing hw)).1.converts)
      have hdBefore := H.before hK (Reach.single (.domain (Profile.triple hw hp)))
      have hadm : J.Admissible (U := U) e' := J.admissible_extension hD he ha
        (fun _ => hn) (fun _ => hnt.2) (fun hnu hnc => by
          rcases hdBefore with hu | hc
          · exact False.elim (hnu hu)
          · exact False.elim (hnc hc))
      have hbody := (ihb _ _ hb e' hadm).1
      have htapp := ((ContextTower.HasType.subst (.abstraction hb hp) (J.typed e)).application hnr).normalize_type hw
      change Ω.HasType (.app (.lam (D.subst (J.images e)) (b.subst (Expr.liftSub (J.images e)))) n)
        ((B.subst (Expr.liftSub (J.images e))).instantiate n).normalForm at htapp
      rw [Expr.instantiate_extended,← J.ext_images he] at htapp
      have hbmem : (b.subst (Expr.liftSub (J.images e))).instantiate n ∈ J.R B e' := by
        rwa [Expr.instantiate_extended,← J.ext_images he]
      exact (J.candidate e' (.of_type hb)).expansion _ _ _ [] htapp hDs hbs hnt.2 .nil hbmem
    · rw [J.outside e (.sorted hp) (.inr hKa)]; exact htop
  · rw [J.outside e (.sorted hp) (.inl hK)]; exact htop

/-- Strongly-normalizing substitution transport,
including a neutral G-prefix invariant. -/
theorem sn_fundamental {M : Expr S} (hs : StronglyNormalizing M) :
    J.Transports (U := U) M := by
  apply StronglyNormalizing.induction_descendants (Q := J.Transports (U := U)) _ hs
  intro M _ ihr ihp Γ A ht e ha
  cases M with
  | var i => exact J.transported_var H ht e ha
  | sort s =>
    obtain ⟨t,hat,hc⟩ := ht.generation
    have hst := HasType.sort_of_valid ht.valid hat
    exact (J.transported_at_sort hst (Normal.sort s).stronglyNormalizing).convert
      (.inl ⟨t,rfl⟩) (.of_type ht) (.symm _ _ hc)
  | pi D E =>
    obtain ⟨a,b,c,hD,hE,hr,hc⟩ := ht.generation_pi
    have hDs := (ihp D (Expr.ProperPart.child (.pi_domain D E)) _ _ hD e ha).sn (.of_type hD)
    have hEs := J.open_sn hE hD (ihp E (Expr.ProperPart.child (.pi_body D E))) e ha
    exact (J.transported_at_sort (.product hD hE hr) (hDs.pi hEs)).convert
      (.inl ⟨c,rfl⟩) (.of_type ht) (.symm _ _ hc)
  | lam D b =>
    obtain ⟨B,s,hb,hp,hc⟩ := ht.generation_lam
    exact (J.transports_lam H hb hp
      (ihp D (Expr.ProperPart.child (.lam_domain D b)))
      (ihp b (Expr.ProperPart.child (.lam_body D b))) e ha).convert
      (.sorted hp) (.of_type ht) (.symm _ _ hc)
  | app f n =>
    rcases ht.app_spine with hf | ⟨D,b,n',ns,he⟩
    · obtain ⟨D,E,hft,hnt,hc⟩ := ht.generation_app
      obtain ⟨s,hp⟩ := hft.product_type_sorted
      have hfr := ihp f (Expr.ProperPart.child (.app_left f n)) _ _ hft e ha
      have hnr := ihp n (Expr.ProperPart.child (.app_right f n)) _ _ hnt e ha
      exact (J.transported_neutral_app H hp hnt hf e hfr hnr).convert
        (.of_type (.application hft hnt)) (.of_type ht) (.symm _ _ hc)
    · have ht' : HasType P Γ ((Expr.app (.lam D b) n').apps ns) A := he ▸ ht
      have parts : ∀ N, Expr.ProperPart N ((Expr.app (.lam D b) n').apps ns) →
          J.Transports (U := U) N := by
        intro N hN; apply ihp N; change Expr.ProperPart N (.app f n); rwa [he]
      have hlampart : Expr.ProperPart (.lam D b) ((Expr.app (.lam D b) n').apps ns) :=
        (Expr.ProperPart.child (.app_left _ _)).trans_right (Expr.Subterm.apps_head ns)
      obtain ⟨T,hthead⟩ := ht'.apps_head
      obtain ⟨D',E',hlam,hn',_⟩ := hthead.generation_app
      obtain ⟨B,s,hb,hp,_⟩ := hlam.generation_lam
      obtain ⟨a,c,d,hD,_,_,_⟩ := hp.generation_pi
      have hDs := (parts D (Expr.ProperPart.trans_left (Expr.Subterm.of_child (.lam_domain D b)) hlampart) _ _ hD e ha).sn (.of_type hD)
      have hbs := J.open_sn hb hD (parts b (Expr.ProperPart.trans_left (Expr.Subterm.of_child (.lam_body D b)) hlampart)) e ha
      have hnp := (Expr.ProperPart.child (.app_right (.lam D b) n')).trans_right (Expr.Subterm.apps_head ns)
      have hns := (parts n' hnp _ _ hn' e ha).sn (.of_type hn')
      have hargs : StronglyNormalizingArgs (ns.map (Expr.subst (J.images e))) := by
        apply StronglyNormalizingArgs.of_forall
        intro z hz
        rcases List.mem_map.mp hz with ⟨L,hL,rfl⟩
        obtain ⟨Z,hZ⟩ := ht'.apps_arg hL
        exact (parts L (Expr.ProperPart.apps_arg hL) _ _ hZ e ha).sn (.of_type hZ)
      have hred : Beta (.app f n) ((b.instantiate n').apps ns) := by
        rw [he]; exact (Beta.head D b n').apps ns
      have hctr := (ihr _ hred _ _ (ht.subject_reduction hred) e ha).1
      have hctr' : ((b.subst (Expr.liftSub (J.images e))).instantiate (n'.subst (J.images e))).apps
          (ns.map (Expr.subst (J.images e))) ∈ J.R A e := by
        simpa only [Expr.subst_apps,Expr.instantiate_subst] using hctr
      have hty := (ContextTower.HasType.subst ht' (J.typed e)).normalize_type hw
      rw [Expr.subst_apps] at hty
      have hexp := (J.candidate e (.of_type ht)).expansion _ _ _ _ hty hDs hbs hns hargs hctr'
      constructor
      · rw [he,Expr.subst_apps]
        exact hexp
      · intro hn
        rw [he] at hn
        have hh := hn.apps_head
        cases hh with
        | app hn => cases hn
end ComponentInterface

namespace StronglyNormalizing
variable {S : Type u} {M : Expr S}
theorem reverseIndex (h : StronglyNormalizing M) (k : Nat) :
    StronglyNormalizing (M.rename (Expr.reverseIndex k)) := by
  apply of_rename (Expr.reverseIndex k)
  simpa only [Expr.reverseIndex_twice] using h
end StronglyNormalizing

namespace Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
/-- A single finite prefix supporting every exact typing of a tested stack. -/
inductive StackAt (k : Nat) : Expr S → List (Expr S) → Prop
  | nil (T) : StackAt k T []
  | cons {D E n ns} :
      HasType P (Ω.context k) (n.rename (Expr.reverseIndex k)) (D.rename (Expr.reverseIndex k)) →
      StronglyNormalizing n → StackAt k (E.instantiate n).normalForm ns →
      StackAt k (.pi D E) (n :: ns)
namespace StackAt
variable {Ω} {k j : Nat} {T : Expr S} {ns : List (Expr S)}
theorem mono (h : StackAt Ω k T ns) (hkj : k ≤ j) : StackAt Ω j T ns := by
  induction h with
  | nil T => exact .nil T
  | cons hn hsn _ ih => exact .cons (Ω.at_mono hn hkj) hsn ih

theorem tested (h : StackAt Ω k T ns) : TestedStack Ω T ns := by
  induction h with
  | nil T => exact .nil T
  | cons hn hs _ ih => exact .cons ⟨⟨k,hn⟩,hs⟩ ih
end StackAt
namespace TestedStack
variable {Ω} {T : Expr S} {ns : List (Expr S)}
theorem common_stage (h : TestedStack Ω T ns) : ∃ k, StackAt Ω k T ns := by
  induction h with
  | nil T => exact ⟨0,.nil T⟩
  | cons hn _ ih =>
    obtain ⟨k,hk⟩ := ih
    obtain ⟨j,hj⟩ := hn.1
    exact ⟨max j k,.cons (Ω.at_mono hj (le_max_left j k)) hn.2 (hk.mono (le_max_right j k))⟩
end TestedStack
end Candidates

namespace ComponentInterface

section
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

theorem identity_admissible {k : Nat} {e : J.Env (Ω.context k)}
    (he : J.images e = Expr.var ∘ Expr.reverseIndex k) : J.Admissible (U := U) e := by
  intro i B hi
  obtain ⟨s,hB⟩ := HasType.lookup_sorted (Ω.valid k) hi
  have ht := (J.typed e i B hi).normalize_type hw
  have hG : J.images e i ∈ Ground Ω (B.subst (J.images e)).normalForm := by
    rw [he] at ht ⊢
    exact var_ground _ ht
  exact ⟨fun _ => (J.candidate e (.sorted hB)).lower hG,
    fun _ => (ground_le_top hG).2,fun _ _ => hG⟩

@[simp] theorem identity_actual {k : Nat} {e : J.Env (Ω.context k)}
    (he : J.images e = Expr.var ∘ Expr.reverseIndex k) (T : Expr S) :
    (T.rename (Expr.reverseIndex k)).subst (J.images e) = T := by
  rw [he,Expr.subst_var_rename,Expr.reverseIndex_twice]

end

open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C) (H : Processed Ω U C)
include J H

theorem run_stack {k : Nat} {e : J.Env (Ω.context k)}
    (he : J.images e = Expr.var ∘ Expr.reverseIndex k)
    {T : Expr S} {ns : List (Expr S)} (hstack : StackAt Ω k T ns) :
    ∀ {s}, HasType P (Ω.context k) (T.rename (Expr.reverseIndex k)) (.sort s) →
    Normal T → Ω.profile T ∈ U ∨ Ω.profile T ∈ C →
    ∀ h, h ∈ J.R (T.rename (Expr.reverseIndex k)) e → StronglyNormalizing (h.apps ns) := by
  induction hstack with
  | nil T =>
      intro s ht hN _ h hr
      exact (J.candidate e (.sorted ht)).upper hr |>.2
  | @cons D E n ns hn hsn hstack ih =>
      intro s ht hN hprofile h hr
      have hactual : ActualType Ω (.pi D E) := .inl ⟨hN,s,⟨k,ht⟩⟩
      rcases hprofile with hU | hC
      · have htop := (J.candidate e (.sorted ht)).upper hr
        rw [J.identity_actual he,Expr.normalForm_of_normal hN] at htop
        have hg : h ∈ Ground Ω (.pi D E) := by
          rw [H.invariant hactual hU]; exact htop
        exact hg.2 (n :: ns) (.cons ⟨⟨k,hn⟩,hsn⟩ hstack.tested)
      · obtain ⟨a,b,c,hD,hE,_,_⟩ := ht.generation_pi
        have hnR := (J.sn_fundamental H (hsn.reverseIndex k) _ _ hn e
          (J.identity_admissible he)).1
        have hr' := J.specialization e ht hn (by
          change Profile P (Ω.context k) ((Expr.pi D E).rename (Expr.reverseIndex k)) ∈ C
          rwa [← Ω.profile_at hw ht])
          (by
            change Ω.profile (((Expr.pi D E).rename (Expr.reverseIndex k)).subst (J.images e)) ∈ C
            rwa [J.identity_actual he]) h hr hnR
        change Expr.app h ((n.rename (Expr.reverseIndex k)).subst (J.images e)) ∈
          J.R ((E.rename (Expr.liftRen (Expr.reverseIndex k))).instantiate
            (n.rename (Expr.reverseIndex k))) e at hr'
        rw [J.identity_actual he,Expr.instantiate_rename] at hr'
        have htarget : HasType P (Ω.context k) ((E.instantiate n).rename (Expr.reverseIndex k)) (.sort b) := by
          have hti := hE.instantiate hn
          change HasType P (Ω.context k) ((E.rename (Expr.liftRen (Expr.reverseIndex k))).instantiate
            (n.rename (Expr.reverseIndex k))) (.sort b) at hti
          rwa [Expr.instantiate_rename] at hti
        have htargetΩ : Ω.HasType (E.instantiate n) (.sort b) := ⟨k,htarget⟩
        have hwtarget := htargetΩ.weaklyNormalizing hw
        have htargetN : HasType P (Ω.context k) ((E.instantiate n).normalForm.rename (Expr.reverseIndex k)) (.sort b) := by
          rw [← Expr.normalForm_rename hwtarget]
          exact htarget.normalForm hw
        have hconv : Converts ((E.instantiate n).rename (Expr.reverseIndex k))
            ((E.instantiate n).normalForm.rename (Expr.reverseIndex k)) :=
          (Expr.normalForm_spec hwtarget).1.converts.rename _
        rw [J.conversion e (.sorted htarget) (.sorted htargetN) hconv] at hr'
        have hprofile' : Ω.profile (E.instantiate n).normalForm ∈ U ∨
            Ω.profile (E.instantiate n).normalForm ∈ C := by
          rw [Ω.profile_normalForm]
          exact H.before hC (Ω.profile_instantiate_product_path hw ⟨k,ht⟩ ⟨k,hn⟩).reach
        exact ih htargetN (Expr.normalForm_spec hwtarget).2 hprofile' (.app h n) hr'

/-- Advancing a component uses one identity evaluation, not a new
substitution choice at each stack prefix. -/
theorem advance {T : Expr S} (hT : ActualType Ω T) (hC : Ω.profile T ∈ C) :
    Ground Ω T = Top Ω T := by
  apply Set.Subset.antisymm ground_le_top
  intro h hh
  rcases hT with ⟨hN,s,ks,ht⟩ | ⟨s,rfl⟩
  · refine ⟨hh.1,?_⟩
    intro ns hstack
    obtain ⟨kn,hs⟩ := hstack.common_stage
    obtain ⟨kh,hhT⟩ := hh.1
    let k := max ks (max kn kh)
    have hkT : ks ≤ k := le_max_left _ _
    have hkN : kn ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
    have hkH : kh ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
    have ht' := Ω.at_mono ht hkT
    have hh' := Ω.at_mono hhT hkH
    obtain ⟨e,he⟩ := J.inhabit (.var ∘ Expr.reverseIndex k) (.identity k)
    have hr := (J.sn_fundamental H (hh.2.reverseIndex k) _ _ hh' e
      (J.identity_admissible he)).1
    rw [J.identity_actual he] at hr
    exact J.run_stack H he (hs.mono hkN) ht' hN (.inr hC) h hr
  · rwa [sort_ground_eq_top]

end ComponentInterface
end

universe u v
open Classical Candidates

namespace Beta
variable {S : Type u}
/-- Renaming cannot create a redex, and every renamed step has an exact source. -/
theorem rename_source {M N : Expr S} {ρ : Nat → Nat} (h : Beta (M.rename ρ) N) :
    ∃ M', Beta M M' ∧ N = M'.rename ρ := by
  induction M generalizing ρ N with
  | var n => cases h
  | sort s => cases h
  | pi A B ihA ihB =>
    cases h with
    | pi_domain hh =>
      obtain ⟨A',ha,rfl⟩ := ihA hh
      exact ⟨_,.pi_domain ha,rfl⟩
    | pi_body hh =>
      obtain ⟨B',hb,rfl⟩ := ihB hh
      exact ⟨_,.pi_body hb,rfl⟩
  | lam A b ihA ihb =>
    cases h with
    | lam_domain hh =>
      obtain ⟨A',ha,rfl⟩ := ihA hh
      exact ⟨_,.lam_domain ha,rfl⟩
    | lam_body hh =>
      obtain ⟨b',hb,rfl⟩ := ihb hh
      exact ⟨_,.lam_body hb,rfl⟩
  | app f a ihf iha =>
    cases f <;> cases h
    all_goals first
      | (rename_i hh
         obtain ⟨f',hf,rfl⟩ := ihf hh
         exact ⟨_,.app_left hf,rfl⟩)
      | (rename_i hh
         obtain ⟨a',ha,rfl⟩ := iha hh
         exact ⟨_,.app_right ha,rfl⟩)
      | exact ⟨_,.head _ _ _,Expr.instantiate_rename _ _ _⟩
end Beta
namespace StronglyNormalizing
variable {S : Type u} {M : Expr S}
theorem rename (h : StronglyNormalizing M) (ρ : Nat → Nat) :
    StronglyNormalizing (M.rename ρ) := by
  induction h with
  | intro M _ ih =>
    apply Acc.intro
    intro N hn
    obtain ⟨M',hm,rfl⟩ := hn.rename_source
    exact ih M' hm
end StronglyNormalizing

namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- Every valid finite context has a variable-valued interpretation in the
saturated tower. Substitution reflection does not require these names to be
surjective or even injective. -/
theorem variable_substitution {Γ : List (Expr S)} (hΓ : ValidContext P Γ) :
    ∃ ρ : Nat → Nat, Ω.TypedSubstitution Γ (Expr.var ∘ ρ) := by
  induction hΓ with
  | nil => exact ⟨id,fun _ _ h => nomatch h⟩
  | @cons Γ A s hΓ hA ih =>
    obtain ⟨ρ,hρ⟩ := ih
    have ht := HasType.subst hA hρ
    obtain ⟨n,_,hn⟩ := Ω.fresh_variable ht 0
    refine ⟨fun i => match i with | 0 => n | i+1 => ρ i,?_⟩
    convert hρ.cons hn using 1
    funext i; cases i <;> rfl

end ContextTower

/-- Finite primary-component induction. The supplied interfaces are consumed
one at a time, and Ground=Top is only used at strict predecessor components. -/
theorem all_ground_eq_top {S : Type u} [Fintype S] {P : Specification S}
    (Ω : ContextTower P) (hw : SystemWeaklyNormalizing P)
    (interfaces : ∀ C, IsComponent (PrimaryEdge P) C →
      Nonempty (ComponentInterface.{u,v} Ω hw C)) :
    ∀ {T}, ActualType Ω T → Ground Ω T = Top Ω T := by
  intro T hT
  let E := PrimaryEdge P
  have h : ∀ n, ∀ T : Expr S, Reach.rank E (Ω.profile T) = n → ActualType Ω T →
      Ground Ω T = Top Ω T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hr hT
      let V := Ω.profile T
      let C := Reach.component E V
      let U := {I | Reach.rank E I < n}
      have hC : IsComponent E C := Reach.component_isComponent E V
      have rankC {I} (hi : I ∈ C) : Reach.rank E I = n := by
        exact (Nat.le_antisymm (Reach.rank_mono E hi.2) (Reach.rank_mono E hi.1)).trans hr
      have hp : Processed Ω U C := by
        refine ⟨?_,?_,?_,?_⟩
        · apply Set.disjoint_left.mpr
          intro I hI hc
          have : Reach.rank E I < n := hI
          rw [rankC hc] at this
          exact Nat.lt_irrefl _ this
        · intro I J hj hij
          exact lt_of_le_of_lt (Reach.rank_mono E hij) hj
        · intro I J hj hij
          have hle : Reach.rank E I ≤ n := (Reach.rank_mono E hij).trans (le_of_eq (rankC hj))
          rcases lt_or_eq_of_le hle with hlt | heq
          · exact .inl hlt
          · exact .inr ⟨hj.1.trans (Reach.reverse_of_rank_eq E hij (heq.trans (rankC hj).symm)),
              hij.trans hj.2⟩
        · intro A hA hAu
          exact ih _ hAu A rfl hA
      obtain ⟨J⟩ := interfaces C hC
      exact J.advance hp hT (Reach.mem_component E V)
  exact h _ T rfl hT

/-- Once all actual types have Ground=Top, typed application preserves SN.
Types and annotations are normalized using WN, not assumed SN. -/
theorem application_sn_of_ground {S : Type u} {P : Specification S}
    (Ω : ContextTower P) (hw : SystemWeaklyNormalizing P)
    (hground : ∀ {T}, ActualType Ω T → Ground Ω T = Top Ω T)
    {Γ : List (Expr S)} {f a D E : Expr S}
    (hf : HasType P Γ f (.pi D E)) (ha : HasType P Γ a D)
    (hsf : StronglyNormalizing f) (hsa : StronglyNormalizing a) :
    StronglyNormalizing (.app f a) := by
  obtain ⟨ρ,hρ⟩ := Ω.variable_substitution hf.valid
  have hf' := ContextTower.HasType.subst hf hρ
  have ha' := ContextTower.HasType.subst ha hρ
  simp only [Expr.subst_var_rename] at hf' ha'
  obtain ⟨s,hpi⟩ := hf.product_type_sorted
  have hpi' := ContextTower.HasType.subst hpi hρ
  simp only [Expr.subst_var_rename,Expr.rename] at hpi'
  obtain ⟨a',b',c',hD,hE,hr,_⟩ := hpi.generation_pi
  have hDw := (ContextTower.HasType.subst hD hρ).weaklyNormalizing hw
  simp only [Expr.subst_var_rename] at hDw
  have hPw := hpi'.weaklyNormalizing hw
  have hDN : Normal (D.rename ρ).normalForm := (Expr.normalForm_spec hDw).2
  have hPN := (Expr.normalForm_spec hPw).2
  have hpNF : ((Expr.pi D E).rename ρ).normalForm =
      .pi (D.rename ρ).normalForm (E.rename (Expr.liftRen ρ)).normalForm := by
    apply Expr.normalForm_pi hDw
    obtain ⟨target, reduces, normal⟩ := hPw
    obtain ⟨domain, body, rfl, _, bodyReduces⟩ := Reduces.pi_inv reduces
    exact ⟨body, bodyReduces, normal.pi_body⟩
  have htype : ActualType Ω ((Expr.pi D E).rename ρ).normalForm :=
    .inl ⟨hPN,s,hpi'.normalForm hw⟩
  have hfg : f.rename ρ ∈ Ground Ω ((Expr.pi D E).rename ρ).normalForm := by
    rw [hground htype]
    exact ⟨hf'.normalize_type hw,hsf.rename ρ⟩
  rw [hpNF] at hfg
  have hag : a.rename ρ ∈ Top Ω (D.rename ρ).normalForm := ⟨ha'.normalize_type hw,hsa.rename ρ⟩
  have hs := (ground_le_top (ground_application hw hfg hag)).2
  exact StronglyNormalizing.of_rename ρ hs

end PureTypeSystem

end OAI
