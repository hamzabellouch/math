import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.Projection
import OAI.Combinatorics.SharpRamsey.Marking.MultiplicityClass

namespace OAI

section
namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset SharpLogRamsey.Incidence SharpLogRamsey.Projection
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def center (W : Submodule K V) (hW : Module.finrank K W + 1 = Module.finrank K V) :
    Projectivization K (Module.Dual K V) :=
  Projectivization.mk'' W.dualAnnihilator (by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    omega)

lemma center_submodule (W : Submodule K V)
    (hW : Module.finrank K W + 1 = Module.finrank K V) :
    (center W hW).submodule = W.dualAnnihilator := by
  simp [center]

lemma restrict_ne_zero (W : Submodule K V)
    (hW : Module.finrank K W + 1 = Module.finrank K V)
    (t : Projectivization K (Module.Dual K V)) (ht : t ≠ center W hW) :
    W.dualRestrict t.rep ≠ 0 := by
  intro h
  apply ht
  apply (rep_mem_line_iff t (center W hW)).mp
  rw [center_submodule, ← W.dualRestrict_ker_eq_dualAnnihilator]
  exact h

def restrict (W : Submodule K V)
    (hW : Module.finrank K W + 1 = Module.finrank K V)
    (t : {t : Projectivization K (Module.Dual K V) // t ≠ center W hW}) :
    Projectivization K (Module.Dual K W) :=
  Projectivization.mk K (W.dualRestrict t.val.rep) (restrict_ne_zero W hW t.val t.property)

lemma restrict_eq_project (W : Submodule K V)
    (hW : Module.finrank K W + 1 = Module.finrank K V)
    (t u : {t : Projectivization K (Module.Dual K V) // t ≠ center W hW})
    (he : restrict W hW t = restrict W hW u) :
    project (center W hW) t = project (center W hW) u := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp he
  have hz : t.val.rep - a • u.val.rep ∈ (center W hW).submodule := by
    rw [center_submodule, ← W.dualRestrict_ker_eq_dualAnnihilator]
    change W.dualRestrict (t.val.rep-a • u.val.rep)=0
    rw [map_sub,map_smul,← ha,sub_self]
  unfold project
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨a,?_⟩
  change a • (center W hW).submodule.mkQ u.val.rep = _
  have hh : (center W hW).submodule.mkQ (t.val.rep-a • u.val.rep)=0 := by
    change _ ∈ LinearMap.ker (center W hW).submodule.mkQ
    rwa [Submodule.ker_mkQ]
  rw [map_sub,map_smul,sub_eq_zero] at hh
  exact hh.symm

omit [FiniteDimensional K V] in
lemma incident_mk_left (v : V) (hv : v ≠ 0)
    (f : Projectivization K (Module.Dual K V)) :
    SharpLogRamsey.Incidence.Incident (Projectivization.mk K v hv) f ↔ f.rep v=0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  unfold SharpLogRamsey.Incidence.Incident
  rw [←ha]
  simp [Units.smul_def]

omit [FiniteDimensional K V] in
lemma incident_mk_right (p : Projectivization K V) (f : Module.Dual K V) (hf : f ≠ 0) :
    SharpLogRamsey.Incidence.Incident p (Projectivization.mk K f hf) ↔ f p.rep=0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K f hf
  unfold SharpLogRamsey.Incidence.Incident
  rw [←ha]
  simp [Units.smul_def]

lemma restrict_incident_iff (W : Submodule K V)
    (hW : Module.finrank K W + 1 = Module.finrank K V)
    (a : Projectivization K W)
    (t : {t : Projectivization K (Module.Dual K V) // t ≠ center W hW}) :
    SharpLogRamsey.Incidence.Incident a (restrict W hW t) ↔
      SharpLogRamsey.Incidence.Incident (Projectivization.map W.subtype W.injective_subtype a) t.val := by
  rw [restrict,incident_mk_right]
  conv_rhs => rw [←a.mk_rep,Projectivization.map_mk,incident_mk_left]
  rfl

variable [Finite K] [Fintype (Projectivization K (Module.Dual K V))]

theorem restrict_fiber_card (W : Submodule K V)
    (hW : Module.finrank K W + 1 = Module.finrank K V)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (b : Projectivization K (Module.Dual K W)) :
    ((A.subtype (· ≠ center W hW)).filter (fun t => restrict W hW t=b)).card ≤ Nat.card K := by
  let F := (A.subtype (· ≠ center W hW)).filter (fun t => restrict W hW t=b)
  by_cases hF : F.Nonempty
  · obtain ⟨t,ht⟩ := hF
    apply le_trans _ (project_fiber_card A (center W hW) (project (center W hW) t))
    apply card_le_card
    intro u hu
    obtain ⟨hu,hue⟩ := mem_filter.mp hu
    apply mem_filter.mpr ⟨hu,?_⟩
    exact restrict_eq_project W hW u t (hue.trans (mem_filter.mp ht).2.symm)
  · change F.card ≤ _
    rw [not_nonempty_iff_eq_empty.mp hF]
    simp

end
end SharpLogRamsey.HeavyPlaneRestriction

namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset SharpLogRamsey.Incidence SharpLogRamsey.Projection
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma center_restrict_zero (W : Submodule K V)
    (hW : Module.finrank K W+1=Module.finrank K V) :
    W.dualRestrict (center W hW).rep=0 := by
  have hm : (center W hW).rep ∈ (center W hW).submodule :=
    (rep_mem_line_iff _ _).mpr rfl
  rw [center_submodule,←W.dualRestrict_ker_eq_dualAnnihilator] at hm
  exact hm

lemma center_incident (W : Submodule K V)
    (hW : Module.finrank K W+1=Module.finrank K V) (a : Projectivization K W) :
    SharpLogRamsey.Incidence.Incident (Projectivization.map W.subtype W.injective_subtype a) (center W hW) := by
  rw [←a.mk_rep,Projectivization.map_mk,incident_mk_left]
  have he := congrArg (fun f : Module.Dual K W => f a.rep) (center_restrict_zero W hW)
  exact he

lemma sparse_noncentral (W : Submodule K V)
    (hW : Module.finrank K W+1=Module.finrank K V)
    (S : Finset (Projectivization K W)) (hS : S.Nonempty)
    (t : Projectivization K (Module.Dual K V)) (δ : ℝ) (hδ : δ<1)
    (hs : ((S.filter (fun a => SharpLogRamsey.Incidence.Incident (Projectivization.map W.subtype W.injective_subtype a) t)).card:ℝ)
      ≤δ*S.card) : t≠center W hW := by
  intro ht
  subst t
  have hf : S.filter (fun a => SharpLogRamsey.Incidence.Incident (Projectivization.map W.subtype W.injective_subtype a)
      (center W hW))=S := filter_eq_self.mpr (fun a _ => center_incident W hW a)
  rw [hf] at hs
  have hp : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  nlinarith

variable [Finite K] [Fintype (Projectivization K (Module.Dual K V))]

theorem sparse_restriction_class (W : Submodule K V)
    (hW : Module.finrank K W+1=Module.finrank K V)
    (S : Finset (Projectivization K W)) (hS : S.Nonempty)
    (T U : Finset (Projectivization K (Module.Dual K V)))
    (hT : T.Nonempty) (hTU : T⊆U) (δ : ℝ) (hδ : δ<1)
    (hs : ∀ t∈T,((S.filter (fun a => SharpLogRamsey.Incidence.Incident
      (Projectivization.map W.subtype W.injective_subtype a) t)).card:ℝ)≤δ*S.card) :
    ∃ (h : ℕ) (T₁ U₁ : Finset (Projectivization K (Module.Dual K W))),
      1≤h ∧ h≤Nat.card K ∧ T₁.Nonempty ∧ T₁⊆U₁ ∧
      h*U₁.card≤U.card ∧
      (T.card:ℝ)≤2*h*(Nat.log 2 (Nat.card K)+1:ℕ)*(T₁.card:ℝ) ∧
      (∀ t∈T₁,((S.filter (fun a => SharpLogRamsey.Incidence.Incident a t)).card:ℝ)≤δ*S.card) ∧
      U₁=MultiplicityClass.domain (U.subtype (· ≠ center W hW)) (restrict W hW) h := by
  have hn : ∀ t∈T,t≠center W hW := fun t ht => sparse_noncentral W hW S hS t δ hδ (hs t ht)
  let A := T.subtype (· ≠ center W hW)
  let B := U.subtype (· ≠ center W hW)
  have hA : A.Nonempty := by
    obtain ⟨t,ht⟩ := hT
    exact ⟨⟨t,hn t ht⟩,mem_subtype.mpr ht⟩
  have hAB : A⊆B := fun t ht => mem_subtype.mpr (hTU (mem_subtype.mp ht))
  have hAc : A.card=T.card := by
    rw [card_subtype,filter_eq_self.mpr hn]
  have hBc : B.card≤U.card := by rw [card_subtype]; exact card_filter_le _ _
  have hq : 1≤Nat.card K := (Finite.one_lt_card : 1<Nat.card K).le
  obtain ⟨h,T₁,hh,hq',hT₁,hsub,himage,hsize,hweights⟩ :=
    MultiplicityClass.exists_class A B hA hAB (restrict W hW) (Nat.card K) hq
      (fun t => restrict_fiber_card W hW T t)
  refine ⟨h,T₁,MultiplicityClass.domain B (restrict W hW) h,hh,hq',hT₁,hsub,
    (MultiplicityClass.domain_card B (restrict W hW) h).trans hBc,?_,?_,rfl⟩
  · rwa [hAc] at hsize
  · intro t ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp (himage ht)
    have hs' := hs u.val (mem_subtype.mp hu)
    have he : S.filter (fun a => SharpLogRamsey.Incidence.Incident a (restrict W hW u))=
      S.filter (fun a => SharpLogRamsey.Incidence.Incident (Projectivization.map W.subtype W.injective_subtype a) u.val) := by
      apply filter_congr
      intro a ha
      exact restrict_incident_iff W hW a u
    rwa [he]

end
end SharpLogRamsey.HeavyPlaneRestriction

end

end OAI
