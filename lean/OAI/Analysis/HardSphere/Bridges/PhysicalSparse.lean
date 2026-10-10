import Mathlib
import OAI.Analysis.HardSphere.Geometry.SparseChecks
import OAI.Analysis.HardSphere.Bridges.PhysicalFactorChecks

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {V : I → Type*} [∀i,MeasurableSpace (V i)]

def physicalEdges (anchor : J → Torus L) :=
  Bool×{p : J×J // p.1≠p.2 ∧ torusDistance L (anchor p.1) (anchor p.2)≤21}

instance physicalEdges_fintype (anchor : J → Torus L) : Fintype (physicalEdges anchor) :=
  inferInstanceAs (Fintype (Bool×{p : J×J // p.1≠p.2 ∧ torusDistance L (anchor p.1) (anchor p.2)≤21}))

def physicalSparseChecks (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (owner : Bool → J → I) (path : ∀b j,V (owner b j) → allowed j)
    (hpath : ∀b j,Measurable (path b j)) : physicalEdges anchor → LocalCheck V :=
  factorPathCheck (L:=L) allowed owner Prod.fst (fun e ↦ e.2.val.1) (fun e ↦ e.2.val.2) path hpath r

omit [Fintype J] [DecidableEq J] in
lemma physicalSparseChecks_complete (r : ℝ) (hr : r≤1)
    (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (hconf : ∀j,∀f : allowed j,Confined (anchor j) (projectCurve L f.val))
    (owner : Bool → J → I) (path : ∀b j,V (owner b j) → allowed j)
    (hpath : ∀b j,Measurable (path b j)) (x : ∀i,V i)
    (hx : x∈retainedEvent (physicalSparseChecks r anchor allowed owner path hpath) Finset.univ) :
    ∀b j k,j≠k → ¬TrialCollision r (projectCurve L (path b k (x (owner b k))).val)
      (path b j (x (owner b j))).val := by
  intro b j k hjk
  by_cases hn : torusDistance L (anchor j) (anchor k)≤21
  · exact hx (b,⟨(j,k),hjk,hn⟩) (Finset.subset_univ _)
  · rintro ⟨s,hs⟩
    exact (not_le_of_gt (confined_far_avoid (anchor j) (anchor k)
      (projectCurve L (path b j (x (owner b j))).val)
      (projectCurve L (path b k (x (owner b k))).val)
      (hconf _ _) (hconf _ _) (lt_of_not_ge hn) hr s)) hs

lemma physicalSparseChecks_degree {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (anchor : J → Torus L) (center : I → Fin 3 → Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ center i=v)).card≤M)
    (owner : Bool → J → I) (howner : ∀b,Function.Injective (owner b))
    (hcenter : ∀b j,torusDistance L (anchor j) (gridCenter L (center (owner b j)))≤1)
    (i : I) :
    (Finset.univ.filter (fun e : physicalEdges anchor ↦ owner e.1 e.2.val.1=i ∨ owner e.1 e.2.val.2=i)).card≤4*(49^3*M) := by
  have hinj : Function.Injective (fun e : physicalEdges anchor ↦
      (e.1,(owner e.1 e.2.val.1,owner e.1 e.2.val.2))) := by
    rintro ⟨b,⟨⟨j,k⟩,h⟩⟩ ⟨b',⟨⟨j',k'⟩,h'⟩⟩ he
    have hb : b=b' := congrArg Prod.fst he
    subst b'
    have hj : j=j' := howner b (congrArg (fun p ↦ p.2.1) he)
    have hk : k=k' := howner b (congrArg (fun p ↦ p.2.2) he)
    subst j';subst k';rfl
  have hn : ∀e : physicalEdges anchor,
      torusDistance L (gridCenter L (center (owner e.1 e.2.val.1)))
        (gridCenter L (center (owner e.1 e.2.val.2)))≤23 := by
    intro e
    exact incident_centers_close anchor (fun j ↦ gridCenter L (center (owner e.1 j))) id
      (hcenter e.1) e.2.val.1 e.2.val.2 e.2.property.2
  have hd := physical_incident_degree L hL center M hm
    (fun e : physicalEdges anchor ↦ owner e.1 e.2.val.1)
    (fun e : physicalEdges anchor ↦ owner e.1 e.2.val.2) Prod.fst hinj hn i
  simp only [Fintype.card_bool] at hd
  omega

lemma physicalSparseChecks_insertion {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (r : ℝ) (anchor : J → Torus L) (center : I → Fin 3 → Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ center i=v)).card≤M)
    (allowed : J → Set C(Time,Point))
    (owner : Bool → J → I) (howner : ∀b,Function.Injective (owner b))
    (hcenter : ∀b j,torusDistance L (anchor j) (gridCenter L (center (owner b j)))≤1)
    (path : ∀b j,V (owner b j) → allowed j) (hpath : ∀b j,Measurable (path b j))
    (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞) (U : Finset I)
    (hdom : ∀b j,owner b j∈U → (μ (owner b j)).map (path b j)≤G • P j)
    (hq : ∀j k,j≠k → ∀g : allowed k,P j {f | TrialCollision r (projectCurve L g.val) f.val}≤q)
    (hsmall : a+(4*(49^3*M):ℕ)*(G*q)≤1) :
    UniformInsertionOn (physicalSparseChecks r anchor allowed owner path hpath) μ a U := by
  have hd : ∀i∈U,(Finset.univ.filter (fun e : physicalEdges anchor ↦
      owner e.1 e.2.val.1=i ∨ owner e.1 e.2.val.2=i)).card≤4*(49^3*M) := by
    intro i _
    exact physicalSparseChecks_degree hL anchor center M hm owner howner hcenter i
  exact factorPath_insertion (L:=L) allowed owner howner
    (fun e : physicalEdges anchor ↦ e.1)
    (fun e : physicalEdges anchor ↦ e.2.val.1)
    (fun e : physicalEdges anchor ↦ e.2.val.2)
    (fun e : physicalEdges anchor ↦ e.2.property.1) path hpath r μ P G q a
    (4*(49^3*M)) U hdom hq hd hsmall

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I → Type*} [∀i,MeasurableSpace (X i)]

def fiberEquiv {i j : I} (h : i=j) : X i ≃ᵐ X j := by
  subst j
  exact MeasurableEquiv.refl _
omit [Fintype I] [DecidableEq I] in
lemma fiberEquiv_pi {i j : I} (h : i=j) (x : ∀i,X i) : fiberEquiv h (x i)=x j := by
  subst j
  rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma fiberEquiv_self {i : I} (h : i=i) (x : X i) : fiberEquiv h x=x := rfl

variable (σ : Equiv.Perm I) (S : Finset I) (hfix : ∀i,i∉S → σ i=i)
omit [Fintype I] in
include hfix in
lemma move_mem_iff (i : I) : σ i∈S ↔ i∈S := by
  constructor
  · intro hi
    by_contra hn
    exact hn (by simpa only [hfix i hn] using hi)
  · intro hi
    by_contra hn
    have hf := hfix (σ i) hn
    have he := σ.injective hf
    exact hn (he.symm ▸ hi)

def routeOwner (label : J → I) (b : Bool) (j : J) : I := if b then σ (label j) else label j
omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
lemma routeOwner_injective (label : J → I) (hlabel : Function.Injective label) (b : Bool) :
    Function.Injective (routeOwner σ label b) := by
  cases b
  · exact hlabel
  · exact σ.injective.comp hlabel

def routePath (allowed : J → Set C(Time,Point)) (label : J → I)
    (get : ∀j,X (label j) → allowed j) (b : Bool) (j : J) :
    (X (routeOwner σ label b j)×X (σ.symm (routeOwner σ label b j))) → allowed j := by
  cases b
  · exact fun p ↦ get j p.1
  · exact fun p ↦ if h : label j∈S then
      get j (fiberEquiv (σ.symm_apply_apply (label j)) p.2)
    else get j (fiberEquiv (hfix (label j) h) p.1)

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routePath_measurable (allowed : J → Set C(Time,Point)) (label : J → I)
    (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j)) (b : Bool) (j : J) :
    Measurable (routePath σ S hfix allowed label get b j) := by
  cases b
  · exact (hg j).comp measurable_fst
  · by_cases h : label j∈S
    · simp only [routePath,dite_eq_left h]
      exact (hg j).comp ((fiberEquiv (σ.symm_apply_apply (label j))).measurable.comp measurable_snd)
    · simp only [routePath,dite_eq_right h]
      exact (hg j).comp ((fiberEquiv (hfix (label j) h)).measurable.comp measurable_fst)

def routeChecks (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (label : J → I) (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j)) :=
  physicalSparseChecks (V:=fun i ↦ X i×X (σ.symm i)) r anchor allowed (routeOwner σ label)
    (routePath σ S hfix allowed label get) (routePath_measurable σ S hfix allowed label get hg)

def primaryChecks (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (label : J → I) (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j)) :=
  physicalSparseChecks r anchor allowed (fun _ ↦ label) (fun _ ↦ get) (fun _ ↦ hg)

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routeChecks_primary (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (label : J → I) (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j))
    (u : Finset I) (p : ∀i,X i×X (σ.symm i))
    (hp : p∈retainedEvent (routeChecks σ S hfix r anchor allowed label get hg) u) :
    (fun i ↦ (p i).1)∈retainedEvent (primaryChecks r anchor allowed label get hg) u := by
  intro e he
  exact hp (false,e.2) he

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routePath_unselected (allowed : J → Set C(Time,Point)) (label : J → I)
    (get : ∀j,X (label j) → allowed j) (j : J) (hj : label j∉S)
    (p : ∀i,X i×X (σ.symm i)) :
    routePath σ S hfix allowed label get true j (p (routeOwner σ label true j))=
      get j (p (label j)).1 := by
  simp only [routePath,dite_eq_right hj]
  exact congrArg (get j) (fiberEquiv_pi (hfix (label j) hj) (fun i ↦ (p i).1))

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routeChecks_outside (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (label : J → I) (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j))
    (o : Finset I) (hso : Disjoint S o) (p : ∀i,X i×X (σ.symm i))
    (hp : (fun i ↦ (p i).1)∈retainedEvent (primaryChecks r anchor allowed label get hg) o) :
    p∈retainedEvent (routeChecks σ S hfix r anchor allowed label get hg) o := by
  intro e he
  rcases e with ⟨b,⟨⟨j,k⟩,hjk,hnear⟩⟩
  cases b
  · exact hp (false,⟨(j,k),hjk,hnear⟩) he
  · have hj : label j∉S := by
      intro hs
      exact Finset.disjoint_left.mp hso ((move_mem_iff σ S hfix (label j)).mpr hs)
        (he (by simp [routeChecks,physicalSparseChecks,factorPathCheck,dependentCheck,routeOwner]))
    have hk : label k∉S := by
      intro hs
      exact Finset.disjoint_left.mp hso ((move_mem_iff σ S hfix (label k)).mpr hs)
        (he (by simp [routeChecks,physicalSparseChecks,factorPathCheck,dependentCheck,routeOwner]))
    have he' : (primaryChecks r anchor allowed label get hg (false,⟨(j,k),hjk,hnear⟩)).support⊆o := by
      simpa [routeChecks,primaryChecks,physicalSparseChecks,factorPathCheck,dependentCheck,routeOwner,
        hfix (label j) hj,hfix (label k) hk] using he
    have hh := hp (false,⟨(j,k),hjk,hnear⟩) he'
    change ¬TrialCollision r (projectCurve L (routePath σ S hfix allowed label get true k
      (p (routeOwner σ label true k))).val) (routePath σ S hfix allowed label get true j
      (p (routeOwner σ label true j))).val
    rw [routePath_unselected σ S hfix allowed label get j hj,
      routePath_unselected σ S hfix allowed label get k hk]
    exact hh

end HardSphere.Bridge

end
end

end

end OAI
