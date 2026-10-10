import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.GoodRealization

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]
lemma Law.eq_of_integrals (p q : Law A)
    (h : ∀ f : A→ℝ,(∑ a,p.mass a*f a)=∑ a,q.mass a*f a) : p=q := by
  ext a
  simpa using h (fun x=>if x=a then 1 else 0)
end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.ActualPivot
open Finset Selection
open scoped Classical BigOperators
noncomputable section
variable {K V I Y₀ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  {d : ℕ} {b : ℝ} [Fintype Y₀]

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma Realization.integral {q : Law Y₀} (e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q)
    (f : Y₀→ℝ) : (∑ ω,e.μ.mass ω*f (e.source ω))=∑ y,q.mass y*f y := by
  rw [←e.μ.sum_map e.source f,e.marginal]

variable {Θ : Type} [Fintype Θ] {Y : Θ→Type} [∀ θ,Fintype (Y θ)]

def Realization.mix (ν : Law Θ) (q : ∀ θ,Law (Y θ))
    (e : ∀ θ : {θ // ν.mass θ≠0},Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) (q θ)) :
    Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) (ν.sigma q) where
  Ω := Σ θ : {θ // ν.mass θ≠0},(e θ).Ω
  inst := inferInstance
  μ := ν.nullFree.sigma (fun θ=>(e θ).μ)
  source ω := ⟨ω.1.val,(e ω.1).source ω.2⟩
  supports ω := (e ω.1).supports ω.2
  marginal := by
    apply Law.eq_of_integrals
    intro f
    rw [Law.sum_map,Law.sigma_sum,Law.sigma_sum]
    calc
      _ = ∑ z,ν.nullFree.mass z*∑ y,(q z).mass y*f ⟨z.val,y⟩ := by
        apply sum_congr rfl
        intro z _
        congr 1
        exact (e z).integral (fun y=>f ⟨z.val,y⟩)
      _ = _ := ν.nullFree_integral (fun θ=>∑ y,(q θ).mass y*f ⟨θ,y⟩)

def Realization.attach {Ω B : Type} [Fintype Ω] [Fintype B]
    {q : Law Y₀} (e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q)
    (p : Law Ω) (tag : Y₀→B) (g : Ω→B)
    (h : q.map tag=p.map g) :
    Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) p where
  Ω := Σ _x : e.Ω,Ω
  inst := inferInstance
  μ := e.μ.attach p (tag∘e.source) g
  source ω := ω.2
  supports ω := e.supports ω.1
  marginal := by
    apply Law.eq_of_integrals
    intro f
    rw [Law.sum_map]
    apply Law.attach_source
    rw [←Law.map_map,e.marginal,h]

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma Realization.attach_agrees {Ω B : Type} [Fintype Ω] [Fintype B]
    {q : Law Y₀} (e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q)
    (p : Law Ω) (tag : Y₀→B) (g : Ω→B) (h : q.map tag=p.map g)
    (ω : (e.attach p tag g h).Ω) (hω : (e.attach p tag g h).μ.mass ω≠0) :
    e.μ.mass ω.1≠0 ∧ p.mass ω.2≠0 ∧ g ω.2=tag (e.source ω.1) := by
  apply Law.attach_support e.μ p (tag∘e.source) g _ ω hω
  rw [←Law.map_map,e.marginal,h]
end
end SharpLogRamsey.ActualPivot

namespace SharpLogRamsey.Selection.ExposureModel
open Finset
open scoped Classical BigOperators
noncomputable section
variable {β C ι Θ Ω : Type} [Fintype β] [Fintype C] [Fintype ι]
  [DecidableEq ι] [Fintype Θ] [Fintype Ω]

lemma afterDraw_tagged_map (n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→ι→β) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z) :
    ((contextual n k p θ G e own t).afterDraw hp).joint.map
      (fun x=>(x.1.1.1,(contextual n k p θ G e own t).restore x.1.1 x.2))=
        p.map (fun ω=>(θ ω,G ω)) := by
  rw [←contextual_tagged_map n k p θ G e own t]
  apply Law.eq_of_integrals
  intro f
  rw [Law.sum_map,Law.sum_map]
  let M:=contextual n k p θ G e own t
  change (∑ x,((M.freshLaw hp).sigma (fun z=>M.tupleLaw z.1)).mass x*
      f (x.1.1.1,M.restore x.1.1 x.2))=
        ∑ x,(M.historyLaw.sigma M.tupleLaw).mass x*f (x.1.1,M.restore x.1 x.2)
  rw [Law.sigma_sum,Law.sigma_sum]
  exact M.freshLaw_old hp (fun z=>∑ y,(M.tupleLaw z).mass y*f (z.1,M.restore z y))
end
end SharpLogRamsey.Selection.ExposureModel

end

end OAI
