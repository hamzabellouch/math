import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticNashRefinement
import OAI.Analysis.SymmetricDomains.AffineBand

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

lemma hasFiniteNashCover_graph {n : ℕ} {B : Set (Fin n → ℝ)}
    {a : (Fin n → ℝ) → (Fin 1 → ℝ)} (hs : SemialgebraicOn B a)
    (hc : HasAnalyticNashCover B a) :
    HasFiniteNashCover {y : Fin (n+1) → ℝ | Fin.tail y ∈ B ∧ y 0 = a (Fin.tail y) 0} := by
  obtain ⟨P,hP,haP⟩ := hc
  have hsub (p : {p // p ∈ P}) : MapsTo p.val.toFun p.val.domain B := by
    intro x hx
    exact (hP _).mpr ⟨p,p.property,x,hx,rfl⟩
  let g (p : {p // p ∈ P}) := p.val.graph (a ∘ p.val.toFun)
    (hs.comp p.val.semialgebraic_toFun (hsub p)) (haP p p.property)
  refine ⟨P.attach.image g,fun y => ?_⟩
  constructor
  · rintro ⟨hy,he⟩
    obtain ⟨p,hp,x,hx,hxy⟩ := (hP _).mp hy
    refine ⟨g ⟨p,hp⟩,Finset.mem_image.mpr ⟨⟨p,hp⟩,by simp,rfl⟩,x,hx,?_⟩
    change Fin.cons (a (p.toFun x) 0) (p.toFun x) = y
    rw [hxy,← he,Fin.cons_self_tail]
  · rintro ⟨q,hq,x,hx,hxy⟩
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hq
    change Fin.cons (a (p.val.toFun x) 0) (p.val.toFun x) = y at hxy
    subst y
    exact ⟨hsub p hx,rfl⟩

lemma hasFiniteNashCover_affineBand {n : ℕ} {B : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → (Fin 2 → ℝ)} (hs : SemialgebraicOn B f)
    (hc : HasAnalyticNashCover B f) (hb : ∀ x ∈ B, f x 1 ≠ 0)
    (I : Set ℝ) (hI : IsOpen I) (hcI : IsConnected I)
    (hsI : PolynomialSignSet (fun t : ℝ => fun _ : Fin 1 => t) I) :
    HasFiniteNashCover {y : Fin (n+1) → ℝ | Fin.tail y ∈ B ∧
      ∃ t ∈ I, y 0 = f (Fin.tail y) 0 + f (Fin.tail y) 1 * t} := by
  obtain ⟨P,hP,haP⟩ := hc
  have hsub (p : {p // p ∈ P}) : MapsTo p.val.toFun p.val.domain B := by
    intro x hx
    exact (hP _).mpr ⟨p,p.property,x,hx,rfl⟩
  let a (p : {p // p ∈ P}) := fun x : Fin p.val.dim → ℝ => fun _ : Fin 1 => f (p.val.toFun x) 0
  let b (p : {p // p ∈ P}) := fun x : Fin p.val.dim → ℝ => fun _ : Fin 1 => f (p.val.toFun x) 1
  have hsa (p : {p // p ∈ P}) : SemialgebraicOn p.val.domain (a p) :=
    (hs.comp p.val.semialgebraic_toFun (hsub p)).reindex (fun _ => 0)
  have hsb (p : {p // p ∈ P}) : SemialgebraicOn p.val.domain (b p) :=
    (hs.comp p.val.semialgebraic_toFun (hsub p)).reindex (fun _ => 1)
  have haa (p : {p // p ∈ P}) : AnalyticOnNhd ℝ (a p) p.val.domain := by
    intro x hx
    exact analyticAt_pi_iff.mpr (fun _ => analyticAt_pi_iff.mp (haP p p.property x hx) 0)
  have hab (p : {p // p ∈ P}) : AnalyticOnNhd ℝ (b p) p.val.domain := by
    intro x hx
    exact analyticAt_pi_iff.mpr (fun _ => analyticAt_pi_iff.mp (haP p p.property x hx) 1)
  let g (p : {p // p ∈ P}) := p.val.affineBand I hI hcI hsI (a p) (b p)
    (hsa p) (hsb p) (haa p) (hab p) (fun x hx => hb _ (hsub p hx))
  refine ⟨P.attach.image g,fun y => ?_⟩
  constructor
  · rintro ⟨hy,t,ht,he⟩
    obtain ⟨p,hp,x,hx,hxy⟩ := (hP _).mp hy
    refine ⟨g ⟨p,hp⟩,Finset.mem_image.mpr ⟨⟨p,hp⟩,by simp,rfl⟩,Fin.cons t x,⟨hx,ht⟩,?_⟩
    change Fin.cons (f (p.toFun x) 0 + f (p.toFun x) 1 * t) (p.toFun x) = y
    rw [hxy,← he,Fin.cons_self_tail]
  · rintro ⟨q,hq,x,hx,hxy⟩
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hq
    change Fin (p.val.dim+1) → ℝ at x
    change Fin.cons (f (p.val.toFun (Fin.tail x)) 0 + f (p.val.toFun (Fin.tail x)) 1 * x 0)
      (p.val.toFun (Fin.tail x)) = y at hxy
    subst y
    exact ⟨hsub p hx.1,x 0,hx.2,rfl⟩

end Release061

end

end OAI
