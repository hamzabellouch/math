import Mathlib
import OAI.Analysis.SymmetricDomains.NormalOffsetFamilyJoint
import OAI.Analysis.SymmetricDomains.Pair

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
open Set Filter Topology MeasureTheory
open scoped Classical

structure NashPatch (n : ℕ) where
  dim : ℕ
  domain : Set (Fin dim → ℝ)
  isOpen_domain : IsOpen domain
  isConnected_domain : IsConnected domain
  semialgebraic_domain : PolynomialSignSet id domain
  toFun : (Fin dim → ℝ) → (Fin n → ℝ)
  semialgebraic_toFun : SemialgebraicOn domain toFun
  analytic_toFun : AnalyticOnNhd ℝ toFun domain
  injective_fderiv : ∀ x ∈ domain, Function.Injective (fderiv ℝ toFun x)

namespace NashPatch
variable {n : ℕ}

def image (p : NashPatch n) : Set (Fin n → ℝ) := p.toFun '' p.domain

lemma image_nonempty (p : NashPatch n) : p.image.Nonempty :=
  p.isConnected_domain.nonempty.image _

lemma image_connected (p : NashPatch n) : IsConnected p.image :=
  p.isConnected_domain.image _ p.analytic_toFun.continuousOn

lemma image_semialgebraic (p : NashPatch n) : PolynomialSignSet id p.image :=
  p.semialgebraic_toFun.image

lemma dim_le (p : NashPatch n) : p.dim ≤ n := by
  obtain ⟨x,hx⟩ := p.isConnected_domain.nonempty
  simpa using (fderiv ℝ p.toFun x).toLinearMap.finrank_le_finrank_of_injective (p.injective_fderiv x hx)

lemma image_mem_nhds_of_dim_eq (p : NashPatch n) (hdim : p.dim = n)
    {x : Fin p.dim → ℝ} (hx : x ∈ p.domain) : p.image ∈ 𝓝 (p.toFun x) := by
  let L := fderiv ℝ p.toFun x
  have hdim' : Module.finrank ℝ (Fin p.dim → ℝ) = Module.finrank ℝ (Fin n → ℝ) := by
    simpa using hdim
  let e := (L.toLinearMap.linearEquivOfInjective (p.injective_fderiv x hx) hdim').toContinuousLinearEquiv
  have he : (e : (Fin p.dim → ℝ) →L[ℝ] (Fin n → ℝ)) = L := by
    ext v
    rfl
  have hder : HasStrictFDerivAt p.toFun (e : (Fin p.dim → ℝ) →L[ℝ] (Fin n → ℝ)) x := by
    rw [he]
    exact (p.analytic_toFun x hx).hasStrictFDerivAt
  rw [← hder.map_nhds_eq_of_equiv]
  exact Filter.image_mem_map (p.isOpen_domain.mem_nhds hx)

lemma dim_lt_of_empty_interior (p : NashPatch n) {S : Set (Fin n → ℝ)}
    (hS : interior S = ∅) (hsub : p.image ⊆ S) : p.dim < n := by
  apply lt_of_le_of_ne p.dim_le
  intro he
  obtain ⟨x,hx⟩ := p.isConnected_domain.nonempty
  have hm : p.toFun x ∈ interior S := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (p.image_mem_nhds_of_dim_eq he hx) hsub)
  simp only [hS,mem_empty_iff_false] at hm

noncomputable def identity (B : Set (Fin n → ℝ)) (hB : IsOpen B) (hc : IsConnected B)
    (hs : PolynomialSignSet id B) : NashPatch n where
  dim := n
  domain := B
  isOpen_domain := hB
  isConnected_domain := hc
  semialgebraic_domain := hs
  toFun := id
  semialgebraic_toFun := SemialgebraicOn.identity hs
  analytic_toFun := analyticOnNhd_id
  injective_fderiv x _ := by simpa only [fderiv_id,ContinuousLinearMap.coe_id',id_eq] using Function.injective_id

noncomputable def restrict (p : NashPatch n) (C : Set (Fin p.dim → ℝ))
    (hC : IsOpen C) (hc : IsConnected C) (hs : PolynomialSignSet id C) (hCB : C ⊆ p.domain) :
    NashPatch n where
  dim := p.dim
  domain := C
  isOpen_domain := hC
  isConnected_domain := hc
  semialgebraic_domain := hs
  toFun := p.toFun
  semialgebraic_toFun := p.semialgebraic_toFun.mono hs hCB
  analytic_toFun := p.analytic_toFun.mono hCB
  injective_fderiv x hx := p.injective_fderiv x (hCB hx)

noncomputable def comp (p : NashPatch n) (q : NashPatch p.dim) (hqp : q.image ⊆ p.domain) :
    NashPatch n where
  dim := q.dim
  domain := q.domain
  isOpen_domain := q.isOpen_domain
  isConnected_domain := q.isConnected_domain
  semialgebraic_domain := q.semialgebraic_domain
  toFun := p.toFun ∘ q.toFun
  semialgebraic_toFun := p.semialgebraic_toFun.comp q.semialgebraic_toFun
    (fun x hx => hqp ⟨x,hx,rfl⟩)
  analytic_toFun x hx := (p.analytic_toFun _ (hqp ⟨x,hx,rfl⟩)).comp (q.analytic_toFun x hx)
  injective_fderiv x hx := by
    rw [fderiv_comp x (p.analytic_toFun _ (hqp ⟨x,hx,rfl⟩)).differentiableAt
      (q.analytic_toFun x hx).differentiableAt]
    exact (p.injective_fderiv _ (hqp ⟨x,hx,rfl⟩)).comp (q.injective_fderiv x hx)

lemma comp_image (p : NashPatch n) (q : NashPatch p.dim) (hqp : q.image ⊆ p.domain) :
    (p.comp q hqp).image = p.toFun '' q.image := by
  change (p.toFun ∘ q.toFun) '' q.domain = p.toFun '' (q.toFun '' q.domain)
  exact Set.image_comp _ _ _

end NashPatch

def HasFiniteNashCover {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ P : Finset (NashPatch n), ∀ x, x ∈ S ↔ ∃ p ∈ P, x ∈ p.image

namespace HasFiniteNashCover
variable {n : ℕ}

lemma empty : HasFiniteNashCover (∅ : Set (Fin n → ℝ)) := by
  exact ⟨∅,by simp⟩

lemma patch (p : NashPatch n) : HasFiniteNashCover p.image := by
  refine ⟨{p},?_⟩
  simp

lemma union {S T : Set (Fin n → ℝ)} (hS : HasFiniteNashCover S) (hT : HasFiniteNashCover T) :
    HasFiniteNashCover (S ∪ T) := by
  obtain ⟨P,hP⟩ := hS
  obtain ⟨Q,hQ⟩ := hT
  refine ⟨P ∪ Q,fun x => ?_⟩
  simp only [mem_union,hP,hQ,Finset.mem_union]
  aesop

lemma finite_union {α : Type*} (s : Finset α) {S : α → Set (Fin n → ℝ)}
    (hS : ∀ i ∈ s, HasFiniteNashCover (S i)) : HasFiniteNashCover (⋃ i ∈ s, S i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (empty (n := n))
  | @insert i s hi ih =>
    simpa only [Finset.mem_insert,ofPred_or,iUnion_iUnion_eq_or_left] using
      (hS i (Finset.mem_insert_self _ _)).union
        (ih (fun j hj => hS j (Finset.mem_insert_of_mem hj)))

end HasFiniteNashCover
end Release061

end

end OAI
