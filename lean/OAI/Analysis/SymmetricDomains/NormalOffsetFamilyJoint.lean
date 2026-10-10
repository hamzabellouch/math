import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialSignSetInf

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
namespace Release061.SignElimination
open Set Metric Filter Topology Classical

lemma polynomialSignSet_preimage_of_graph {X ι κ : Type*} [Finite κ]
    {c : X → ι → ℝ} {B : Set X} {f : X → κ → ℝ} {T : Set (κ → ℝ)}
    (hf : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.1 ∈ B ∧ z.2 = f z.1}) (hT : PolynomialSignSet id T) :
    PolynomialSignSet c {x | x ∈ B ∧ f x ∈ T} := by
  have ht : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ T} :=
    hT.coordinate_preimage (fun z : X × (κ → ℝ) => z.2) Sum.inr (by intros; rfl)
  convert polynomialSignSet_projection_finite (hf.inter ht) using 1
  ext x
  simp only [mem_ofPred_eq,mem_inter_iff]
  constructor
  · rintro ⟨hx,hf⟩
    exact ⟨f x,⟨hx,rfl⟩,hf⟩
  · rintro ⟨y,⟨hx,rfl⟩,hy⟩
    exact ⟨hx,hy⟩

end Release061.SignElimination

namespace Release061.PolynomialSignSet
open Set Metric Filter Topology Classical SignElimination

lemma closure {κ : Type*} [Fintype κ] {A : Set (κ → ℝ)}
    (hA : PolynomialSignSet id A) : PolynomialSignSet id (closure A) := by
  by_cases hne : A.Nonempty
  · let d := fun z : (κ → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2
    have ha : PolynomialSignSet d {z | z.2 ∈ A} :=
      hA.coordinate_preimage (fun z : (κ → ℝ) × (κ → ℝ) => z.2) Sum.inr
        (by intros; rfl)
    have hg := polynomialSignSet_infDist_graph (c := id) (fun _ : κ → ℝ => A) ha
      (fun k => MvPolynomial.X k)
    have he : PolynomialSignSet id {x : κ → ℝ | 0 = infDist x A} := by
      convert hg.polynomial_preimage (fun x : κ → ℝ => (x,0))
        (fun o => Option.elim o 0 MvPolynomial.X) (d := id) ?_ using 1
      · ext x
        simp only [mem_preimage,mem_ofPred_eq,MvPolynomial.eval_X,id_eq]
      · intro x o
        cases o <;> simp
    convert he using 1
    ext x
    exact (mem_closure_iff_infDist_zero hne).trans eq_comm
  · rw [not_nonempty_iff_eq_empty.mp hne,closure_empty]
    exact .empty

lemma interior {κ : Type*} [Fintype κ] {A : Set (κ → ℝ)}
    (hA : PolynomialSignSet id A) : PolynomialSignSet id (interior A) := by
  simpa only [closure_compl,compl_compl] using hA.compl.closure.compl

lemma frontier {κ : Type*} [Fintype κ] {A : Set (κ → ℝ)}
    (hA : PolynomialSignSet id A) : PolynomialSignSet id (frontier A) := by
  rw [frontier_eq_closure_inter_closure]
  exact hA.closure.inter hA.compl.closure

end Release061.PolynomialSignSet

namespace Release061
open Set Metric Filter Topology Classical SignElimination

def normalOffsetFamily {ι κ : Type*} [Fintype κ]
    (U : Set ((ι → ℝ) × (κ → ℝ))) (B : Set (ι → ℝ))
    (φ : (ι → ℝ) → (κ → ℝ)) (ρ : ℝ) (s : ι → ℝ) : Set (κ → ℝ) :=
  {v | s ∈ B ∧ ‖v‖ < ρ ∧ (s,φ s+v) ∈ U}

lemma normalOffsetFamily_polynomialSignSet {ι κ : Type*} [Fintype κ]
    {U : Set ((ι → ℝ) × (κ → ℝ))} {B : Set (ι → ℝ)}
    {φ : (ι → ℝ) → (κ → ℝ)} (ρ : ℝ)
    (hU : PolynomialSignSet (fun z => Sum.elim z.1 z.2) U)
    (hφ : PolynomialSignSet (fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
      {z | z.1 ∈ B ∧ z.2 = φ z.1}) :
    PolynomialSignSet (fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 ∈ normalOffsetFamily U B φ ρ z.1} := by
  let c := fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2
  let d := fun z : ((ι → ℝ) × (κ → ℝ)) × (κ → ℝ) => Sum.elim (c z.1) z.2
  have hf : PolynomialSignSet d {z | z.1.1 ∈ B ∧ z.2 = φ z.1.1} :=
    hφ.coordinate_preimage (fun z : ((ι → ℝ) × (κ → ℝ)) × (κ → ℝ) => (z.1.1,z.2))
      (Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr) (by intro z i; cases i <;> rfl)
  have hu : PolynomialSignSet d {z | (z.1.1,z.2+z.1.2) ∈ U} :=
    hU.polynomial_preimage (fun z : ((ι → ℝ) × (κ → ℝ)) × (κ → ℝ) => (z.1.1,z.2+z.1.2))
      (Sum.elim (fun i => MvPolynomial.X (Sum.inl (Sum.inl i)))
        (fun k => MvPolynomial.X (Sum.inr k)+MvPolynomial.X (Sum.inl (Sum.inr k))))
      (by intro z i; cases i <;> simp [c,d])
  have hp : PolynomialSignSet c {z | z.1 ∈ B ∧ (z.1,φ z.1+z.2) ∈ U} := by
    convert polynomialSignSet_projection_finite (hf.inter hu) using 1
    ext z
    simp only [mem_ofPred_eq,mem_inter_iff]
    constructor
    · rintro ⟨hs,hu⟩
      exact ⟨φ z.1,⟨hs,rfl⟩,hu⟩
    · rintro ⟨y,⟨hs,rfl⟩,hu⟩
      exact ⟨hs,hu⟩
  have hn : PolynomialSignSet c {z | ‖z.2‖ < ρ} := by
    convert PolynomialSignSet.norm_lt_polynomial (c := c)
      (fun k : κ => MvPolynomial.X (Sum.inr k)) (MvPolynomial.C ρ) using 1
    ext z
    simp [c]
  convert hp.inter hn using 1
  ext z
  simp only [normalOffsetFamily,mem_ofPred_eq,mem_inter_iff]
  tauto

lemma normalOffsetFamily_isOpen {ι κ : Type*} [Fintype κ]
    {U : Set ((ι → ℝ) × (κ → ℝ))} (hU : IsOpen U) (B : Set (ι → ℝ))
    (φ : (ι → ℝ) → (κ → ℝ)) (ρ : ℝ) (s : ι → ℝ) :
    IsOpen (normalOffsetFamily U B φ ρ s) := by
  by_cases hs : s ∈ B
  · have hf : Continuous (fun v : κ → ℝ => (s,φ s+v)) :=
      continuous_const.prodMk (continuous_const.add continuous_id)
    have hn : IsOpen {v : κ → ℝ | ‖v‖ < ρ} := isOpen_lt continuous_norm continuous_const
    change IsOpen {v : κ → ℝ | s ∈ B ∧ ‖v‖ < ρ ∧ (s,φ s+v) ∈ U}
    simp only [hs,true_and]
    exact hn.inter (hU.preimage hf)
  · simp only [normalOffsetFamily,hs,false_and,ofPred_false,isOpen_empty]

lemma normalOffsetFamily_zero_not_mem {ι κ : Type*} [Fintype κ]
    {U : Set ((ι → ℝ) × (κ → ℝ))} {B : Set (ι → ℝ)}
    {φ : (ι → ℝ) → (κ → ℝ)} {ρ : ℝ} {s : ι → ℝ}
    (hs : (s,φ s) ∉ U) : (0 : κ → ℝ) ∉ normalOffsetFamily U B φ ρ s := by
  rintro ⟨_,_,h⟩
  exact hs (by simpa using h)

lemma normalOffsetFamily_joint_closure {ι κ : Type*} [Fintype κ]
    {U : Set ((ι → ℝ) × (κ → ℝ))} {B : Set (ι → ℝ)}
    {φ : (ι → ℝ) → (κ → ℝ)} {ρ : ℝ} {s : ι → ℝ}
    (hB : B ∈ 𝓝 s) (hφ : ContinuousAt φ s) (hρ : 0 < ρ)
    (hs : (s,φ s) ∈ closure U) :
    (s,(0 : κ → ℝ)) ∈ closure
      {z : (ι → ℝ) × (κ → ℝ) | z.2 ∈ normalOffsetFamily U B φ ρ z.1} := by
  let f : ((ι → ℝ) × (κ → ℝ)) → ((ι → ℝ) × (κ → ℝ)) :=
    fun p => (p.1,p.2-φ p.1)
  have hc : ContinuousAt f (s,φ s) :=
    continuousAt_fst.prodMk (continuousAt_snd.sub (hφ.comp continuousAt_fst))
  have he : f (s,φ s) = (s,0) := by simp [f]
  have hb : ∀ᶠ p : (ι → ℝ) × (κ → ℝ) in 𝓝 (s,φ s), p.1 ∈ B :=
    continuousAt_fst.preimage_mem_nhds hB
  have hn : ∀ᶠ p : (ι → ℝ) × (κ → ℝ) in 𝓝 (s,φ s), ‖p.2-φ p.1‖ < ρ := by
    have ht := hc.snd.norm.tendsto
    have hn := ht.eventually (Iio_mem_nhds (by simpa [f] using hρ))
    exact hn
  rw [← he,mem_closure_iff_frequently]
  apply hc.tendsto.frequently
  apply ((mem_closure_iff_frequently.mp hs).and_eventually (hb.and hn)).mono
  intro p hp
  change p.1 ∈ B ∧ ‖p.2-φ p.1‖ < ρ ∧ (p.1,φ p.1+(p.2-φ p.1)) ∈ U
  exact ⟨hp.2.1,hp.2.2,by simpa only [add_sub_cancel,Prod.mk.eta] using hp.1⟩

end Release061

end

end OAI
