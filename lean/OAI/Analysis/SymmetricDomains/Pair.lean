import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialSignSetFinite2

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
open SignElimination
open scoped Classical

def SemialgebraicOn {ι κ : Type*} (B : Set (ι → ℝ)) (f : (ι → ℝ) → (κ → ℝ)) : Prop :=
  PolynomialSignSet (fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
    {z | z.1 ∈ B ∧ z.2 = f z.1}

namespace SemialgebraicOn
variable {ι κ δ : Type*}
variable {B C : Set (ι → ℝ)} {f : (ι → ℝ) → (κ → ℝ)}

lemma domain [Finite κ] (h : SemialgebraicOn B f) : PolynomialSignSet id B := by
  simpa only [mem_ofPred_eq, exists_and_left, exists_eq, and_true, ofPred_mem_eq] using
    polynomialSignSet_projection_finite (c := id) h

lemma restrict (hf : SemialgebraicOn B f) (hC : PolynomialSignSet id C) :
    SemialgebraicOn (B ∩ C) f := by
  have hc := hC.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => z.1) Sum.inl
    (d := fun z => Sum.elim z.1 z.2) (by intro z i; rfl)
  unfold SemialgebraicOn at hf ⊢
  convert hf.inter hc using 1
  ext z
  simp only [mem_inter_iff,mem_ofPred_eq,mem_preimage]
  tauto

lemma mono (hf : SemialgebraicOn B f) (hC : PolynomialSignSet id C) (hCB : C ⊆ B) :
    SemialgebraicOn C f := by
  simpa only [inter_eq_right.mpr hCB] using hf.restrict hC

lemma congr (hf : SemialgebraicOn B f) {g : (ι → ℝ) → (κ → ℝ)} (hfg : EqOn f g B) :
    SemialgebraicOn B g := by
  have he : {z : (ι → ℝ) × (κ → ℝ) | z.1 ∈ B ∧ z.2 = f z.1} =
      {z | z.1 ∈ B ∧ z.2 = g z.1} := by
    ext z
    constructor <;> rintro ⟨hz,he⟩ <;> refine ⟨hz,?_⟩
    · exact he.trans (hfg hz)
    · exact he.trans (hfg hz).symm
  unfold SemialgebraicOn at hf ⊢
  exact he ▸ hf

lemma polynomial [Finite κ] (hB : PolynomialSignSet id B) (p : κ → MvPolynomial ι ℝ) :
    SemialgebraicOn B (fun x j => MvPolynomial.eval x (p j)) := by
  have hb := hB.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => z.1) Sum.inl
    (d := fun z => Sum.elim z.1 z.2) (by intro z i; rfl)
  have hj (j : κ) : PolynomialSignSet (fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 j = MvPolynomial.eval z.1 (p j)} := by
    convert PolynomialSignSet.zero (c := fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
      (MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (p j)) using 1
    ext z
    simp [MvPolynomial.eval_rename,sub_eq_zero]
  unfold SemialgebraicOn
  convert hb.inter (PolynomialSignSet.forall_finite _ hj) using 1
  ext z
  simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,funext_iff]

lemma identity [Finite ι] (hB : PolynomialSignSet id B) : SemialgebraicOn B (id : (ι → ℝ) → _) := by
  exact (polynomial hB (MvPolynomial.X (R := ℝ))).congr (fun x _ => by
    funext j
    simp)

lemma constant [Finite κ] (hB : PolynomialSignSet id B) (v : κ → ℝ) :
    SemialgebraicOn B (fun _ => v) := by
  simpa only [MvPolynomial.eval_C] using polynomial hB (fun j => MvPolynomial.C (v j))

lemma preimage [Finite κ] (hf : SemialgebraicOn B f) {S : Set (κ → ℝ)} (hS : PolynomialSignSet id S) :
    PolynomialSignSet id (B ∩ f ⁻¹' S) := by
  have hs := hS.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => z.2) Sum.inr
    (d := fun z => Sum.elim z.1 z.2) (by intro z i; rfl)
  have hh := polynomialSignSet_projection_finite (c := id) (hf.inter hs)
  convert hh using 1
  ext x
  simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨f x,⟨h.1,rfl⟩,h.2⟩
  · rintro ⟨y,⟨hx,rfl⟩,hy⟩
    exact ⟨hx,hy⟩

lemma image [Finite ι] (hf : SemialgebraicOn B f) : PolynomialSignSet id (f '' B) := by
  have hh := polynomialSignSet_projection_finite (c := id)
    (hf.coordinate_preimage (fun z : (κ → ℝ) × (ι → ℝ) => (z.2,z.1))
      (Sum.swap) (d := fun z => Sum.elim z.1 z.2) (by intro z i; cases i <;> rfl))
  convert hh using 1
  ext y
  simp only [mem_image,mem_preimage,mem_ofPred_eq,eq_comm]

lemma comp [Finite κ] {D : Set (κ → ℝ)} {g : (κ → ℝ) → (δ → ℝ)}
    (hg : SemialgebraicOn D g) (hf : SemialgebraicOn B f) (hBD : MapsTo f B D) :
    SemialgebraicOn B (g ∘ f) := by
  let c : ((ι → ℝ) × (δ → ℝ)) → (ι ⊕ δ) → ℝ := fun z => Sum.elim z.1 z.2
  have hf' := hf.coordinate_preimage
    (fun z : ((ι → ℝ) × (δ → ℝ)) × (κ → ℝ) => (z.1.1,z.2))
    (Sum.map Sum.inl id) (d := fun z => Sum.elim (c z.1) z.2)
    (by intro z i; cases i <;> rfl)
  have hg' := hg.coordinate_preimage
    (fun z : ((ι → ℝ) × (δ → ℝ)) × (κ → ℝ) => (z.2,z.1.2))
    (Sum.elim Sum.inr (fun j => Sum.inl (Sum.inr j)))
    (d := fun z => Sum.elim (c z.1) z.2) (by intro z i; cases i <;> rfl)
  have hh := polynomialSignSet_projection_finite (c := c) (hf'.inter hg')
  unfold SemialgebraicOn
  convert hh using 1
  ext z
  simp only [mem_preimage,mem_ofPred_eq,mem_inter_iff,Function.comp_apply]
  constructor
  · rintro ⟨hz,he⟩
    exact ⟨f z.1,⟨hz,rfl⟩,hBD hz,he⟩
  · rintro ⟨y,⟨hz,rfl⟩,_,he⟩
    exact ⟨hz,he⟩

lemma pair {g : (ι → ℝ) → (δ → ℝ)} (hf : SemialgebraicOn B f) (hg : SemialgebraicOn B g) :
    SemialgebraicOn B (fun x => Sum.elim (f x) (g x)) := by
  have hf' := hf.coordinate_preimage
    (fun z : (ι → ℝ) × ((κ ⊕ δ) → ℝ) => (z.1,fun j => z.2 (Sum.inl j)))
    (Sum.map id Sum.inl) (d := fun z => Sum.elim z.1 z.2)
    (by intro z i; cases i <;> rfl)
  have hg' := hg.coordinate_preimage
    (fun z : (ι → ℝ) × ((κ ⊕ δ) → ℝ) => (z.1,fun j => z.2 (Sum.inr j)))
    (Sum.map id Sum.inr) (d := fun z => Sum.elim z.1 z.2)
    (by intro z i; cases i <;> rfl)
  unfold SemialgebraicOn
  convert hf'.inter hg' using 1
  ext z
  simp only [mem_preimage,mem_ofPred_eq,mem_inter_iff]
  constructor
  · rintro ⟨hz,he⟩
    refine ⟨⟨hz,?_⟩,hz,?_⟩ <;> rw [he] <;> rfl
  · rintro ⟨⟨hz,hf⟩,_,hg⟩
    refine ⟨hz,funext fun i => ?_⟩
    cases i with
    | inl i => exact congrFun hf i
    | inr i => exact congrFun hg i

end SemialgebraicOn
end Release061

end

end OAI
