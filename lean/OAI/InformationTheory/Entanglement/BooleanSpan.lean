import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace FiniteConstruction
variable {α β 𝔽 : Type} [Fintype α] [DecidableEq α]
  [Field 𝔽]
variable (B : β → Finset α)

def monomial (s : Finset α) : β → 𝔽 := fun b => if s ⊆ B b then 1 else 0

def smallSets (α : Type) [Fintype α] [DecidableEq α] (d : ℕ) : Finset (Finset α) :=
  (Finset.range (d+1)).biUnion (fun j => Finset.univ.powersetCard j)
lemma mem_smallSets (s : Finset α) (d : ℕ) : s ∈ smallSets α d ↔ s.card ≤ d := by
  simp only [smallSets,Finset.mem_biUnion,Finset.mem_range,Finset.mem_powersetCard,
    Finset.subset_univ,true_and]
  constructor
  · rintro ⟨j,hj,he⟩
    omega
  · intro hs
    exact ⟨s.card,by omega,rfl⟩

def lowDegree (d : ℕ) : Submodule 𝔽 (β → 𝔽) :=
  Submodule.span 𝔽 (monomial (𝔽 := 𝔽) B '' (smallSets α d : Set (Finset α)))

lemma monomial_mem {s : Finset α} {d : ℕ} (hs : s.card ≤ d) :
    monomial (𝔽 := 𝔽) B s ∈ lowDegree B d := by
  exact Submodule.subset_span ⟨s,(mem_smallSets s d).mpr hs,rfl⟩
omit [Fintype α] in
lemma monomial_empty : monomial (𝔽 := 𝔽) B ∅=1 := by ext b; simp [monomial]
omit [Fintype α] in
lemma monomial_mul (s t : Finset α) :
    monomial (𝔽 := 𝔽) B s * monomial B t=monomial B (s ∪ t) := by
  ext b
  by_cases hs : s ⊆ B b <;> by_cases ht : t ⊆ B b <;>
    simp [monomial,Finset.union_subset_iff,hs,ht]
lemma coordinate_mul_mem {d : ℕ} {f : β → 𝔽} (hf : f ∈ lowDegree B d) (a : α) :
    monomial B {a} * f ∈ lowDegree B (d+1) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s,hs,rfl⟩ := hx
    rw [monomial_mul]
    apply monomial_mem
    have hc := (Finset.card_union_le ({a} : Finset α) s)
    have hd := (mem_smallSets s d).mp hs
    simp only [Finset.card_singleton] at hc
    omega
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [mul_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [mul_smul_comm] using Submodule.smul_mem _ c ih

lemma sum_power_mem (A : Finset α) (d : ℕ) :
    (∑ a ∈ A, monomial (𝔽 := 𝔽) B {a})^d ∈ lowDegree B d := by
  induction d with
  | zero => simpa only [pow_zero,monomial_empty] using
      (monomial_mem (𝔽 := 𝔽) B (s := ∅) (d := 0) (by simp))
  | succ d ih =>
    rw [pow_succ',Finset.sum_mul]
    exact Submodule.sum_mem _ (fun a _ => coordinate_mul_mem B ih a)

variable [Fintype β] [DecidableEq β]

lemma interpolation_dimension_bound (d : ℕ)
    (h : ∀ b : β, Pi.single b (1 : 𝔽) ∈ lowDegree B d) :
    Fintype.card β ≤ ∑ j ∈ Finset.range (d+1), (Fintype.card α).choose j := by
  have ht : lowDegree (𝔽 := 𝔽) B d=⊤ := by
    apply top_unique
    intro f hf
    have he : f=∑ b, f b • Pi.single b (1 : 𝔽) := by
      ext b
      simp [Pi.single_apply]
    rw [he]
    exact Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ (f b) (h b))
  classical
  have hd := finrank_span_finset_le_card (R := 𝔽)
    ((smallSets α d).image (monomial (𝔽 := 𝔽) B))
  have he : Submodule.span 𝔽 (((smallSets α d).image (monomial (𝔽 := 𝔽) B)) : Set (β → 𝔽))=
      lowDegree B d := by rw [Finset.coe_image]; rfl
  change Module.finrank 𝔽 (Submodule.span 𝔽 _) ≤ _ at hd
  rw [he,ht,finrank_top,Module.finrank_fintype_fun_eq_card] at hd
  refine hd.trans (Finset.card_image_le.trans ?_)
  calc
    (smallSets α d).card ≤ ∑ j ∈ Finset.range (d+1), ((Finset.univ : Finset α).powersetCard j).card := by
      exact Finset.card_biUnion_le
    _ = _ := by simp only [Finset.card_powersetCard,Finset.card_univ]
end FiniteConstruction

end

end OAI
