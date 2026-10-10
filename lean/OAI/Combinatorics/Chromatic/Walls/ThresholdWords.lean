import Mathlib

namespace OAI

section
namespace ElementaryPositivity.ThresholdWords
noncomputable section
attribute [local instance] Classical.propDecidable
variable {A : Type*} (P : A → Prop) (μ : A → ℝ)

abbrev Word := {l : List A // (∀x∈l,P x) ∧ l.Pairwise (fun x y=>μ y<μ x)}
abbrev High (θ : ℝ) := {l : Word P μ // ∀x∈l.val,θ<μ x}
abbrev Low (θ : ℝ) := {l : Word P μ // ∀x∈l.val,μ x≤θ}

lemma ordered_filter_partition (θ : ℝ) (l : List A)
    (hl : l.Pairwise (fun x y=>μ y<μ x)) :
    l.filter (fun x=>decide (θ<μ x)) ++ l.filter (fun x=>decide (μ x≤θ))=l := by
  induction l with
  | nil=>rfl
  | cons x l ih=>
    have hp:=List.pairwise_cons.mp hl
    by_cases hx : θ<μ x
    · simpa only [List.filter_cons,decide_eq_true hx,decide_eq_false (not_le.mpr hx),
        Bool.false_eq_true,ite_true,ite_false,List.cons_append] using congrArg (List.cons x) (ih hp.2)
    · have hx' : μ x≤θ := le_of_not_gt hx
      have hall : ∀y∈l,μ y≤θ := fun y hy=>(hp.1 y hy).le.trans hx'
      have H : l.filter (fun x=>decide (θ<μ x))=[] := by
        simp only [List.filter_eq_nil_iff,decide_eq_true_eq]
        exact fun y hy=>not_lt.mpr (hall y hy)
      have L : l.filter (fun x=>decide (μ x≤θ))=l := by
        apply List.filter_eq_self.mpr
        simpa only [decide_eq_true_eq] using hall
      simp only [List.filter_cons,decide_eq_false hx,decide_eq_true hx',Bool.false_eq_true,ite_true,ite_false,H,L,List.nil_append]

def high (θ : ℝ) (l : Word P μ) : High P μ θ :=
  ⟨⟨l.val.filter (fun x=>decide (θ<μ x)),
    ⟨fun x hx=>l.property.1 x (List.mem_of_mem_filter hx),
      l.property.2.sublist List.filter_sublist⟩⟩,
    fun _ hx=>of_decide_eq_true (List.mem_filter.mp hx).2⟩

def low (θ : ℝ) (l : Word P μ) : Low P μ θ :=
  ⟨⟨l.val.filter (fun x=>decide (μ x≤θ)),
    ⟨fun x hx=>l.property.1 x (List.mem_of_mem_filter hx),
      l.property.2.sublist List.filter_sublist⟩⟩,
    fun _ hx=>of_decide_eq_true (List.mem_filter.mp hx).2⟩

def merge (θ : ℝ) (l : High P μ θ) (r : Low P μ θ) : Word P μ :=
  ⟨l.val.val++r.val.val,⟨fun x hx=>by
    rcases List.mem_append.mp hx with hx|hx
    · exact l.val.property.1 x hx
    · exact r.val.property.1 x hx,
    List.pairwise_append.mpr ⟨l.val.property.2,r.val.property.2,
      fun x hx y hy=>(r.property y hy).trans_lt (l.property x hx)⟩⟩⟩

@[simp] lemma merge_high_low (θ : ℝ) (l : Word P μ) :
    merge P μ θ (high P μ θ l) (low P μ θ l)=l :=
  Subtype.ext (ordered_filter_partition μ θ l.val l.property.2)

@[simp] lemma high_merge (θ : ℝ) (l : High P μ θ) (r : Low P μ θ) :
    high P μ θ (merge P μ θ l r)=l := by
  apply Subtype.ext
  apply Subtype.ext
  change (l.val.val++r.val.val).filter (fun x=>decide (θ<μ x))=l.val.val
  rw [List.filter_append]
  have H : l.val.val.filter (fun x=>decide (θ<μ x))=l.val.val := by
    apply List.filter_eq_self.mpr
    simpa only [decide_eq_true_eq] using l.property
  have L : r.val.val.filter (fun x=>decide (θ<μ x))=[] := by
    simp only [List.filter_eq_nil_iff,decide_eq_true_eq]
    exact fun x hx=>not_lt.mpr (r.property x hx)
  rw [H,L,List.append_nil]

@[simp] lemma low_merge (θ : ℝ) (l : High P μ θ) (r : Low P μ θ) :
    low P μ θ (merge P μ θ l r)=r := by
  apply Subtype.ext
  apply Subtype.ext
  change (l.val.val++r.val.val).filter (fun x=>decide (μ x≤θ))=r.val.val
  rw [List.filter_append]
  have H : l.val.val.filter (fun x=>decide (μ x≤θ))=[] := by
    simp only [List.filter_eq_nil_iff,decide_eq_true_eq]
    exact fun x hx=>not_le.mpr (l.property x hx)
  have L : r.val.val.filter (fun x=>decide (μ x≤θ))=r.val.val := by
    apply List.filter_eq_self.mpr
    simpa only [decide_eq_true_eq] using r.property
  rw [H,L,List.nil_append]

def splitEquiv (θ : ℝ) : Word P μ ≃ High P μ θ × Low P μ θ where
  toFun l:=(high P μ θ l,low P μ θ l)
  invFun p:=merge P μ θ p.1 p.2
  left_inv l:=merge_high_low P μ θ l
  right_inv p:=by simp

end
end ElementaryPositivity.ThresholdWords

end

end OAI
