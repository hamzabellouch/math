import OAI.Combinatorics.ContingencyTables.Transport.MeasuredFold

namespace OAI

/-! # Costs for mapping cached computations over a finite list -/

namespace ContingencyTables.MeasuredMap
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

/-- The map accumulator adds linear copying overhead to one call of the
underlying computation. Its cost may use an external finite-box measure. -/
lemma mapStep_cost {f : A×B → C} (F : Realizer f) (a : A) (b : B) (cs : List C) :
    (mapStepRealizer F).cost (b,(a,cs)) ≤
      F.cost (a,b)+500*(weight a+weight b+weight cs+weight (f (a,b))+1) := by
  simp only [mapStepRealizer,composition,pair,first,second,listCons,Function.comp_apply]
  simp only [weight,encode_prod,MatchingFPRAS.TreeFunction.size_cons]
  omega

def listMeasure (μ : A×B → ℕ) (z : A×List B) : ℕ :=
  weight z+(z.2.map (fun b => μ (z.1,b))).sum

def foldMeasure (μ : A×B → ℕ) (z : List B×(A×List C)) : ℕ :=
  weight z+(z.1.map (fun b => μ (z.2.1,b))).sum

private lemma measure_entry (μ : A×B → ℕ) (as : List B) (a : A) (cs : List C)
    (b : B) (hb : b∈as) : μ (a,b) ≤ foldMeasure μ (as,(a,cs)) := by
  have h := List.single_le_sum (fun _ _ => Nat.zero_le _) (μ (a,b))
    (List.mem_map.mpr ⟨b,hb,rfl⟩ : μ (a,b)∈as.map (fun b => μ (a,b)))
  exact h.trans (Nat.le_add_left _ _)

/-- Mapping a finite list costs a polynomial in its encoded size and
in the sum of the work measures of its individual cached computations. -/
lemma work_mapWith {f : A×B → C} (F : Realizer f) (μ : A×B → ℕ)
    (hF : WorkBound F μ) : WorkBound (mapWith F) (listMeasure μ) := by
  obtain ⟨p,hp⟩ := hF
  let q : Polynomial ℕ := 2*X+X*(p+1)+2
  have hstate (as : List B) (a : A) (cs : List C) (pre post : List B)
      (he : as=pre++post) :
      weight (pre.foldl (fun z b => mapStep f (b,z)) (a,cs)) ≤
        q.eval (foldMeasure μ (as,(a,cs))) := by
    let S := foldMeasure μ (as,(a,cs))
    have hi : weight (as,(a,cs)) ≤ S := Nat.le_add_right _ _
    have hbs : weight as ≤ S := by rw [weight_prod] at hi; omega
    have ha : weight a ≤ S := by simp only [weight_prod] at hi; omega
    have hc : weight cs ≤ S := by simp only [weight_prod] at hi; omega
    have hl : pre.length ≤ S := (list_length_le_weight pre).trans ((weight_prefix he).trans hbs)
    have hm := weight_map_bound (as := pre) (f := fun b => f (a,b)) (N := p.eval S) (by
      intro b hb
      have hμ := measure_entry μ as a cs b (by rw [he]; exact List.mem_append_left _ hb)
      have ht := polynomial_eval_monotone p hμ
      have hf := hp (a,b)
      change p.eval (μ (a,b)) ≤ p.eval S at ht
      omega)
    rw [mapStep_fold,weight_prod]
    have happ := weight_append (pre.map (fun b => f (a,b))).reverse cs
    rw [weight_reverse] at happ
    change _ ≤ q.eval S
    simp only [q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
      Polynomial.eval_ofNat,Polynomial.eval_one]
    have hlm := Nat.mul_le_mul_right (p.eval S+1) hl
    omega
  have hfold : WorkBound (fold (mapStepRealizer F)) (foldMeasure μ) := by
    apply MeasuredFold.work_fold _ _ (p+500*(2*X+q+p+1)) q
    · intro z
      exact Nat.le_add_right _ _
    · rintro as ⟨a,cs⟩ pre b post he
      let S := foldMeasure μ (as,(a,cs))
      have hz := hstate as a cs pre (b::post) he
      have hi : weight (as,(a,cs)) ≤ S := Nat.le_add_right _ _
      have ha : weight a ≤ S := by simp only [weight_prod] at hi; omega
      have hb : weight b ≤ S := (weight_mem (show b∈as by rw [he]; simp)).trans (by
        simp only [weight_prod] at hi; omega)
      have hμ := measure_entry μ as a cs b (by rw [he]; simp)
      have ht := polynomial_eval_monotone p hμ
      have hf := hp (a,b)
      change p.eval (μ (a,b)) ≤ p.eval S at ht
      rw [mapStep_fold] at hz ⊢
      have hcs : weight ((pre.map (fun b => f (a,b))).reverse++cs) ≤ q.eval S := by
        rw [weight_prod] at hz
        exact (Nat.le_add_left _ _).trans hz
      have hm := mapStep_cost F a b ((pre.map (fun b => f (a,b))).reverse++cs)
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X,Polynomial.eval_one]
      change _ ≤ p.eval S+500*(2*S+q.eval S+p.eval S+1)
      apply hm.trans
      have hcost : F.cost (a,b) ≤ p.eval S := (Nat.le_add_right _ _).trans (hf.trans ht)
      have hout : weight (f (a,b)) ≤ p.eval S := (Nat.le_add_left _ _).trans (hf.trans ht)
      omega
    · rintro as ⟨a,cs⟩ pre post he
      exact hstate as a cs pre post he
  unfold mapWith
  apply work_congr
  apply work_then_polynomial _ (polynomial_composition polynomial_second polynomial_reverse)
  have hi : WorkBound (pair (second (A := A)) (pair first (constant ([] : List C))))
      (listMeasure μ) :=
    work_of_polynomial
      (polynomial_pair polynomial_second (polynomial_pair polynomial_first (polynomial_constant []))) X
      (fun z => by simp only [Polynomial.eval_X,listMeasure]; omega)
  apply work_composition hi hfold (X+2)
  rintro ⟨a,bs⟩
  simp only [foldMeasure,listMeasure,weight_prod,weight_nil,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  omega

end ContingencyTables.MeasuredMap

end OAI
