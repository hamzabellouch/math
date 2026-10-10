import Mathlib
import OAI.Probability.SKGap.Localization.Append

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace InverseDiagram

def blockDegree (bs : List Bool) : ℕ := (bs.map (fun b => if b then 1 else 2)).sum

def blockEnumerate : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (blockEnumerate n).map (true::·) ++
      (if n=0 then [] else (blockEnumerate (n-1)).map (false::·))
termination_by m => m

def Blocks (n : ℕ) := {bs : List Bool // blockDegree bs=n}

@[simp] lemma blockDegree_nil : blockDegree []=0 := rfl
@[simp] lemma blockDegree_true (bs : List Bool) :
    blockDegree (true::bs)=blockDegree bs+1 := by simp [blockDegree,add_comm]
@[simp] lemma blockDegree_false (bs : List Bool) :
    blockDegree (false::bs)=blockDegree bs+2 := by simp [blockDegree,add_comm]

lemma mem_blockEnumerate (bs : List Bool) (n : ℕ) :
    bs∈blockEnumerate n ↔ blockDegree bs=n := by
  induction n using Nat.strong_induction_on generalizing bs with
  | h n ih =>
    cases n with
    | zero =>
      cases bs with
      | nil => simp [blockEnumerate]
      | cons b bs => cases b <;> simp [blockEnumerate]
    | succ n =>
      rw [blockEnumerate]
      cases bs with
      | nil => split_ifs <;> simp
      | cons b bs =>
        cases b with
        | true =>
          have ht : ((true::bs)∈(blockEnumerate n).map (true::·) ++
            (if n=0 then [] else (blockEnumerate (n-1)).map (false::·))) ↔
              bs∈blockEnumerate n := by split_ifs <;> simp
          rw [ht,ih n (by omega) bs,blockDegree_true]
          omega
        | false =>
          by_cases hn : n=0
          · subst n; simp
          · have hf : ((false::bs)∈(blockEnumerate n).map (true::·) ++
                (if n=0 then [] else (blockEnumerate (n-1)).map (false::·))) ↔
                  bs∈blockEnumerate (n-1) := by simp [hn]
            rw [hf,ih (n-1) (by omega) bs,blockDegree_false]
            omega

lemma blockEnumerate_nodup (n : ℕ) : (blockEnumerate n).Nodup := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [blockEnumerate]
    | succ n =>
      rw [blockEnumerate,List.nodup_append]
      refine ⟨(List.nodup_map_iff (by intro a b h; exact List.cons.inj h |>.2)).mpr
        (ih n (by omega)),?_,?_⟩
      · split_ifs
        · simp
        · exact (List.nodup_map_iff (by intro a b h; exact List.cons.inj h |>.2)).mpr
            (ih (n-1) (by omega))
      · split_ifs
        · simp
        · intro bs h1 cs h2 he
          obtain ⟨p,_,rfl⟩ := List.mem_map.mp h1
          obtain ⟨q,_,rfl⟩ := List.mem_map.mp h2
          cases he

instance blocksFintype (n : ℕ) : Fintype (Blocks n) :=
  Fintype.ofFinset (blockEnumerate n).toFinset (by
    intro bs
    simp only [List.mem_toFinset,mem_blockEnumerate]; rfl)

def LiteralPaired (n : ℕ) := Σ bs : Blocks n, Diagram.Paired (expandBlocks bs.val)
instance literalPairedFintype (n : ℕ) : Fintype (LiteralPaired n) :=
  inferInstanceAs (Fintype (Σ bs : Blocks n, Diagram.Paired (expandBlocks bs.val)))

def AtDegree (n : ℕ) := {d : InverseDiagram // d.degree=n}
instance atDegreeFintype (n : ℕ) : Fintype (AtDegree n) :=
  Fintype.ofFinset (enumerate n).toFinset (by
    intro d
    simp only [List.mem_toFinset,mem_enumerate]; rfl)

def toLiteral {n : ℕ} (d : AtDegree n) : LiteralPaired (2*n) :=
  ⟨⟨d.val.blocks,by
      simpa only [blockDegree,d.property] using d.val.blocks_degree⟩,
    ⟨d.val.toDiagram,d.val.toDiagram_word⟩⟩

lemma toLiteral_bijective (n : ℕ) : Function.Bijective (@toLiteral n) := by
  constructor
  · intro d e he
    apply Subtype.ext
    apply toDiagram_injective
    exact congrArg (fun z : LiteralPaired (2*n) => z.2.val) he
  · intro z
    obtain ⟨e,he,hed⟩ := toDiagram_surjective z.2.val z.1.val z.2.property
    have hn : e.degree=n := by
      have hh := e.blocks_degree
      rw [he] at hh
      change blockDegree z.1.val=2*e.degree at hh
      rw [z.1.property] at hh
      omega
    use ⟨e,hn⟩
    apply Sigma.ext
    · exact Subtype.ext he
    · apply (Subtype.heq_iff_coe_eq (fun d => ?_)).mpr hed
      change d.word=expandBlocks e.blocks ↔ d.word=expandBlocks z.1.val
      rw [he]

def literalEquiv (n : ℕ) : AtDegree n ≃ LiteralPaired (2*n) :=
  Equiv.ofBijective toLiteral (toLiteral_bijective n)

lemma literal_odd_empty (n : ℕ) : IsEmpty (LiteralPaired (2*n+1)) := by
  constructor
  intro z
  obtain ⟨e,he,hed⟩ := toDiagram_surjective z.2.val z.1.val z.2.property
  have hh := e.blocks_degree
  rw [he] at hh
  change blockDegree z.1.val=2*e.degree at hh
  rw [z.1.property] at hh
  omega

variable {ι : Type*} [Fintype ι]

def blockLabel (j : ℝ) (a : ι→ℝ) : Bool → ι→ℝ
  | true => a
  | false => fun i => -(j*average a)*a i

lemma toDiagram_value (j : ℝ) (a : ι→ℝ) (d : InverseDiagram) (i : ι) :
    (d.toDiagram.map (blockLabel j a)).value j i = d.value j a i := by
  induction d generalizing i with
  | empty => rfl
  | counterterm d ih => simp [toDiagram,Diagram.map,Diagram.value,blockLabel,value,ih]
  | arch u v iu iv =>
    simp only [toDiagram,Diagram.map,Diagram.map_append,Diagram.value,blockLabel,
      value,iv]
    have hm : Diagram.mean (fun k => (u.toDiagram.map (blockLabel j a)).value j k*a k) =
        average (fun k => a k*value j a u k) := by
      simp only [Diagram.mean,average]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [iu]
      ring
    have hv : Diagram.value j ((u.toDiagram.map (blockLabel j a)).append (.diag a .nil)) =
        (fun k => (u.toDiagram.map (blockLabel j a)).value j k * a k) := by
      funext k
      simp only [Diagram.value_append,Diagram.value,mul_one]
    rw [hv,hm]
    ring

def literalCoefficient (j : ℝ) (a : ι→ℝ) (n : ℕ) (i : ι) : ℝ :=
  ∑ z : LiteralPaired n, (z.2.val.map (blockLabel j a)).value j i

lemma literalCoefficient_even (j : ℝ) (a : ι→ℝ) (n : ℕ) (i : ι) :
    literalCoefficient j a (2*n) i=coefficient j a n i := by
  have hh := Fintype.sum_equiv (literalEquiv n)
    (fun d => value j a d.val i)
    (fun z => (z.2.val.map (blockLabel j a)).value j i)
    (fun d => (toDiagram_value j a d.val i).symm)
  change _=literalCoefficient j a (2*n) i at hh
  rw [← hh]
  let : Fintype {d : InverseDiagram // d.degree=n} := atDegreeFintype n
  change (∑ d : {d : InverseDiagram // d.degree=n}, value j a d.val i) = _
  have hx := Finset.sum_subtype (p := fun d : InverseDiagram => d.degree=n)
    (F := atDegreeFintype n)
    (enumerate n).toFinset (by
      intro d; simpa only [List.mem_toFinset] using mem_enumerate d n)
    (fun d => value j a d i)
  exact hx.symm.trans (List.sum_toFinset _ (enumerate_nodup n))

lemma literalCoefficient_odd (j : ℝ) (a : ι→ℝ) (n : ℕ) (i : ι) :
    literalCoefficient j a (2*n+1) i=0 := by
  let := literal_odd_empty n
  exact Finset.sum_eq_zero (by intro z; exact isEmptyElim z)

theorem literalCoefficient_eq (j : ℝ) (a : ι→ℝ) (n : ℕ) (i : ι) :
    literalCoefficient j a n i = if n=0 then 1 else 0 := by
  obtain ⟨m,hm⟩|⟨m,hm⟩ := Nat.even_or_odd n
  · have he : n=2*m := by omega
    rw [he,literalCoefficient_even]
    by_cases h : m=0
    · subst m; simp
    · rw [coefficient_positive j a m (by omega)]
      simp [h]
  · have he : n=2*m+1 := by omega
    rw [he,literalCoefficient_odd]
    simp

end InverseDiagram
end SKGap.Noncrossing

noncomputable section
open scoped BigOperators

end
end
end
end
end
end
end

end OAI
