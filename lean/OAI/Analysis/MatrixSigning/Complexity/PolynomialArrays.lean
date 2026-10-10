import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.SumEncodingSize
import OAI.Analysis.MatrixSigning.Complexity.PolynomialScalar
import OAI.Analysis.MatrixSigning.Complexity.PolynomialLists
import OAI.Analysis.MatrixSigning.Realization.VectorRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma fold_add_eq (xs : List ℚ) (q : ℚ) : xs.foldl (fun a b => a+b) q=q+xs.sum := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih => simp [ih,add_assoc]
lemma rat_sum_lengths_le (xs : List ℚ) :
    (xs.map KS.W01.ratLength).sum+xs.length≤(listCode ratCode xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,listCode_cons,prodCode_length]
      change KS.W01.ratLength x+_+_≤2*KS.W01.ratLength x+1+_
      omega
instance size_ratAdd : FoldSize (ratOp .add) := by
  refine ⟨⟨40*X+40,?_⟩⟩
  intro s xs ys zs h
  change (ratCode (ys.foldl (fun a b => a+b) s)).length≤_
  rw [fold_add_eq]
  have h1 := KS.W01.ratLength_sum_le ys
  have h2 := KS.W01.ratLength_add_le s ys.sum
  have hs := le_prodCode_left (ea:=ratCode) (eb:=listCode ratCode) (s,xs)
  have hy := (rat_sum_lengths_le ys).trans ((prefix_code_length ratCode xs ys zs h).trans
    (le_prodCode_right (ea:=ratCode) (s,xs)))
  change KS.W01.ratLength s≤_ at hs
  change KS.W01.ratLength (s+ys.sum)≤40*(prodCode ratCode (listCode ratCode) (s,xs)).length+40
  omega
instance poly_sumRationals : PolyTime sumRationals := by
  unfold sumRationals
  apply poly_congr
instance poly_l1Rationals : PolyTime l1Rationals := by unfold l1Rationals;apply poly_then

instance poly_lookupStep (ea : α → Word) : PolyTime (lookupStepRealizes ea) := by
  dsimp only [lookupStepRealizes]
  apply poly_congr
lemma lookup_fold_size (ea : α → Word) (s : ℕ×α) (xs : List α) (K B : ℕ)
    (hk : s.1≤K) (ha : (ea s.2).length≤B) (hx : ∀x∈xs,(ea x).length≤B) :
    (xs.foldl (fun s x => lookupStep (s,x)) s).1≤K ∧
    (ea (xs.foldl (fun s x => lookupStep (s,x)) s).2).length≤B := by
  induction xs generalizing s with
  | nil => exact ⟨hk,ha⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      apply ih
      · dsimp only [lookupStep]
        split_ifs <;> (try dsimp only) <;> omega
      · dsimp only [lookupStep]
        split_ifs <;> try dsimp only
        · exact ha
        · exact hx x (by simp)
        · exact ha
      · intro y hy;exact hx y (by simp [hy])
instance size_lookupStep (ea : α → Word) : FoldSize (lookupStepRealizes ea) := by
  refine ⟨⟨3*X+1,?_⟩⟩
  intro s xs ys zs h
  let L := (prodCode (prodCode natCode ea) (listCode ea) (s,xs)).length
  have hk : s.1≤L := by
    have hl := (le_prodCode_left (ea:=natCode) (eb:=ea) s).trans (le_prodCode_left (eb:=listCode ea) (s,xs))
    simpa only [natCode,List.length_replicate] using hl
  have ha : (ea s.2).length≤L := (le_prodCode_right s).trans (le_prodCode_left (s,xs))
  have hy : (listCode ea ys).length≤L := (prefix_code_length ea xs ys zs h).trans (le_prodCode_right (s,xs))
  have ht := lookup_fold_size ea s ys L L hk ha (fun x hx => (mem_length_le_code ys hx).trans hy)
  change (prodCode natCode ea _).length≤3*L+1
  rw [prodCode_length]
  simp only [natCode,List.length_replicate]
  omega
instance poly_getD (ea : α → Word) (a : α) : PolyTime (getD ea a) := by unfold getD;infer_instance

instance poly_zipWith {f : α×β → γ} (r : Realizes (prodCode ea eb) ec f) (a : α) (b : β)
    [PolyTime r] : PolyTime (r.zipWith a b) := by unfold Realizes.zipWith;apply poly_then
instance poly_vectorAdd : PolyTime vectorAdd := by unfold vectorAdd;infer_instance
instance poly_vectorScaleBody : PolyTime vectorScaleBody := by unfold vectorScaleBody;exact poly_ratOp .mul
instance poly_vectorScale : PolyTime vectorScale := by unfold vectorScale;infer_instance
instance poly_matrixAdd : PolyTime matrixAdd := by unfold matrixAdd;infer_instance
instance poly_matrixScale : PolyTime matrixScale := by unfold matrixScale;infer_instance
instance poly_dot : PolyTime dot := by unfold dot;apply poly_then
instance poly_matVec : PolyTime matVec := by unfold matVec;apply poly_then
instance poly_quadratic : PolyTime quadratic := by unfold quadratic;apply poly_then

lemma ratLength_natCast (n : ℕ) : KS.W01.ratLength (n : ℚ)≤4*n+11 := by
  apply (KS.W01.ratLength_le_of_parts (n : ℚ) n n ?_ ?_).trans (by omega)
  · simpa only [Rat.num_natCast,Int.natAbs_natCast] using (Nat.le_of_lt (Nat.lt_two_pow_self (n:=n)))
  · simpa only [Rat.den_natCast] using (Nat.one_le_two_pow (n:=n))
instance size_ratSucc : IterateSize ((identity ratCode).add (constant ratCode ratCode 1)) := by
  refine ⟨⟨20*X+60,?_⟩⟩
  intro q n
  change (ratCode ((fun x : ℚ => x+1)^[n] q)).length≤_
  rw [iterate_ratSucc]
  have h := KS.W01.ratLength_add_le q (n : ℚ)
  have hn := ratLength_natCast n
  change KS.W01.ratLength (q+(n : ℚ))≤20*(KS.W01.ratLength q+n)+60
  omega
instance poly_natToRat : PolyTime natToRat := by unfold natToRat;infer_instance
instance size_natMulStep : IterateSize ((first natCode natCode).both natAdd) := by
  refine ⟨⟨10*(X+1)^2,?_⟩⟩
  intro s n
  change (prodCode natCode natCode ((fun a : ℕ×ℕ => (a.1,a.1+a.2))^[n] s)).length≤_
  rcases s with ⟨k,z⟩
  rw [fold_natAdd]
  simp only [prodCode_length,natCode,List.length_replicate]
  change 2*k+1+(n*k+z)≤10*(2*k+1+z+n+1)^2
  nlinarith
instance poly_natMul : PolyTime natMul := by unfold natMul;infer_instance
end CurrentKS.Realization

end OAI
