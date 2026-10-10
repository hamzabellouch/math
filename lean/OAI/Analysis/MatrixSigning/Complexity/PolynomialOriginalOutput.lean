import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialOriginalSigning
import OAI.Analysis.MatrixSigning.Realization.OriginalOutputRoutine

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

instance poly_appendBit : PolyTime appendBit := by
  refine ⟨⟨5*X+4,?_⟩⟩
  intro p
  have h := le_prodCode_left (ea:=wordCode) (eb:=boolCode) p
  change 5*p.1.length+4≤5*(prodCode wordCode boolCode p).length+4
  change p.1.length≤_ at h
  omega
instance size_appendBit : FoldSize appendBit := by
  refine ⟨⟨2*X,?_⟩⟩
  intro s xs ys zs he
  have h1 := le_prodCode_left (ea:=wordCode) (eb:=listCode boolCode) (s,xs)
  have h2 := (list_length_le_code boolCode xs).trans (le_prodCode_right (ea:=wordCode) (s,xs))
  have hy : ys.length≤xs.length := by rw [he,List.length_append];omega
  change (ys.foldl (fun a b => a++[b]) s).length≤2*(prodCode wordCode (listCode boolCode) (s,xs)).length
  rw [fold_appendBit,List.length_append]
  change s.length≤_ at h1
  omega
instance poly_outputBits : PolyTime outputBits := by unfold outputBits;apply poly_congr

instance poly_originalEmpty : PolyTime originalEmpty := by
  unfold originalEmpty
  apply PolyTime.congr
  apply PolyTime.then
  · exact ⟨⟨3*X+2,OriginalTailRoutine.ticks_le⟩⟩
  · exact ⟨⟨X+6,fun _ => le_rfl⟩⟩

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_fullBody (a : ι → Input)
    (ha : IsPoly L (fun i => (a i).encode.length))
    (hx : ∀i,Admissible (a i)) (hn : ∀i,(a i).N≠0) : RunsPoly L fullBody a := by
  have hp : RunsPoly L
      ({cost := OriginalParserRoutine.ticks,routine := OriginalParserRoutine.routine} : Realizes Input.encode originalCode id) a := by
    refine ⟨ha,?_⟩
    apply (ha.eval (800*(X+1)^5)).mono
    intro i
    have h := OriginalParserRoutine.ticks_le (a i) (hn i)
    simp only [NaturalPolynomial.eval_mul,
      NaturalPolynomial.eval_power,NaturalPolynomial.eval_add,NaturalPolynomial.eval_variable,Input.length] at h ⊢
    exact h
  unfold fullBody
  exact hp.then ((runsPoly_originalSigningFramed a hp.output hx).then_poly outputBits)

lemma runsPoly_originalSigning (a : ι → Input)
    (ha : IsPoly L (fun i => (a i).encode.length))
    (hx : ∀i,Admissible (a i)) : RunsPoly L originalSigning a := by
  have hb := RunsPoly.of_poly originalEmpty a ha
  have ht := RunsPoly.of_poly (constant Input.encode wordCode []) a ha
  have hs := runsPoly_fullBody (fun i : {i // (a i).N≠0} => a i.val)
    (ha.reindex Subtype.val) (fun i => hx i.val) (fun i => i.property)
  have hc : IsPoly L (fun i => if (a i).N=0 then
      (constant Input.encode wordCode []).cost (a i) else fullBody.cost (a i)) := by
    exact isPoly_dite (ht.cost.reindex (fun i : {i // (a i).N=0} => i.val)) hs.cost
  unfold originalSigning
  apply RunsPoly.congr
  apply hb.ite_on
  simpa only [decide_eq_true_eq] using hc
end CurrentKS.Realization

end OAI
