import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListExtras
import OAI.Combinatorics.KMedian.Sparse.SparseAlgorithm
import OAI.Combinatorics.KMedian.Sparse.SparseCompressProgram

namespace OAI


                                           
section
namespace MetricKMedian.Binary.PolyProgram
open Function
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
noncomputable def pairList : PolyProgram (encodePair ea ea) (encodeList ea) (fun x => [x.1,x.2]) := by
  let second := ((snd ea ea).fanout (constant (encodePair ea ea) (encodeList ea) [])).comp (listCons ea)
  exact (((fst ea ea).fanout second).comp (listCons ea)).congr _ (fun _ => rfl)
end MetricKMedian.Binary.PolyProgram

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function
variable {α γ : Type}

theorem two_expand {n : ℕ} {δ : Type} (f : Fin n → Fin 2 → δ) :
    List.ofFn (fun i : Fin (n*2) => f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)=
      (List.ofFn (fun i => [f i 0,f i 1])).flatten := by
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext i
  have he (j : Fin 2) : (finProdFinEquiv.symm ⟨i.val*2+j.val,by omega⟩ : Fin n × Fin 2)=(i,j) :=
    by
      have hh : (⟨i.val*2+j.val,by omega⟩ : Fin (n*2))=finProdFinEquiv (i,j) := by
        apply Fin.ext
        change i.val*2+j.val=j.val+2*i.val
        omega
      rw [hh]
      exact finProdFinEquiv.symm_apply_apply (i,j)
  simp only [he]
  simp [List.ofFn_succ]

def branchLawData (x : LawData × List ℚ) : LawData :=
  let D := IntegerList.denominator x.2
  let zs := IntegerList.numerators x.2
  (x.1.1*D,(x.1.2.zip zs).flatMap (fun z => [z.1*z.2,z.1*(D-z.2)]))

noncomputable def branchLawProgram :
    PolyProgram (encodePair el (encodeList Ratio.encode)) el branchLawData := by
  let en := encodePair el (encodeList Ratio.encode)
  let law := fst el (encodeList Ratio.encode)
  let probs := snd el (encodeList Ratio.encode)
  let D := probs.comp IntegerList.denominatorProgram
  let nums := law.comp (snd Signed.encode er)
  let zs := probs.comp IntegerList.numeratorsProgram
  let triples := D.fanout ((nums.fanout zs).comp (listZip Signed.encode Signed.encode 0 0))
  let ez := encodePair Signed.encode Signed.encode
  let z := snd Signed.encode ez
  let w := z.comp (fst Signed.encode Signed.encode)
  let a := z.comp (snd Signed.encode Signed.encode)
  let d := fst Signed.encode ez
  let p0 := (w.fanout a).comp intMul
  let p1 := (w.fanout ((d.fanout a).comp intSub)).comp intMul
  let entries := (p0.fanout p1).comp pairList
  let outputnums := triples.comp (entries.listFlatMapWith (0,0) 0)
  let den := ((law.comp (fst Signed.encode er)).fanout D).comp intMul
  exact (den.fanout outputnums).congr _ (fun _ => rfl)

theorem branchLaw_ofFn {n : ℕ} (μ : IntegerLaw (Fin n)) (p : Fin n → ℚ)
    (hp : ∀ i, 0≤p i ∧ p i≤1) :
    branchLawData ((μ.denominator,List.ofFn μ.numerator),List.ofFn p)=
      ((IntegerBranching.branch μ p hp).denominator,
        List.ofFn ((IntegerBranching.branch μ p hp).reindex finProdFinEquiv).numerator) := by
  simp only [branchLawData,IntegerList.denominator_ofFn,IntegerList.numerators_ofFn,
    Gaussian.ListOperation.zip_ofFn,List.flatMap_def,List.map_ofFn,Function.comp_def]
  congr 1
  rw [show ((IntegerBranching.branch μ p hp).reindex finProdFinEquiv).numerator=
    (fun i => μ.numerator (finProdFinEquiv.symm i).1 *
      IntegerBranching.branchNumerator p (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) from by
      funext i; simp only [IntegerLaw.reindex,IntegerBranching.branch,Vector.getElem_ofFn]]
  rw [two_expand (fun i b => μ.numerator i * IntegerBranching.branchNumerator p i b)]
  simp only [IntegerBranching.branchNumerator,show (1:Fin 2)≠0 from by decide,ite_true,ite_false]

noncomputable def branchWith (ea : α → List Bool) (ec : γ → List Bool)
    (a0 : α) (p : γ → α → ℚ) (hp : ∀ c a, 0≤p c a ∧ p c a≤1)
    (next : γ → α → Fin 2 → α)
    (P : PolyProgram (encodePair ec ea) Ratio.encode (fun x => p x.1 x.2))
    (E0 : PolyProgram (encodePair ec ea) ea (fun x => next x.1 x.2 0))
    (E1 : PolyProgram (encodePair ec ea) ea (fun x => next x.1 x.2 1)) :
    PolyProgram (encodePair ec (encode ea)) (encode ea)
      (fun x => x.2.branch (p x.1) (hp x.1) (next x.1)) := by
  let c := fst ec (encode ea)
  let μ := snd ec (encode ea)
  let states := μ.comp (statesProgram ea)
  let probs := (c.fanout states).comp (P.listMapWith a0 0)
  let law := ((μ.comp (lawProgram ea)).fanout probs).comp branchLawProgram
  let endpoints := (E0.fanout E1).comp pairList
  let outputstates := (c.fanout states).comp (endpoints.listFlatMapWith a0 a0)
  exact (law.fanout outputstates).recode id (fun _ => rfl) (fun x => by
    change ed ea (branchLawData ((raw x.2).1,x.2.states.toList.map (p x.1)),
      x.2.states.toList.flatMap (fun a => [next x.1 a 0,next x.1 a 1]))=_
    simp only [states_list,List.map_ofFn,raw,Function.comp_def]
    rw [branchLaw_ofFn _ _ (fun i => hp x.1 x.2.states[i.val])]
    congr 2
    simp only [SparseIntegerLaw.branch,List.flatMap_def,List.map_ofFn,Function.comp_def,Vector.toList_ofFn]
    exact (two_expand (fun i b => next x.1 x.2.states[i.val] b)).symm)

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
