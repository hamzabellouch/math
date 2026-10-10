import OAI.Computability.DegreeRigidity.Computability.ArithmeticGenericTruth

namespace OAI


namespace TuringRigidity.ArithmeticGenericDensity
open UniformArithmetic ArithmeticPrefixForcing ArithmeticGenericTruth ShuffleRequirements
open EncodedForcing (word)

theorem truth_of_dense {P : Predicate} (hP : Arith P) (O : Oracles) (v : ℕ)
    (hd : ∀ s : List Bool, ∃ H : Oracle,
      Generic O H ∧ Realizes s H ∧ P (Function.update O 0 H) v) :
    ∀ G : Oracle, Generic O G → P (Function.update O 0 G) v := by
  obtain ⟨Q,hQ,hup,ht⟩ := arithmetic_generic_truth hP
  have har : Arith (fun O n => Q O v (word n)) :=
    (hQ.comp _ (Primrec₂.natPair.comp (Primrec.const v) Primrec.id)).congr
      (fun _ _ => by simp only [left,right,Nat.unpair_pair,id_eq])
  have hden : FiniteShuffle.DenseOpen (Q O v) := by
    refine ⟨?_,hup O v⟩
    intro s
    obtain ⟨H,hH,hs,hPH⟩ := hd s
    obtain ⟨t,htQ,htH⟩ := (ht O v H hH).mp hPH
    obtain ⟨u,hsu,htu,_⟩ := realizes_common hs htH
    exact ⟨u,hsu,hup O v t u htu htQ⟩
  intro G hG
  exact (ht O v G hG).mpr (hG (fun O s => Q O v s) har hden)

end TuringRigidity.ArithmeticGenericDensity

end OAI
