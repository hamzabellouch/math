import OAI.Computability.DegreeRigidity.Computability.ArithmeticJoinSections

namespace OAI


namespace TuringRigidity.ArithmeticIteratedJoin
open UniformArithmetic ArithmeticPrefixForcing FiniteJoinSections
open FiniteShuffle ShuffleRequirements
open EncodedForcing (word)

theorem reindex_arith {P : Predicate} (hP : Arith P) (f : ℕ → ℕ) :
    Arith (fun O v => P (fun i => O (f i)) v) := by
  have h := hP.substitute (fun O _ i => O (f i))
    (fun i => (Arith.query (f i)).comp _ right_primrec)
  exact (h.comp _ (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id)).congr
    (fun _ _ => by simp only [right,Nat.unpair_pair,id_eq])

theorem generic_join (O : Oracles) (L R : Oracle)
    (hL : Generic O L)
    (hR : Generic (fun i => if i = 0 then L else O (i - 1)) R) :
    Generic O (join L R) := by
  intro D hD hd
  have hsections : ∀ t, L ∈ OpenSet (Section (D O) t) := fun t =>
    hL (fun O => Section (D O) t) (ArithmeticJoinSections.section_arith hD t)
      (section_dense hd t)
  have hfiber := fiber_dense hsections
  let O' : Oracles := fun i => if i = 0 then L else O (i - 1)
  have htail : (fun i => O' (i + 1)) = O := by
    funext i
    simp [O']
  have ha := ArithmeticJoinSections.fiber_arith (reindex_arith hD (fun i => i + 1))
    (parameter_arith 0)
  have hd' : DenseOpen (Fiber (D (fun i => O' (i + 1))) (O' 0)) := by
    simpa only [htail,O',ite_true] using hfiber
  obtain ⟨t,ht,hRt⟩ := hR
    (fun O t => Fiber (D (fun i => O (i + 1))) (O 0) t) ha hd'
  change Fiber (D (fun i => O' (i + 1))) (O' 0) t at ht
  rw [htail] at ht
  obtain ⟨s,hs,hp⟩ := ht
  exact product_realizes hp hs hRt

end TuringRigidity.ArithmeticIteratedJoin

end OAI
