import OAI.Computability.DegreeRigidity.Computability.ArithmeticGenericTruth

namespace OAI


namespace TuringRigidity.ArithmeticPrefixFamilies
open UniformArithmetic ArithmeticPrefixForcing ShuffleRequirements FiniteShuffle

theorem prefix_comp {Q : PrefixPredicate} (hQ : ArithmeticPrefix Q)
    {f : ℕ → ℕ} (hf : Primrec f) : ArithmeticPrefix (fun O v => Q O (f v)) :=
  (hQ.comp _ (Primrec₂.natPair.comp (hf.comp left_primrec) right_primrec)).congr
    (fun _ _ => by simp only [left,right,Nat.unpair_pair])

theorem prefix_exists {Q : PrefixPredicate} (hQ : ArithmeticPrefix Q) :
    ArithmeticPrefix (fun O v s => ∃ n, Q O (Nat.pair v n) s) :=
  ((hQ.comp _ (Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (left_primrec.comp left_primrec) right_primrec)
    (right_primrec.comp left_primrec))).ex).congr
      (fun _ _ => by simp only [left,right,Nat.unpair_pair])

theorem dense_and {D E : List Bool → Prop} (hD : DenseOpen D) (hE : DenseOpen E) :
    DenseOpen (fun s => D s ∧ E s) := by
  constructor
  · intro s
    obtain ⟨t,hst,ht⟩ := hD.1 s
    obtain ⟨u,htu,hu⟩ := hE.1 t
    exact ⟨u,hst.trans htu,hD.2 t u htu ht,hu⟩
  · intro s t hst hs
    exact ⟨hD.2 s t hst hs.1,hE.2 s t hst hs.2⟩

theorem dense_true : DenseOpen (fun _ : List Bool => True) :=
  ⟨fun s => ⟨s,List.prefix_rfl,True.intro⟩,fun _ _ _ _ => True.intro⟩

theorem avoid_truth_of_decides (Q : List Bool → Prop) (hQ : Upward Q) (G : Oracle)
    (hG : G ∈ OpenSet (Decides Q)) :
    G ∈ OpenSet (Avoid Q) ↔ ¬ G ∈ OpenSet Q := by
  constructor
  · rintro ⟨s,hs,hGs⟩ ⟨t,ht,hGt⟩
    obtain ⟨u,hsu,htu,_⟩ := realizes_common hGs hGt
    exact hs u hsu (hQ t u htu ht)
  · intro hn
    obtain ⟨s,hs,hGs⟩ := hG
    rcases hs with hs | hs
    · exact False.elim (hn ⟨s,hs,hGs⟩)
    · exact ⟨s,hs,hGs⟩

end TuringRigidity.ArithmeticPrefixFamilies

end OAI
