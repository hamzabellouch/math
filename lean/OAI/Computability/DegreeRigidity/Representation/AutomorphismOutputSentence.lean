import OAI.Computability.DegreeRigidity.Representation.AmbientExtensionBody

namespace OAI

namespace TuringRigidity.FullSetForcing
open TransitiveNameModel BoundedSetTheory ElementaryModel SentenceForm
open SetDegreeDecoding PersistentRestrictions SetModelSatisfaction
universe u

noncomputable def outputSentence : SentenceForm :=
  .ex (.ex (.conj (.member 3 1)
    (.conj (.member 4 0) (fromBounded (.pairMem 1 0 2)))))

theorem outputSentence_raw (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    outputSentence.Sat (M : Set ZFSet) e ↔
      ∃ d ∈ M, ∃ b ∈ M, e 1 ∈ d ∧ e 2 ∈ b ∧ ZFSet.pair d b ∈ e 0 := by
  change (∃ d ∈ M, ∃ b ∈ M, e 1 ∈ d ∧ e 2 ∈ b ∧
    (fromBounded (.pairMem 1 0 2)).Sat (M : Set ZFSet) (cons b (cons d e))) ↔ _
  apply exists_congr; intro d
  apply and_congr_right; intro hd
  apply exists_congr; intro b
  apply and_congr_right; intro hb
  rw [bounded_sat, Formula.absolute _ M hM _ (by
    intro i; rcases i with _|_|i
    exact hb
    exact hd
    exact he i)]
  simp only [Formula.eval_pairMem, cons_zero, cons_succ]

theorem outputSentence_spec (M : ZFSet.{u}) (hM : Transitive M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (σ : I ≃o I)
    (A : Oracle) (hA : degree A ∈ I.carrier)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hf : e 0 = automorphismSet σ) (hx : e 1 = realCode A) :
    outputSentence.Sat (M : Set ZFSet) e ↔
      ∃ B : Oracle, realCode B = e 2 ∧ degree B = (σ ⟨degree A,hA⟩).val := by
  rw [outputSentence_raw M hM e he, hf, hx]
  constructor
  · rintro ⟨d,_,b,_,had,hbb,hf⟩
    obtain ⟨a,hpair⟩ := (mem_automorphismSet σ _).mp hf
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hpair
    have ha : degree A = a.val := (real_mem_degreeSet A a.val).mp had
    have ha' : (⟨degree A,hA⟩ : I) = a := Subtype.ext ha
    obtain ⟨B,hB,hdeg⟩ := (mem_degreeSet (σ a).val (e 2)).mp hbb
    exact ⟨B,hB.symm,by rwa [ha']⟩
  · rintro ⟨B,hB,hdeg⟩
    have hm (a : I) : degreeSet.{u} a.val ∈ M :=
      hM _ hI _ ((mem_idealSet I _).mpr ⟨a.val,a.property,rfl⟩)
    refine ⟨degreeSet (degree A),hm ⟨degree A,hA⟩,
      degreeSet (σ ⟨degree A,hA⟩).val,hm (σ ⟨degree A,hA⟩),
      (real_mem_degreeSet A _).mpr rfl,?_,?_⟩
    · rw [←hB]
      exact (real_mem_degreeSet B _).mpr hdeg
    · exact (mem_automorphismSet σ _).mpr ⟨⟨degree A,hA⟩,rfl⟩

theorem modelIdeal_internal (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) : idealSet (modelIdeal M hM hT) ∈ M := by
  obtain ⟨R,hRM,hR⟩ := internal_power M hM hT.powerSet (sourceT_omega_mem M hM hT)
  rw [←ownDegreeUniverse_eq_idealSet M hM hT R hR]
  apply internal_degreeUniverse M hM hT R hRM
  intro w hw
  exact ⟨decodeReal w,realCode_decodeReal ((hR w).mp hw).2⟩

end TuringRigidity.FullSetForcing

end OAI
