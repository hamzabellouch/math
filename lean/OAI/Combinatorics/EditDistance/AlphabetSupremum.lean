import OAI.Combinatorics.EditDistance.DistortionMonotonicity

namespace OAI

/-!
# Alphabet equivalences and universe-independent suprema
-/

namespace EditDistortion
universe u v

lemma E_le_of_alphabet_embedding (A : Type u) (B : Type v) [Fintype A] [Fintype B]
    [Nonempty A] (a : A ↪ B) {d : ℕ} (hd : 1 ≤ d) : E A d ≤ E B d := by
  classical
  let : Finite (Words A d) := finite_words A d
  let : Finite (Words B d) := finite_words B d
  let : Fintype (Words A d) := Fintype.ofFinite _
  let : Fintype (Words B d) := Fintype.ofFinite _
  let x : Words A d := ⟨[],by simp⟩
  let y : Words A d := ⟨[Classical.arbitrary A],by simpa using hd⟩
  let : Nontrivial (Words A d) := ⟨⟨x,y,by simp [x,y]⟩⟩
  let e : Words A d ↪ Words B d :=
    ⟨fun z => ⟨z.val.map a,by simpa only [List.length_map] using z.property⟩,
      fun z w h => Subtype.ext ((List.map_inj_right a.injective).mp (congrArg Subtype.val h))⟩
  let : Nontrivial (Words B d) := by
    obtain ⟨z,w,hzw⟩ := exists_pair_ne (Words A d)
    exact ⟨⟨e z,e w,fun h => hzw (e.injective h)⟩⟩
  apply leastDistortion_mono _ _
    (fun z => edit_real_diag z.val)
    (fun z w h => edit_real_pos z.val w.val (fun hh => h (Subtype.ext hh)))
    (fun z => edit_real_diag z.val)
    (fun z w h => edit_real_pos z.val w.val (fun hh => h (Subtype.ext hh))) e
  intro z w
  exact_mod_cast cost_map_eq_of_leftInverse (s := true) a (Function.invFun a)
    (Function.leftInverse_invFun a.injective) z.val w.val

lemma E_equiv (A : Type u) (B : Type v) [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ≃ B) {d : ℕ} (hd : 1 ≤ d) : E A d = E B d :=
  le_antisymm (E_le_of_alphabet_embedding A B e.toEmbedding hd)
    (E_le_of_alphabet_embedding B A e.symm.toEmbedding hd)

theorem alphabet_values_eq_all {d : ℕ} (hd : 1 ≤ d) :
    {r : ℝ | ∃ (A : Type u) (i : Fintype A), 2 ≤ @Fintype.card A i ∧ r = E A d} =
      {r : ℝ | ∃ n : ℕ, 2 ≤ n ∧ r = E (Fin n) d} := by
  ext r
  constructor
  · rintro ⟨A,i,hA,rfl⟩
    let := i
    let : Nonempty A := Fintype.card_pos_iff.mp (by omega)
    let : NeZero (Fintype.card A) := ⟨by omega⟩
    exact ⟨Fintype.card A,hA,E_equiv A (Fin (Fintype.card A)) (Fintype.equivFin A) hd⟩
  · rintro ⟨n,hn,rfl⟩
    let : NeZero n := ⟨by omega⟩
    refine ⟨ULift.{u} (Fin n),inferInstance,by simpa using hn,?_⟩
    exact (E_equiv (ULift.{u} (Fin n)) (Fin n) Equiv.ulift hd).symm

theorem alphabetSup_eq_all {d : ℕ} (hd : 1 ≤ d) :
    alphabetSup d = sSup {r : ℝ | ∃ (A : Type u) (i : Fintype A),
      2 ≤ @Fintype.card A i ∧ r = E A d} := by
  rw [alphabet_values_eq_all hd]
  rfl

end EditDistortion

end OAI
