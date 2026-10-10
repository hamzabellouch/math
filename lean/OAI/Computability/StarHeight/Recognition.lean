import OAI.Computability.StarHeight.EpisodeHeight

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uM uAlphabet2 uM2

namespace RightRegular

open EpisodeAlgebra
open scoped Computability
variable {Alphabet : Type uAlphabet} {M : Type uM} [Monoid M] [Fintype M]

lemma updateWord_product (T : FreeMonoid Alphabet →* M)
    (es : List (List Alphabet)) (x : V M) :
    updateWord (fun w => action M (T (FreeMonoid.ofList w))) x es =
      action M (T (FreeMonoid.ofList es.flatten)) x := by
  induction es generalizing x with
  | nil =>
    change x=action M (T 1) x
    rw [map_one,action_one]
    rfl
  | cons e es ih =>
    rw [updateWord_cons,ih]
    change action M (T (FreeMonoid.ofList es.flatten))
      (action M (T (FreeMonoid.ofList e)) x) =
      action M (T (FreeMonoid.ofList e * FreeMonoid.ofList es.flatten)) x
    rw [map_mul,action_mul]
    rfl

lemma graph_fiber (T : FreeMonoid Alphabet →* M) (E : Language Alphabet) (d : M) :
    graph E (fun w => action M (T (FreeMonoid.ofList w))) (basis M 1) (basis M d) =
      ({w | w∈E∗ ∧ T (FreeMonoid.ofList w)=d} : Language Alphabet) := by
  ext w
  constructor
  · rintro ⟨es,hes,rfl,h⟩
    refine ⟨Language.join_mem_kstar hes,?_⟩
    rw [updateWord_product] at h
    exact (value_recovery M _ _).mp h
  · rintro ⟨hw,hd⟩
    obtain ⟨es,rfl,hes⟩ := Language.mem_kstar.mp hw
    refine ⟨es,hes,rfl,?_⟩
    rw [updateWord_product]
    exact (value_recovery M _ _).mpr hd

end RightRegular

namespace FiniteRecognition

open EpisodeAlgebra
open scoped Computability

theorem recognized_height_three {Alphabet : Type uAlphabet2} {M : Type uM2} [Finite Alphabet] [Nonempty Alphabet]
    [Monoid M] [Fintype M] (T : FreeMonoid Alphabet →* M) (F : Set M) :
    HasHeightAtMost ({w | T (FreeMonoid.ofList w)∈F} : Language Alphabet) 3 := by
  classical
  obtain ⟨E,hE,hB,hG⟩ := SourceSchedule.episode_linear_graphs T (RightRegular.action M)
  let A : M → Language Alphabet := fun d => {w | w∈E∗ ∧ T (FreeMonoid.ofList w)=d}
  let B : M → Language Alphabet := fun f => {w | w∈remainder E ∧ T (FreeMonoid.ofList w)=f}
  have hA : ∀ d, HasHeightAtMost (A d) 3 := by
    intro d
    change HasHeightAtMost ({w | w∈E∗ ∧ T (FreeMonoid.ofList w)=d} : Language Alphabet) 3
    rw [←RightRegular.graph_fiber T E d]
    exact hG (RightRegular.basis M 1) (RightRegular.basis M d)
  let I := {p : M × M // p.1*p.2∈F}
  have hU : HasHeightAtMost (⨆ p : I, A p.1.1 * B p.1.2) 3 :=
    HasHeightAtMost.iSup _ (fun p => (hA p.1.1).concat ((hB p.1.2).mono (by decide)))
  have heq : ({w | T (FreeMonoid.ofList w)∈F} : Language Alphabet)=
      ⨆ p : I, A p.1.1 * B p.1.2 := by
    ext w
    constructor
    · intro hw
      obtain ⟨es,r,hes,hr,hwr⟩ := factor_remainder hE.1 w
      let d := T (FreeMonoid.ofList es.flatten)
      let f := T (FreeMonoid.ofList r)
      have hdf : d*f∈F := by
        change T (FreeMonoid.ofList es.flatten)*T (FreeMonoid.ofList r)∈F
        rw [←map_mul]
        change T (FreeMonoid.ofList (es.flatten++r))∈F
        rw [←hwr]
        exact hw
      apply Language.mem_iSup.mpr
      refine ⟨⟨(d,f),hdf⟩,Language.mem_mul.mpr ⟨es.flatten,?_,r,?_,hwr.symm⟩⟩
      · exact ⟨Language.join_mem_kstar hes,rfl⟩
      · exact ⟨hr,rfl⟩
    · intro hw
      obtain ⟨p,hp⟩ := Language.mem_iSup.mp hw
      obtain ⟨a,ha,b,hb,rfl⟩ := Language.mem_mul.mp hp
      change T (FreeMonoid.ofList a * FreeMonoid.ofList b)∈F
      rw [map_mul,ha.2,hb.2]
      exact p.2
  exact heq.symm ▸ hU

end FiniteRecognition

end GeneralizedStarHeight

end OAI
