import Mathlib
import OAI.Probability.SKGap.Localization.Append
import OAI.Probability.SKGap.Localization.NoiseSplit

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace Diagram
variable {D E : Type*}

@[simp] lemma map_size (f : D→E) (d : Diagram D) : (d.map f).size=d.size := by
  induction d <;> simp_all [map,size]
lemma map_map {G : Type*} (f : D→E) (g : E→G) (d : Diagram D) :
    (d.map f).map g=d.map (g∘f) := by induction d <;> simp_all [map]

lemma fiber_map_injective (f : D→E) (d e : Diagram D)
    (hw : d.word=e.word) (he : d.map f=e.map f) : d=e := by
  induction d generalizing e with
  | nil => cases e <;> simp_all [word,map]
  | diag a d ih =>
    cases e with
    | nil => simp [word] at hw
    | arch u v => simp [word] at hw
    | diag b e =>
      simp only [word,List.cons.injEq,Letter.diag.injEq] at hw
      simp only [map,Diagram.diag.injEq] at he
      obtain ⟨rfl,hw⟩ := hw
      exact congrArg (Diagram.diag a) (ih e hw he.2)
  | arch d r hd hr =>
    cases e with
    | nil => simp [word] at hw
    | diag b e => simp [word] at hw
    | arch u v =>
      simp only [map,Diagram.arch.injEq] at he
      have hlen : d.word.length=u.word.length := by
        simpa only [word_length,map_size] using congrArg Diagram.size he.1
      simp only [word,List.cons.injEq,true_and] at hw
      have hw' := List.append_inj hw hlen
      have hu := hd u hw'.1 he.1
      have hv := hr v (List.cons.inj hw'.2).2 he.2
      subst u; subst v; rfl

lemma exists_map_of_word (f : D→E) (d : Diagram E) (F : List (Letter D))
    (hw : F.map (Letter.map f)=d.word) :
    ∃ e : Diagram D, e.word=F ∧ e.map f=d := by
  induction d generalizing F with
  | nil =>
    have hF : F=[] := List.map_eq_nil_iff.mp hw
    subst F
    exact ⟨.nil,rfl,rfl⟩
  | diag a d ih =>
    cases F with
    | nil => simp [word] at hw
    | cons l F =>
      cases l with
      | noise => simp [Letter.map,word] at hw
      | diag b =>
        simp only [List.map_cons,Letter.map,word,List.cons.injEq,Letter.diag.injEq] at hw
        obtain ⟨e,he,hef⟩ := ih F hw.2
        exact ⟨.diag b e,by simp [word,he],by simp [map,hef,hw.1]⟩
  | arch d e hd he =>
    cases F with
    | nil => simp [word] at hw
    | cons l F =>
      cases l with
      | diag b => simp [Letter.map,word] at hw
      | noise =>
        simp only [List.map_cons,Letter.map,word,List.cons.injEq,true_and] at hw
        obtain ⟨P,Q,hF,hP,hQ⟩ := List.map_eq_append_iff.mp hw
        cases Q with
        | nil => simp at hQ
        | cons l Q =>
          cases l with
          | diag b => simp [Letter.map] at hQ
          | noise =>
            simp only [List.map_cons,Letter.map,List.cons.injEq,true_and] at hQ
            obtain ⟨u,hu,huf⟩ := hd P hP
            obtain ⟨v,hv,hvf⟩ := he Q hQ
            exact ⟨.arch u v,by simp [word,hu,hv,hF],by simp [map,huf,hvf]⟩

def Paired.map (f : D→E) (F : List (Letter D)) (d : Paired F) :
    Paired (F.map (Letter.map f)) := ⟨d.val.map f,by rw [map_word,d.property]⟩
lemma Paired.map_bijective (f : D→E) (F : List (Letter D)) :
    Function.Bijective (Paired.map f F) := by
  constructor
  · intro d e h
    apply Subtype.ext
    exact fiber_map_injective f d.val e.val (d.property.trans e.property.symm)
      (congrArg (fun z => z.val) h)
  · intro d
    obtain ⟨e,he,hef⟩ := exists_map_of_word f d.val F d.property.symm
    exact ⟨⟨e,he⟩,Subtype.ext hef⟩
def Paired.mapEquiv (f : D→E) (F : List (Letter D)) :
    Paired F ≃ Paired (F.map (Letter.map f)) :=
  Equiv.ofBijective (Paired.map f F) (Paired.map_bijective f F)

variable {ι : Type*} [Fintype ι]
lemma evaluate_map (j : ℝ) (v : E→ι→ℝ) (f : D→E) (d : Diagram D) :
    evaluate j v (d.map f)=evaluate j (v∘f) d := by simp [evaluate,map_map]

lemma expect_map (j : ℝ) (v : E→ι→ℝ) (f : D→E) (F : List (Letter D)) (i : ι) :
    expect j v (F.map (Letter.map f)) i=expect j (v∘f) F i := by
  symm
  apply Fintype.sum_equiv (Paired.mapEquiv f F)
  intro d
  exact congrFun (evaluate_map j v f d.val).symm i

end Diagram
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
end
end
end
end

end OAI
