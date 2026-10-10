import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreeChoiceCosts
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeFractionExtra

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
open TreeTyped TreeFraction

abbrev Options (A : Type) := List (A×Fraction)
variable {A B C Ω : Type} [Codec A] [Codec B] [Codec C]

noncomputable def repr (e : Ω→A) (c : WeightedOptions Ω) : Options A :=
  List.ofFn (fun i=>(e (c.out i),TreeFraction.repr (c.mass i)))

def listSingleton : Realizer (fun a : A=>[a]) :=
  composition (pair identity (constant ([] : List A))) listCons
omit [Codec B] [Codec C] in
lemma polynomial_listSingleton : PolynomialTime (listSingleton (A:=A)) :=
  polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant _)) polynomial_listCons

def pure (a : A) : Options A := [(a,(1,1))]
def pureRealizer : Realizer (pure (A:=A)) :=
  (composition (pair identity (constant (1,1))) listSingleton).congr (fun _=>rfl)
omit [Codec B] [Codec C] in
lemma polynomial_pure : PolynomialTime (pureRealizer (A:=A)) :=
  polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant _)) polynomial_listSingleton)
omit [Codec A] [Codec B] [Codec C] in
lemma pure_repr (e : Ω→A) (a : Ω) : pure (e a)=repr e (.pure a) := by
  simp [pure,repr,WeightedOptions.pure,TreeFraction.repr,List.ofFn_succ]

def scale (x : Fraction×Options A) : Options A := x.2.map fun a=>(a.1,mul (x.1,a.2))
def scaleRealizer : Realizer (scale (A:=A)) :=
  (mapWith (pair second.fst (composition (pair first second.snd) mulRealizer))).congr (fun _=>rfl)
omit [Codec B] [Codec C] in
lemma polynomial_scale : PolynomialTime (scaleRealizer (A:=A)) := by
  unfold scaleRealizer
  apply polynomial_congr
  exact polynomial_mapWith (polynomial_pair (polynomial_fst polynomial_second)
    (polynomial_composition (polynomial_pair polynomial_first (polynomial_snd polynomial_second)) polynomial_mul))

def mix (x : Fraction×(Options A×Options A)) : Options A :=
  scale (x.1,x.2.1)++scale (sub ((1,1),x.1),x.2.2)
def mixRealizer : Realizer (mix (A:=A)) := composition
  (pair (composition (pair first second.fst) scaleRealizer)
    (composition (pair (composition (pair (constant (1,1)) first) subRealizer) second.snd) scaleRealizer)) append
omit [Codec B] [Codec C] in
lemma polynomial_mix : PolynomialTime (mixRealizer (A:=A)) := by
  unfold mixRealizer
  apply polynomial_composition _ polynomial_append
  have := polynomial_scale (A:=A)
  have := polynomial_sub
  dsimp only [Realizer.fst, Realizer.snd]
  tree_cost
omit [Codec A] [Codec B] [Codec C] in
lemma mix_repr (e : Ω→A) (p : ℚ) (hp : 0≤p) (hp1 : p≤1) (a b : WeightedOptions Ω) :
    mix (TreeFraction.repr p,(repr e a,repr e b))=repr e (.mix p hp hp1 a b) := by
  have h1 : (1,1)=TreeFraction.repr 1 := rfl
  simp only [mix,scale,repr,List.map_ofFn,h1,sub_repr (by decide) hp hp1]
  simp only [WeightedOptions.mix]
  rw [List.ofFn_add]
  apply congrArg₂ List.append <;> apply List.ofFn_inj.mpr <;> funext i
  · change (e (a.out i),mul (TreeFraction.repr p,TreeFraction.repr (a.mass i))) =
      (e (Fin.addCases a.out b.out (i.castAdd b.size)),TreeFraction.repr (Fin.addCases (fun i=>p*a.mass i) (fun i=>(1-p)*b.mass i) (i.castAdd b.size)))
    simp only [Fin.addCases_left,mul_repr hp (a.nonneg i)]
  · simp only [Function.comp_def,Fin.addCases_right]
    rw [mul_repr (sub_nonneg.mpr hp1) (b.nonneg i)]

def map (f : C×A→B) (x : C×Options A) : Options B := x.2.map fun a=>(f (x.1,a.1),a.2)
def mapRealizer {f : C×A→B} (F : Realizer f) : Realizer (map f) :=
  (mapWith (pair (composition (pair first second.fst) F) second.snd)).congr (fun _=>rfl)
lemma polynomial_map {f : C×A→B} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (mapRealizer F) := by
  unfold mapRealizer
  apply polynomial_congr
  exact polynomial_mapWith (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_fst polynomial_second)) hF) (polynomial_snd polynomial_second))
omit [Codec A] [Codec B] [Codec C] in
lemma map_repr {Ψ : Type} (e : Ω→A) (d : Ψ→B) (f : Ω→Ψ) (g : C×A→B) (z : C)
    (h : ∀ a,g (z,e a)=d (f a)) (c : WeightedOptions Ω) :
    map g (z,repr e c)=repr d (c.map f) := by
  simp only [map,repr,List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  simp only [WeightedOptions.map,Function.comp_apply,h]

def draw (d : A) (x : Options A×List Bool) : A :=
  (x.1.map Prod.fst).getD (ExecutableChoice.chooseBits (x.1.map Prod.snd,x.2)) d
def drawRealizer (d : A) : Realizer (draw d) := by
  let index : Realizer (fun x : Options A×List Bool=>
      ExecutableChoice.chooseBits (x.1.map Prod.snd,x.2)) :=
    (composition (pair (composition first (TreeTyped.map second)) second) ExecutableChoice.chooseBitsFast).congr (fun _=>rfl)
  exact (composition (pair (composition first (TreeTyped.map first)) index) (getDFast d)).congr (fun _=>rfl)
omit [Codec B] [Codec C] in
lemma polynomial_draw (d : A) : PolynomialTime (drawRealizer d) := by
  unfold drawRealizer
  dsimp only
  apply polynomial_congr
  have := ExecutableChoice.polynomial_chooseBitsFast
  have := polynomial_getDFast d
  tree_cost
omit [Codec A] [Codec B] [Codec C] in
lemma draw_repr [Fintype Ω] [DecidableEq Ω] (e : Ω→A) (c : WeightedOptions Ω) (d : A)
    {k : ℕ} (bits : Fin k→Bool) :
    draw d (repr e c,List.ofFn bits)=e (c.draw k bits) := by
  simp only [draw,repr,List.map_ofFn,Function.comp_def]
  rw [ExecutableChoice.chooseBits_eq c.mass c.nonneg c.total bits]
  simp only [List.getD,List.getElem?_ofFn,(FiniteChoice.chooseBits c.mass c.total k bits).isLt,
    ↓reduceDIte,Option.getD_some,WeightedOptions.draw]

end MatchingFPRAS.ExecutableOptions

end OAI
