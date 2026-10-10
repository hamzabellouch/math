import OAI.Combinatorics.CompleteCrossing.CircleArcs
import OAI.Combinatorics.Crossing.FiniteCircleCoordinates
import OAI.Combinatorics.Crossing.GenericPolynomialBox
import OAI.Combinatorics.Crossing.TangentTrackIdentity
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Order.Basic

namespace OAI

/-! Generic circular placement, prescribed arcs, restrictions, and existence of drawings. -/

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

variable {V E : Type} {m : ℕ}

def completeEdgeOf (G : Graph V E) (ι : V ↪ Fin m) (e : E) : CompleteEdge m :=
  if h : ι (G.src e) < ι (G.dst e) then ⟨(ι (G.src e), ι (G.dst e)), h⟩
  else ⟨(ι (G.dst e), ι (G.src e)), by change ι (G.dst e) < ι (G.src e); have := ι.injective.ne (G.loopless e); omega⟩

theorem completeEdgeOf_endpoints (G : Graph V E) (ι : V ↪ Fin m) (e : E) :
    ((completeEdgeOf G ι e).val.1 = ι (G.src e) ∧
      (completeEdgeOf G ι e).val.2 = ι (G.dst e)) ∨
    ((completeEdgeOf G ι e).val.1 = ι (G.dst e) ∧
      (completeEdgeOf G ι e).val.2 = ι (G.src e)) := by
  unfold completeEdgeOf
  split_ifs <;> simp

theorem completeEdgeOf_injective (G : Graph V E) (ι : V ↪ Fin m) :
    Function.Injective (completeEdgeOf G ι) := by
  intro e f h
  have h₁ := congrArg (fun a : CompleteEdge m => a.val.1) h
  have h₂ := congrArg (fun a : CompleteEdge m => a.val.2) h
  rcases completeEdgeOf_endpoints G ι e with he | he <;>
    rcases completeEdgeOf_endpoints G ι f with hf | hf
  · exact G.simple e f (Or.inl ⟨ι.injective (he.1.symm.trans (h₁.trans hf.1)),
      ι.injective (he.2.symm.trans (h₂.trans hf.2))⟩)
  · exact G.simple e f (Or.inr ⟨ι.injective (he.1.symm.trans (h₁.trans hf.1)),
      ι.injective (he.2.symm.trans (h₂.trans hf.2))⟩)
  · exact G.simple e f (Or.inr ⟨ι.injective (he.2.symm.trans (h₂.trans hf.2)),
      ι.injective (he.1.symm.trans (h₁.trans hf.1))⟩)
  · exact G.simple e f (Or.inl ⟨ι.injective (he.2.symm.trans (h₂.trans hf.2)),
      ι.injective (he.1.symm.trans (h₁.trans hf.1))⟩)

theorem unitInterval_symm_mem_open {t : unitInterval} (ht : t ∈ Ioo (0 : unitInterval) 1) :
    unitInterval.symm t ∈ Ioo (0 : unitInterval) 1 := by
  have h0 : (0 : ℝ) < t.val := ht.1
  have h1 : t.val < (1 : ℝ) := ht.2
  change 0 < 1 - t.val ∧ 1 - t.val < 1
  constructor <;> linarith

theorem path_symm_open_image {a b : Plane} (γ : Path a b) :
    γ.symm '' Ioo (0 : unitInterval) 1 = γ '' Ioo (0 : unitInterval) 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨unitInterval.symm t, unitInterval_symm_mem_open ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨unitInterval.symm t, unitInterval_symm_mem_open ht, ?_⟩
    change γ (unitInterval.symm (unitInterval.symm t)) = γ t
    rw [unitInterval.symm_involutive t]

def restrictedCompletePath (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) (e : E) :
    Path (D.vertex (ι (G.src e))) (D.vertex (ι (G.dst e))) where
  toFun t := if h : ι (G.src e) < ι (G.dst e) then
    D.edge ⟨(ι (G.src e), ι (G.dst e)), h⟩ t
  else D.edge ⟨(ι (G.dst e), ι (G.src e)),
    by change ι (G.dst e) < ι (G.src e); have := ι.injective.ne (G.loopless e); omega⟩
      (unitInterval.symm t)
  continuous_toFun := by
    split_ifs with h
    · exact (D.edge _).continuous
    · exact (D.edge _).continuous.comp unitInterval.continuous_symm
  source' := by
    split_ifs
    · exact (D.edge _).source
    · rw [unitInterval.symm_zero]
      exact (D.edge _).target
  target' := by
    split_ifs
    · exact (D.edge _).target
    · rw [unitInterval.symm_one]
      exact (D.edge _).source

theorem restrictedCompletePath_injective (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) (e : E) :
    Function.Injective (restrictedCompletePath G ι D e) := by
  intro s t he
  by_cases h : ι (G.src e) < ι (G.dst e)
  · let f : CompleteEdge m := ⟨(ι (G.src e), ι (G.dst e)), h⟩
    have hpath : (restrictedCompletePath G ι D e : unitInterval → Plane) = D.edge f := by
      funext t
      exact dite_eq_left h
    exact D.edge_injective f ((congrFun hpath s).symm.trans (he.trans (congrFun hpath t)))
  · let f : CompleteEdge m := ⟨(ι (G.dst e), ι (G.src e)),
      by change ι (G.dst e) < ι (G.src e); have := ι.injective.ne (G.loopless e); omega⟩
    have hpath : (restrictedCompletePath G ι D e : unitInterval → Plane) = (D.edge f).symm := by
      funext t
      exact dite_eq_right h
    have he' := (congrFun hpath s).symm.trans (he.trans (congrFun hpath t))
    exact unitInterval.symm_involutive.injective (D.edge_injective _ he')

theorem restrictedCompletePath_interior (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) (e : E) :
    restrictedCompletePath G ι D e '' Ioo (0 : unitInterval) 1 =
      edgeInterior D.toContinuousDrawing (completeEdgeOf G ι e) := by
  by_cases h : ι (G.src e) < ι (G.dst e)
  · let f : CompleteEdge m := ⟨(ι (G.src e), ι (G.dst e)), h⟩
    have hedge : completeEdgeOf G ι e = f := dite_eq_left h
    have hpath : (restrictedCompletePath G ι D e : unitInterval → Plane) = D.edge f := by
      funext t
      exact dite_eq_left h
    rw [hpath, hedge]
    rfl
  · let f : CompleteEdge m := ⟨(ι (G.dst e), ι (G.src e)),
      by change ι (G.dst e) < ι (G.src e); have := ι.injective.ne (G.loopless e); omega⟩
    have hedge : completeEdgeOf G ι e = f := dite_eq_right h
    have hpath : (restrictedCompletePath G ι D e : unitInterval → Plane) = (D.edge f).symm := by
      funext t
      exact dite_eq_right h
    rw [hpath, hedge]
    exact path_symm_open_image (D.edge f)

theorem restrictedCompletePath_avoids (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) (e : E) (t : unitInterval)
    (ht : t ∈ Ioo (0 : unitInterval) 1) (v : V) :
    restrictedCompletePath G ι D e t ≠ D.vertex (ι v) := by
  have hm : restrictedCompletePath G ι D e t ∈
      restrictedCompletePath G ι D e '' Ioo (0 : unitInterval) 1 := ⟨t, ht, rfl⟩
  rw [restrictedCompletePath_interior] at hm
  obtain ⟨u, hu, he⟩ := hm
  rw [← he]
  exact D.interior_avoids_vertices _ u hu _

def restrictedCompleteContinuous (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) : ContinuousDrawing G where
  vertex := D.vertex ∘ ι
  vertex_injective := D.vertex_injective.comp ι.injective
  edge := restrictedCompletePath G ι D
  edge_injective := restrictedCompletePath_injective G ι D
  interior_avoids_vertices := restrictedCompletePath_avoids G ι D

theorem restrictedComplete_edgeInterior (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) (e : E) :
    edgeInterior (restrictedCompleteContinuous G ι D) e =
      edgeInterior D.toContinuousDrawing (completeEdgeOf G ι e) :=
  restrictedCompletePath_interior G ι D e

theorem restrictedComplete_crossings_subset (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) :
    crossingPoints (restrictedCompleteContinuous G ι D) ⊆ crossingPoints D.toContinuousDrawing := by
  rintro x ⟨e, f, hef, hx, hy⟩
  rw [restrictedComplete_edgeInterior] at hx hy
  exact ⟨_, _, (completeEdgeOf_injective G ι).ne hef, hx, hy⟩

def restrictedCompleteAdmissible (G : Graph V E) (ι : V ↪ Fin m)
    (D : AdmissibleDrawing (completeGraph m)) : AdmissibleDrawing G where
  toContinuousDrawing := restrictedCompleteContinuous G ι D
  crossings_finite := D.crossings_finite.subset (restrictedComplete_crossings_subset G ι D)
  crossings_proper := by
    intro e f hef x hx hy
    simp only [restrictedComplete_edgeInterior] at hx hy ⊢
    exact D.crossings_proper _ _ ((completeEdgeOf_injective G ι).ne hef) x hx hy
  no_triples := by
    intro e f g hef heg hfg
    simp only [restrictedComplete_edgeInterior]
    exact D.no_triples _ _ _ ((completeEdgeOf_injective G ι).ne hef)
      ((completeEdgeOf_injective G ι).ne heg) ((completeEdgeOf_injective G ι).ne hfg)

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

def circleConcurrency {R : Type*} [CommRing R] (a b c d e f : R) : R :=
  (c + d) * e * f - c * d * (e + f) - (a + b) * (e * f - c * d) +
    a * b * (e + f - c - d)

def circleLine (a b : ℝ) (z : Plane) : ℝ :=
  (1 - a * b) * z.1 + (a + b) * z.2 - (1 + a * b)

theorem circleLine_param (a b : ℝ) : circleLine a b (Zarankiewicz.circlePoint a) = 0 := by
  have ha := ne_of_gt (Zarankiewicz.circle_denominator_pos a)
  unfold circleLine Zarankiewicz.circlePoint
  field_simp
  ring

theorem circleLine_chord (a b t : ℝ) :
    circleLine a b (segmentPoint (Zarankiewicz.circlePoint a) (Zarankiewicz.circlePoint b) t) = 0 := by
  have ha := circleLine_param a b
  have hb := circleLine_param b a
  unfold circleLine at *
  change (1 - a * b) * ((1 - t) * (Zarankiewicz.circlePoint a).1 + t * (Zarankiewicz.circlePoint b).1) +
    (a + b) * ((1 - t) * (Zarankiewicz.circlePoint a).2 + t * (Zarankiewicz.circlePoint b).2) -
      (1 + a * b) = 0
  linear_combination (1 - t) * ha + t * hb

theorem circleConcurrency_of_lines (a b c d e f : ℝ) (z : Plane)
    (h₁ : circleLine a b z = 0) (h₂ : circleLine c d z = 0) (h₃ : circleLine e f z = 0) :
    circleConcurrency a b c d e f = 0 := by
  have he : 2 * circleConcurrency a b c d e f = 0 := by
    unfold circleConcurrency circleLine at *
    linear_combination
      -((1 - c * d) * (e + f) - (1 - e * f) * (c + d)) * h₁ -
      ((1 - e * f) * (a + b) - (1 - a * b) * (e + f)) * h₂ -
      ((1 - a * b) * (c + d) - (1 - c * d) * (a + b)) * h₃
  linarith

def circleConcurrencyPolynomial {n : ℕ} (v : Fin 6 → Fin n) : MvPolynomial (Fin n) ℝ :=
  circleConcurrency (MvPolynomial.X (v 0)) (MvPolynomial.X (v 1))
    (MvPolynomial.X (v 2)) (MvPolynomial.X (v 3))
    (MvPolynomial.X (v 4)) (MvPolynomial.X (v 5))

theorem circleConcurrencyPolynomial_eval {n : ℕ} (v : Fin 6 → Fin n) (t : Fin n → ℝ) :
    MvPolynomial.eval t (circleConcurrencyPolynomial v) =
      circleConcurrency (t (v 0)) (t (v 1)) (t (v 2)) (t (v 3)) (t (v 4)) (t (v 5)) := by
  simp [circleConcurrencyPolynomial, circleConcurrency]

theorem circleConcurrencyPolynomial_ne_zero {n : ℕ} (v : Fin 6 → Fin n)
    (hv : Function.Injective v) : circleConcurrencyPolynomial v ≠ 0 := by
  let t : Fin n → ℝ := fun i => if i = v 2 ∨ i = v 4 ∨ i = v 5 then 1 else 0
  have he : MvPolynomial.eval t (circleConcurrencyPolynomial v) = 1 := by
    rw [circleConcurrencyPolynomial_eval]
    simp only [t, hv.eq_iff]
    norm_num [circleConcurrency, Fin.ext_iff]
  intro hz
  rw [hz, map_zero] at he
  exact zero_ne_one he

theorem circle_configuration_exists (n : ℕ) : Nonempty (CircleConfiguration n) := by
  let I := {v : Fin 6 → Fin n // Function.Injective v}
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨t, ht, havoid⟩ := Zarankiewicz.exists_box_avoiding_polynomials
    (fun v : I => circleConcurrencyPolynomial v.val)
    (fun v => circleConcurrencyPolynomial_ne_zero v.val v.property)
    (fun i : Fin n => 2 * (i.val : ℝ) + 1) (fun i : Fin n => 2 * (i.val : ℝ) + 2)
    (by intro i; linarith)
  have htmono : StrictMono t := by
    intro i j hij
    have hij' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
    linarith [(ht i).2, (ht j).1]
  have htpos (i : Fin n) : 0 < t i := by
    have hnonneg : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    linarith [(ht i).1]
  let p := Zarankiewicz.circlePoint ∘ t
  have hp : Function.Injective p := Zarankiewicz.circlePoint_injective.comp htmono.injective
  have hcircle (i : Fin n) : squaredLength (p i) = 1 := Zarankiewicz.circlePoint_on_unit_circle (t i)
  refine ⟨{
    point := p
    injective := hp
    on_circle := hcircle
    cyclic_order := ?_
    no_antipodal := ?_
    no_triple_chords := ?_ }⟩
  · intro i j k hij hjk
    exact Zarankiewicz.circle_orient_pos (t i) (t j) (t k) (htmono hij) (htmono hjk)
  · intro i j _ he
    have hi : 0 < (p i).2 := div_pos (by linarith [htpos i]) (Zarankiewicz.circle_denominator_pos _)
    have hj : 0 < (p j).2 := div_pos (by linarith [htpos j]) (Zarankiewicz.circle_denominator_pos _)
    have hz := congrArg Prod.snd he
    change (p i).2 + (p j).2 = 0 at hz
    linarith
  · intro e f g hef heg hfg
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hEF := circle_chord_endpoints_distinct p hp hcircle e f hef z hz.1.1 hz.1.2
    have hEG := circle_chord_endpoints_distinct p hp hcircle e g heg z hz.1.1 hz.2
    have hFG := circle_chord_endpoints_distinct p hp hcircle f g hfg z hz.1.2 hz.2
    let v : Fin 6 → Fin n := ![e.val.1, e.val.2, f.val.1, f.val.2, g.val.1, g.val.2]
    have hv : Function.Injective v := by
      intro i j heq
      have he' := e.property
      have hf' := f.property
      have hg' := g.property
      fin_cases i <;> fin_cases j <;> norm_num [v, Fin.ext_iff] at heq ⊢ <;> omega
    have hne := havoid (⟨v, hv⟩ : I)
    rw [circleConcurrencyPolynomial_eval] at hne
    have hline (a : CompleteEdge n) (ha : z ∈ chordInterior p a) :
        circleLine (t a.val.1) (t a.val.2) z = 0 := by
      obtain ⟨u, _, rfl⟩ := ha
      exact circleLine_chord _ _ u
    apply hne
    exact circleConcurrency_of_lines _ _ _ _ _ _ z
      (hline e hz.1.1) (hline f hz.1.2) (hline g hz.2)

end Paper170

end
end

section

/-! Generic circle positions can be selected inside arbitrary prescribed open parameter intervals. -/
noncomputable section
open Set MvPolynomial
open scoped Classical
namespace Paper170

lemma circle_differencePolynomial_ne_zero {n : ℕ} (e : CompleteEdge n) :
    (X e.val.1-X e.val.2 : MvPolynomial (Fin n) ℝ) ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval (fun i => if i=e.val.1 then (1:ℝ) else 0)) h
  simp [ne_of_gt e.property] at hh

lemma circle_antipodalPolynomial_ne_zero {n : ℕ} (e : CompleteEdge n) :
    (1+X e.val.1*X e.val.2 : MvPolynomial (Fin n) ℝ) ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval (fun _ => (0:ℝ))) h
  simp at hh

theorem exists_generic_circle_parameters (n : ℕ) (lo hi : Fin n → ℝ)
    (hinterval : ∀i, lo i < hi i) :
    ∃t : Fin n → ℝ, (∀i, t i ∈ Ioo (lo i) (hi i)) ∧ Function.Injective t ∧
      (∀i j, i≠j → 1+t i*t j≠0) ∧
      ∀v : Fin 6 → Fin n, Function.Injective v →
        circleConcurrency (t (v 0)) (t (v 1)) (t (v 2)) (t (v 3)) (t (v 4)) (t (v 5)) ≠ 0 := by
  let S := {v : Fin 6 → Fin n // Function.Injective v}
  let : Fintype S := Fintype.ofFinite S
  let I := CompleteEdge n ⊕ (CompleteEdge n ⊕ S)
  let P : I → MvPolynomial (Fin n) ℝ := fun i => match i with
    | .inl e => X e.val.1-X e.val.2
    | .inr (.inl e) => 1+X e.val.1*X e.val.2
    | .inr (.inr v) => circleConcurrencyPolynomial v.val
  have hP (i : I) : P i ≠ 0 := by
    rcases i with e | e | v
    · exact circle_differencePolynomial_ne_zero e
    · exact circle_antipodalPolynomial_ne_zero e
    · exact circleConcurrencyPolynomial_ne_zero v.val v.property
  obtain ⟨t,ht,ha⟩ := Zarankiewicz.exists_box_avoiding_polynomials P hP lo hi hinterval
  have hdiff (i j : Fin n) (hij : i<j) : t i-t j≠0 := by
    simpa [P] using ha (.inl ⟨(i,j),hij⟩)
  have hanti (i j : Fin n) (hij : i<j) : 1+t i*t j≠0 := by
    simpa [P] using ha (.inr (.inl ⟨(i,j),hij⟩))
  refine ⟨t,ht,?_,?_,?_⟩
  · intro i j he
    rcases lt_trichotomy i j with h | h | h
    · exact False.elim (hdiff i j h (sub_eq_zero.mpr he))
    · exact h
    · exact False.elim (hdiff j i h (sub_eq_zero.mpr he.symm))
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hanti i j h
    · simpa only [mul_comm] using hanti j i h
  · intro v hv
    have h := ha (.inr (.inr ⟨v,hv⟩))
    simpa only [P,circleConcurrencyPolynomial_eval] using h

lemma circlePoint_add_ne_zero (a b : ℝ) (hab : 1+a*b≠0) :
    Zarankiewicz.circlePoint a + Zarankiewicz.circlePoint b ≠ 0 := by
  intro h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  have ha := ne_of_gt (Zarankiewicz.circle_denominator_pos a)
  have hb := ne_of_gt (Zarankiewicz.circle_denominator_pos b)
  dsimp [Zarankiewicz.circlePoint] at h₁ h₂
  field_simp [ha,hb] at h₁ h₂
  have hprod : (1-a*b)*(1+a*b)=0 := by nlinarith [h₁]
  have hsum : (a+b)*(1+a*b)=0 := by nlinarith [h₂]
  have he : a*b=1 := by
    have hh := (mul_eq_zero.mp hprod).resolve_right hab
    linarith
  have hs := (mul_eq_zero.mp hsum).resolve_right hab
  have heq : b = -a := by linarith
  rw [heq] at he
  nlinarith [sq_nonneg a]

end Paper170

end
end

section

/-! Actual generic circle points in prescribed parameter intervals and neighborhoods. -/
noncomputable section
open Set
open scoped Classical
namespace Paper170

lemma circleParameters_no_triples {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t)
    (havoid : ∀v : Fin 6 → Fin n, Function.Injective v →
      circleConcurrency (t (v 0)) (t (v 1)) (t (v 2)) (t (v 3)) (t (v 4)) (t (v 5)) ≠ 0) :
    ∀e f g : CompleteEdge n, e≠f → e≠g → f≠g →
      chordInterior (fun i => Zarankiewicz.circlePoint (t i)) e ∩
        chordInterior (fun i => Zarankiewicz.circlePoint (t i)) f ∩
        chordInterior (fun i => Zarankiewicz.circlePoint (t i)) g = ∅ := by
  let p := fun i => Zarankiewicz.circlePoint (t i)
  have hp : Function.Injective p := Zarankiewicz.circlePoint_injective.comp ht
  have hcircle i : squaredLength (p i)=1 := Zarankiewicz.circlePoint_on_unit_circle (t i)
  intro e f g hef heg hfg
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hEF := circle_chord_endpoints_distinct p hp hcircle e f hef z hz.1.1 hz.1.2
  have hEG := circle_chord_endpoints_distinct p hp hcircle e g heg z hz.1.1 hz.2
  have hFG := circle_chord_endpoints_distinct p hp hcircle f g hfg z hz.1.2 hz.2
  let v : Fin 6 → Fin n := ![e.val.1,e.val.2,f.val.1,f.val.2,g.val.1,g.val.2]
  have hv : Function.Injective v := by
    intro i j heq
    have he' := e.property
    have hf' := f.property
    have hg' := g.property
    fin_cases i <;> fin_cases j <;> norm_num [v,Fin.ext_iff] at heq ⊢ <;> omega
  have hline (a : CompleteEdge n) (ha : z ∈ chordInterior p a) :
      circleLine (t a.val.1) (t a.val.2) z=0 := by
    obtain ⟨u,_,rfl⟩ := ha
    exact circleLine_chord _ _ u
  exact havoid v hv (circleConcurrency_of_lines _ _ _ _ _ _ z
    (hline e hz.1.1) (hline f hz.1.2) (hline g hz.2))

theorem exists_circle_points_in_parameter_intervals (n : ℕ) (lo hi : Fin n → ℝ)
    (hinterval : ∀i, lo i < hi i) :
    ∃t : Fin n → ℝ, (∀i, t i ∈ Ioo (lo i) (hi i)) ∧
      Function.Injective (fun i => Zarankiewicz.circlePoint (t i)) ∧
      (∀i, squaredLength (Zarankiewicz.circlePoint (t i))=1) ∧
      (∀i j, i≠j → Zarankiewicz.circlePoint (t i)+Zarankiewicz.circlePoint (t j)≠0) ∧
      ∀e f g : CompleteEdge n, e≠f → e≠g → f≠g →
        chordInterior (fun i => Zarankiewicz.circlePoint (t i)) e ∩
          chordInterior (fun i => Zarankiewicz.circlePoint (t i)) f ∩
          chordInterior (fun i => Zarankiewicz.circlePoint (t i)) g = ∅ := by
  obtain ⟨t,ht,hinj,hanti,havoid⟩ := exists_generic_circle_parameters n lo hi hinterval
  exact ⟨t,ht,Zarankiewicz.circlePoint_injective.comp hinj,
    fun i => Zarankiewicz.circlePoint_on_unit_circle (t i),
    fun i j hij => circlePoint_add_ne_zero _ _ (hanti i j hij),circleParameters_no_triples t hinj havoid⟩

lemma continuous_circle_similarity (u : Plane) :
    Continuous (fun t : ℝ => Zarankiewicz.similarityPoint 0 u (Zarankiewicz.circlePoint t)) := by
  have hden : Continuous (fun t : ℝ => 1+t^2) := by fun_prop
  have hn (t : ℝ) : 1+t^2≠0 := ne_of_gt (Zarankiewicz.circle_denominator_pos t)
  have hx : Continuous (fun t : ℝ => (1-t^2)/(1+t^2)) :=
    (continuous_const.sub (continuous_id.pow 2)).div hden hn
  have hy : Continuous (fun t : ℝ => 2*t/(1+t^2)) :=
    (continuous_const.mul continuous_id).div hden hn
  change Continuous (fun t : ℝ => (0 : Plane)+
    (u.1*((1-t^2)/(1+t^2))-u.2*(2*t/(1+t^2)),
      u.2*((1-t^2)/(1+t^2))+u.1*(2*t/(1+t^2))))
  exact continuous_const.add (((continuous_const.mul hx).sub (continuous_const.mul hy)).prodMk
    ((continuous_const.mul hx).add (continuous_const.mul hy)))

lemma circle_similarity_add (u a b : Plane) :
    Zarankiewicz.similarityPoint 0 u (a+b) =
      Zarankiewicz.similarityPoint 0 u a+Zarankiewicz.similarityPoint 0 u b := by
  apply Prod.ext <;> dsimp [Zarankiewicz.similarityPoint] <;> ring

lemma circle_similarity_zero (u : Plane) : Zarankiewicz.similarityPoint 0 u 0=0 := by
  simp [Zarankiewicz.similarityPoint]

lemma circle_similarity_no_triples {n : ℕ} (u : Plane) (hu : u≠0) (p : Fin n → Plane)
    (htriple : ∀e f g : CompleteEdge n, e≠f → e≠g → f≠g →
      chordInterior p e ∩ chordInterior p f ∩ chordInterior p g=∅) :
    ∀e f g : CompleteEdge n, e≠f → e≠g → f≠g →
      chordInterior (fun i => Zarankiewicz.similarityPoint 0 u (p i)) e ∩
        chordInterior (fun i => Zarankiewicz.similarityPoint 0 u (p i)) f ∩
        chordInterior (fun i => Zarankiewicz.similarityPoint 0 u (p i)) g=∅ := by
  intro e f g hef heg hfg
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨⟨⟨s,hs,hes⟩,hf⟩,hg⟩
  let y := segmentPoint (p e.val.1) (p e.val.2) s
  have hsy : Zarankiewicz.similarityPoint 0 u y=z := by
    change Zarankiewicz.similarityPoint 0 u (Zarankiewicz.segmentPoint _ _ s)=z
    rw [Zarankiewicz.similarityPoint_segment]
    exact hes
  have hinj := Zarankiewicz.similarityPoint_injective 0 u hu
  have transfer (a : CompleteEdge n)
      (ha : z ∈ chordInterior (fun i => Zarankiewicz.similarityPoint 0 u (p i)) a) :
      y ∈ chordInterior p a := by
    obtain ⟨t,ht,het⟩ := ha
    refine ⟨t,ht,hinj ?_⟩
    change Zarankiewicz.similarityPoint 0 u (Zarankiewicz.segmentPoint _ _ t)=_
    rw [Zarankiewicz.similarityPoint_segment,hsy]
    exact het
  have hm : y ∈ chordInterior p e ∩ chordInterior p f ∩ chordInterior p g :=
    ⟨⟨⟨s,hs,rfl⟩,transfer f hf⟩,transfer g hg⟩
  rw [htriple e f g hef heg hfg] at hm
  exact hm

theorem exists_generic_circle_points_in_neighborhoods (n : ℕ) (anchor : Fin n → Plane)
    (hinj : Function.Injective anchor) (hcircle : ∀i, squaredLength (anchor i)=1)
    (U : Fin n → Set Plane) (hU : ∀i, IsOpen (U i)) (hanchor : ∀i, anchor i ∈ U i) :
    ∃p : Fin n → Plane, (∀i, p i∈U i) ∧ Function.Injective p ∧
      (∀i, squaredLength (p i)=1) ∧ (∀i j, i≠j → p i+p j≠0) ∧
      ∀e f g : CompleteEdge n, e≠f → e≠g → f≠g →
        chordInterior p e ∩ chordInterior p f ∩ chordInterior p g=∅ := by
  obtain ⟨u,hu,hlen,node,_,hpoint⟩ := Zarankiewicz.exists_finite_circle_coordinates
    0 1 (by norm_num) anchor hinj (by intro i; change squaredLength (anchor i-0)=1^2; simpa only [sub_zero,one_pow] using hcircle i)
  have hlen' : Zarankiewicz.squaredLength u=1 := by simpa only [one_pow] using hlen
  let f := fun t : ℝ => Zarankiewicz.similarityPoint 0 u (Zarankiewicz.circlePoint t)
  have hc : Continuous f := continuous_circle_similarity u
  have hex (i : Fin n) : ∃lo hi : ℝ, lo<hi ∧ Ioo lo hi ⊆ f ⁻¹' U i := by
    apply ((hU i).preimage hc).exists_Ioo_subset
    refine ⟨node i,?_⟩
    change f (node i)∈U i
    rw [show f (node i)=anchor i from hpoint i]
    exact hanchor i
  choose lo hi hlt hsub using hex
  obtain ⟨t,ht,hp,hpc,hpa,hpt⟩ := exists_circle_points_in_parameter_intervals n lo hi hlt
  let p := fun i => f (t i)
  have hsim := Zarankiewicz.similarityPoint_injective 0 u hu
  refine ⟨p,fun i => hsub i (ht i),hsim.comp hp,?_,?_,?_⟩
  · intro i
    have hh := Zarankiewicz.similarityPoint_squaredLength 0 u (Zarankiewicz.circlePoint (t i))
    change Zarankiewicz.squaredLength
      (Zarankiewicz.similarityPoint 0 u (Zarankiewicz.circlePoint (t i)))=1
    have hbase : Zarankiewicz.squaredLength (Zarankiewicz.circlePoint (t i))=1 :=
      Zarankiewicz.circlePoint_on_unit_circle (t i)
    simpa only [sub_zero,hlen',hbase,one_mul] using hh
  · intro i j hij he
    apply hpa i j hij
    apply hsim
    rw [circle_similarity_add,circle_similarity_zero]
    exact he
  · exact circle_similarity_no_triples u hu _ hpt

end Paper170

end
end

section

/-! Generic positions in prescribed circle arcs, including arbitrary choices of chart cut. -/
noncomputable section
open Set
open scoped Classical
namespace Paper170

theorem exists_generic_circle_points_in_disjoint_arcs (n : ℕ) (U : Fin n → Set Plane)
    (hU : ∀i, IsOpen (U i))
    (hne : ∀i, (U i ∩ {x | squaredLength x=1}).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (U i ∩ {x | squaredLength x=1})
      (U j ∩ {x | squaredLength x=1}))) :
    ∃p : Fin n → Plane, (∀i, p i∈U i) ∧ Function.Injective p ∧
      (∀i, squaredLength (p i)=1) ∧ (∀i j, i≠j → p i+p j≠0) ∧
      ∀e f g : CompleteEdge n, e≠f → e≠g → f≠g →
        chordInterior p e ∩ chordInterior p f ∩ chordInterior p g=∅ := by
  choose anchor hanchor using hne
  have hinj : Function.Injective anchor := by
    intro i j hij
    by_contra h
    apply Set.disjoint_left.mp (hdisj h) (hanchor i)
    rw [hij]
    exact hanchor j
  exact exists_generic_circle_points_in_neighborhoods n anchor hinj (fun i => (hanchor i).2)
    U hU (fun i => (hanchor i).1)

theorem exists_circle_configuration_in_parameter_arcs (n : ℕ) (u : Plane)
    (hu : squaredLength u=1) (lo hi : Fin n → ℝ) (hinterval : ∀i, lo i<hi i)
    (hordered : ∀i j, i<j → hi i≤lo j) :
    ∃C : CircleConfiguration n, ∀i,
      C.point i∈(fun t : ℝ => Zarankiewicz.similarityPoint 0 u (Zarankiewicz.circlePoint t)) ''
        Ioo (lo i) (hi i) := by
  obtain ⟨t,ht,hinj,hcircle,hanti,htriple⟩ := exists_circle_points_in_parameter_intervals n lo hi hinterval
  have hmono : StrictMono t := fun i j hij => ((ht i).2.trans_le (hordered i j hij)).trans (ht j).1
  have hune : u≠0 := by
    intro h
    rw [h] at hu
    norm_num [squaredLength] at hu
  have hlen : Zarankiewicz.squaredLength u=1 := hu
  let p := fun i => Zarankiewicz.similarityPoint 0 u (Zarankiewicz.circlePoint (t i))
  have hsim := Zarankiewicz.similarityPoint_injective 0 u hune
  refine ⟨{
    point := p
    injective := hsim.comp hinj
    on_circle := ?_
    cyclic_order := ?_
    no_antipodal := ?_
    no_triple_chords := circle_similarity_no_triples u hune _ htriple },?_⟩
  · intro i
    change Zarankiewicz.squaredLength (p i)=1
    have hh := Zarankiewicz.similarityPoint_squaredLength 0 u (Zarankiewicz.circlePoint (t i))
    have hb : Zarankiewicz.squaredLength (Zarankiewicz.circlePoint (t i))=1 := hcircle i
    simpa only [sub_zero,hlen,hb,one_mul] using hh
  · intro i j k hij hjk
    have hh := Zarankiewicz.similarityPoint_det 0 u (Zarankiewicz.circlePoint (t i))
      (Zarankiewicz.circlePoint (t j)) (Zarankiewicz.circlePoint (t i)) (Zarankiewicz.circlePoint (t k))
    change 0 < Zarankiewicz.det2 (p j-p i) (p k-p i)
    rw [hh,hlen,one_mul]
    exact Zarankiewicz.circle_orient_pos _ _ _ (hmono hij) (hmono hjk)
  · intro i j hij he
    apply hanti i j hij
    apply hsim
    rw [circle_similarity_add,circle_similarity_zero]
    exact he
  · intro i
    exact ⟨t i,ht i,rfl⟩

end Paper170

end
end

section

noncomputable section
namespace Paper170

variable {V E : Type}

theorem admissible_drawing_exists [Fintype V] [Fintype E] (G : Graph V E) : Nonempty (AdmissibleDrawing G) := by
  obtain ⟨C⟩ := circle_configuration_exists (Fintype.card V)
  exact ⟨restrictedCompleteAdmissible G (Fintype.equivFin V).toEmbedding (twoPageAdmissible C)⟩

theorem minimum_drawing_exists [Fintype V] [Fintype E] (G : Graph V E) :
    ∃ D : AdmissibleDrawing G, crossingCount D = ordinaryCrossingNumber G ∧
      ∀ A : AdmissibleDrawing G, crossingCount D ≤ crossingCount A := by
  obtain ⟨D₀⟩ := admissible_drawing_exists G
  obtain ⟨D, hD⟩ := Paper170Geometry.crossingCount_attainment D₀
  refine ⟨D, hD, fun A => ?_⟩
  rw [hD]
  exact Paper170Geometry.ordinaryCrossingNumber_le_count A

end Paper170

end
end

end OAI
