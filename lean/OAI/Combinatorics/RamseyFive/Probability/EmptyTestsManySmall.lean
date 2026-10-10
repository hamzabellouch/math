import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Entropy.EmptyWeight

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι H : Type*} [Fintype ι]

theorem emptyTests_many_small (L : ℝ≥0) (weight : ι→ℝ≥0) {R : ℕ}
    (E T : Finset H) (hT : T.Nonempty) (hTE : T⊆E) (lines : H→Finset ι)
    {a c b M : ℝ} (hc : 0≤c) (hb : 0<b)
    (hsmall : ∀h∈T,mass weight (lines h)≤a)
    (hM : ∑h∈E,mass weight (lines h)≤M) :
    let P := (R:ℝ)*(L:ℝ)
    let zmin := (T.card:ℝ)*Real.exp (-P*a)/2
    Real.exp (-P*a)/2-M*Real.exp (-P*c)/(b*zmin) ≤
      (scheduleMeasure (fun i => L*weight i) R).real
        {ω | zmin≤((emptyTests E lines ω).card:ℝ) ∧
          emptyWeight E lines (fun h => mass weight (lines h)) ω≤
            (c+b)*((emptyTests E lines ω).card:ℝ)} := by
  dsimp only
  let P := (R:ℝ)*(L:ℝ)
  let zmin := (T.card:ℝ)*Real.exp (-P*a)/2
  let μ := scheduleMeasure (fun i => L*weight i) R
  let z := fun ω : Fin R→ι→ℕ => ((emptyTests E lines ω).card:ℝ)
  let w := fun h => mass weight (lines h)
  let heavy := emptyWeight (E.filter fun h => c<w h) lines w (R:=R)
  let A := {ω : Fin R→ι→ℕ | zmin≤z ω}
  let G := {ω : Fin R→ι→ℕ | zmin≤z ω ∧ emptyWeight E lines w ω≤(c+b)*z ω}
  let Bad := {ω : Fin R→ι→ℕ | b*zmin≤heavy ω}
  have hz0 : 0<zmin := by
    dsimp [zmin]
    have : (0:ℝ)<T.card := Nat.cast_pos.mpr hT.card_pos
    positivity
  have ha : Real.exp (-P*a)/2≤μ.real A := by
    have hh := emptyTests_probability (R:=R) (fun i => L*weight i) E T hT hTE lines
      (a:=(L:ℝ)*a) (fun h hh => by
        have hi := mul_le_mul_of_nonneg_left (hsmall h hh) L.coe_nonneg
        simpa only [mass,NNReal.coe_mul,Finset.mul_sum] using hi)
    have he : -(R:ℝ)*((L:ℝ)*a)=-P*a := by dsimp [P];ring
    simpa only [he] using hh
  have hbad : μ.real Bad≤M*Real.exp (-P*c)/(b*zmin) :=
    heavy_empty_probability L weight E lines (mul_pos hb hz0) hM
  have hcover : A⊆G∪Bad := by
    intro ω hω
    by_cases hh : b*zmin≤heavy ω
    · exact Or.inr hh
    left
    refine ⟨hω,?_⟩
    have hd := emptyWeight_light_heavy E lines w hc ω
    change emptyWeight E lines w ω≤c*z ω+heavy ω at hd
    have hbz := mul_le_mul_of_nonneg_left hω hb.le
    have ht := lt_of_not_ge hh
    change b*zmin>heavy ω at ht
    linarith only [hd,hbz,ht]
  have hm : μ.real A≤μ.real G+μ.real Bad :=
    (measureReal_mono hcover (measure_ne_top _ _)).trans (measureReal_union_le G Bad)
  change Real.exp (-P*a)/2-M*Real.exp (-P*c)/(b*zmin)≤μ.real G
  linarith only [ha,hbad,hm]

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

lemma abs_bool_centered {b : ℝ} (hb : b∈Set.Icc 0 1) (u : Bool) :
    |(if u then (1:ℝ) else 0)-b|≤1 := by
  cases u <;> simp only [Bool.false_eq_true,ite_false,ite_true,zero_sub]
  · simpa only [abs_neg,abs_of_nonneg hb.1] using hb.2
  · rw [abs_of_nonneg (sub_nonneg.mpr hb.2)]
    linarith [hb.1]

lemma bool_product_error {R : ℕ} (u v : Fin R→Bool) {b : ℝ} (hb : b∈Set.Icc 0 1) :
    |(∏r,if u r then ((if v r then (1:ℝ) else 0)-b) else 0)-
      (if ∀r,u r=true ∧ v r=true then (1-b)^R else 0)|≤b := by
  by_cases hall : ∀r,u r=true ∧ v r=true
  · rw [ite_eq_left hall]
    have he : (∏r,if u r then ((if v r then (1:ℝ) else 0)-b) else 0)=(1-b)^R := by
      simp [fun r => (hall r).1,fun r => (hall r).2]
    rw [he,sub_self,abs_zero]
    exact hb.1
  rw [ite_eq_right hall,sub_zero]
  by_cases hu : ∀r,u r=true
  · have hv : ∃r,v r≠true := by
      by_contra h
      push Not at h
      exact hall fun r => ⟨hu r,h r⟩
    obtain ⟨r,hr⟩ := hv
    simp only [hu,ite_true,Finset.abs_prod]
    have hh := Finset.prod_le_prod_of_subset_of_le_one₀
      (s:={r}) (t:=(Finset.univ:Finset (Fin R)))
      (f:=fun r => |(if v r then (1:ℝ) else 0)-b|)
      (Finset.subset_univ _) (fun _ _ => abs_nonneg _)
      (fun s _ _ => abs_bool_centered hb (v s))
    simpa [Finset.prod_singleton,hr,abs_of_nonneg hb.1] using hh
  · obtain ⟨r,hr⟩ := not_forall.mp hu
    have hz : (∏s,if u s then ((if v s then (1:ℝ) else 0)-b) else 0)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ r) (ite_eq_right hr)
    rw [hz,abs_zero]
    exact hb.1

variable {ι H : Type*} [DecidableEq ι]

noncomputable def ownScore {R : ℕ} (s o : Finset ι) (b : ℝ) (ω : Fin R→ι→ℕ) : ℝ :=
  ∏r,emptyIndicator (s∩o) (ω r)*(emptyIndicator (s\o) (ω r)-b)

lemma emptyEvent_split (s o : Finset ι) (ω : ι→ℕ) :
    ω∈emptyEvent (s∩o) ∧ ω∈emptyEvent (s\o) ↔ ω∈emptyEvent s := by
  simp only [emptyEvent,Set.mem_pi,Finset.mem_coe,Set.mem_singleton_iff]
  constructor
  · intro ⟨h1,h2⟩ i hi
    by_cases ho : i∈o
    · exact h1 i (Finset.mem_inter.mpr ⟨hi,ho⟩)
    · exact h2 i (Finset.mem_sdiff.mpr ⟨hi,ho⟩)
  · intro h
    exact ⟨fun i hi => h i (Finset.mem_inter.mp hi).1,
      fun i hi => h i (Finset.mem_sdiff.mp hi).1⟩

lemma ownScore_error {R : ℕ} (s o : Finset ι) {b : ℝ} (hb : b∈Set.Icc 0 1)
    (ω : Fin R→ι→ℕ) :
    |ownScore s o b ω-(1-b)^R*allEmptyIndicator s ω|≤b := by
  have hh := bool_product_error (fun r => decide (ω r∈emptyEvent (s∩o)))
    (fun r => decide (ω r∈emptyEvent (s\o))) hb
  simp only [decide_eq_true_eq,emptyEvent_split] at hh
  convert hh using 1
  congr 2
  · unfold ownScore emptyIndicator
    apply Finset.prod_congr rfl
    intro r _
    simp only [Set.indicator_apply]
    split_ifs <;> ring
  · rw [allEmptyIndicator_eq_if]
    split_ifs <;> ring

theorem exceptionalScore_error {R : ℕ} (E : Finset H) (lines : H→Finset ι)
    (o : Finset ι) {b : ℝ} (hb : b∈Set.Icc 0 1) (ω : Fin R→ι→ℕ) :
    |(∑h∈E,ownScore (lines h) o b ω)-
      (1-b)^R*((emptyTests E lines ω).card:ℝ)|≤b*E.card := by
  rw [emptyTests_card,Finset.mul_sum,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑h∈E,|ownScore (lines h) o b ω-(1-b)^R*allEmptyIndicator (lines h) ω| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑_h∈E,b := Finset.sum_le_sum fun h _ => ownScore_error (lines h) o hb ω
    _ = _ := by simp [mul_comm]

end SharpRamseyFive.PoissonScore

end OAI
