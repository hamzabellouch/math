import Mathlib
import OAI.Combinatorics.UniformKServer.AllocationAnalysis

namespace OAI

                                     
section

/-! Companion §04: exact primitive input slopes on the entire simplex.  The
 constants do not depend on the number of children.  These estimates apply to
 the old flags after filtering, without requiring feasibility of that input. -/
namespace UniformKServer.AlphaStability
noncomputable section
open Set MeasureTheory Finset
open UniformKServer.LogPrimitive UniformKServer.Denominators UniformKServer.AlphaBounds

/-- Linearity in the two raw inputs, with the improper endpoint justified by
 the same integrable density as the original primitive. -/
theorem primitive_sub {D : ℝ → ℝ} {base a scale S Q S' Q' : ℝ}
    (hb : base ∈ Icc (0:ℝ) 1) (ha : a ∈ Icc (0:ℝ) 1)
    (hI : IntervalIntegrable (fun x => (S-Q/x)/D x) volume 0 1)
    (hI' : IntervalIntegrable (fun x => (S'-Q'/x)/D x) volume 0 1) :
    primitive D base scale S Q a-primitive D base scale S' Q' a =
      primitive D base scale (S-S') (Q-Q') a := by
  have hs : uIcc base a ⊆ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.uIcc_subset_Icc hb ha
  have he : (fun x => (S-S'-(Q-Q')/x)/D x) =
      fun x => (S-Q/x)/D x-(S'-Q'/x)/D x := by funext x; ring
  rw [primitive,primitive,primitive,he,intervalIntegral.integral_sub (hI.mono_set hs) (hI'.mono_set hs)]
  ring

theorem regular_integrable {h : ℝ} (hh : 1 ≤ h) (S Q : ℝ) :
    IntervalIntegrable (fun x => (S-Q/x)/regular h x) volume 0 1 :=
  integrand_integrable (by unfold regular; fun_prop)
    (by positivity : (0:ℝ) < 1/h) (fun x hx hx₁ => regular_lower hh hx hx₁) S Q

theorem marked_integrable {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (S Q : ℝ) :
    IntervalIntegrable (fun x => (S-Q/x)/marked u x) volume 0 1 :=
  integrand_integrable (by unfold marked; fun_prop)
    (by positivity : (0:ℝ) < u/4) (fun x hx hx₁ => marked_lower hu hu₁ hx hx₁) S Q

theorem regular_difference {h a : ℝ} (hh : 1 ≤ h) (ha : a ∈ Icc (0:ℝ) 1)
    (scale S Q S' Q' : ℝ) :
    |primitive (regular h) 0 scale S Q a-primitive (regular h) 0 scale S' Q' a| ≤
      |scale| *(|S-S'| *a+|Q-Q'|) := by
  rw [primitive_sub (by simp) ha (regular_integrable hh S Q) (regular_integrable hh S' Q')]
  exact regular_component hh ha scale (S-S') (Q-Q')

theorem marked_difference {u a : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (ha : a ∈ Icc (0:ℝ) 1)
    (scale S Q S' Q' : ℝ) :
    |primitive (marked u) 1 scale S Q a-primitive (marked u) 1 scale S' Q' a| ≤
      3*|scale| *(|S-S'| *(1-a)+|(S-S')-(Q-Q')|) := by
  rw [primitive_sub (by simp) ha (marked_integrable hu hu₁ S Q) (marked_integrable hu hu₁ S' Q')]
  exact marked_component hu hu₁ ha scale (S-S') (Q-Q')

variable {ι : Type*} [Fintype ι]

theorem sum_difference (B B' : ι → ℝ) : |(∑ i, B i)-(∑ i, B' i)| ≤ ∑ i, |B i-B' i| := by
  rw [←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

/-- Dimension-free whole-simplex input Lipschitz bound in an unmarked epoch. -/
theorem regular_input (h η a B B' : ι → ℝ) (scale E : ℝ)
    (hh : ∀ i, 1 ≤ h i) (ha : ∀ i, a i ∈ Icc (0:ℝ) 1)
    (hasum : ∑ i, a i=1) (hη : ∀ i, 0 ≤ η i) (hηE : ∀ i, η i ≤ E) :
    |(∑ i, primitive (regular (h i)) 0 scale (∑ r, B r) ((1+η i)*B i) (a i))-
      (∑ i, primitive (regular (h i)) 0 scale (∑ r, B' r) ((1+η i)*B' i) (a i))| ≤
      |scale| *(2+E)*(∑ i, |B i-B' i|) := by
  rw [←sum_sub_distrib]
  have hQ (i : ι) : |(1+η i)*B i-(1+η i)*B' i| ≤ (1+E)*|B i-B' i| := by
    rw [←mul_sub,abs_mul,abs_of_nonneg (by linarith [hη i] : 0 ≤ 1+η i)]
    exact mul_le_mul_of_nonneg_right (by linarith [hηE i]) (abs_nonneg _)
  calc
    _ ≤ ∑ i, |primitive (regular (h i)) 0 scale (∑ r, B r) ((1+η i)*B i) (a i)-
        primitive (regular (h i)) 0 scale (∑ r, B' r) ((1+η i)*B' i) (a i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |scale| *(|(∑ r, B r)-(∑ r, B' r)| *a i+(1+E)*|B i-B' i|) := by
      apply sum_le_sum
      intro i _
      exact (regular_difference (hh i) (ha i) ..).trans
        (mul_le_mul_of_nonneg_left (add_le_add_right (hQ i) _) (abs_nonneg scale))
    _ = |scale| *(|(∑ r, B r)-(∑ r, B' r)|+(1+E)*(∑ i, |B i-B' i|)) := by
      rw [←mul_sum,sum_add_distrib,←mul_sum,hasum,mul_one,←mul_sum]
    _ ≤ |scale| *((∑ i, |B i-B' i|)+(1+E)*(∑ i, |B i-B' i|)) :=
      mul_le_mul_of_nonneg_left (add_le_add_left (sum_difference B B') _) (abs_nonneg _)
    _ = _ := by ring


noncomputable def mixedPrimitive [DecidableEq ι] (o : ι) (u : ℝ)
    (h η B : ι → ℝ) (scale : ℝ) (a : ι → ℝ) (i : ι) : ℝ :=
  if i = o then primitive (marked u) 1 scale (∑ r, B r) ((1+η i)*B i) (a i)
  else primitive (regular (h i)) 0 scale (∑ r, B r) ((1+η i)*B i) (a i)

/-- The marked primitive retains a dimension-free input bound as u tends to
 zero. The estimate does not require input feasibility at the old state. -/
theorem marked_input [DecidableEq ι] (o : ι) (h η a B B' : ι → ℝ) (scale E u : ℝ)
    (hu : 0 < u) (hu₁ : u ≤ 1) (hh : ∀ i, i ≠ o → 1 ≤ h i)
    (ha : ∀ i, a i ∈ Icc (0:ℝ) 1) (hasum : ∑ i, a i=1)
    (hη : ∀ i, 0 ≤ η i) (hηE : ∀ i, η i ≤ E) :
    |(∑ i, mixedPrimitive o u h η B scale a i)-
      (∑ i, mixedPrimitive o u h η B' scale a i)| ≤
      |scale| * (11+4*E)*(∑ i, |B i-B' i|) := by
  let D := |(∑ i, B i)-(∑ i, B' i)|
  let V := ∑ i, |B i-B' i|
  let R (i : ι) := |scale| * (D*a i+(1+E)*|B i-B' i|)
  let M := 3*|scale| * (2*D+(1+E)*V)
  have hE : 0 ≤ E := (hη o).trans (hηE o)
  have hDV : D ≤ V := sum_difference B B'
  have hD : 0 ≤ D := abs_nonneg _
  have hV : 0 ≤ V := sum_nonneg fun i _ => abs_nonneg _
  have hiV (i : ι) : |B i-B' i| ≤ V := single_le_sum (fun j _ => abs_nonneg (B j-B' j)) (mem_univ i)
  have hQ (i : ι) : |(1+η i)*B i-(1+η i)*B' i| ≤ (1+E)*|B i-B' i| := by
    rw [←mul_sub,abs_mul,abs_of_nonneg (by linarith [hη i] : 0 ≤ 1+η i)]
    exact mul_le_mul_of_nonneg_right (by linarith [hηE i]) (abs_nonneg _)
  have hc (i : ι) : |mixedPrimitive o u h η B scale a i-
      mixedPrimitive o u h η B' scale a i| ≤ R i+(if i=o then M else 0) := by
    by_cases hi : i=o
    · subst i
      simp only [mixedPrimitive,ite_true]
      have hb := marked_difference hu hu₁ (ha o) scale (∑ i, B i) ((1+η o)*B o)
        (∑ i, B' i) ((1+η o)*B' o)
      have htri := abs_sub ((∑ i, B i)-(∑ i, B' i)) (((1+η o)*B o)-((1+η o)*B' o))
      have hqo : |(1+η o)*B o-(1+η o)*B' o| ≤ (1+E)*V :=
        (hQ o).trans (mul_le_mul_of_nonneg_left (hiV o) (by linarith))
      have hd : D*(1-a o) ≤ D := by nlinarith [(ha o).1]
      have ht : |(∑ i, B i)-(∑ i, B' i)-((1+η o)*B o-(1+η o)*B' o)| ≤ D+(1+E)*V := by
        exact htri.trans (add_le_add_right hqo D)
      have hm : |primitive (marked u) 1 scale (∑ i, B i) ((1+η o)*B o) (a o)-
          primitive (marked u) 1 scale (∑ i, B' i) ((1+η o)*B' o) (a o)| ≤ M :=
        hb.trans (mul_le_mul_of_nonneg_left (by dsimp [D] at hd ht ⊢; linarith) (by positivity))
      have hr : 0 ≤ R o := mul_nonneg (abs_nonneg scale)
        (add_nonneg (mul_nonneg hD (ha o).1) (mul_nonneg (by linarith) (abs_nonneg _)))
      exact hm.trans (le_add_of_nonneg_left hr)
    · simp only [mixedPrimitive,ite_eq_right hi,add_zero]
      exact (regular_difference (hh i hi) (ha i) ..).trans
        (mul_le_mul_of_nonneg_left (add_le_add_right (hQ i) _) (abs_nonneg _))
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ i, |mixedPrimitive o u h η B scale a i-mixedPrimitive o u h η B' scale a i| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (R i+if i=o then M else 0) := sum_le_sum fun i _ => hc i
    _ = |scale| * (D+(1+E)*V)+M := by
      rw [sum_add_distrib,sum_ite_eq',ite_eq_left (Finset.mem_univ o)]
      dsimp [R,V]
      rw [←mul_sum,sum_add_distrib,←mul_sum,hasum,mul_one,←mul_sum]
    _ ≤ |scale| * (11+4*E)*V := by dsimp [M]; nlinarith [mul_le_mul_of_nonneg_left hDV (abs_nonneg scale)]


/-- Refreshing a regular size costs its prepared input, not the parent's
 total size. There is no summation over unchanged coordinates. -/
theorem regular_parameter {h h' a S B η η' E : ℝ} (hh : 1 ≤ h) (hh' : 1 ≤ h')
    (ha : a ∈ Icc (0:ℝ) 1) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hη : 0 ≤ η) (hη' : 0 ≤ η') (hE : η ≤ E) (hE' : η' ≤ E)
    (hprep : S*a ≤ (1+E)*B) (scale : ℝ) :
    |primitive (regular h) 0 scale S ((1+η)*B) a-
      primitive (regular h') 0 scale S ((1+η')*B) a| ≤
      4*|scale| * (1+E)*B := by
  have hc (η : ℝ) (hη : 0 ≤ η) (hηE : η ≤ E) (h : ℝ) (hh : 1 ≤ h) :
      |primitive (regular h) 0 scale S ((1+η)*B) a| ≤ 2*|scale| * (1+E)*B := by
    have hp := regular_component hh ha scale S ((1+η)*B)
    rw [abs_of_nonneg hS,abs_of_nonneg (by positivity : 0 ≤ (1+η)*B)] at hp
    calc
      _ ≤ |scale| * (S*a+(1+η)*B) := hp
      _ ≤ |scale| * (2*(1+E)*B) := mul_le_mul_of_nonneg_left
        (by nlinarith [mul_le_mul_of_nonneg_right hηE hB]) (abs_nonneg _)
      _ = _ := by ring
  have h₁ := hc η hη hE h hh
  have h₂ := hc η' hη' hE' h' hh'
  exact (abs_sub _ _).trans (by linarith)

/-- Cancellation at the marked base point 1 converts a parameter refresh
 into a side-size charge. This bound stays uniform as u tends to zero. -/
theorem marked_prepared_component {u a S B η κ E : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1)
    (ha : a ∈ Icc (0:ℝ) 1) (hS : 0 ≤ S) (hB : 0 ≤ B) (hBS : B ≤ S)
    (hη : 0 ≤ η) (hκ : η ≤ κ*u) (hprep : S*(1-a) ≤ (1+E)*(S-B)) (scale : ℝ) :
    |primitive (marked u) 1 scale S ((1+η)*B) a| ≤
      3*|scale| * ((2+E)*(S-B)+κ*u*S) := by
  have hp := marked_component hu hu₁ ha scale S ((1+η)*B)
  rw [abs_of_nonneg hS] at hp
  have hm : |S-(1+η)*B| ≤ S-B+η*B := by
    have he : S-(1+η)*B=(S-B)-η*B := by ring
    rw [he]
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (sub_nonneg.mpr hBS),abs_of_nonneg (mul_nonneg hη hB)])
  have hηS : η*B ≤ κ*u*S := (mul_le_mul_of_nonneg_left hBS hη).trans
    (mul_le_mul_of_nonneg_right hκ hS)
  exact hp.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end
end UniformKServer.AlphaStability

end

end OAI
