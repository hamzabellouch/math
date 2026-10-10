import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
variable {R σ ι : Type*} [CommRing R]

def Close (n : ℕ) (f g : ι → MvPowerSeries σ R) : Prop :=
  ∀ i e, e.degree < n → coeff e (f i) = coeff e (g i)

 theorem Close.refl (n : ℕ) (f : ι → MvPowerSeries σ R) : Close n f f :=
  fun _ _ _ => rfl
 theorem Close.symm {n : ℕ} {f g : ι → MvPowerSeries σ R} (h : Close n f g) :
    Close n g f := fun i e he => (h i e he).symm
 theorem Close.trans {n : ℕ} {f g h : ι → MvPowerSeries σ R}
    (hfg : Close n f g) (hgh : Close n g h) : Close n f h :=
  fun i e he => (hfg i e he).trans (hgh i e he)
 theorem Close.mono {n m : ℕ} {f g : ι → MvPowerSeries σ R}
    (h : Close n f g) (hm : m ≤ n) : Close m f g :=
  fun i e he => h i e (lt_of_lt_of_le he hm)
 theorem Close.zero (f g : ι → MvPowerSeries σ R) : Close 0 f g :=
  fun _ _ he => (Nat.not_lt_zero _ he).elim
 theorem Close.ext {f g : ι → MvPowerSeries σ R} (h : ∀ n, Close n f g) : f = g := by
  funext i
  ext e
  exact h (e.degree + 1) i e (Nat.lt_succ_self _)

variable (T : (ι → MvPowerSeries σ R) → (ι → MvPowerSeries σ R))
variable (hT : ∀ n f g, Close n f g → Close (n + 1) (T f) (T g))
include hT

 theorem iterate_step_close (n : ℕ) : Close n (T^[n] 0) (T^[n+1] 0) := by
  induction n with
  | zero => exact Close.zero _ _
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using hT n _ _ ih

 theorem iterate_later_close {n m : ℕ} (hnm : n ≤ m) :
    Close n (T^[n] 0) (T^[m] 0) := by
  induction m, hnm using Nat.le_induction with
  | base => exact Close.refl _ _
  | succ m hnm ih =>
    exact ih.trans ((iterate_step_close T hT m).mono hnm)

omit hT in

def fixedPoint : ι → MvPowerSeries σ R :=
  fun i e => coeff e ((T^[e.degree + 1] 0) i)

 theorem fixedPoint_close (n : ℕ) : Close n (fixedPoint T) (T^[n] 0) := by
  intro i e he
  exact iterate_later_close T hT (Nat.add_one_le_iff.mpr he) i e (Nat.lt_succ_self _)

 theorem fixedPoint_eq : T (fixedPoint T) = fixedPoint T := by
  apply Close.ext
  intro n
  apply (hT n _ _ (fixedPoint_close T hT n)).mono (Nat.le_succ n) |>.trans
  simpa only [Function.iterate_succ_apply'] using
    ((fixedPoint_close T hT (n+1)).symm.mono (Nat.le_succ n))

 theorem fixedPoint_unique {f : ι → MvPowerSeries σ R} (hf : T f = f) :
    f = fixedPoint T := by
  apply Close.ext
  intro n
  induction n with
  | zero => exact Close.zero _ _
  | succ n ih => simpa only [hf, fixedPoint_eq T hT] using hT n _ _ ih

 theorem exists_unique_fixedPoint : ∃! f, T f = f :=
  ⟨fixedPoint T, fixedPoint_eq T hT, fun _ h => fixedPoint_unique T hT h⟩

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
variable {R σ τ ι : Type*} [CommRing R]

def Vanishes (n : ℕ) (f : MvPowerSeries σ R) : Prop :=
  ∀ e, e.degree < n → coeff e f = 0

def Jet (n : ℕ) (f g : MvPowerSeries σ R) : Prop := Vanishes n (f-g)

 theorem Vanishes.iff_order {n : ℕ} {f : MvPowerSeries σ R} :
    Vanishes n f ↔ (n : ℕ∞) ≤ f.order := by
  constructor
  · exact nat_le_order
  · intro h e he
    exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast he) h)
 theorem Vanishes.zero (n : ℕ) : Vanishes n (0 : MvPowerSeries σ R) := by
  intro e he; exact map_zero _
 theorem Vanishes.mono {n m : ℕ} {f : MvPowerSeries σ R} (h : Vanishes n f)
    (hm : m ≤ n) : Vanishes m f := fun e he => h e (lt_of_lt_of_le he hm)
 theorem Vanishes.add {n : ℕ} {f g : MvPowerSeries σ R}
    (hf : Vanishes n f) (hg : Vanishes n g) : Vanishes n (f+g) := by
  intro e he; simp only [map_add, hf e he, hg e he, add_zero]
 theorem Vanishes.neg {n : ℕ} {f : MvPowerSeries σ R}
    (hf : Vanishes n f) : Vanishes n (-f) := by
  intro e he; simp only [map_neg, hf e he, neg_zero]
 theorem Vanishes.mul {n m : ℕ} {f g : MvPowerSeries σ R}
    (hf : Vanishes n f) (hg : Vanishes m g) : Vanishes (n+m) (f*g) := by
  apply Vanishes.iff_order.mpr
  calc
    ((n+m : ℕ) : ℕ∞) = (n : ℕ∞) + m := by simp only [Nat.cast_add]
    _ ≤ f.order + g.order := add_le_add (Vanishes.iff_order.mp hf) (Vanishes.iff_order.mp hg)
    _ ≤ (f*g).order := le_order_mul
 theorem Vanishes.all (f : MvPowerSeries σ R) : Vanishes 0 f :=
  fun _ h => (Nat.not_lt_zero _ h).elim
 theorem Vanishes.mul_right {n : ℕ} {f : MvPowerSeries σ R}
    (hf : Vanishes n f) (g : MvPowerSeries σ R) : Vanishes n (f*g) := by
  simpa only [Nat.add_zero] using hf.mul (Vanishes.all g)
 theorem Vanishes.mul_left {n : ℕ} {f : MvPowerSeries σ R}
    (hf : Vanishes n f) (g : MvPowerSeries σ R) : Vanishes n (g*f) := by
  simpa only [Nat.zero_add] using (Vanishes.all g).mul hf
 theorem Vanishes.sum {n : ℕ} (s : Finset ι) (f : ι → MvPowerSeries σ R)
    (hf : ∀ i ∈ s, Vanishes n (f i)) : Vanishes n (∑ i ∈ s, f i) := by
  classical
  intro e he
  simp only [map_sum]
  exact Finset.sum_eq_zero fun i hi => hf i hi e he
 theorem Vanishes.one_iff {f : MvPowerSeries σ R} :
    Vanishes 1 f ↔ constantCoeff f = 0 := by
  rw [Vanishes.iff_order]
  exact one_le_order_iff_constCoeff_eq_zero

 theorem Jet.iff_coeff {n : ℕ} {f g : MvPowerSeries σ R} :
    Jet n f g ↔ ∀ e, e.degree < n → coeff e f = coeff e g := by
  simp only [Jet, Vanishes, map_sub, sub_eq_zero]
 theorem Jet.refl (n : ℕ) (f : MvPowerSeries σ R) : Jet n f f :=
  Jet.iff_coeff.mpr fun _ _ => rfl
 theorem Jet.symm {n : ℕ} {f g : MvPowerSeries σ R} (h : Jet n f g) : Jet n g f :=
  Jet.iff_coeff.mpr fun e he => (Jet.iff_coeff.mp h e he).symm
 theorem Jet.trans {n : ℕ} {f g h : MvPowerSeries σ R}
    (hfg : Jet n f g) (hgh : Jet n g h) : Jet n f h :=
  Jet.iff_coeff.mpr fun e he => (Jet.iff_coeff.mp hfg e he).trans (Jet.iff_coeff.mp hgh e he)
 theorem Jet.mono {n m : ℕ} {f g : MvPowerSeries σ R} (h : Jet n f g)
    (hm : m ≤ n) : Jet m f g := Vanishes.mono h hm
 theorem Jet.neg {n : ℕ} {f g : MvPowerSeries σ R} (h : Jet n f g) : Jet n (-f) (-g) := by
  apply Jet.iff_coeff.mpr
  intro e he
  simp only [map_neg, Jet.iff_coeff.mp h e he]
 theorem Jet.sub {n : ℕ} {f g f' g' : MvPowerSeries σ R}
    (hf : Jet n f f') (hg : Jet n g g') : Jet n (f-g) (f'-g') := by
  apply Jet.iff_coeff.mpr
  intro e he
  simp only [map_sub, Jet.iff_coeff.mp hf e he, Jet.iff_coeff.mp hg e he]
 theorem jet_iff_truncTotal [Finite σ] {n : ℕ} {f g : MvPowerSeries σ R} :
    Jet n f g ↔ truncTotal n f = truncTotal n g := by
  rw [Jet.iff_coeff]
  constructor
  · intro h
    ext e
    by_cases he : e.degree < n
    · simpa only [coeff_truncTotal _ he] using h e he
    · simp only [coeff_truncTotal_eq_zero _ (not_lt.mp he)]
  · intro h e he
    simpa only [coeff_truncTotal _ he] using
      congrArg (fun polynomial : MvPolynomial σ R => polynomial.coeff e) h

 theorem Jet.subst [Finite σ] [Finite τ] {n : ℕ} {a b : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, Jet n (a i) (b i)) (f : MvPowerSeries σ R) :
    Jet n (MvPowerSeries.subst a f) (MvPowerSeries.subst b f) := by
  apply jet_iff_truncTotal.mpr
  have ha' := hasSubst_of_constantCoeff_zero ha
  have hb' := hasSubst_of_constantCoeff_zero hb
  have harg : (fun i => (truncTotal n (a i)).toMvPowerSeries) =
      (fun i => (truncTotal n (b i)).toMvPowerSeries) := by
    funext i
    exact congrArg MvPolynomial.toMvPowerSeries (jet_iff_truncTotal.mp (hab i))
  calc
    truncTotal n (MvPowerSeries.subst a f) = truncTotal n
      (MvPowerSeries.subst (fun i => (truncTotal n (a i)).toMvPowerSeries) f) :=
        truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le ha' (fun _ => le_refl n)
    _ = truncTotal n (MvPowerSeries.subst (fun i => (truncTotal n (b i)).toMvPowerSeries) f) :=
        congrArg (fun z => truncTotal n (MvPowerSeries.subst z f)) harg
    _ = truncTotal n (MvPowerSeries.subst b f) :=
        (truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le hb' (fun _ => le_refl n)).symm

end BoundaryOnly.FormalObstruction.FormalCorrection

end

end OAI
