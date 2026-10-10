import OAI.MathematicalPhysics.RapidForcing.FieldSyntax

namespace OAI


open scoped BigOperators Topology
open Set Filter
namespace RapidForcing

namespace ScaleData
def δQ (d : ScaleData) (n : ℕ) : ℚ := (1 / 2) ^ d.s n
def bQ (d : ScaleData) (n : ℕ) : ℚ := d.δQ (n + 1) * d.capacity (n + 1)
@[simp] lemma cast_deltaQ (d : ScaleData) (n : ℕ) : (d.δQ n : ℝ) = d.δ n := by simp [δQ, δ]
@[simp] lemma cast_bQ (d : ScaleData) (n : ℕ) : (d.bQ n : ℝ) = d.b n := by simp [bQ, b]
end ScaleData

namespace EffectiveProfile
namespace Formula
variable {d : ℕ}

def listSum (l : List (Formula d)) : Formula d := l.foldr Formula.add (Formula.const 0)
def listProd (l : List (Formula d)) : Formula d := l.foldr Formula.mul (Formula.const 1)
lemma value_listSum (l : List (Formula d)) (x : Fin d → ℝ) :
    (listSum l).value x = (l.map (fun a => a.value x)).sum := by
  induction l with
  | nil => simp [listSum, value]
  | cons h l ih => simpa [listSum, value] using congrArg (h.value x + ·) ih
lemma value_listProd (l : List (Formula d)) (x : Fin d → ℝ) :
    (listProd l).value x = (l.map (fun a => a.value x)).prod := by
  induction l with
  | nil => simp [listProd, value]
  | cons h l ih => simpa [listProd, value] using congrArg (h.value x * ·) ih

def switch (a : Formula d) : Formula d := Formula.profile (switchExpr 0) a
def theta (a : Formula d) : Formula d := switch ((Formula.mul (Formula.const 2) a).sub (Formula.const (1 / 2)))
def thetaDot (a : Formula d) : Formula d :=
  Formula.mul (Formula.const 2) (Formula.profile (switchExpr 1) ((Formula.mul (Formula.const 2) a).sub (Formula.const (1 / 2))))
lemma value_switch (a : Formula d) (x : Fin d → ℝ) :
    a.switch.value x = Real.smoothTransition (a.value x) := by
  simp [switch, value, switchExpr_value]
lemma value_theta (a : Formula d) (x : Fin d → ℝ) : a.theta.value x = θ (a.value x) := by
  simp [theta, value_switch, value_sub, value, θ]
lemma value_thetaDot (a : Formula d) (x : Fin d → ℝ) :
    a.thetaDot.value x = deriv θ (a.value x) := by
  have hd : HasDerivAt (fun t : ℝ => 2 * t - 1 / 2) 2 (a.value x) := by
    simpa using ((hasDerivAt_id (a.value x)).const_mul 2).sub_const (1 / 2)
  have hH : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hh := ((hH.differentiable (by simp) _).hasDerivAt).comp _ hd
  change a.thetaDot.value x = deriv (fun s : ℝ => Real.smoothTransition (2 * s - 1 / 2)) (a.value x)
  simpa [thetaDot, value, value_sub, switchExpr_value, iteratedDeriv_one, Function.comp_def, mul_comm] using hh.deriv.symm

def zeta (a : Fin 3 → Formula d) : Formula d := listProd ((List.finRange 3).map fun i =>
  Formula.mul (switch (Formula.mul (Formula.const 16) (Formula.add (a i) (Formula.const (1 / 8)))))
    (switch (Formula.mul (Formula.const 16) ((Formula.const (1 / 8)).sub (a i)))))
lemma value_zeta (a : Fin 3 → Formula d) (x : Fin d → ℝ) :
    (zeta a).value x = ζ (WithLp.toLp 2 (fun i => (a i).value x)) := by
  simp [zeta, value_listProd, value, value_switch, value_sub, ζ,
    List.finRange_succ, List.finRange_zero, Fin.prod_univ_three, mul_assoc]

def crossF (a b : Fin 3 → Formula d) : Fin 3 → Formula d :=
  ![(Formula.mul (a 1) (b 2)).sub (Formula.mul (a 2) (b 1)),
    (Formula.mul (a 2) (b 0)).sub (Formula.mul (a 0) (b 2)),
    (Formula.mul (a 0) (b 1)).sub (Formula.mul (a 1) (b 0))]
lemma value_crossF (a b : Fin 3 → Formula d) (x : Fin d → ℝ) :
    WithLp.toLp 2 (fun i => (crossF a b i).value x) =
      cross (WithLp.toLp 2 (fun i => (a i).value x)) (WithLp.toLp 2 (fun i => (b i).value x)) := by
  ext i
  fin_cases i <;> simp [crossF, cross, vec, value, value_sub]

def curlF (a : Fin 3 → Formula 5) : Fin 3 → Formula 5 :=
  ![((a 2).diff (spaceIndex 1)).sub ((a 1).diff (spaceIndex 2)),
    ((a 0).diff (spaceIndex 2)).sub ((a 2).diff (spaceIndex 0)),
    ((a 1).diff (spaceIndex 0)).sub ((a 0).diff (spaceIndex 1))]
lemma vectorField_curlF (a : Fin 3 → Formula 5) (ν t : ℝ) (x : Space) :
    vectorField (curlF a) ν t x = curl (vectorField a ν t) x := by
  have hs (i : Fin 3) := congrFun (congrFun (spatial_vectorField a ν i) t) x
  change ∀ i, fderiv ℝ (vectorField a ν t) x (basis i) = _ at hs
  ext i
  fin_cases i <;> simp [vectorField, scalarField, curlF, curl, vec, hs, value_sub]

def moving (a v : Fin 3 → ℚ) (δ τ : ℚ) : Fin 3 → Formula 5 :=
  let s := (Formula.var 0 : Formula 5).sub (Formula.const τ)
  let c := fun i => Formula.add (Formula.const (a i)) (Formula.mul s.theta (Formula.const (v i)))
  let y := fun i => (Formula.var (spaceIndex i) : Formula 5).sub (c i)
  let z := zeta (fun i => Formula.mul (Formula.const δ⁻¹) (y i))
  let speed := fun i => Formula.mul s.thetaDot (Formula.const (v i))
  curlF (fun i => Formula.mul z (Formula.mul (Formula.const (1 / 2)) (crossF speed y i)))

lemma deriv_affine_theta (a v : Space) (σ : ℝ) :
    deriv (fun s => a + θ s • v) σ = deriv θ σ • v := by
  exact (((theta_smooth.differentiable (by simp) σ).hasDerivAt).smul_const v |>.const_add a).deriv

lemma vectorField_moving (a v : Fin 3 → ℚ) (δ τ : ℚ) (ν t : ℝ) (x : Space) :
    vectorField (moving a v δ τ) ν t x =
      movingCurl (fun s => WithLp.toLp 2 (fun i => (a i : ℝ)) +
        θ s • WithLp.toLp 2 (fun i => (v i : ℝ))) δ (t - τ) x := by
  unfold moving
  rw [vectorField_curlF]
  unfold movingCurl
  congr 1
  funext y
  have hc : WithLp.toLp 2 (fun i => ((Formula.var (spaceIndex i) : Formula 5).sub
      (Formula.add (Formula.const (a i)) (Formula.mul ((Formula.var 0 : Formula 5).sub (Formula.const τ)).theta (Formula.const (v i))))).value
      (pack ν t y)) = y - (WithLp.toLp 2 (fun i => (a i : ℝ)) +
        θ (t - τ) • WithLp.toLp 2 (fun i => (v i : ℝ))) := by
    ext i
    fin_cases i <;> simp [value_sub, value, value_theta, pack, spaceIndex]
  have hc' : WithLp.toLp 2 (fun i => (Formula.mul (Formula.const δ⁻¹)
      ((Formula.var (spaceIndex i) : Formula 5).sub
        (Formula.add (Formula.const (a i)) (Formula.mul ((Formula.var 0 : Formula 5).sub (Formula.const τ)).theta (Formula.const (v i)))))).value
      (pack ν t y)) = (δ : ℝ)⁻¹ • (y - (WithLp.toLp 2 (fun i => (a i : ℝ)) +
        θ (t - τ) • WithLp.toLp 2 (fun i => (v i : ℝ)))) := by
    rw [← hc]
    ext i
    simp [value]
  have hv : WithLp.toLp 2 (fun i => (Formula.mul ((Formula.var 0 : Formula 5).sub (Formula.const τ)).thetaDot
      (Formula.const (v i))).value (pack ν t y)) =
      deriv θ (t - τ) • WithLp.toLp 2 (fun i => (v i : ℝ)) := by
    ext i
    simp [value, value_thetaDot, value_sub, pack]
  rw [deriv_affine_theta]
  have hcross := value_crossF (fun i => Formula.mul ((Formula.var 0 : Formula 5).sub (Formula.const τ)).thetaDot (Formula.const (v i)))
    (fun i => (Formula.var (spaceIndex i) : Formula 5).sub
      (Formula.add (Formula.const (a i)) (Formula.mul ((Formula.var 0 : Formula 5).sub (Formula.const τ)).theta (Formula.const (v i))))) (pack ν t y)
  rw [hc, hv] at hcross
  ext i
  have hi := congrArg (fun z : Space => z i) hcross
  simp only [vectorField, scalarField, PiLp.toLp_apply, value, value_zeta]
  simp only [value] at hc'
  rw [hc']
  simpa only [PiLp.smul_apply, smul_eq_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using congrArg (fun z : ℝ => ζ ((δ : ℝ)⁻¹ •
      (y - (WithLp.toLp 2 (fun i => (a i : ℝ)) + θ (t - τ) • WithLp.toLp 2 (fun i => (v i : ℝ))))) *
      ((1 / 2 : ℝ) * z)) hi

end Formula
end EffectiveProfile
end RapidForcing

end OAI
