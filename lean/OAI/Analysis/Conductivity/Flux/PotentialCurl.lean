import Mathlib
import OAI.Analysis.Conductivity.Branching.CrossingBlock
import OAI.Analysis.Conductivity.Variational.DirectionCalculus

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def potentialCurl (S : Fin 3 → Fin 3 → Coord3 → ℝ) (x : Coord3) (i : Fin 3) : ℝ :=
  ∑ j, direction (Pi.single j 1) (S i j) x

lemma potentialCurl_add {S T : Fin 3 → Fin 3 → Coord3 → ℝ}
    (hS : ∀ i j, Differentiable ℝ (S i j)) (hT : ∀ i j, Differentiable ℝ (T i j)) (x : Coord3) (i : Fin 3) :
    potentialCurl (fun i j x => S i j x+T i j x) x i = potentialCurl S x i+potentialCurl T x i := by
  simp only [potentialCurl,direction_add (hS _ _ _) (hT _ _ _),Finset.sum_add_distrib]

lemma potentialCurl_dilation {S : Fin 3 → Fin 3 → Coord3 → ℝ}
    (hS : ∀ i j, Differentiable ℝ (S i j)) (s r : ℝ) (c x : Coord3) (i : Fin 3) :
    potentialCurl (fun i j y => s*S i j (r • (y-c))) x i =
      s*r*potentialCurl S (r • (x-c)) i := by
  simp only [potentialCurl,direction_dilation (hS _ _),Finset.mul_sum]

lemma wedgePotential_diff {H : Coord3 → ℝ} (hH : Differentiable ℝ H) (a b i j : Fin 3) :
    Differentiable ℝ (wedgePotential a b H i j) := by
  unfold wedgePotential
  split <;> split <;> fun_prop

lemma potentialCurl_wedge {H : Coord3 → ℝ} (hH : Differentiable ℝ H) (a b : Fin 3) (x : Coord3) (i : Fin 3) :
    potentialCurl (wedgePotential a b H) x i =
      (if i=a then direction (Pi.single b 1) H x else 0) -
      (if i=b then direction (Pi.single a 1) H x else 0) :=
  wedgePotential_flux a b i hH x

lemma potentialCurl_congr_nhds {S T : Fin 3 → Fin 3 → Coord3 → ℝ} (x : Coord3)
    (h : ∀ i j, S i j =ᶠ[𝓝 x] T i j) (i : Fin 3) : potentialCurl S x i = potentialCurl T x i := by
  apply Finset.sum_congr rfl
  intro j _
  exact direction_congr_nhds (h i j) _

def crossingPotential (L : ℝ) (a b i j : Fin 3) (x : Coord3) : ℝ :=
  wedgePotential 0 a (fun y => deriv (crossingFirst L) (y 0)*sin (y a)) i j x +
  wedgePotential 0 b (fun y => (deriv (crossingSecond L) (y 0)/2)*sin (2*y b)) i j x +
  wedgePotential a b (angularStream (crossingResidualFirst L) (crossingResidualSecond L) a b) i j x

lemma crossingPotential_diff (L : ℝ) (a b i j : Fin 3) : Differentiable ℝ (crossingPotential L a b i j) := by
  have hf := (smooth_deriv_infty (crossingFirst_smooth L)).differentiable (by simp)
  have hg := (smooth_deriv_infty (crossingSecond_smooth L)).differentiable (by simp)
  have hF := (crossingResidualFirst_smooth L).differentiable (by simp)
  have hG := (crossingResidualSecond_smooth L).differentiable (by simp)
  apply Differentiable.add
  · apply Differentiable.add
    · exact wedgePotential_diff (by fun_prop) _ _ _ _
    · exact wedgePotential_diff (by fun_prop) _ _ _ _
  · exact wedgePotential_diff (angularStream_diff hF hG _ _) _ _ _ _

lemma crossingPotential_curl (L : ℝ) {a b : Fin 3} (ha : a≠0) (hb : b≠0) (hab : a≠b)
    (x : Coord3) (i : Fin 3) :
    potentialCurl (crossingPotential L a b) x i =
      (if i=0 then crossingCurrentZ L (x 0) (x a) (x b) else 0) +
      (if i=a then crossingCurrentX L (x 0) (x a) (x b) else 0) +
      (if i=b then crossingCurrentY L (x 0) (x a) (x b) else 0) := by
  have hf := (smooth_deriv_infty (crossingFirst_smooth L)).differentiable (by simp)
  have hg := (smooth_deriv_infty (crossingSecond_smooth L)).differentiable (by simp)
  have hF := (crossingResidualFirst_smooth L).differentiable (by simp)
  have hG := (crossingResidualSecond_smooth L).differentiable (by simp)
  let H : Coord3 → ℝ := fun y => deriv (crossingFirst L) (y 0)*sin (y a)
  let J : Coord3 → ℝ := fun y => (deriv (crossingSecond L) (y 0)/2)*sin (2*y b)
  have hH : Differentiable ℝ H := by dsimp only [H]; fun_prop
  have hJ : Differentiable ℝ J := by dsimp only [J]; fun_prop
  have hW := angularStream_diff hF hG a b
  have hdHa : direction (Pi.single a 1) H x = deriv (crossingFirst L) (x 0)*cos (x a) := by
    simpa [H,Ne.symm ha] using direction_scalar_sin hf 1 a a x
  have hdH0 : direction (Pi.single 0 1) H x = deriv (deriv (crossingFirst L)) (x 0)*sin (x a) := by
    simpa [H,ha,mul_comm] using direction_scalar_sin hf 1 0 a x
  have hg' : Differentiable ℝ (fun t => deriv (crossingSecond L) t/2) := by fun_prop
  have hgder (t : ℝ) : deriv (fun t => deriv (crossingSecond L) t/2) t =
      deriv (deriv (crossingSecond L)) t/2 := (hg t).hasDerivAt.div_const 2 |>.deriv
  have hdJb : direction (Pi.single b 1) J x = deriv (crossingSecond L) (x 0)*cos (2*x b) := by
    have hh := direction_scalar_sin hg' 2 b b x
    simp only [Ne.symm hb,ite_false,ite_true,mul_zero,add_zero] at hh
    dsimp only [J]
    rw [hh]
    ring
  have hdJ0 : direction (Pi.single 0 1) J x = deriv (deriv (crossingSecond L)) (x 0)/2*sin (2*x b) := by
    simpa only [J,hb,ite_false,ite_true,mul_zero,zero_mul,zero_add,mul_one,one_mul,hgder,mul_comm] using
      direction_scalar_sin hg' 2 0 b x
  have hx : -direction (Pi.single 0 1) H x +
      direction (Pi.single b 1) (angularStream (crossingResidualFirst L) (crossingResidualSecond L) a b) x =
      crossingCurrentX L (x 0) (x a) (x b) := by
    rw [hdH0,angularStream_b hF hG hb hab]
    unfold crossingCurrentX crossingResidualFirst
    have hc := Real.cos_two_mul (2*x b)
    have ht : 2*(2*x b)=4*x b := by ring
    rw [ht] at hc
    have hs := Real.sin_sq_add_cos_sq (2*x b)
    linear_combination
      (deriv (deriv (crossingFirst L)) (x 0)-9*crossingFirst L (x 0))*sin (x a)*hc +
      2*(deriv (deriv (crossingFirst L)) (x 0)-9*crossingFirst L (x 0))*sin (x a)*hs
  have hy : -direction (Pi.single 0 1) J x -
      direction (Pi.single a 1) (angularStream (crossingResidualFirst L) (crossingResidualSecond L) a b) x =
      crossingCurrentY L (x 0) (x a) (x b) := by
    rw [hdJ0,angularStream_a hF hG ha hab]
    unfold crossingCurrentY crossingResidualSecond
    have hs := Real.sin_two_mul (2*x b)
    have ht : 2*(2*x b)=4*x b := by ring
    rw [ht] at hs
    rw [hs]
    have hc := Real.sin_sq_add_cos_sq (x a)
    linear_combination (deriv (deriv (crossingSecond L)) (x 0)-crossingSecond L (x 0))/2*sin (2*x b)*hc
  change potentialCurl (fun i j x => wedgePotential 0 a H i j x + wedgePotential 0 b J i j x +
    wedgePotential a b (angularStream (crossingResidualFirst L) (crossingResidualSecond L) a b) i j x) x i = _
  have hHJ : ∀ i j, Differentiable ℝ (fun x => wedgePotential 0 a H i j x + wedgePotential 0 b J i j x) :=
    fun i j => (wedgePotential_diff hH 0 a i j).add (wedgePotential_diff hJ 0 b i j)
  rw [potentialCurl_add hHJ (fun i j => wedgePotential_diff hW a b i j),
    potentialCurl_add (fun i j => wedgePotential_diff hH 0 a i j) (fun i j => wedgePotential_diff hJ 0 b i j)]
  simp_rw [potentialCurl_wedge hH,potentialCurl_wedge hJ,potentialCurl_wedge hW]
  by_cases hi0 : i=0
  · subst i
    simp only [Ne.symm ha,Ne.symm hb,ite_false,ite_true,sub_zero,hdHa,hdJb,add_zero]
    rfl
  · by_cases hia : i=a
    · subst i
      simp only [ha,hab,ite_false,ite_true,zero_add,zero_sub,sub_zero,add_zero]
      exact hx
    · by_cases hib : i=b
      · subst i
        simp only [hb,Ne.symm hab,ite_false,ite_true,zero_add,zero_sub,sub_zero,add_zero]
        linarith [hy]
      · simp [hi0,hia,hib]

end ScalarConductivity

end

end OAI
