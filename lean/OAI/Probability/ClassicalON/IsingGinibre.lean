import OAI.Probability.ClassicalON.GibbsCovariance

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def isingEnergy (left right : E → V) (e : E) (s : V → Bool) : ℝ :=
  signValue (s (left e))*signValue (s (right e))

def isingHamiltonian (left right : E → V) (b : E → ℝ) (s : V → Bool) : ℝ :=
  ∑ e,b e*isingEnergy left right e s

def isingMean (left right : E → V) (b : E → ℝ) (f : (V → Bool) → ℝ) : ℝ :=
  exponentialMean isingReference (isingHamiltonian left right b) f

def isingDoubleVariable (i : V×Bool) (p : V → Bool×Bool) : ℝ :=
  if i.2 then isingU (p i.1) else isingW (p i.1)

def isingDoubleEnergy (left right : E → V) (e : E) (p : V → Bool×Bool) : ℝ :=
  isingU (p (left e))*isingU (p (right e))+isingW (p (left e))*isingW (p (right e))

def isingDoubleDifference (left right : E → V) (e : E) (p : V → Bool×Bool) : ℝ :=
  2*(isingU (p (left e))*isingW (p (right e))+isingW (p (left e))*isingU (p (right e)))

omit [Fintype V] [Fintype E] in
theorem isingDoubleEnergy_cone (left right : E → V) (e : E) :
    MomentCone isingDoubleVariable (isingDoubleEnergy left right e) := by
  exact momentCone_add
    (momentCone_mul (momentCone_coordinate (left e,true)) (momentCone_coordinate (right e,true)))
    (momentCone_mul (momentCone_coordinate (left e,false)) (momentCone_coordinate (right e,false)))

omit [Fintype V] [Fintype E] in
theorem isingDoubleDifference_cone (left right : E → V) (e : E) :
    MomentCone isingDoubleVariable (isingDoubleDifference left right e) := by
  exact momentCone_mul (momentCone_const (by norm_num : (0 : ℝ)≤2)) (momentCone_add
    (momentCone_mul (momentCone_coordinate (left e,true)) (momentCone_coordinate (right e,false)))
    (momentCone_mul (momentCone_coordinate (left e,false)) (momentCone_coordinate (right e,true))))

omit [Fintype E] in
theorem isingDoubleVariable_moments (k : ℕ) (p : Fin k → V×Bool) :
    0≤∫ z : V → Bool×Bool,∏ i,isingDoubleVariable (p i) z
      ∂Measure.pi (fun _ => signLaw.prod signLaw) := by
  classical
  have hh := independent_moments_nonneg (V := V) (signLaw.prod signLaw)
    (fun b t => if b then isingU t else isingW t) isingUW_product_moment (List.ofFn p)
  simpa only [isingDoubleVariable,List.map_ofFn,List.prod_ofFn,Function.comp_def] using hh

omit [Fintype V] [Fintype E] in
theorem isingDoubleEnergy_identity (left right : E → V) (e : E) (p : V → Bool×Bool) :
    isingEnergy left right e (fun v => (p v).1)+
      isingEnergy left right e (fun v => (p v).2)=2*isingDoubleEnergy left right e p := by
  unfold isingEnergy isingDoubleEnergy isingU isingW
  ring

omit [Fintype V] [Fintype E] in
theorem isingDoubleDifference_identity (left right : E → V) (e : E) (p : V → Bool×Bool) :
    isingEnergy left right e (fun v => (p v).1)-
      isingEnergy left right e (fun v => (p v).2)=isingDoubleDifference left right e p := by
  unfold isingEnergy isingDoubleDifference isingU isingW
  ring

theorem ising_edge_covariance_nonneg (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0≤b e) (e f : E) :
    isingMean left right b (isingEnergy left right e)*
      isingMean left right b (isingEnergy left right f) ≤
    isingMean left right b (fun s => isingEnergy left right e s*isingEnergy left right f s) := by
  classical
  let T := isingEnergy left right
  let H := isingHamiltonian left right b
  let D := isingDoubleDifference left right
  let A := isingDoubleEnergy left right
  let μ := (isingReference (V := V)).prod (isingReference (V := V))
  let ν := Measure.pi (fun _ : V => signLaw.prod signLaw)
  let F : ((V → Bool)×(V → Bool)) → ℝ := fun p =>
    Real.exp (H p.1)*Real.exp (H p.2)*(T e p.1-T e p.2)*(T f p.1-T f p.2)
  apply covariance_nonneg_of_doubled isingReference (continuous_of_discreteTopology)
    (fun s => Real.exp_pos (H s)) continuous_of_discreteTopology continuous_of_discreteTopology
  change 0≤∫ p,F p ∂μ
  let h := measurePreserving_arrowProdEquivProdArrow Bool Bool V (fun _ => signLaw) (fun _ => signLaw)
  change 0≤∫ p,F p ∂(Measure.pi (fun _ : V => signLaw)).prod (Measure.pi (fun _ : V => signLaw))
  rw [← h.integral_comp' F]
  have he : (fun p => F (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool V p))=
      (fun p => (D e p*D f p)*Real.exp (∑ g,(2*b g)*A g p)) := by
    funext p
    change Real.exp (H (fun v => (p v).1))*Real.exp (H (fun v => (p v).2))*
      (T e (fun v => (p v).1)-T e (fun v => (p v).2))*
      (T f (fun v => (p v).1)-T f (fun v => (p v).2))=_
    rw [← Real.exp_add]
    have hH : H (fun v => (p v).1)+H (fun v => (p v).2)=∑ g,(2*b g)*A g p := by
      simp only [H,isingHamiltonian,← Finset.sum_add_distrib,← mul_add,isingDoubleEnergy_identity]
      apply Finset.sum_congr rfl; intro g _; change b g*(2*A g p)=(2*b g)*A g p; ring
    rw [hH]
    change Real.exp _*(isingEnergy _ _ _ _-isingEnergy _ _ _ _)*
      (isingEnergy _ _ _ _-isingEnergy _ _ _ _)=_
    rw [isingDoubleDifference_identity,isingDoubleDifference_identity]
    dsimp only [D]
    ring
  rw [he]
  apply integral_mul_sum_exp_nonneg ν continuous_of_discreteTopology
    (fun _ => continuous_of_discreteTopology) (fun g => 2*b g)
    (fun g => mul_nonneg (by norm_num) (hb g))
  intro k p
  apply momentCone_integral_nonneg ν (fun _ => continuous_of_discreteTopology)
    isingDoubleVariable_moments
  apply momentCone_mul
  · exact momentCone_mul (isingDoubleDifference_cone _ _ e) (isingDoubleDifference_cone _ _ f)
  · exact momentCone_finsetProd Finset.univ (fun i => A (p i))
      (fun i _ => isingDoubleEnergy_cone _ _ _)

end ClassicalON

end

end OAI
