import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricPairingCLM
import OAI.Geometry.TamingCompatibility.Elliptic.NormalSystem
import OAI.Geometry.TamingCompatibility.Hodge.HodgeFrozenEnergy

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeFrame
open ContinuousAlternatingMap ExteriorForms MetricForms MetricModel
open EuclideanEnergy
open HodgeNormalSymbol (W)

def wedgeBy (ξ : V →L[ℝ] ℝ) : MetricForms.Form V 2 →L[ℝ] MetricForms.Form V 3 :=
  wedgeOneBilinear (ofSubsingletonLIE (0 : Fin 1) ξ)
lemma wedgeBy_apply (ξ : V →L[ℝ] ℝ) (a : MetricForms.Form V 2) :
    wedgeBy ξ a = wedgeOne ξ a := rfl

def combine (a : Fin 6 → MetricForms.Form V 2) : W →L[ℝ] MetricForms.Form V 2 :=
  ∑ j, (EuclideanSpace.proj j).smulRight (a j)
lemma combine_apply (a : Fin 6 → MetricForms.Form V 2) (u : W) :
    combine a u = ∑ j, u j • a j := by
  simp only [combine,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply]

def combineThree (a : Fin 6 → MetricForms.Form V 3) : W →L[ℝ] MetricForms.Form V 3 :=
  ∑ j, (EuclideanSpace.proj j).smulRight (a j)
lemma combineThree_apply (a : Fin 6 → MetricForms.Form V 3) (u : W) :
    combineThree a u = ∑ j, u j • a j := by
  simp only [combineThree,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply]

lemma extDeriv_sum {f : Fin 6 → V → MetricForms.Form V 2} {x : V}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    extDeriv (fun y => ∑ j, f j y) x = ∑ j, extDeriv (f j) x := by
  simp only [extDeriv,fderiv_fun_sum (fun j _ => hf j)]
  change (alternatizeUncurryFinCLM ℝ V ℝ) (∑ j, fderiv ℝ (f j) x) = _
  rw [_root_.map_sum]
  rfl

lemma extDeriv_frame (f : Fin 6 → V → ℝ) (a : Fin 6 → V → MetricForms.Form V 2)
    {x : V} (hf : ∀ j, DifferentiableAt ℝ (f j) x)
    (ha : ∀ j, DifferentiableAt ℝ (a j) x) :
    extDeriv (fun y => ∑ j, f j y • a j y) x =
      (∑ j, f j x • extDeriv (a j) x) +
      ∑ i : Fin 4, wedgeOne (EuclideanSpace.proj i)
        (∑ j : Fin 6, (fderiv ℝ (f j) x (e i)) • a j x) := by
  rw [extDeriv_sum (f := fun j y => f j y • a j y) (fun j => (hf j).smul (ha j))]
  simp_rw [extDeriv_variable_smul (hf _) (ha _)]
  rw [Finset.sum_add_distrib]
  congr 1
  have he (j : Fin 6) : wedgeOne (fderiv ℝ (f j) x) (a j x) =
      ∑ i : Fin 4, (fderiv ℝ (f j) x (e i)) • wedgeOne (EuclideanSpace.proj i) (a j x) := by
    conv_lhs => rw [LocalMatrixOperator.covector_expansion (fderiv ℝ (f j) x)]
    change (wedgeOneRight (a j x)) (∑ i, (fderiv ℝ (f j) x (e i)) • EuclideanSpace.proj i) = _
    simp only [_root_.map_sum,_root_.map_smul,wedgeOneRight_apply]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change _ = wedgeBy (EuclideanSpace.proj i) (∑ j, (fderiv ℝ (f j) x (e i)) • a j x)
  simp only [_root_.map_sum,_root_.map_smul,wedgeBy_apply]

end TamingCompatibility.HodgeFrame

end
end

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open HodgeNormalSymbol (W)
open FormMetric (pairLeft pairRight)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
  (J : E →L[ℝ] E) (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : MetricForms.Form E 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
include hb h0 h1 h2 h3 hF hdim horth
lemma coordinates_star (a : MetricForms.Form E 2) :
    coordinates b (starTwo g J F a) = UnitaryFrame.star (coordinates b a) := by
  rw [coordinates_model g hdim b hb,coordinates_model g hdim b hb a,
    formEquiv_starTwo g J horth]
  apply HermitianHodge.coords_star
  · simp only [basisOfFrame_apply,LinearIsometry.coe_toContinuousLinearMap]
    change @Eq E (J (b 0)) (b 1)
    exact h0
  · simp only [basisOfFrame_apply,LinearIsometry.coe_toContinuousLinearMap]
    change @Eq E (J (b 1)) (-b 0)
    exact h1
  · simp only [basisOfFrame_apply,LinearIsometry.coe_toContinuousLinearMap]
    change @Eq E (J (b 2)) (b 3)
    exact h2
  · simp only [basisOfFrame_apply,LinearIsometry.coe_toContinuousLinearMap]
    change @Eq E (J (b 3)) (-b 2)
    exact h3
  · intro u v
    exact hF u v

omit horth in
lemma star_wedge_coordinate (ξ : E →L[ℝ] ℝ) (a : MetricForms.Form E 2) (i : Fin 4) :
    starThree g F (wedgeOne ξ a) ![b i] =
      UnitaryFrame.interior (WithLp.toLp 2 (fun j => ξ (b j))) (UnitaryFrame.star (coordinates b a)) i := by
  rw [AntiInvariantFrame.starThree_on_frame g hdim b hb J h0 h1 h2 h3 F hF]
  have ht : (fun l => b (FormMetric.tripleIndices i l)) =
      ![b (FormMetric.tripleIndices i 0),b (FormMetric.tripleIndices i 1),b (FormMetric.tripleIndices i 2)] := by
    ext l; fin_cases l <;> rfl
  rw [ht,wedgeOne_apply_three]
  fin_cases i <;>
    simp [UnitaryFrame.interior,UnitaryFrame.star,coordinates_apply,
      FormMetric.tripleIndices,pairLeft,pairRight] <;> ring

lemma star_wedge_star_coordinate (ξ : E →L[ℝ] ℝ) (a : MetricForms.Form E 2) (i : Fin 4) :
    starThree g F (wedgeOne ξ (starTwo g J F a)) ![b i] =
      UnitaryFrame.interior (WithLp.toLp 2 (fun j => ξ (b j))) (coordinates b a) i := by
  rw [star_wedge_coordinate g hdim b hb J h0 h1 h2 h3 F hF,
    coordinates_star g hdim b hb J horth h0 h1 h2 h3 F hF,UnitaryFrame.star_square]
end TamingCompatibility.HodgeFrame

end
end

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeNormalOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy HodgeFrame
open HodgeNormalSymbol (W Q)

def join (u v : V) : Q := WithLp.toLp 2 ![u 0,u 1,u 2,u 3,v 0,v 1,v 2,v 3]
def joinCLM : (V × V) →L[ℝ] Q := LinearMap.toContinuousLinearMap {
  toFun := fun p => join p.1 p.2
  map_add' := by intro a b; ext i; fin_cases i <;> simp [join]
  map_smul' := by intro c a; ext i; fin_cases i <;> simp [join] }
lemma joinCLM_apply (u v : V) : joinCLM (u,v) = join u v := rfl

def left (b : Fin 4 → V) : MetricForms.Form V 1 →L[ℝ] Q :=
  joinCLM ∘L (LocalMatrixOperator.frameVector b).prod 0
def right (b : Fin 4 → V) : MetricForms.Form V 1 →L[ℝ] Q :=
  joinCLM ∘L (0 : MetricForms.Form V 1 →L[ℝ] V).prod (LocalMatrixOperator.frameVector b)
lemma left_apply (b : Fin 4 → V) (a : MetricForms.Form V 1) :
    left b a = join (LocalMatrixOperator.frameVector b a) 0 := rfl
lemma right_apply (b : Fin 4 → V) (a : MetricForms.Form V 1) :
    right b a = join 0 (LocalMatrixOperator.frameVector b a) := rfl
lemma join_norm_sq (u v : V) : ‖join u v‖^2 = ‖u‖^2+‖v‖^2 := by
  simp [join,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
  ring
lemma left_add_right (b : Fin 4 → V) (a c : MetricForms.Form V 1) :
    left b a + right b c = join (LocalMatrixOperator.frameVector b a) (LocalMatrixOperator.frameVector b c) := by
  ext i; fin_cases i <;> simp [left_apply,right_apply,join]
lemma output_norm (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (a c : MetricForms.Form V 1) :
    ‖left b a+right b c‖^2 = pairing g a a+pairing g c c := by
  rw [left_add_right,join_norm_sq,← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq,LocalMatrixOperator.frameVector_pairing g b hb,
    LocalMatrixOperator.frameVector_pairing g b hb]

def rawPrincipal (g : Metric V) (F : MetricForms.Form V 2) (b : Fin 4 → V)
    (ψ φ : Fin 6 → MetricForms.Form V 2) (i : Fin 4) : W →L[ℝ] Q :=
  left b ∘L starThreeCLM g F ∘L wedgeBy (EuclideanSpace.proj i) ∘L combine φ +
    right b ∘L starThreeCLM g F ∘L wedgeBy (EuclideanSpace.proj i) ∘L combine ψ

def lower (g : Metric V) (F : MetricForms.Form V 2) (b : Fin 4 → V)
    (ψ φ : Fin 6 → V → MetricForms.Form V 2) (x : V) : W →L[ℝ] Q :=
  left b ∘L starThreeCLM g F ∘L combineThree (fun j => extDeriv (φ j) x) +
    right b ∘L starThreeCLM g F ∘L combineThree (fun j => extDeriv (ψ j) x)

lemma combine_basis (g : Metric V) (b : Fin 4 → V) (u : W) :
    combine (basisForm g b) u = reconstruct g b u := rfl
def starCLM (g : Metric V) (J : V →L[ℝ] V) (F : MetricForms.Form V 2) :
    MetricForms.Form V 2 →L[ℝ] MetricForms.Form V 2 :=
  ((MetricForms.pairingCLM g 2).flip F).smulRight F - compContinuousLinearMapCLM J
lemma starCLM_apply (g : Metric V) (J : V →L[ℝ] V) (F a : MetricForms.Form V 2) :
    starCLM g J F a = starTwo g J F a := rfl

lemma combine_star_basis (g : Metric V) (J : V →L[ℝ] V) (F : MetricForms.Form V 2)
    (b : Fin 4 → V) (u : W) :
    combine (fun j => starTwo g J F (basisForm g b j)) u = starTwo g J F (reconstruct g b u) := by
  rw [combine_apply,reconstruct_apply]
  change _ = starCLM g J F (∑ j, u j • basisForm g b j)
  simp only [_root_.map_sum,_root_.map_smul,starCLM_apply]

lemma rawPrincipal_eq (g : Metric V) (F : MetricForms.Form V 2) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (J : V →L[ℝ] V) (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
    (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v) (i : Fin 4) :
    rawPrincipal g F b (basisForm g b) (fun j => starTwo g J F (basisForm g b j)) i =
      HodgeFrozenEnergy.coefficient b i := by
  ext u k
  simp only [rawPrincipal,_root_.add_apply,ContinuousLinearMap.comp_apply,
    combine_basis,combine_star_basis,wedgeBy_apply,starThreeCLM_apply,
    left_apply,right_apply,PiLp.add_apply]
  have hA (t : Fin 4) := star_wedge_star_coordinate g (by simp [V]) b hb J horth h0 h1 h2 h3 F hF
    (EuclideanSpace.proj i) (reconstruct g b u) t
  have hB (t : Fin 4) := star_wedge_coordinate g (by simp [V]) b hb J h0 h1 h2 h3 F hF
    (EuclideanSpace.proj i) (reconstruct g b u) t
  simp only [coordinates_reconstruct g b hb] at hA hB
  fin_cases k <;>
    simp [join,LocalMatrixOperator.frameVector_apply,
      HodgeFrozenEnergy.coefficient,HodgeNormalSymbol.normalSymbol_apply,HodgeNormalSymbol.symbol]
  all_goals first | exact hA _ | exact hB _

lemma operator_expansion (g : Metric V) (F : MetricForms.Form V 2) (b : Fin 4 → V)
    (ψ φ : Fin 6 → V → MetricForms.Form V 2) (f : Fin 6 → V → ℝ) {x : V}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x)
    (hψ : ∀ j, DifferentiableAt ℝ (ψ j) x) (hφ : ∀ j, DifferentiableAt ℝ (φ j) x) :
    left b (starThree g F (extDeriv (fun y => ∑ j, f j y • φ j y) x)) +
      right b (starThree g F (extDeriv (fun y => ∑ j, f j y • ψ j y) x)) =
      (∑ i : Fin 4, rawPrincipal g F b (fun j => ψ j x) (fun j => φ j x) i
        (WithLp.toLp 2 (fun j => fderiv ℝ (f j) x (e i)))) +
      lower g F b ψ φ x (WithLp.toLp 2 (fun j => f j x)) := by
  rw [extDeriv_frame f φ hf hφ,extDeriv_frame f ψ hf hψ]
  simp only [rawPrincipal,lower,_root_.add_apply,ContinuousLinearMap.comp_apply,
    combine_apply,combineThree_apply,wedgeBy_apply]
  change left b (starThreeCLM g F (_ + _)) + right b (starThreeCLM g F (_ + _)) = _
  simp only [map_add,_root_.map_sum]
  rw [Finset.sum_add_distrib]
  abel
end TamingCompatibility.HodgeNormalOperator

end
end

end
end

end OAI
