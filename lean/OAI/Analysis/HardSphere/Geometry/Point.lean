import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates

abbrev Point := ℝ × (ℝ × ℝ)
def angle : Set ℝ := Ioo (-Real.pi) Real.pi

def spherePoint (r φ θ : ℝ) : Point :=
  (r*Real.sin φ,(r*Real.cos φ*Real.cos θ,r*Real.cos φ*Real.sin θ))

lemma measurable_angle : MeasurableSet angle := measurableSet_Ioo

lemma polar_integral (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p) = ∫⁻ θ in angle, ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal r*F (r*Real.cos θ,r*Real.sin θ) := by
  rw [← lintegral_comp_polarCoord_symm F]
  exact setLIntegral_prod_symm _ (by fun_prop)

lemma cylindrical_integral (F : Point → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p)=∫⁻ θ in angle, ∫⁻ z : ℝ, ∫⁻ r : ℝ,
      ENNReal.ofReal r*F (z,(r*Real.cos θ,r*Real.sin θ)) := by
  rw [Measure.volume_eq_prod,lintegral_prod _ hF.aemeasurable]
  have hp (z : ℝ) := polar_integral (fun p ↦ F (z,p)) (hF.comp (measurable_const.prodMk measurable_id))
  conv_lhs => arg 2; ext z; rw [hp z]
  have he (z θ : ℝ) : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r*F (z,(r*Real.cos θ,r*Real.sin θ)))=
      ∫⁻ r : ℝ, ENNReal.ofReal r*F (z,(r*Real.cos θ,r*Real.sin θ)) := by
    apply setLIntegral_eq_of_support_subset
    intro r hr
    by_contra h
    have hr0 : r≤0 := not_lt.mp h
    simp only [ENNReal.ofReal_of_nonpos hr0,zero_mul,Function.mem_support,ne_eq,not_true_eq_false] at hr
  simp_rw [he]
  apply lintegral_lintegral_swap
  exact (by fun_prop : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
    ENNReal.ofReal p.2*F (p.1.1,(p.2*Real.cos p.1.2,p.2*Real.sin p.1.2)))).lintegral_prod_right.aemeasurable

lemma spherical_integral (F : Point → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p)=∫⁻ θ in angle, ∫⁻ φ in angle, ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal (r^2*Real.cos φ)*F (spherePoint r φ θ) := by
  rw [cylindrical_integral F hF]
  apply lintegral_congr
  intro θ
  let G : ℝ × ℝ → ℝ≥0∞ := fun p ↦
    ENNReal.ofReal p.1*F (p.2,(p.1*Real.cos θ,p.1*Real.sin θ))
  have hG : Measurable G := by unfold G; fun_prop
  rw [← lintegral_prod_symm G hG.aemeasurable,← Measure.volume_eq_prod,polar_integral G hG]
  apply lintegral_congr
  intro φ
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp [G,spherePoint]
  rw [← mul_assoc,← ENNReal.ofReal_mul (le_of_lt hr)]
  congr 2
  ring

open Filter
open scoped Topology BigOperators

def sqRadius (x : Point) : ℝ := x.1^2+x.2.1^2+x.2.2^2

def direction (φ θ : ℝ) : Point :=
  (Real.sin φ,(Real.cos φ*Real.cos θ,Real.cos φ*Real.sin θ))

lemma spherePoint_eq (r φ θ : ℝ) : spherePoint r φ θ=r • direction φ θ := by
  ext <;> simp [spherePoint,direction,mul_assoc]

lemma sqRadius_smul (t : ℝ) (x : Point) : sqRadius (t • x)=t^2*sqRadius x := by
  simp only [sqRadius,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

lemma direction_unit (φ θ : ℝ) : sqRadius (direction φ θ)=1 := by
  have hp := Real.sin_sq_add_cos_sq φ
  have ht := Real.cos_sq_add_sin_sq θ
  dsimp [sqRadius,direction]
  nlinarith [sq_nonneg (Real.cos φ)]

lemma ray_terminal {K : Set Point} (hk : IsClosed K) (hc : Convex ℝ K) (h0 : (0:Point)∈K)
    {B : ℝ} (hB : 0≤B) (hb : ∀ x∈K, sqRadius x≤B^2) {ω : Point} (hu : sqRadius ω=1) :
    ∃ R : ℝ, 0≤R ∧ R≤B ∧ {t : ℝ | 0≤t ∧ t • ω∈K}=Icc 0 R := by
  let S : Set ℝ := {t : ℝ | 0≤t ∧ t • ω∈K}
  have hs0 : (0:ℝ)∈S := by simpa [S] using h0
  have hsclosed : IsClosed S := isClosed_Ici.inter (hk.preimage (continuous_id.smul continuous_const))
  have hsub : S⊆Icc 0 B := by
    intro t ht
    have hn := hb (t • ω) ht.2
    rw [sqRadius_smul,hu,mul_one] at hn
    exact ⟨ht.1,(sq_le_sq₀ ht.1 hB).mp hn⟩
  have hscompact : IsCompact S := isCompact_Icc.of_isClosed_subset hsclosed hsub
  have hsconvex : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),?_⟩
    simpa only [smul_eq_mul,add_smul,mul_smul] using hc hx.2 hy.2 ha hb hab
  let R := sSup S
  have hR : R∈S := hscompact.sSup_mem ⟨0,hs0⟩
  refine ⟨R,(hsub hR).1,(hsub hR).2,?_⟩
  ext t
  constructor
  · intro ht
    exact ⟨ht.1,le_csSup hscompact.bddAbove ht⟩
  · intro ht
    exact hsconvex.ordConnected.out hs0 hR ht

end HardSphere.SphericalCoordinates

namespace HardSphere.SphericalCoordinates
open scoped Topology

def axis0 : Point := (1,(0,0))
def axis1 : Point := (0,(1,0))
def axis2 : Point := (0,(0,1))

def gradSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Point → E) (x : Point) : ℝ :=
  ‖fderiv ℝ f x axis0‖^2+‖fderiv ℝ f x axis1‖^2+‖fderiv ℝ f x axis2‖^2

lemma linear_unit_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Point →L[ℝ] E) {ω : Point} (hu : sqRadius ω=1) :
    ‖D ω‖^2 ≤ ‖D axis0‖^2+‖D axis1‖^2+‖D axis2‖^2 := by
  have he : ω=ω.1 • axis0+ω.2.1 • axis1+ω.2.2 • axis2 := by
    ext <;> simp [axis0,axis1,axis2]
  have hn : ‖D ω‖ ≤ |ω.1| * ‖D axis0‖+|ω.2.1| * ‖D axis1‖+|ω.2.2| * ‖D axis2‖ := by
    have hd := congrArg D he
    simp only [map_add,map_smul] at hd
    rw [hd]
    calc
      _ ≤ (‖ω.1 • D axis0‖+‖ω.2.1 • D axis1‖)+‖ω.2.2 • D axis2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by simp only [norm_smul,Real.norm_eq_abs]
  have hcs (a b c A B C : ℝ) : (a*A+b*B+c*C)^2≤(a^2+b^2+c^2)*(A^2+B^2+C^2) := by
    nlinarith [sq_nonneg (a*B-b*A),sq_nonneg (a*C-c*A),sq_nonneg (b*C-c*B)]
  have hs := hcs |ω.1| |ω.2.1| |ω.2.2| ‖D axis0‖ ‖D axis1‖ ‖D axis2‖
  simp only [sq_abs] at hs
  change ω.1^2+ω.2.1^2+ω.2.2^2=1 at hu
  rw [hu,one_mul] at hs
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs

lemma gradSq_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Point → E) (x : Point) : 0≤gradSq f x := by unfold gradSq; positivity

lemma continuous_gradSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) : Continuous (gradSq f) := by
  have hd := hf.continuous_fderiv (by norm_num)
  unfold gradSq
  exact (((hd.clm_apply continuous_const).norm.pow 2).add
    ((hd.clm_apply continuous_const).norm.pow 2)).add
    ((hd.clm_apply continuous_const).norm.pow 2)

lemma ray_deriv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) {ω : Point} (hu : sqRadius ω=1) (t : ℝ) :
    ‖deriv (fun s : ℝ ↦ f (s • ω)) t‖^2≤gradSq f (t • ω) := by
  have hd := ((hf.differentiable (by norm_num) (t • ω)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const ω)
  have he : deriv (fun s : ℝ ↦ f (s • ω)) t=fderiv ℝ f (t • ω) ω := by
    simpa only [Function.comp_def,id_eq,one_smul] using hd.deriv
  rw [he]
  simpa only [one_smul,gradSq] using linear_unit_bound (fderiv ℝ f (t • ω)) hu

end HardSphere.SphericalCoordinates

end

end OAI
