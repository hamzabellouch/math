import Mathlib
import OAI.Probability.Subsphere.Geometry.MassBounds

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent.Affine

def AllAffineEstimate : Prop :=
  ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ k : ℕ,
    (d+1)/2 + 2*k ≤ d → ∀ W : ℝ, 1 ≤ W →
    ∀ (J : Type v) [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J],
    (Fintype.card J : ℝ) ≤ W → W^(1/((d/8 : ℕ) : ℝ)) ≤ (2 : ℝ)^d →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Ω → Fixed.Stream (Vector d) J (k*(d/16)),
    (∀ᵐ ω ∂ρ, (L ω).BorelRules ∧ ∀ q, ∀ᵐ y ∂(L ω).output q, ‖y‖ = 1) →
    ∀ ell : ℕ, ell ≤ k → ∀ v : J, ∀ n : ℕ, (d+1)/2 + 2*ell ≤ n →
    ∀ A : Test d n,
    AEMeasurable (fun z : Sphere A.space × (Ω × (Fin (ell*(d/16)) → Vector d)) =>
      ((L z.2.1).suffix ((k-ell)*(d/16)) (ell*(d/16)) v).angularSuccess ε (A.point z.1) z.2.2)
      ((sphereLaw A.space).prod (ρ.prod (Fixed.rowsLaw (Vector d) (ell*(d/16))))) →
    (∫⁻ z : Sphere A.space × (Ω × (Fin (ell*(d/16)) → Vector d)),
      ((L z.2.1).suffix ((k-ell)*(d/16)) (ell*(d/16)) v).angularSuccess ε (A.point z.1) z.2.2
        ∂(sphereLaw A.space).prod (ρ.prod (Fixed.rowsLaw (Vector d) (ell*(d/16)))))
      ≤ ENNReal.ofReal (((16 * ((1000 : ℝ)^32)^ell * ε)/A.radius)^(2*(d/32)))

end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Fixed
namespace Stream
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J] [Nonempty J]
  {T : ℕ}

abbrev Tape (E J : Type*) (T : ℕ) := J × ((Fin T → ℝ) × (J → E))

def tapeLaw (L : Stream E J T) : Measure (Tape E J T) :=
  L.initial.toMeasure.prod ((Measure.pi (fun _ : Fin T => coinLaw)).prod
    (Measure.pi L.output))

instance tapeLaw_probability (L : Stream E J T) : IsProbabilityMeasure L.tapeLaw := by
  let : ∀ q, IsProbabilityMeasure (L.output q) := L.output_probability
  unfold tapeLaw
  infer_instance

instance estimateLaw_probability (L : Stream E J T) (s : E) (x : Fin T → E) :
    IsProbabilityMeasure (L.estimateLaw s x) := by
  apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
  exact ae_of_all _ L.output_probability

def stepPMF (L : Stream E J T) (s : E) (x : Fin T → E) (n : ℕ) (q : J) : PMF J :=
  if hn : n < T then L.transition (n+1) q (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s⟫)
  else PMF.pure q

def stepDet (L : Stream E J T) (s : E) (x : Fin T → E) (n : ℕ) (q : J) (r : ℝ) : J :=
  samplePMF (L.stepPMF s x n q) r

omit [FiniteDimensional ℝ E] [BorelSpace E] [MeasurableSingletonClass J] in
lemma stepDet_measurable (L : Stream E J T) (s : E) (x : Fin T → E) (n : ℕ) (q : J) :
    Measurable (L.stepDet s x n q) :=
  measurable_samplePMF (fun _ => measurable_const) measurable_id

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma stepDet_map (L : Stream E J T) (s : E) (x : Fin T → E) (n : ℕ) (q : J) :
    coinLaw.map (L.stepDet s x n q) = (L.stepPMF s x n q).toMeasure := samplePMF_map _

omit [FiniteDimensional ℝ E] [BorelSpace E] [MeasurableSpace J] [Fintype J]
  [MeasurableSingletonClass J] [Nonempty J] in
lemma run_eq_bind_chain (L : Stream E J T) (s : E) (x : Fin T → E) (n : ℕ) :
    L.run s x n = L.initial.bind (fun q => lawChain (L.stepPMF s x) q n) := by
  induction n with
  | zero => simp [run, lawChain]
  | succ n ih =>
    change (L.run s x n).bind (L.stepPMF s x n) = _
    rw [ih, PMF.bind_bind]
    rfl

def tapeEstimate (L : Stream E J T) (s : E) (ω : Tape E J T) (x : Fin T → E) : E :=
  ω.2.2 (detChain (L.stepDet s x) ω.1 T ω.2.1)

lemma measurable_detChain_param (L : Stream E J T) (hL : L.BorelRules)
    {X : Type*} [MeasurableSpace X]
    {s : X → E} {x : X → Fin T → E} {q : X → J}
    (hs : Measurable s) (hx : Measurable x) (hq : Measurable q) (n : ℕ)
    {r : X → Fin n → ℝ} (hr : Measurable r) :
    Measurable (fun z => detChain (L.stepDet (s z) (x z)) (q z) n (r z)) := by
  induction n with
  | zero => exact hq
  | succ n ih =>
    have hp : Measurable (fun z => detChain (L.stepDet (s z) (x z)) (q z) n (Fin.init (r z))) :=
      ih (by fun_prop)
    have hstep (a : J) : Measurable (fun z => L.stepDet (s z) (x z) n a (r z (Fin.last n))) := by
      unfold stepDet stepPMF
      split_ifs with hn
      · exact measurable_samplePMF (fun b => (hL (n+1) a b).comp
          (by fun_prop)) (by fun_prop)
      · exact measurable_samplePMF (fun _ => measurable_const) (by fun_prop)
    exact SubsphereRegression.measurable_select hstep hp

lemma measurable_tapeEstimate (L : Stream E J T) (hL : L.BorelRules)
    {X : Type*} [MeasurableSpace X]
    {s : X → E} {ω : X → Tape E J T} {x : X → Fin T → E}
    (hs : Measurable s) (hω : Measurable ω) (hx : Measurable x) :
    Measurable (fun z => L.tapeEstimate (s z) (ω z) (x z)) := by
  unfold tapeEstimate
  exact SubsphereRegression.measurable_select (h := fun a z => (ω z).2.2 a) (fun a => by fun_prop)
    (L.measurable_detChain_param hL hs hx (measurable_fst.comp hω) T
      (measurable_fst.comp (measurable_snd.comp hω)))

lemma lintegral_tapeEstimate (L : Stream E J T) (hL : L.BorelRules)
    (s : E) (x : Fin T → E) (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (L.tapeEstimate s ω x) ∂L.tapeLaw) = ∫⁻ u, f u ∂L.estimateLaw s x := by
  let : ∀ q, IsProbabilityMeasure (L.output q) := L.output_probability
  have hE : Measurable (fun ω => f (L.tapeEstimate s ω x)) :=
    hf.comp (L.measurable_tapeEstimate hL measurable_const measurable_id measurable_const)
  rw [tapeLaw, lintegral_prod _ hE.aemeasurable]
  calc
    _ = ∫⁻ q, ∫⁻ r : Fin T → ℝ, ∫⁻ u, f u
        ∂L.output (detChain (L.stepDet s x) q T r)
        ∂Measure.pi (fun _ => coinLaw) ∂L.initial.toMeasure := by
      apply lintegral_congr
      intro q
      rw [lintegral_prod (fun y : (Fin T → ℝ) × (J → E) => f (L.tapeEstimate s (q,y) x))
        (hE.comp (measurable_const.prodMk measurable_id)).aemeasurable]
      apply lintegral_congr
      intro r
      exact (measurePreserving_eval L.output (detChain (L.stepDet s x) q T r)).lintegral_comp hf
    _ = ∫⁻ q, ∫⁻ a, ∫⁻ u, f u ∂L.output a
        ∂(lawChain (L.stepPMF s x) q T).toMeasure ∂L.initial.toMeasure := by
      apply lintegral_congr
      intro q
      exact detChain_lintegral (L.stepDet_measurable s x) (L.stepDet_map s x) q T (fun a => ∫⁻ u, f u ∂L.output a)
    _ = ∫⁻ a, ∫⁻ u, f u ∂L.output a ∂(L.run s x T).toMeasure := by
      rw [run_eq_bind_chain, pmf_lintegral_bind]
    _ = _ := by
      rw [estimateLaw, Measure.lintegral_bind (measurable_of_countable _).aemeasurable hf.aemeasurable]

def tapeTransition (L : Stream E J T) (ω : Tape E J T) (n : ℕ) (q : J) (obs : E × ℝ) : J :=
  samplePMF (L.transition n q obs) (if h : n-1 < T then ω.2.1 ⟨n-1,h⟩ else 0)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [MeasurableSingletonClass J] in
lemma tapeTransition_measurable (L : Stream E J T) (hL : L.BorelRules)
    (ω : Tape E J T) (n : ℕ) (q : J) : Measurable (L.tapeTransition ω n q) :=
  measurable_samplePMF (hL n q) measurable_const

omit [FiniteDimensional ℝ E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamRoute_eq_detChain (L : Stream E J T) (s : E) (ω : Tape E J T)
    (x : Fin T → E) {n : ℕ} (hn : n ≤ T) :
    SubsphereRegression.streamRoute (L.tapeTransition ω) 0 n ω.1
      ((fun i => x (Fin.castLE hn i)), fun i => ⟪s,x (Fin.castLE hn i)⟫) =
      detChain (L.stepDet s x) ω.1 n (fun i => ω.2.1 (Fin.castLE hn i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [SubsphereRegression.fin_prefix_snoc hn x,
      SubsphereRegression.fin_prefix_snoc hn (fun i => ⟪s,x i⟫),
      SubsphereRegression.streamRoute_snoc, ih (by omega),
      SubsphereRegression.fin_prefix_snoc hn ω.2.1, detChain_snoc]
    simp [tapeTransition, stepDet, stepPMF, show n < T by omega, real_inner_comm]

omit [FiniteDimensional ℝ E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma tapeEstimate_eq_route (L : Stream E J T) (s : E) (ω : Tape E J T) (x : Fin T → E) :
    L.tapeEstimate s ω x = ω.2.2
      (SubsphereRegression.streamRoute (L.tapeTransition ω) 0 T ω.1 (x,fun i => ⟪s,x i⟫)) := by
  simpa [tapeEstimate] using congrArg ω.2.2 (L.streamRoute_eq_detChain s ω x le_rfl).symm

end Stream
end SubsphereCurrent.Fixed
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Fixed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance sphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (sphereLaw E) :=
  SubsphereRegression.sphereLaw_probability
instance rowsLaw_probability (T : ℕ) : IsProbabilityMeasure (rowsLaw E T) := by
  unfold rowsLaw
  infer_instance

def euclideanTest (η : ℝ) (s y : E) : ℝ≥0∞ :=
  {y | ‖y-s‖ ≤ η}.indicator (fun _ => 1) y

lemma measurable_euclideanTest {X : Type*} [MeasurableSpace X]
    {s y : X → E} (hs : Measurable s) (hy : Measurable y) (η : ℝ) :
    Measurable (fun x => euclideanTest η (s x) (y x)) := by
  simpa only [euclideanTest,Set.indicator_apply,Set.mem_ofPred_eq] using
    (Measurable.ite (measurableSet_le ((hy.sub hs).norm) measurable_const)
      measurable_const measurable_const :
      Measurable (fun x => if ‖y x-s x‖ ≤ η then (1 : ℝ≥0∞) else 0))

namespace Stream
variable {J : Type*} [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J] [Nonempty J]
  {T : ℕ}

lemma euclideanSuccess_eq_integral_tape (L : Stream E J T) (hL : L.BorelRules)
    (η : ℝ) (s : E) (x : Fin T → E) :
    L.euclideanSuccess η s x = ∫⁻ ω, euclideanTest η s (L.tapeEstimate s ω x) ∂L.tapeLaw := by
  rw [L.lintegral_tapeEstimate hL s x (euclideanTest η s)
    (measurable_euclideanTest measurable_const measurable_id η)]
  have hS : MeasurableSet {y : E | ‖y-s‖ ≤ η} :=
    measurableSet_le (by fun_prop) measurable_const
  simp only [euclideanTest,euclideanSuccess,lintegral_indicator_const hS,one_mul]

lemma measurable_euclideanSuccess (L : Stream E J T) (hL : L.BorelRules) (η : ℝ) :
    Measurable (fun z : E × (Fin T → E) => L.euclideanSuccess η z.1 z.2) := by
  simp_rw [L.euclideanSuccess_eq_integral_tape hL η]
  exact (measurable_euclideanTest (measurable_fst.comp measurable_fst)
    (L.measurable_tapeEstimate hL (measurable_fst.comp measurable_fst)
      measurable_snd (measurable_snd.comp measurable_fst)) η).lintegral_prod_right

lemma average_euclideanSuccess_bound [Nontrivial E] (L : Stream E J T) (hL : L.BorelRules)
    {η : ℝ} (hη : 0 < η) {a q : ℕ}
    (ha : 2*a ≤ Module.finrank ℝ E-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    (∫⁻ z : Sphere E × (Fin T → E), L.euclideanSuccess η z.1.val z.2
      ∂(sphereLaw E).prod (rowsLaw E T)) ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (η^a)) *
        SubsphereRegression.streamFactor (E := E) (J := J) q ^ (T/q+1) := by
  simp_rw [L.euclideanSuccess_eq_integral_tape hL η]
  have hm : Measurable (fun z : (Sphere E × (Fin T → E)) × Tape E J T =>
      euclideanTest η z.1.1.val (L.tapeEstimate z.1.1.val z.2 z.1.2)) :=
    measurable_euclideanTest (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst))
      (L.measurable_tapeEstimate hL
        (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)) measurable_snd
        (measurable_snd.comp measurable_fst)) η
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ ≤ ∫⁻ _ : Tape E J T,
        (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (η^a)) *
          SubsphereRegression.streamFactor (E := E) (J := J) q ^ (T/q+1) ∂L.tapeLaw := by
      apply lintegral_mono
      intro ω
      have hb := SubsphereRegression.route_cap_bound (L.tapeTransition_measurable hL ω)
        ω.2.2 hη ha hq hqa T ω.1
      have hS : MeasurableSet {z : Sphere E × (Fin T → E) |
          dist z.1.val (L.tapeEstimate z.1.val ω z.2) ≤ η} :=
        measurableSet_le ((measurable_subtype_coe.comp measurable_fst).dist
          (L.measurable_tapeEstimate hL (measurable_subtype_coe.comp measurable_fst) measurable_const measurable_snd))
          measurable_const
      have he : (fun z : Sphere E × (Fin T → E) => euclideanTest η z.1.val
          (L.tapeEstimate z.1.val ω z.2)) =
          {z : Sphere E × (Fin T → E) |
            dist z.1.val (L.tapeEstimate z.1.val ω z.2) ≤ η}.indicator (fun _ => 1) := by
        funext z
        simp [euclideanTest,Set.indicator_apply,dist_eq_norm,norm_sub_rev]
      dsimp only
      rw [he,lintegral_indicator_const hS,one_mul]
      simpa only [L.tapeEstimate_eq_route, sphereLaw,rowsLaw,SubsphereRegression.sphereLaw] using hb
    _ = _ := by simp

omit [Nonempty J] in
lemma average_euclideanSuccess_le_one [Nontrivial E] (L : Stream E J T) (η : ℝ) :
    (∫⁻ z : Sphere E × (Fin T → E), L.euclideanSuccess η z.1.val z.2
      ∂(sphereLaw E).prod (rowsLaw E T)) ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : Sphere E × (Fin T → E), (1 : ℝ≥0∞)
        ∂(sphereLaw E).prod (rowsLaw E T) := lintegral_mono fun _ => prob_le_one
    _ = _ := by simp

end Stream
end SubsphereCurrent.Fixed
end
end
section
/-! Exact Gaussian reconstruction for an affine-sphere test. The complementary
rows are independent random parameters, not an extra sample channel to a learner. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent

lemma stdGaussian_prod_map {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] :
    ((stdGaussian E).prod (stdGaussian F)).map (WithLp.toLp 2) =
      stdGaussian (WithLp 2 (E × F)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_prod,charFun_stdGaussian,charFun_stdGaussian,charFun_stdGaussian,
    ← Complex.exp_add, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    WithLp.prod_norm_sq_eq_of_L2]
  congr 1
  push_cast
  change -(↑‖t.fst‖ : ℂ)^2 / 2 + -↑‖t.snd‖^2 / 2 = _
  ring

lemma gaussian_orthogonal_sum {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (H : Submodule ℝ E) :
    MeasurePreserving (fun z : H × Hᗮ => (z.1 : E) + (z.2 : E))
      ((stdGaussian H).prod (stdGaussian Hᗮ)) (stdGaussian E) := by
  have hmap := stdGaussian_map H.orthogonalDecomposition.symm
  rw [← stdGaussian_prod_map,Measure.map_map (by fun_prop) (by fun_prop)] at hmap
  refine ⟨by fun_prop,?_⟩
  convert hmap using 1
  congr 1

lemma gaussian_orthogonal_rows {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (H : Submodule ℝ E) (T : ℕ) :
    MeasurePreserving (fun z : (Fin T → H) × (Fin T → Hᗮ) =>
      fun i => (z.1 i : E) + (z.2 i : E))
      ((Measure.pi (fun _ => stdGaussian H)).prod (Measure.pi (fun _ => stdGaussian Hᗮ)))
      (Measure.pi (fun _ : Fin T => stdGaussian E)) := by
  have h1 := (measurePreserving_arrowProdEquivProdArrow H Hᗮ (Fin T)
    (fun _ => stdGaussian H) (fun _ => stdGaussian Hᗮ)).symm
  exact (measurePreserving_pi (fun _ : Fin T => (stdGaussian H).prod (stdGaussian Hᗮ))
    (fun _ => stdGaussian E) (fun _ => gaussian_orthogonal_sum H)).comp h1

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Affine
variable {d n : ℕ}
namespace Test
variable (A : Test d n)

lemma measurable_point : Measurable A.point := by unfold point; fun_prop

lemma norm_point (s : Sphere A.space) : ‖A.point s‖ = 1 := by
  have hs : ‖(s.val : Vector d)‖ = 1 := by
    rw [Submodule.norm_coe]
    exact mem_sphere_zero_iff_norm.mp s.property
  have ho : ⟪A.center, (s.val : Vector d)⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal s.val.property A.perpendicular
  have hz : ‖A.point s‖^2 = 1 := by
    rw [point,norm_add_sq_real,real_inner_smul_right,ho,mul_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos A.radius_positive,hs,mul_one]
    nlinarith [A.unit]
  nlinarith [norm_nonneg (A.point s)]

def project (y : Vector d) : A.space :=
  A.radius⁻¹ • A.space.orthogonalProjectionOnto (y-A.center)

lemma measurable_project : Measurable A.project := by unfold project; fun_prop

lemma project_point (s : Sphere A.space) : A.project (A.point s) = s.val := by
  simp [project,point,map_smul,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    smul_smul,A.radius_positive.ne']

lemma project_error (s : Sphere A.space) (y : Vector d) :
    ‖A.project y-s.val‖ ≤ ‖y-A.point s‖/A.radius := by
  rw [← A.project_point s]
  have he : A.project y - A.project (A.point s) =
      A.radius⁻¹ • A.space.orthogonalProjectionOnto (y-A.point s) := by
    simp only [project,← smul_sub,← map_sub]
    congr 2
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr A.radius_positive),div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left (A.space.norm_orthogonalProjectionOnto_apply_le _) (inv_nonneg.mpr A.radius_positive.le)).trans_eq (mul_comm _ _)

lemma angular_project_error {ε : ℝ} (s : Sphere A.space) (y : Vector d)
    (hy : ‖y‖ = 1) (h : Real.arccos ⟪y,A.point s⟫ ≤ ε) :
    ‖A.project y-s.val‖ ≤ ε/A.radius := by
  apply (A.project_error s y).trans
  apply div_le_div_of_nonneg_right _ A.radius_positive.le
  have hc : ‖y-A.point s‖ ≤ Real.arccos ⟪y,A.point s⟫ := by
    simpa only [dist_eq_norm] using (SubsphereRegression.chord_le_arccos
      (⟨y,mem_sphere_zero_iff_norm.mpr hy⟩ : Sphere (Vector d))
      ⟨A.point s,mem_sphere_zero_iff_norm.mpr (A.norm_point s)⟩)
  exact hc.trans h

lemma observation_identity (s : Sphere A.space) (x : A.space) (w : A.spaceᗮ) :
    ⟪(x : Vector d)+(w : Vector d),A.point s⟫ =
      ⟪(x : Vector d)+(w : Vector d),A.center⟫ + A.radius * ⟪x,s.val⟫ := by
  simp only [point,inner_add_right,real_inner_smul_right,inner_add_left]
  rw [Submodule.inner_left_of_mem_orthogonal s.val.property w.property]
  simp only [mul_zero,add_zero]
  rfl

end Test

namespace Simulation
variable {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ} (A : Test d n) (L : Fixed.Stream (Vector d) J T)

def stream (w : Fin T → A.spaceᗮ) : Fixed.Stream A.space J T where
  initial := L.initial
  transition t q obs :=
    let v : Vector d := obs.1.val + ((if h : t-1 < T then w ⟨t-1,h⟩ else 0) : A.spaceᗮ).val
    L.transition t q (v,⟪v,A.center⟫ + A.radius*obs.2)
  output q := (L.output q).map A.project
  output_probability q := by
    let := L.output_probability q
    infer_instance

omit [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma borel (hL : L.BorelRules) (w : Fin T → A.spaceᗮ) : (stream A L w).BorelRules := by
  intro t q a
  exact (hL t q a).comp (by fun_prop)

omit [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma run_eq (w : Fin T → A.spaceᗮ) (s : Sphere A.space) (x : Fin T → A.space) (l : ℕ) :
    (stream A L w).run s.val x l =
      L.run (A.point s) (fun i => (x i : Vector d)+(w i : Vector d)) l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    simp only [Fixed.Stream.run,ih]
    congr 1
    funext q
    split_ifs with hl
    · change L.transition (l+1) q _ = L.transition (l+1) q _
      congr 1
      simp [A.observation_identity s (x ⟨l,hl⟩) (w ⟨l,hl⟩),hl]
    · rfl

omit [Nonempty J] in
lemma success_le (w : Fin T → A.spaceᗮ) (s : Sphere A.space) (x : Fin T → A.space)
    (hu : ∀ q, ∀ᵐ y ∂L.output q, ‖y‖ = 1) (ε : ℝ) :
    L.angularSuccess ε (A.point s) (fun i => (x i : Vector d)+(w i : Vector d)) ≤
      (stream A L w).euclideanSuccess (ε/A.radius) s.val x := by
  have hA : MeasurableSet {y : Vector d | Real.arccos ⟪y,A.point s⟫ ≤ ε} :=
    measurableSet_le (by fun_prop) measurable_const
  have hB : MeasurableSet {y : A.space | ‖y-s.val‖ ≤ ε/A.radius} :=
    measurableSet_le (by fun_prop) measurable_const
  unfold Fixed.Stream.angularSuccess Fixed.Stream.euclideanSuccess Fixed.Stream.estimateLaw
  rw [Measure.bind_apply hA (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hB (measurable_of_countable _).aemeasurable,run_eq]
  apply lintegral_mono
  intro q
  change L.output q _ ≤ (L.output q).map A.project _
  rw [Measure.map_apply A.measurable_project hB]
  apply measure_mono_ae
  filter_upwards [hu q] with y hy
  exact fun h => A.angular_project_error s y hy h

end Simulation
end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Fixed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def angularTest (ε : ℝ) (s y : E) : ℝ≥0∞ :=
  {y | Real.arccos ⟪y,s⟫ ≤ ε}.indicator (fun _ => 1) y

lemma measurable_angularTest {X : Type*} [MeasurableSpace X]
    {s y : X → E} (hs : Measurable s) (hy : Measurable y) (ε : ℝ) :
    Measurable (fun x => angularTest ε (s x) (y x)) := by
  have he := Real.continuous_arccos.measurable.comp (hy.inner hs)
  simpa only [angularTest,Set.indicator_apply,Set.mem_ofPred_eq] using
    (Measurable.ite (measurableSet_le he measurable_const) measurable_const measurable_const :
      Measurable (fun x => if Real.arccos ⟪y x,s x⟫ ≤ ε then (1 : ℝ≥0∞) else 0))

namespace Stream
variable {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ}
lemma angularSuccess_eq_integral_tape (L : Stream E J T) (hL : L.BorelRules)
    (ε : ℝ) (s : E) (x : Fin T → E) :
    L.angularSuccess ε s x = ∫⁻ ω, angularTest ε s (L.tapeEstimate s ω x) ∂L.tapeLaw := by
  rw [L.lintegral_tapeEstimate hL s x (angularTest ε s)
    (measurable_angularTest measurable_const measurable_id ε)]
  have hS : MeasurableSet {y : E | Real.arccos ⟪y,s⟫ ≤ ε} :=
    measurableSet_le (by fun_prop) measurable_const
  simp only [angularTest,angularSuccess,lintegral_indicator_const hS,one_mul]

lemma measurable_angularSuccess (L : Stream E J T) (hL : L.BorelRules) (ε : ℝ) :
    Measurable (fun z : E × (Fin T → E) => L.angularSuccess ε z.1 z.2) := by
  simp_rw [L.angularSuccess_eq_integral_tape hL ε]
  exact (measurable_angularTest (measurable_fst.comp measurable_fst)
    (L.measurable_tapeEstimate hL (measurable_fst.comp measurable_fst)
      measurable_snd (measurable_snd.comp measurable_fst)) ε).lintegral_prod_right

lemma average_euclideanSuccess_zero_bound [Nontrivial E] (L : Stream E J 0) (hL : L.BorelRules)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (∫⁻ z : Sphere E × (Fin 0 → E), L.euclideanSuccess η z.1.val z.2
      ∂(sphereLaw E).prod (rowsLaw E 0)) ≤
      ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) *
        ENNReal.ofReal (η^(Module.finrank ℝ E-1)) := by
  simp_rw [L.euclideanSuccess_eq_integral_tape hL η]
  have hm : Measurable (fun z : (Sphere E × (Fin 0 → E)) × Tape E J 0 =>
      euclideanTest η z.1.1.val (L.tapeEstimate z.1.1.val z.2 z.1.2)) :=
    measurable_euclideanTest (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst))
      (L.measurable_tapeEstimate hL
        (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)) measurable_snd
        (measurable_snd.comp measurable_fst)) η
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ ≤ ∫⁻ _ : Tape E J 0, ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) *
        ENNReal.ofReal (η^(Module.finrank ℝ E-1)) ∂L.tapeLaw := by
      apply lintegral_mono
      intro ω
      have htest : Measurable (fun z : Sphere E × (Fin 0 → E) =>
          euclideanTest η z.1.val (ω.2.2 ω.1)) :=
        measurable_euclideanTest (measurable_subtype_coe.comp measurable_fst) measurable_const η
      change (∫⁻ z : Sphere E × (Fin 0 → E), euclideanTest η z.1.val (ω.2.2 ω.1)
        ∂(sphereLaw E).prod (rowsLaw E 0)) ≤ _
      rw [lintegral_prod _ htest.aemeasurable]
      simp only [lintegral_const,measure_univ,mul_one]
      have he : (fun s : Sphere E => euclideanTest η s.val (ω.2.2 ω.1)) =
          {s : Sphere E | dist s.val (ω.2.2 ω.1) ≤ η}.indicator (fun _ => 1) := by
        ext s
        simp [euclideanTest,Set.indicator_apply,dist_eq_norm,norm_sub_rev]
      rw [he,lintegral_indicator_const (measurableSet_le (by fun_prop) measurable_const),one_mul]
      exact SubsphereRegression.sphereLaw_cap_raw _ hη hη1 (Module.finrank_pos (R := ℝ) (M := E))
    _ = _ := by simp

end Stream
end SubsphereCurrent.Fixed
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Affine
namespace Simulation
local instance affineSimulationSphereLaw_probability {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] :
    IsProbabilityMeasure (sphereLaw E) := Fixed.sphereLaw_probability

variable {d n : ℕ} (A : Test d n) [Nontrivial A.space]
  {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ} (L : Fixed.Stream (Vector d) J T)

lemma reconstruct_preserving :
    MeasurePreserving
      (fun z : (Fin T → A.spaceᗮ) × (Sphere A.space × (Fin T → A.space)) =>
        (z.2.1,fun i => (z.2.2 i : Vector d)+(z.1 i : Vector d)))
      ((Fixed.rowsLaw A.spaceᗮ T).prod ((sphereLaw A.space).prod (Fixed.rowsLaw A.space T)))
      ((sphereLaw A.space).prod (Fixed.rowsLaw (Vector d) T)) := by
  have h1 : MeasurePreserving
      (fun z : (Fin T → A.spaceᗮ) × (Fin T → A.space) =>
        fun i => (z.2 i : Vector d)+(z.1 i : Vector d))
      ((Fixed.rowsLaw A.spaceᗮ T).prod (Fixed.rowsLaw A.space T))
      (Fixed.rowsLaw (Vector d) T) :=
    (gaussian_orthogonal_rows A.space T).comp
      (Measure.measurePreserving_swap (μ := Fixed.rowsLaw A.spaceᗮ T) (ν := Fixed.rowsLaw A.space T))
  exact ((MeasurePreserving.id (sphereLaw A.space)).prod h1).comp
    (measurePreserving_swapFirstTwo (Fixed.rowsLaw A.spaceᗮ T) (sphereLaw A.space)
      (Fixed.rowsLaw A.space T))

lemma integral_reconstruct (f : Sphere A.space × (Fin T → Vector d) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z, f z ∂(sphereLaw A.space).prod (Fixed.rowsLaw (Vector d) T)) =
      ∫⁻ w : Fin T → A.spaceᗮ, ∫⁻ z : Sphere A.space × (Fin T → A.space),
        f (z.1,fun i => (z.2 i : Vector d)+(w i : Vector d))
          ∂(sphereLaw A.space).prod (Fixed.rowsLaw A.space T)
        ∂Fixed.rowsLaw A.spaceᗮ T := by
  have hp := reconstruct_preserving (T := T) A
  rw [← hp.lintegral_comp hf]
  exact lintegral_prod _ (hf.comp hp.measurable).aemeasurable

omit [Nontrivial A.space] in
lemma measurable_angular_onTest (hL : L.BorelRules) (ε : ℝ) :
    Measurable (fun z : Sphere A.space × (Fin T → Vector d) =>
      L.angularSuccess ε (A.point z.1) z.2) := by
  have hm0 : Measurable (fun z : Vector d × (Fin T → Vector d) => L.angularSuccess ε z.1 z.2) :=
    L.measurable_angularSuccess hL ε
  have harg : Measurable (fun z : Sphere A.space × (Fin T → Vector d) => (A.point z.1,z.2)) :=
    (A.measurable_point.comp measurable_fst).prodMk measurable_snd
  exact Measurable.comp
    (g := fun z : Vector d × (Fin T → Vector d) => L.angularSuccess ε z.1 z.2)
    (f := fun z : Sphere A.space × (Fin T → Vector d) => (A.point z.1,z.2)) hm0 harg

lemma average_le_of_simulated (hL : L.BorelRules)
    (hu : ∀ q, ∀ᵐ y ∂L.output q, ‖y‖ = 1) (ε : ℝ) (B : ℝ≥0∞)
    (hb : ∀ w : Fin T → A.spaceᗮ,
      (∫⁻ z : Sphere A.space × (Fin T → A.space),
        (stream A L w).euclideanSuccess (ε/A.radius) z.1.val z.2
          ∂(sphereLaw A.space).prod (Fixed.rowsLaw A.space T)) ≤ B) :
    (∫⁻ z : Sphere A.space × (Fin T → Vector d),
      L.angularSuccess ε (A.point z.1) z.2
        ∂(sphereLaw A.space).prod (Fixed.rowsLaw (Vector d) T)) ≤ B := by
  calc
    _ = ∫⁻ w : Fin T → A.spaceᗮ, ∫⁻ z : Sphere A.space × (Fin T → A.space),
        L.angularSuccess ε (A.point z.1) (fun i => (z.2 i : Vector d)+(w i : Vector d))
          ∂(sphereLaw A.space).prod (Fixed.rowsLaw A.space T)
        ∂Fixed.rowsLaw A.spaceᗮ T :=
      integral_reconstruct A _ (measurable_angular_onTest A L hL ε)
    _ ≤ ∫⁻ _ : Fin T → A.spaceᗮ, B ∂Fixed.rowsLaw A.spaceᗮ T := by
      apply lintegral_mono
      intro w
      apply (lintegral_mono ?_).trans (hb w)
      intro z
      exact success_le A L w z.1 z.2 hu ε
    _ = _ := by simp

end Simulation
end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Weighted
variable {d n m : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
variable {V : Type*} [Fintype V]

def pullObservation (w : Fin m → A.spaceᗮ)
    (z : (Fin m → A.space) × (Fin m → ℝ)) : Observation d m :=
  (fun i => (z.1 i : Vector d)+(w i : Vector d),
   fun i => ⟪(z.1 i : Vector d)+(w i : Vector d),A.center⟫ + A.radius*z.2 i)

omit [Nontrivial A.space] in
lemma measurable_pullObservation (w : Fin m → A.spaceᗮ) : Measurable (pullObservation A w) := by
  unfold pullObservation
  fun_prop

lemma block_reconstruct (κ : V → Observation d m → ℝ≥0∞) (hκ : ∀ v, Measurable (κ v))
    (g : V → Sphere d → ℝ≥0∞) (hg : ∀ v, Measurable (g v)) :
    (ENNReal.ofReal A.radius)^((d : ℝ)/16) *
      (∫⁻ s, blockInput κ g (onTest A s) ∂Affine.sphereLaw A.space) =
    ∫⁻ w : Fin m → A.spaceᗮ,
      (∑ v, ∫⁻ s : Affine.Sphere A.space, weightedOnTest A (g v) s *
        (∫⁻ X : Fin m → A.space, κ v (pullObservation A w (X,fun i => ⟪s.val,X i⟫))
          ∂Measure.pi (fun _ => stdGaussian A.space)) ∂Affine.sphereLaw A.space)
      ∂Measure.pi (fun _ => stdGaussian A.spaceᗮ) := by
  classical
  let f (z : Affine.Sphere A.space × (Fin m → Vector d)) :=
    ∑ v, κ v (z.2,fun i => ⟪z.2 i,A.point z.1⟫)*g v (onTest A z.1)
  have hf : Measurable f := by
    apply Finset.measurable_sum
    intro v _
    exact ((hκ v).comp (measurable_snd.prodMk (Measurable.of_eval (fun index =>
      ((measurable_pi_apply index).comp measurable_snd).inner (A.measurable_point.comp measurable_fst))))).mul
      ((hg v).comp ((borel_onTest A).comp measurable_fst))
  have he : (∫⁻ s, blockInput κ g (onTest A s) ∂Affine.sphereLaw A.space) =
      ∫⁻ z, f z ∂(Affine.sphereLaw A.space).prod (Fixed.rowsLaw (Vector d) m) :=
    (lintegral_prod _ hf.aemeasurable).symm
  rw [he,Affine.Simulation.integral_reconstruct A f hf]
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)]
  apply lintegral_congr
  intro w
  have hr : Measurable (fun z : Affine.Sphere A.space × (Fin m → A.space) =>
      f (z.1,fun i => (z.2 i : Vector d)+(w i : Vector d))) := by
    apply hf.comp
    fun_prop
  rw [lintegral_prod _ hr.aemeasurable,
    ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)]
  have hmeas (v : V) : Measurable (fun s : Affine.Sphere A.space =>
      weightedOnTest A (g v) s *
        ∫⁻ X : Fin m → A.space, κ v (pullObservation A w (X,fun i => ⟪s.val,X i⟫))
          ∂Measure.pi (fun _ => stdGaussian A.space)) := by
    apply (measurable_weightedOnTest A (hg v)).mul
    apply Measurable.lintegral_prod_right
    apply (hκ v).comp
    apply (measurable_pullObservation A w).comp
    fun_prop
  rw [← lintegral_finsetSum _ (fun v _ => hmeas v)]
  apply lintegral_congr
  intro s
  have hm (v : V) : Measurable (fun X : Fin m → A.space =>
      κ v ((fun i => (X i : Vector d)+(w i : Vector d)),
        fun i => ⟪(X i : Vector d)+(w i : Vector d),A.point s⟫)*g v (onTest A s)) := by
    apply Measurable.mul _ measurable_const
    apply (hκ v).comp
    fun_prop
  change (ENNReal.ofReal A.radius)^((d : ℝ)/16) *
    (∫⁻ X, ∑ v, κ v ((fun i => (X i : Vector d)+(w i : Vector d)),
      fun i => ⟪(X i : Vector d)+(w i : Vector d),A.point s⟫)*g v (onTest A s)
        ∂Measure.pi (fun _ => stdGaussian A.space)) = _
  rw [lintegral_finsetSum _ (fun v _ => hm v),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hroute : (fun X : Fin m → A.space => κ v ((fun i => (X i : Vector d)+(w i : Vector d)),
      fun i => ⟪(X i : Vector d)+(w i : Vector d),A.point s⟫)) =
    fun X => κ v (pullObservation A w (X,fun i => ⟪s.val,X i⟫)) := by
    funext X
    congr 2
    funext i
    rw [A.observation_identity]
    simp only [real_inner_comm]
  have hmroute : Measurable (fun X : Fin m → A.space => κ v
      ((fun i => (X i : Vector d)+(w i : Vector d)),
        fun i => ⟪(X i : Vector d)+(w i : Vector d),A.point s⟫)) := by
    apply (hκ v).comp
    fun_prop
  rw [lintegral_mul_const _ hmroute,hroute]
  simp only [weightedOnTest]
  ac_rfl

end SubsphereCurrent.Weighted
end
end

end OAI
