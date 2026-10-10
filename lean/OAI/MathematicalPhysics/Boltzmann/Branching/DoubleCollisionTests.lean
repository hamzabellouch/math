import OAI.MathematicalPhysics.Boltzmann.Branching.SubmersionNullPreimage
import OAI.MathematicalPhysics.Boltzmann.Collision.AngularPairTests
import OAI.MathematicalPhysics.Boltzmann.Collision.SphereDirectionAbsolute
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityFourierMultiplier
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairPatchIdentity
import OAI.MathematicalPhysics.Boltzmann.Model
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

namespace OAI

section

/-! # Surjectivity of the two-output collision variation away from grazing and parallel normals -/
noncomputable section
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness

private def normalPlaneLift (n m : Velocity) (u v : ℝ) : Velocity :=
  ((u-(inner ℝ n m)*v)/(1-(inner ℝ n m)^2)) • n+
    ((v-(inner ℝ n m)*u)/(1-(inner ℝ n m)^2)) • m

private theorem inner_values {n m : Velocity}
    (hn : inner ℝ n n = 1) (hm : inner ℝ m m = 1)
    (hc : 1-(inner ℝ n m)^2 ≠ 0) (u v : ℝ) :
    inner ℝ (normalPlaneLift n m u v) n = u ∧
      inner ℝ (normalPlaneLift n m u v) m = v := by
  let c := inner ℝ n m
  let D := 1-c^2
  change inner ℝ (((u-c*v)/D) • n+((v-c*u)/D) • m) n = u ∧
    inner ℝ (((u-c*v)/D) • n+((v-c*u)/D) • m) m = v
  constructor
  · simp only [inner_add_left,real_inner_smul_left,hn,mul_one]
    rw [real_inner_comm n m]
    dsimp only [c,D] at *
    field_simp
    ring
  · simp only [inner_add_left,real_inner_smul_left,hm,mul_one]
    dsimp only [c,D] at *
    field_simp
    ring

/-- The derivative when the first normal varies through unit vectors. The normal
component of its variation is included, so the formula also applies to the
radially normalized extension off the sphere. -/
def doubleOutgoingVariation (d n m : Velocity) (z : (Velocity × Velocity) × Velocity) :
    Velocity × Velocity :=
  (z.1.1-(inner ℝ z.1.2 n+inner ℝ d z.2-2*(inner ℝ d n)*inner ℝ n z.2) • n-
      (inner ℝ d n) • z.2,
    z.1.1-(inner ℝ z.1.2 m) • m)

theorem doubleOutgoingVariation_surjective {d n m : Velocity}
    (hn : inner ℝ n n = 1) (hm : inner ℝ m m = 1)
    (hc : 1-(inner ℝ n m)^2 ≠ 0) (hd : inner ℝ d n ≠ 0) :
    Function.Surjective (doubleOutgoingVariation d n m) := by
  rintro ⟨a,b⟩
  let q := b-a
  let z := normalPlaneLift n m (inner ℝ q n) (inner ℝ q m)
  have hzn := (inner_values hn hm hc (inner ℝ q n) (inner ℝ q m)).1
  let k := q-z
  have hkn : inner ℝ k n = 0 := by
    change inner ℝ (q-normalPlaneLift n m (inner ℝ q n) (inner ℝ q m)) n = 0
    rw [inner_sub_left,hzn,sub_self]
  let dn := (inner ℝ d n)⁻¹ • k
  have hdn : inner ℝ n dn = 0 := by
    rw [real_inner_comm]
    simp only [dn,real_inner_smul_left,hkn,mul_zero]
  have hscale : (inner ℝ d n) • dn = k := by
    simp only [dn,smul_smul,mul_inv_cancel₀ hd,one_smul]
  let c := inner ℝ n m
  let D := 1-c^2
  let A := (inner ℝ q n-c*inner ℝ q m)/D
  let B := (inner ℝ q m-c*inner ℝ q n)/D
  have hzrepr : z = A • n+B • m := by
    dsimp only [A,B,c,D]
    rfl
  let dd := normalPlaneLift n m (A-inner ℝ d dn) (-B)
  obtain ⟨hddn,hddm⟩ := inner_values hn hm hc (A-inner ℝ d dn) (-B)
  refine ⟨((b+(inner ℝ dd m) • m,dd),dn),?_⟩
  apply Prod.ext
  · change b+(inner ℝ dd m) • m-
        (inner ℝ dd n+inner ℝ d dn-2*(inner ℝ d n)*inner ℝ n dn) • n-
        (inner ℝ d n) • dn = a
    rw [hdn,hddn,hddm,hscale]
    simp only [mul_zero,sub_zero,sub_add_cancel,neg_smul]
    have hq : q = A • n+B • m+k := by rw [← hzrepr]; dsimp only [k]; module
    change b-a = A • n+B • m+k at hq
    calc
      _ = b-(A • n+B • m+k) := by module
      _ = a := by rw [← hq]; abel
  · change b+(inner ℝ dd m) • m-(inner ℝ dd m) • m = b
    module

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The genuine doubled collision map has the surjective outgoing variation -/
noncomputable section
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness
namespace DoubleGain

abbrev Domain := (Velocity × Velocity) × Velocity

def velocityProjection : Domain →L[ℝ] Velocity :=
  (ContinuousLinearMap.fst ℝ Velocity Velocity).comp
    (ContinuousLinearMap.fst ℝ (Velocity × Velocity) Velocity)

def relativeProjection : Domain →L[ℝ] Velocity :=
  (ContinuousLinearMap.snd ℝ Velocity Velocity).comp
    (ContinuousLinearMap.fst ℝ (Velocity × Velocity) Velocity)

def normalProjection : Domain →L[ℝ] Velocity :=
  ContinuousLinearMap.snd ℝ (Velocity × Velocity) Velocity

def coefficientDifferential (d n : Velocity) : Domain →L[ℝ] ℝ :=
  (innerSL ℝ n).comp relativeProjection+(innerSL ℝ d).comp normalProjection-
    (2*inner ℝ d n) • ((innerSL ℝ n).comp normalProjection)

def differential (d n m : Velocity) : Domain →L[ℝ] (Velocity × Velocity) :=
  (velocityProjection-((inner ℝ d n) • normalProjection+
    (coefficientDifferential d n).smulRight n)).prod
    (velocityProjection-((innerSL ℝ m).comp relativeProjection).smulRight m)

def outgoing (m : Velocity) (z : Domain) : Velocity × Velocity :=
  (z.1.1-((inner ℝ z.1.2 z.2)*(inner ℝ z.2 z.2)⁻¹) • z.2,
    z.1.1-(inner ℝ z.1.2 m) • m)

theorem differential_apply (d n m : Velocity) (z : Domain) :
    differential d n m z = doubleOutgoingVariation d n m z := by
  apply Prod.ext
  · change z.1.1-((inner ℝ d n) • z.2+
      (inner ℝ n z.1.2+inner ℝ d z.2-2*(inner ℝ d n)*inner ℝ n z.2) • n) = _
    rw [real_inner_comm z.1.2 n]
    dsimp only [doubleOutgoingVariation]
    module
  · change z.1.1-(inner ℝ m z.1.2) • m = _
    rw [real_inner_comm z.1.2 m]
    rfl

def numeratorDifferential (d n : Velocity) : Domain →L[ℝ] ℝ :=
  (innerSL ℝ n).comp relativeProjection+(innerSL ℝ d).comp normalProjection

def denominatorDifferential (n : Velocity) : Domain →L[ℝ] ℝ :=
  (2 : ℝ) • ((innerSL ℝ n).comp normalProjection)

def coefficient (z : Domain) : ℝ := inner ℝ z.1.2 z.2*(inner ℝ z.2 z.2)⁻¹

theorem numerator_hasFDerivAt (v d n : Velocity) :
    HasFDerivAt (fun z : Domain => inner ℝ z.1.2 z.2)
      (numeratorDifferential d n) ((v,d),n) := by
  have h := (relativeProjection.hasFDerivAt (x := ((v,d),n))).inner ℝ
    (normalProjection.hasFDerivAt (x := ((v,d),n)))
  convert h using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro z
    change inner ℝ n z.1.2+inner ℝ d z.2 = inner ℝ d z.2+inner ℝ z.1.2 n
    rw [real_inner_comm z.1.2 n]
    ring

theorem denominator_hasFDerivAt (v d n : Velocity) :
    HasFDerivAt (fun z : Domain => inner ℝ z.2 z.2)
      (denominatorDifferential n) ((v,d),n) := by
  have h := (normalProjection.hasFDerivAt (x := ((v,d),n))).inner ℝ
    (normalProjection.hasFDerivAt (x := ((v,d),n)))
  convert h using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro z
    change 2*inner ℝ n z.2 = inner ℝ n z.2+inner ℝ z.2 n
    rw [real_inner_comm z.2 n]
    ring

theorem inverse_denominator_hasFDerivAt (v d n : Velocity) (hn : inner ℝ n n = 1) :
    HasFDerivAt (fun z : Domain => (inner ℝ z.2 z.2)⁻¹)
      (-denominatorDifferential n) ((v,d),n) := by
  have h := (hasDerivAt_inv (show inner ℝ n n ≠ 0 by rw [hn]; norm_num)).comp_hasFDerivAt
    ((v,d),n) (denominator_hasFDerivAt v d n)
  convert h using 1
  · rfl
  · rw [hn]
    norm_num

theorem coefficient_hasFDerivAt (v d n : Velocity) (hn : inner ℝ n n = 1) :
    HasFDerivAt coefficient (coefficientDifferential d n) ((v,d),n) := by
  have h := (numerator_hasFDerivAt v d n).mul (inverse_denominator_hasFDerivAt v d n hn)
  convert h using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro z
    change inner ℝ n z.1.2+inner ℝ d z.2-2*(inner ℝ d n)*inner ℝ n z.2 =
    (inner ℝ d n)*(-(2*inner ℝ n z.2))+(inner ℝ n n)⁻¹*
      (inner ℝ n z.1.2+inner ℝ d z.2)
    rw [hn]
    norm_num only
    ring


theorem outgoing_hasFDerivAt (v d n m : Velocity) (hn : inner ℝ n n = 1) :
    HasFDerivAt (outgoing m) (differential d n m) ((v,d),n) := by
  let x : Domain := ((v,d),n)
  have hv := velocityProjection.hasFDerivAt (x := x)
  have hnorm := normalProjection.hasFDerivAt (x := x)
  have hc : coefficient x = inner ℝ d n := by
    change inner ℝ d n*(inner ℝ n n)⁻¹ = inner ℝ d n
    rw [hn]
    norm_num
  have hmult : HasFDerivAt (fun z : Domain => coefficient z • z.2)
      ((inner ℝ d n) • normalProjection+(coefficientDifferential d n).smulRight n) x := by
    have h := (coefficient_hasFDerivAt v d n hn).smul hnorm
    rwa [hc] at h
  have hm : HasFDerivAt (fun z : Domain => inner ℝ z.1.2 m)
      ((innerSL ℝ m).comp relativeProjection) x := by
    have h := (innerSL ℝ m).hasFDerivAt.comp x (relativeProjection.hasFDerivAt (x := x))
    convert h using 1
    funext z
    exact real_inner_comm m z.1.2
  exact (hv.sub hmult).prodMk (hv.sub (hm.smul_const m))

theorem differential_surjective {d n m : Velocity}
    (hn : inner ℝ n n = 1) (hm : inner ℝ m m = 1)
    (hc : 1-(inner ℝ n m)^2 ≠ 0) (hd : inner ℝ d n ≠ 0) :
    Function.Surjective (differential d n m) := by
  intro y
  obtain ⟨z,hz⟩ := doubleOutgoingVariation_surjective hn hm hc hd y
  exact ⟨z,(differential_apply d n m z).trans hz⟩

end DoubleGain
end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Parallel and grazing normals occupy null sets in the doubled gain parameters -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem velocity_line_null {m : Velocity} (hm : m ≠ 0) :
    (volume : Measure Velocity) (Submodule.span ℝ {m}) = 0 := by
  apply MeasureTheory.Measure.addHaar_submodule
  intro htop
  have hdim := congrArg (fun S : Submodule ℝ Velocity => Module.finrank ℝ S) htop
  rw [finrank_top,finrank_span_singleton hm] at hdim
  norm_num at hdim

theorem normalized_parallel_mem_span {m n : Velocity} (hm : ‖m‖ = 1) (hn : n ≠ 0)
    (h : 1-(inner ℝ (NormedSpace.normalize n) m)^2 = 0) :
    n ∈ Submodule.span ℝ {m} := by
  let N := NormedSpace.normalize n
  let c := inner ℝ N m
  have hN : ‖N‖ = 1 := NormedSpace.norm_normalize hn
  have hc : c^2 = 1 := by dsimp only [c,N]; linarith
  have hzero : N-c • m = 0 := by
    apply norm_eq_zero.mp
    have he := norm_sub_sq_real N (c • m)
    rw [hN,norm_smul,hm,real_inner_smul_right] at he
    simp only [one_pow,Real.norm_eq_abs,mul_one,sq_abs] at he
    change ‖N-c • m‖^2 = 1-2*(c*c)+c^2 at he
    nlinarith [norm_nonneg (N-c • m)]
  have hNm : N ∈ Submodule.span ℝ {m} :=
    Submodule.mem_span_singleton.mpr ⟨c,(sub_eq_zero.mp hzero).symm⟩
  have hns := (Submodule.span ℝ {m}).smul_mem ‖n‖ hNm
  simpa only [N,NormedSpace.norm_smul_normalize] using hns

theorem regular_normal_ae {m : Velocity} (hm : ‖m‖ = 1) :
    ∀ᵐ n : Velocity ∂volume, n ≠ 0 ∧
      1-(inner ℝ (NormedSpace.normalize n) m)^2 ≠ 0 := by
  have hm0 : m ≠ 0 := norm_ne_zero_iff.mp (by rw [hm]; norm_num)
  have hout : ∀ᵐ n : Velocity ∂volume, n ∉ Submodule.span ℝ {m} := by
    apply ae_iff.mpr
    have hs : {a : Velocity | ¬a ∉ Submodule.span ℝ {m}} =
        (Submodule.span ℝ {m} : Set Velocity) := by ext a; simp
    rw [hs]
    exact velocity_line_null hm0
  filter_upwards [volume.ae_ne (0:Velocity),hout] with n hn hout
  exact ⟨hn,fun h => hout (normalized_parallel_mem_span hm hn h)⟩

theorem regular_grazing_ae {n : Velocity} (hn : n ≠ 0) :
    ∀ᵐ d : Velocity ∂volume, inner ℝ d (NormedSpace.normalize n) ≠ 0 := by
  have hN : NormedSpace.normalize n ≠ 0 := (NormedSpace.normalize_eq_zero_iff n).not.mpr hn
  have he := Published.affine_velocity_hyperplane_null 0 hN
  have hh : ∀ᵐ d : Velocity ∂volume, inner ℝ (NormedSpace.normalize n) d ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not,zero_add] using he
  filter_upwards [hh] with d hd
  rwa [real_inner_comm (NormedSpace.normalize n) d]

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The two-output submersion for nonzero, unnormalized collision normals -/
noncomputable section
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

def scaleNormal (r : ℝ) : Domain →L[ℝ] Domain :=
  (ContinuousLinearMap.fst ℝ (Velocity × Velocity) Velocity).prod
    (r • normalProjection)

theorem outgoing_scale (m v d n : Velocity) {r : ℝ} (hr : r ≠ 0) :
    outgoing m ((v,d),r • n) = outgoing m ((v,d),n) := by
  by_cases hn : n = 0
  · simp [hn,outgoing]
  have hnn : inner ℝ n n ≠ 0 := (real_inner_self_pos.mpr hn).ne'
  apply Prod.ext
  · change v-(inner ℝ d (r • n)*(inner ℝ (r • n) (r • n))⁻¹) • (r • n) =
      v-(inner ℝ d n*(inner ℝ n n)⁻¹) • n
    rw [real_inner_smul_right,real_inner_smul_left,real_inner_smul_right,smul_smul]
    congr 2
    field_simp
  · rfl

theorem outgoing_comp_scale (m : Velocity) {r : ℝ} (hr : r ≠ 0) :
    outgoing m ∘ scaleNormal r = outgoing m := by
  funext z
  exact outgoing_scale m z.1.1 z.1.2 z.2 hr

theorem scaleNormal_surjective {r : ℝ} (hr : r ≠ 0) :
    Function.Surjective (scaleNormal r) := by
  intro z
  refine ⟨(z.1,r⁻¹ • z.2),?_⟩
  change (z.1,r • r⁻¹ • z.2) = z
  rw [smul_smul,mul_inv_cancel₀ hr,one_smul]

theorem raw_outgoing_regular {v d n m : Velocity} (hn : n ≠ 0) (hm : ‖m‖ = 1)
    (hc : 1-(inner ℝ (NormedSpace.normalize n) m)^2 ≠ 0)
    (hd : inner ℝ d (NormedSpace.normalize n) ≠ 0) :
    ∃ A : Domain →L[ℝ] (Velocity × Velocity),
      HasFDerivAt (outgoing m) A ((v,d),n) ∧ Function.Surjective A := by
  let N := NormedSpace.normalize n
  have hN : inner ℝ N N = 1 := by
    rw [real_inner_self_eq_norm_sq,NormedSpace.norm_normalize hn]
    norm_num
  have hM : inner ℝ m m = 1 := by rw [real_inner_self_eq_norm_sq,hm]; norm_num
  have hr : ‖n‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hn)
  let S := scaleNormal ‖n‖⁻¹
  have H := (outgoing_hasFDerivAt v d N m hN).comp ((v,d),n)
    (S.hasFDerivAt (x := ((v,d),n)))
  have H' : HasFDerivAt (outgoing m)
      ((differential d N m).comp S) ((v,d),n) := by
    simpa only [S,outgoing_comp_scale m hr] using H
  refine ⟨(differential d N m).comp S,H',?_⟩
  exact (differential_surjective hN hM hc hd).comp (scaleNormal_surjective hr)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Full rank for almost every doubled outgoing collision parameter -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

def good (m d n : Velocity) : Prop := n ≠ 0 ∧
  1-(inner ℝ (NormedSpace.normalize n) m)^2 ≠ 0 ∧
    inner ℝ d (NormedSpace.normalize n) ≠ 0

theorem good_measurable (m : Velocity) :
    MeasurableSet {p : Velocity × Velocity | good m p.2 p.1} := by
  have hN : Measurable (fun p : Velocity × Velocity => NormedSpace.normalize p.1) := by
    unfold NormedSpace.normalize
    fun_prop
  have hc : Measurable (fun p : Velocity × Velocity =>
      1-(inner ℝ (NormedSpace.normalize p.1) m)^2) := by fun_prop
  have hd : Measurable (fun p : Velocity × Velocity => inner ℝ p.2 (NormedSpace.normalize p.1)) :=
    measurable_snd.inner hN
  exact (measurableSet_eq_fun measurable_fst measurable_const).compl.inter
    ((measurableSet_eq_fun hc measurable_const).compl.inter
      (measurableSet_eq_fun hd measurable_const).compl)

theorem good_ae (m : Velocity) (hm : ‖m‖ = 1) :
    ∀ᵐ p : Velocity × Velocity ∂(volume : Measure Velocity).prod volume, good m p.1 p.2 := by
  have hh : ∀ᵐ n : Velocity ∂volume, ∀ᵐ d : Velocity ∂volume, good m d n := by
    filter_upwards [regular_normal_ae hm] with n hn
    filter_upwards [regular_grazing_ae hn.1] with d hd
    exact ⟨hn.1,hn.2,hd⟩
  have hp := (Measure.ae_prod_iff_ae_ae (good_measurable m)).mpr hh
  exact (Measure.measurePreserving_swap (μ := (volume : Measure Velocity))
    (ν := (volume : Measure Velocity))).quasiMeasurePreserving.ae hp

theorem outgoing_rank_ae (m : Velocity) (hm : ‖m‖ = 1) :
    ∀ᵐ z : Domain ∂(volume : Measure (Velocity × Velocity)).prod volume,
      Function.Surjective (fderiv ℝ (outgoing m) z) := by
  have hp := good_ae m hm
  have htrip : ∀ᵐ z : Velocity × (Velocity × Velocity)
      ∂(volume : Measure Velocity).prod ((volume : Measure Velocity).prod volume),
      good m z.2.1 z.2.2 := Measure.quasiMeasurePreserving_snd.ae hp
  have hassoc := (measurePreserving_prodAssoc (volume : Measure Velocity)
    (volume : Measure Velocity) (volume : Measure Velocity)).quasiMeasurePreserving.ae htrip
  rw [← Measure.volume_eq_prod] at hassoc
  filter_upwards [hassoc] with z hz
  change good m z.1.2 z.2 at hz
  obtain ⟨A,hA,hsur⟩ := raw_outgoing_regular (v := z.1.1) hz.1 hm hz.2.1 hz.2.2
  change HasFDerivAt (outgoing m) A z at hA
  rwa [hA.fderiv]

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Local smoothness of the doubled outgoing map off the zero normal -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

def normalDomain : Set Domain := {z | z.2 ≠ 0}

theorem normalDomain_open : IsOpen normalDomain :=
  isClosed_singleton.isOpen_compl.preimage continuous_snd

theorem outgoing_measurable (m : Velocity) : Measurable (outgoing m) := by
  unfold outgoing
  fun_prop

theorem outgoing_contDiffAt (m : Velocity) {z : Domain} (hz : z ∈ normalDomain) :
    ContDiffAt ℝ 1 (outgoing m) z := by
  have hv : ContDiff ℝ 1 (fun x : Domain => x.1.1) := by fun_prop
  have hd : ContDiff ℝ 1 (fun x : Domain => x.1.2) := by fun_prop
  have hn : ContDiff ℝ 1 (fun x : Domain => x.2) := by fun_prop
  have hnum : ContDiff ℝ 1 (fun x : Domain => inner ℝ x.1.2 x.2) := hd.inner ℝ hn
  have hden : ContDiff ℝ 1 (fun x : Domain => inner ℝ x.2 x.2) := hn.inner ℝ hn
  have hne : inner ℝ z.2 z.2 ≠ 0 := (real_inner_self_pos.mpr hz).ne'
  have hfirst := hv.contDiffAt.sub ((hnum.contDiffAt.mul (hden.contDiffAt.inv hne)).smul hn.contDiffAt)
  have hsecond : ContDiff ℝ 1 (fun x : Domain => x.1.1-(inner ℝ x.1.2 m) • m) :=
    hv.sub ((hd.inner ℝ contDiff_const).smul contDiff_const)
  exact hfirst.prodMk hsecond.contDiffAt

theorem outgoing_contDiffOn (m : Velocity) : ContDiffOn ℝ 1 (outgoing m) normalDomain :=
  fun _ hz => (outgoing_contDiffAt m hz).contDiffWithinAt

theorem outgoing_hasFDerivAt_fderiv (m : Velocity) {z : Domain} (hz : z ∈ normalDomain) :
    HasFDerivAt (outgoing m) (fderiv ℝ (outgoing m) z) z :=
  (outgoing_contDiffAt m hz).differentiableAt_one.hasFDerivAt

theorem outgoing_fderiv_continuousAt (m : Velocity) {z : Domain} (hz : z ∈ normalDomain) :
    ContinuousAt (fderiv ℝ (outgoing m)) z :=
  ((outgoing_contDiffOn m).continuousOn_fderiv_of_isOpen normalDomain_open (by norm_num)).continuousAt
    (normalDomain_open.mem_nhds hz)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The joint outgoing law has a density on every compact nonzero-normal parameter set -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem compact_outgoing_law_absolutelyContinuous (m : Velocity) (hm : ‖m‖ = 1)
    {K : Set Domain} (hK : IsCompact K) (hKO : K ⊆ normalDomain) :
    (Measure.map (outgoing m)
      (((volume : Measure (Velocity × Velocity)).prod volume).restrict K)) ≪
        (volume : Measure (Velocity × Velocity)) := by
  have : Measure.IsAddHaarMeasure (volume : Measure (Velocity × Velocity)) := by
    change Measure.IsAddHaarMeasure ((volume : Measure Velocity).prod volume)
    infer_instance
  let Z : Set Domain := {z | ¬Function.Surjective (fderiv ℝ (outgoing m) z)}
  have hZ : ((volume : Measure (Velocity × Velocity)).prod volume) Z = 0 :=
    ae_iff.mp (outgoing_rank_ae m hm)
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [Measure.map_apply (outgoing_measurable m) hN]
  apply GainPullback.compact_submersion_null_preimage normalDomain_open hK hKO hZ
    (outgoing_measurable m)
    (fun _ hz => outgoing_hasFDerivAt_fderiv m hz)
    (fun _ hz => outgoing_fderiv_continuousAt m hz)
  · intro z hz
    exact not_not.mp hz.2
  · exact hN
  · exact hN0

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Absolute continuity of the full doubled outgoing law -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem outgoing_law_absolutelyContinuous (m : Velocity) (hm : ‖m‖ = 1) :
    (Measure.map (outgoing m) ((volume : Measure (Velocity × Velocity)).prod volume)) ≪
      (volume : Measure (Velocity × Velocity)) := by
  let μ : Measure Domain := (volume : Measure (Velocity × Velocity)).prod volume
  let : LocallyCompactSpace normalDomain := normalDomain_open.locallyCompactSpace
  let K (i : ℕ) : Set Domain := Subtype.val '' compactCovering normalDomain i
  have hK i : IsCompact (K i) := (isCompact_compactCovering normalDomain i).image continuous_subtype_val
  have hKO i : K i ⊆ normalDomain := by
    rintro _ ⟨z,_,rfl⟩
    exact z.property
  have hcover : (⋃ i, K i) = normalDomain := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      exact hKO i hi
    · intro hz
      obtain ⟨i,hi⟩ := exists_mem_compactCovering (⟨z,hz⟩ : normalDomain)
      exact mem_iUnion.mpr ⟨i,⟨⟨z,hz⟩,hi,rfl⟩⟩
  have hout : μ normalDomainᶜ = 0 := by
    have hgood : ∀ᵐ z ∂μ, z ∈ normalDomain :=
      Measure.quasiMeasurePreserving_snd.ae (volume.ae_ne (0 : Velocity))
    exact ae_iff.mp hgood
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [Measure.map_apply (outgoing_measurable m) hN]
  have hKi i : μ ((outgoing m ⁻¹' N) ∩ K i) = 0 := by
    have h := compact_outgoing_law_absolutelyContinuous m hm (hK i) (hKO i) hN0
    rw [Measure.map_apply (outgoing_measurable m) hN,Measure.restrict_apply (hN.preimage (outgoing_measurable m))] at h
    exact h
  have hinside : μ ((outgoing m ⁻¹' N) ∩ normalDomain) = 0 := by
    rw [← hcover,inter_iUnion]
    exact measure_iUnion_null hKi
  apply measure_mono_null (show outgoing m ⁻¹' N ⊆
    normalDomainᶜ ∪ ((outgoing m ⁻¹' N) ∩ normalDomain) from by
      intro z hz
      by_cases hzo : z ∈ normalDomain
      · exact Or.inr ⟨hz,hzo⟩
      · exact Or.inl hzo)
  exact measure_union_null hout hinside

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The doubled outgoing law with the physical surface-area normal measure -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

def angularOutgoing (m : Velocity) (z : (Velocity × Velocity) × Sphere) : Velocity × Velocity :=
  outgoing m (z.1,z.2.1)

theorem angularOutgoing_measurable (m : Velocity) : Measurable (angularOutgoing m) :=
  (outgoing_measurable m).comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

theorem direction_outgoing (e : Sphere) (m : Velocity) (p : Velocity × Velocity)
    {n : Velocity} (hn : n ≠ 0) :
    outgoing m (p,(sphereDirection e n).1) = outgoing m (p,n) := by
  dsimp only [sphereDirection]
  rw [dite_eq_right hn]
  exact outgoing_scale m p.1 p.2 n (inv_ne_zero (norm_ne_zero_iff.mpr hn))

theorem angular_outgoing_law_absolutelyContinuous (m : Velocity) (hm : ‖m‖ = 1) :
    (Measure.map (angularOutgoing m)
      ((volume : Measure (Velocity × Velocity)).prod sphereArea)) ≪
        (volume : Measure (Velocity × Velocity)) := by
  let e : Sphere := ⟨m,mem_sphere_zero_iff_norm.mpr hm⟩
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [Measure.map_apply (angularOutgoing_measurable m) hN]
  have hraw := outgoing_law_absolutelyContinuous m hm hN0
  rw [Measure.map_apply (outgoing_measurable m) hN] at hraw
  have hrawae : ∀ᵐ z : Domain ∂(volume : Measure (Velocity × Velocity)).prod volume,
      outgoing m z ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not,Set.preimage] using hraw
  have hsections := Measure.ae_ae_of_ae_prod hrawae
  have hsections' : ∀ᵐ p : Velocity × Velocity ∂volume,
      ∀ᵐ n : Sphere ∂sphereArea, angularOutgoing m (p,n) ∉ N := by
    filter_upwards [hsections] with p hp
    let A : Set Sphere := {n | angularOutgoing m (p,n) ∈ N}
    have hA : MeasurableSet A := hN.preimage
      ((angularOutgoing_measurable m).comp (measurable_const.prodMk measurable_id))
    have hdir : ∀ᵐ n : Velocity ∂volume, sphereDirection e n ∉ A := by
      filter_upwards [hp,volume.ae_ne (0 : Velocity)] with n hn hn0
      change outgoing m (p,(sphereDirection e n).1) ∉ N
      rwa [direction_outgoing e m p hn0]
    have hz : (Measure.map (sphereDirection e)
        ((volume : Measure Velocity).restrict (Metric.ball 0 1))) A = 0 := by
      rw [Measure.map_apply (sphereDirection_measurable e) hA]
      have hrestrict := ae_restrict_of_ae hdir (s := Metric.ball (0 : Velocity) 1)
      simpa only [not_not,Set.preimage] using ae_iff.mp hrestrict
    have ha := sphereArea_absolutelyContinuous_directions e hz
    apply ae_iff.mpr
    simpa only [not_not,A] using ha
  have hall : ∀ᵐ z : (Velocity × Velocity) × Sphere
      ∂(volume : Measure (Velocity × Velocity)).prod sphereArea, angularOutgoing m z ∉ N :=
    (Measure.ae_prod_iff_ae_ae (hN.preimage (angularOutgoing_measurable m)).compl).mpr hsections'
  simpa only [not_not,Set.preimage] using ae_iff.mp hall

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Absolute continuity for two physical outgoing velocities with common incoming pair -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

local instance doublePhysicalSFinite :
    SFinite ((volume : Measure (Velocity × Velocity)).prod sphereArea) :=
  Measure.prod.instSFinite

def relativePair (p : Velocity × Velocity) : Velocity × Velocity := (p.1,p.1-p.2)

theorem relativePair_measurePreserving : MeasurePreserving relativePair
    (volume : Measure (Velocity × Velocity)) volume := by
  have hneg := (MeasurePreserving.id (volume : Measure Velocity)).prod
    (Measure.measurePreserving_neg (volume : Measure Velocity))
  have hp := hneg.comp (measurePreserving_prod_sub
    (volume : Measure Velocity) (volume : Measure Velocity))
  change MeasurePreserving relativePair ((volume : Measure Velocity).prod volume)
    ((volume : Measure Velocity).prod volume)
  have he : Prod.map id Neg.neg ∘ (fun p : Velocity × Velocity => (p.1,p.2-p.1)) = relativePair := by
    funext p
    exact Prod.ext rfl (neg_sub _ _)
  rw [he] at hp
  exact hp

def physicalPairAt (m : Velocity) (z : (Velocity × Velocity) × Sphere) : Velocity × Velocity :=
  (scatterLeft z.1.1 z.1.2 z.2.1,scatterLeft z.1.1 z.1.2 m)

theorem physicalPairAt_eq (m : Velocity) (z : (Velocity × Velocity) × Sphere) :
    physicalPairAt m z = angularOutgoing m (relativePair z.1,z.2) := by
  have hn := mem_sphere_zero_iff_norm.mp z.2.property
  have hi : inner ℝ z.2.1 z.2.1 = 1 := by rw [real_inner_self_eq_norm_sq,hn]; norm_num
  simp only [physicalPairAt,angularOutgoing,outgoing,relativePair,scatterLeft,normalComponent,hi,inv_one,mul_one]

theorem physicalPairAt_measurable (m : Velocity) : Measurable (physicalPairAt m) := by
  unfold physicalPairAt scatterLeft normalComponent
  fun_prop

theorem physicalPairAt_law_absolutelyContinuous (m : Velocity) (hm : ‖m‖ = 1) :
    (Measure.map (physicalPairAt m) ((volume : Measure (Velocity × Velocity)).prod sphereArea)) ≪
      (volume : Measure (Velocity × Velocity)) := by
  have hp := relativePair_measurePreserving.prod (MeasurePreserving.id sphereArea)
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [Measure.map_apply (physicalPairAt_measurable m) hN]
  have h := angular_outgoing_law_absolutelyContinuous m hm hN0
  rw [Measure.map_apply (angularOutgoing_measurable m) hN] at h
  have hae : ∀ᵐ z : (Velocity × Velocity) × Sphere
      ∂(volume : Measure (Velocity × Velocity)).prod sphereArea, angularOutgoing m z ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not,Set.preimage] using h
  have hh := hp.quasiMeasurePreserving.ae hae
  have hf : ∀ᵐ z : (Velocity × Velocity) × Sphere
      ∂(volume : Measure (Velocity × Velocity)).prod sphereArea, physicalPairAt m z ∉ N := by
    filter_upwards [hh] with z hz
    rwa [physicalPairAt_eq]
  simpa only [not_not,Set.preimage] using ae_iff.mp hf

def physicalDoubleOutgoing (z : ((Velocity × Velocity) × Sphere) × Sphere) : Velocity × Velocity :=
  physicalPairAt z.2.1 z.1

theorem physicalDoubleOutgoing_measurable : Measurable physicalDoubleOutgoing := by
  unfold physicalDoubleOutgoing physicalPairAt scatterLeft normalComponent
  fun_prop

theorem physical_double_law_absolutelyContinuous :
    (Measure.map physicalDoubleOutgoing
      (((volume : Measure (Velocity × Velocity)).prod sphereArea).prod sphereArea)) ≪
        (volume : Measure (Velocity × Velocity)) := by
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [Measure.map_apply physicalDoubleOutgoing_measurable hN]
  have hsection (m : Sphere) : ∀ᵐ z : (Velocity × Velocity) × Sphere
      ∂(volume : Measure (Velocity × Velocity)).prod sphereArea, physicalPairAt m.1 z ∉ N := by
    have h := physicalPairAt_law_absolutelyContinuous m.1
      (mem_sphere_zero_iff_norm.mp m.property) hN0
    rw [Measure.map_apply (physicalPairAt_measurable m.1) hN] at h
    apply ae_iff.mpr
    simpa only [not_not,Set.preimage] using h
  have hswap : ∀ᵐ z : Sphere × ((Velocity × Velocity) × Sphere)
      ∂sphereArea.prod ((volume : Measure (Velocity × Velocity)).prod sphereArea),
      physicalDoubleOutgoing (z.2,z.1) ∉ N := by
    apply (Measure.ae_prod_iff_ae_ae
      ((hN.preimage physicalDoubleOutgoing_measurable).preimage measurable_swap).compl).mpr
    exact ae_of_all _ hsection
  have hh := (Measure.measurePreserving_swap
    (μ := ((volume : Measure (Velocity × Velocity)).prod sphereArea))
    (ν := sphereArea)).quasiMeasurePreserving.ae hswap
  change ∀ᵐ z : ((Velocity × Velocity) × Sphere) × Sphere
    ∂((volume : Measure (Velocity × Velocity)).prod sphereArea).prod sphereArea,
      physicalDoubleOutgoing z ∉ N at hh
  simpa only [not_not,Set.preimage] using ae_iff.mp hh

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Finite, absolutely continuous physical two-output reference measures -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

abbrev Parameters := ((Velocity × Velocity) × Sphere) × Sphere

def incomingBall (R : ℝ) : Set (Velocity × Velocity) :=
  Metric.closedBall 0 R ×ˢ Metric.closedBall 0 R

def parameterMeasure (R : ℝ) : Measure Parameters :=
  (((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)).prod sphereArea).prod sphereArea

instance parameterMeasureFinite (R : ℝ) : IsFiniteMeasure (parameterMeasure R) := by
  have : IsFiniteMeasure ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) :=
    isFiniteMeasure_restrict.mpr ((isCompact_closedBall (0 : Velocity) R).prod
      (isCompact_closedBall (0 : Velocity) R)).measure_lt_top.ne
  unfold parameterMeasure
  infer_instance

local instance doubleReferenceSFinite :
    SFinite ((volume : Measure (Velocity × Velocity)).prod sphereArea) := Measure.prod.instSFinite

def rateProduct (z : Parameters) : ℝ :=
  collisionKernel z.1.1.1 z.1.1.2 z.1.2.1*collisionKernel z.1.1.1 z.1.1.2 z.2.1

theorem rateProduct_measurable : Measurable rateProduct := by
  unfold rateProduct collisionKernel normalComponent
  fun_prop

theorem rateProduct_integrable (R : ℝ) : Integrable rateProduct (parameterMeasure R) := by
  have hpair : ∀ᵐ p : Velocity × Velocity
      ∂(volume : Measure (Velocity × Velocity)).restrict (incomingBall R), p ∈ incomingBall R :=
    ae_restrict_mem ((isCompact_closedBall (0 : Velocity) R).prod
      (isCompact_closedBall (0 : Velocity) R)).measurableSet
  have hfirst : ∀ᵐ z : (Velocity × Velocity) × Sphere
      ∂((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)).prod sphereArea,
      z.1 ∈ incomingBall R := Measure.quasiMeasurePreserving_fst.ae hpair
  have hall : ∀ᵐ z : Parameters ∂parameterMeasure R, z.1.1 ∈ incomingBall R :=
    Measure.quasiMeasurePreserving_fst.ae hfirst
  apply (integrable_const ((2*|R|)^2)).mono' rateProduct_measurable.aestronglyMeasurable
  filter_upwards [hall] with z hz
  have hv : ‖z.1.1.1‖ ≤ |R| := (by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1 : ‖z.1.1.1‖ ≤ R).trans (le_abs_self R)
  have hw : ‖z.1.1.2‖ ≤ |R| := (by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2 : ‖z.1.1.2‖ ≤ R).trans (le_abs_self R)
  have hb (n : Sphere) : collisionKernel z.1.1.1 z.1.1.2 n ≤ 2*|R| := by
    have hk : collisionKernel z.1.1.1 z.1.1.2 n ≤ ‖z.1.1.1-z.1.1.2‖ := by
      simpa only [collisionKernel,normalComponent,mem_sphere_zero_iff_norm.mp n.property,mul_one] using
        abs_real_inner_le_norm (z.1.1.1-z.1.1.2) (n : Velocity)
    exact hk.trans ((norm_sub_le _ _).trans (by linarith))
  change ‖collisionKernel z.1.1.1 z.1.1.2 z.1.2.1*collisionKernel z.1.1.1 z.1.1.2 z.2.1‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (collisionKernel_nonneg _ _ _) (collisionKernel_nonneg _ _ _))]
  simpa only [pow_two] using mul_le_mul (hb z.1.2) (hb z.2) (collisionKernel_nonneg _ _ _) (by positivity)

def physicalReferenceMeasure (R : ℝ) : Measure (Velocity × Velocity) :=
  Measure.map physicalDoubleOutgoing ((parameterMeasure R).withDensity (fun z => ENNReal.ofReal (rateProduct z)))

instance physicalReferenceMeasureFinite (R : ℝ) : IsFiniteMeasure (physicalReferenceMeasure R) := by
  have := isFiniteMeasure_withDensity_ofReal (rateProduct_integrable R).hasFiniteIntegral
  unfold physicalReferenceMeasure
  infer_instance

theorem physicalReferenceMeasure_absolutelyContinuous (R : ℝ) :
    physicalReferenceMeasure R ≪ (volume : Measure (Velocity × Velocity)) := by
  have hbase : parameterMeasure R ≪
      ((volume : Measure (Velocity × Velocity)).prod sphereArea).prod sphereArea :=
    (Measure.absolutelyContinuous_restrict.prod Measure.AbsolutelyContinuous.rfl).prod
      Measure.AbsolutelyContinuous.rfl
  have hw := (withDensity_absolutelyContinuous (parameterMeasure R)
    (fun z => ENNReal.ofReal (rateProduct z))).trans hbase
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [physicalReferenceMeasure,Measure.map_apply physicalDoubleOutgoing_measurable hN]
  apply hw
  have h := physical_double_law_absolutelyContinuous hN0
  rwa [Measure.map_apply physicalDoubleOutgoing_measurable hN] at h

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The integrable physical two-output density and its translation continuity -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

def referenceDensity (R : ℝ) (p : Velocity × Velocity) : ℝ :=
  ((physicalReferenceMeasure R).rnDeriv volume p).toReal

theorem referenceDensity_measurable (R : ℝ) : Measurable (referenceDensity R) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem referenceDensity_nonneg (R : ℝ) (p : Velocity × Velocity) :
    0 ≤ referenceDensity R p := ENNReal.toReal_nonneg

theorem referenceDensity_integrable (R : ℝ) : Integrable (referenceDensity R) := by
  have h := Measure.integrableOn_toReal_rnDeriv
    (μ := physicalReferenceMeasure R) (ν := (volume : Measure (Velocity × Velocity)))
    (measure_ne_top (physicalReferenceMeasure R) Set.univ)
  rw [IntegrableOn,Measure.restrict_univ] at h
  change Integrable (fun p : Velocity × Velocity =>
    ((physicalReferenceMeasure R).rnDeriv (volume : Measure (Velocity × Velocity)) p).toReal) volume
  exact h

theorem referenceDensity_integral (R : ℝ) (φ : Velocity × Velocity → ℝ) :
    (∫ p, referenceDensity R p*φ p) = ∫ p, φ p ∂physicalReferenceMeasure R :=
  integral_toReal_rnDeriv_mul (physicalReferenceMeasure_absolutelyContinuous R)

theorem referenceDensity_translate (R : ℝ) :
    Tendsto (fun h : Velocity × Velocity =>
      eLpNorm (fun p => referenceDensity R (p+h)-referenceDensity R p) 1 volume)
      (𝓝 0) (𝓝 0) := by
  simpa only [add_zero] using pair_translation_L1 (referenceDensity_integrable R) 0

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Physical two-output tests and the squared angular adjoint -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

local instance doubleTestInnerSFinite (R : ℝ) :
    SFinite (((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)).prod sphereArea) :=
  Measure.prod.instSFinite

theorem referenceDensity_test (R : ℝ) {φ : Velocity × Velocity → ℝ}
    (hφ : Measurable φ) :
    (∫ p, referenceDensity R p*φ p) =
      ∫ z, rateProduct z*φ (physicalDoubleOutgoing z) ∂parameterMeasure R := by
  rw [referenceDensity_integral,physicalReferenceMeasure,
    integral_map physicalDoubleOutgoing_measurable.aemeasurable hφ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul rateProduct_measurable.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : 0 ≤ rateProduct z :=
    mul_nonneg (collisionKernel_nonneg _ _ _) (collisionKernel_nonneg _ _ _)
  rw [ENNReal.toReal_ofReal hz,smul_eq_mul]

def angularAdjoint (ψ : Velocity → ℝ) (p : Velocity × Velocity) : ℝ :=
  ∫ n : Sphere, collisionKernel p.1 p.2 n*ψ (scatterLeft p.1 p.2 n) ∂sphereArea

theorem angularAdjoint_integrable {ψ : Velocity → ℝ} (hψ : Measurable ψ)
    {C : ℝ} (hC : ∀ v, |ψ v| ≤ C) (p : Velocity × Velocity) :
    Integrable (fun n : Sphere => collisionKernel p.1 p.2 n*ψ (scatterLeft p.1 p.2 n))
      sphereArea := by
  have hm : Measurable (fun n : Sphere => ψ (scatterLeft p.1 p.2 n)) := by
    apply hψ.comp
    unfold scatterLeft normalComponent
    fun_prop
  apply ((integrable_collisionKernel_sphereArea p.1 p.2).bdd_mul
    hm.aestronglyMeasurable (ae_of_all _ (fun n => hC _))).congr
  exact ae_of_all _ (fun _ => mul_comm _ _)

theorem angularAdjoint_measurable {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (angularAdjoint ψ) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  change Measurable (fun z : (Velocity × Velocity) × Sphere =>
    collisionKernel z.1.1 z.1.2 z.2*ψ (scatterLeft z.1.1 z.1.2 z.2))
  apply Measurable.mul
  · unfold collisionKernel normalComponent
    fun_prop
  · apply hψ.comp
    unfold scatterLeft normalComponent
    fun_prop

theorem double_test_integrable (R : ℝ) {ψ : Velocity → ℝ}
    (hψ : Measurable ψ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |ψ v| ≤ C) :
    Integrable (fun z => rateProduct z*
      (ψ (physicalDoubleOutgoing z).1*ψ (physicalDoubleOutgoing z).2)) (parameterMeasure R) := by
  have hm : Measurable (fun z => ψ (physicalDoubleOutgoing z).1*ψ (physicalDoubleOutgoing z).2) :=
    (hψ.comp (measurable_fst.comp physicalDoubleOutgoing_measurable)).mul
      (hψ.comp (measurable_snd.comp physicalDoubleOutgoing_measurable))
  have hb z : |ψ (physicalDoubleOutgoing z).1*ψ (physicalDoubleOutgoing z).2| ≤ C^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul (hC _) (hC _) (abs_nonneg _) hC0
  apply ((rateProduct_integrable R).bdd_mul hm.aestronglyMeasurable
    (ae_of_all _ hb)).congr
  exact ae_of_all _ (fun _ => mul_comm _ _)

theorem angularAdjoint_square (R : ℝ) {ψ : Velocity → ℝ}
    (hψ : Measurable ψ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |ψ v| ≤ C) :
    (∫ p in incomingBall R, (angularAdjoint ψ p)^2) =
      ∫ p, referenceDensity R p*(ψ p.1*ψ p.2) := by
  have hφ : Measurable (fun p : Velocity × Velocity => ψ p.1*ψ p.2) :=
    (hψ.comp measurable_fst).mul (hψ.comp measurable_snd)
  rw [referenceDensity_test R hφ]
  rw [parameterMeasure,integral_prod _ (double_test_integrable R hψ hC0 hC)]
  have hi := (double_test_integrable R hψ hC0 hC).integral_prod_left
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with p
  have hfactor (n : Sphere) :
      (∫ m : Sphere, rateProduct ((p,n),m)*
        (ψ (physicalDoubleOutgoing ((p,n),m)).1*ψ (physicalDoubleOutgoing ((p,n),m)).2)
        ∂sphereArea) =
      (collisionKernel p.1 p.2 n*ψ (scatterLeft p.1 p.2 n))*angularAdjoint ψ p := by
    change (∫ m : Sphere, (collisionKernel p.1 p.2 n*collisionKernel p.1 p.2 m)*
      (ψ (scatterLeft p.1 p.2 n)*ψ (scatterLeft p.1 p.2 m)) ∂sphereArea) = _
    rw [show (fun m : Sphere => (collisionKernel p.1 p.2 n*collisionKernel p.1 p.2 m)*
      (ψ (scatterLeft p.1 p.2 n)*ψ (scatterLeft p.1 p.2 m))) =
      (fun m : Sphere => (collisionKernel p.1 p.2 n*ψ (scatterLeft p.1 p.2 n))*
        (collisionKernel p.1 p.2 m*ψ (scatterLeft p.1 p.2 m))) by funext m; ring]
    exact integral_const_mul _ _
  simp_rw [hfactor]
  rw [integral_mul_const]
  exact (pow_two _).trans rfl

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
