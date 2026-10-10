import OAI.Geometry.Perimeter.Regularity.SmoothFlatOrder
import OAI.Geometry.Perimeter.Regularity.EllipticTestSpace

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def scalarDirection (φ : Euc n → ℝ) (a : Euc n) (x : Euc n) := fderiv ℝ φ x a

theorem scalarDirection_contDiff {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (a : Euc n) :
    ContDiff ℝ ∞ (scalarDirection φ a) :=
  (hφ.fderiv_right (by simp)).clm_apply contDiff_const

theorem scalarDirection_tsupport (φ : Euc n → ℝ) (a : Euc n) :
    tsupport (scalarDirection φ a) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hh
  exact hx (by simp [scalarDirection,fderiv_of_notMem_tsupport ℝ hh])

theorem scalarDirection_fderiv {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (a x b : Euc n) :
    fderiv ℝ (scalarDirection φ a) x b=fderiv ℝ (fderiv ℝ φ) x b a := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have h := ((ContinuousLinearMap.apply ℝ ℝ a).hasFDerivAt.comp x
    ((hd.differentiable (by simp)) x).hasFDerivAt).fderiv
  exact congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L b) h

def directionLocalTest {U : Set (Euc n)} (φ : SmoothLocalTest U) (a : Euc n) : SmoothLocalTest U :=
  ⟨scalarDirection φ.val a,scalarDirection_contDiff φ.property.1 a,
    φ.property.2.1.of_isClosed_subset (isClosed_tsupport _) (scalarDirection_tsupport _ _),
    (scalarDirection_tsupport _ _).trans φ.property.2.2⟩

def curlTest (φ : Euc n → ℝ) (a b : Euc n) (x : Euc n) : Euc n :=
  scalarDirection φ a x • b - scalarDirection φ b x • a

theorem curlTest_contDiff {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (a b : Euc n) :
    ContDiff ℝ ∞ (curlTest φ a b) :=
  ((scalarDirection_contDiff hφ a).smul contDiff_const).sub
    ((scalarDirection_contDiff hφ b).smul contDiff_const)

theorem curlTest_tsupport (φ : Euc n → ℝ) (a b : Euc n) :
    tsupport (curlTest φ a b) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hh
  exact hx (by simp [curlTest,scalarDirection,fderiv_of_notMem_tsupport ℝ hh])

theorem curlTest_divergence {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (a b : Euc n) :
    divergence (curlTest φ a b)=0 := by
  have ha := (scalarDirection_contDiff hφ a).differentiable (by simp)
  have hb := (scalarDirection_contDiff hφ b).differentiable (by simp)
  rw [show curlTest φ a b=(fun x ↦ scalarDirection φ a x • b)-(fun x ↦ scalarDirection φ b x • a) from rfl,
    divergence_sub (ha.smul_const b) (hb.smul_const a),divergence_scalar_direction ha,
    divergence_scalar_direction hb]
  funext x
  simp only [Pi.sub_apply,Pi.zero_apply,scalarDirection_fderiv hφ]
  exact sub_eq_zero.mpr ((hφ.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) b a)

def curlTestLp {U : Set (Euc n)} (φ : SmoothLocalTest U) (a b : Euc n) : VectorL2 n :=
  ((curlTest_contDiff φ.property.1 a b).continuous.memLp_of_hasCompactSupport
    (φ.property.2.1.of_isClosed_subset (isClosed_tsupport _) (curlTest_tsupport _ _ _))).toLp
      (curlTest φ.val a b)

theorem curlTestLp_ae {U : Set (Euc n)} (φ : SmoothLocalTest U) (a b : Euc n) :
    (curlTestLp φ a b : Euc n → Euc n)=ᵐ[volume] curlTest φ.val a b := MemLp.coeFn_toLp _

def CurlFreeLpOn (u : VectorL2 n) (U : Set (Euc n)) : Prop :=
  ∀ (φ : SmoothLocalTest U) (a b : Euc n), inner ℝ u (curlTestLp φ a b)=0

theorem testGradient_curlTest_inner {U V : Set (Euc n)} (ψ : SmoothLocalTest V)
    (φ : SmoothLocalTest U) (a b : Euc n) :
    inner ℝ (testGradientLp ψ) (curlTestLp φ a b)=0 := by
  rw [MeasureTheory.L2.inner_def]
  have he : (∫ x, inner ℝ (testGradientLp ψ x) (curlTestLp φ a b x))=
      ∫ x, inner ℝ (gradient ψ.val x) (curlTest φ.val a b x) := by
    apply integral_congr_ae
    filter_upwards [testGradientLp_ae ψ,curlTestLp_ae φ a b] with x hx hy
    rw [hx,hy]
  rw [he]
  have hi := integral_mul_divergence_eq_neg_inner_gradient_local ψ.property.1
    (curlTest_contDiff φ.property.1 a b)
    (φ.property.2.1.of_isClosed_subset (isClosed_tsupport _) (curlTest_tsupport _ _ _))
  rw [curlTest_divergence φ.property.1] at hi
  simpa only [Pi.zero_apply,mul_zero,integral_zero,eq_neg_iff_add_eq_zero,zero_add] using hi

theorem testGradientSpace_curlFree {U V : Set (Euc n)} {u : VectorL2 n}
    (hu : u∈testGradientSpace V) : CurlFreeLpOn u U := by
  intro φ a b
  have hz := inner_zero_on_closed_span (Set.range (testGradientLp (U := V)))
    (u := curlTestLp φ a b) (by
      rintro _ ⟨ψ,rfl⟩
      rw [real_inner_comm]
      exact testGradient_curlTest_inner ψ φ a b) u hu
  rwa [real_inner_comm] at hz

theorem CurlFreeLpOn.sub {U : Set (Euc n)} {u v : VectorL2 n}
    (hu : CurlFreeLpOn u U) (hv : CurlFreeLpOn v U) : CurlFreeLpOn (u-v) U := by
  intro φ a b
  rw [inner_sub_left,hu φ a b,hv φ a b,sub_self]

theorem weak_curl_harmonic_comparison {U : Set (Euc n)} {u e : VectorL2 n}
    (hu : CurlFreeLpOn u U)
    (h : ∀ φ : SmoothLocalTest U, (∫ x, inner ℝ (u x) (gradient φ.val x))=
      ∫ x, inner ℝ (e x) (gradient φ.val x)) :
    ∃ g : VectorL2 n, DivFreeLpOn g U ∧ CurlFreeLpOn g U ∧ ‖u-g‖≤‖e‖ := by
  obtain ⟨g,hg,hug,he⟩ := weak_harmonic_gradient_comparison h
  have hcf := hu.sub (testGradientSpace_curlFree hug)
  rw [sub_sub_cancel] at hcf
  exact ⟨g,hg,hcf,he⟩

end RPISingularHarnack

end

end OAI
