import OAI.Analysis.HotSpots.Potentials

namespace OAI

section ActualVectorSupport
noncomputable section
section ActualNeumannHilbertLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots
namespace H1
variable {Ω : Set Plane}

lemma norm_value_sq (u : H1 Ω) :
    ‖value u‖ ^ 2 = ∫ x in Ω, (value u x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

lemma norm_grad_sq (u : H1 Ω) :
    ‖grad u‖ ^ 2 = ∫ x in Ω, ‖grad u x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]


lemma rayleigh (u : H1 Ω) (hm : (∫ x in Ω, value u x) = 0) :
    firstPositiveNeumannValue Ω * ‖value u‖ ^ 2 ≤ ‖grad u‖ ^ 2 := by
  by_cases hz : ‖value u‖ = 0
  · simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact sq_nonneg _
  · have hp : 0 < ‖value u‖ ^ 2 := sq_pos_of_ne_zero hz
    rw [norm_value_sq] at hp
    simpa only [norm_value_sq, norm_grad_sq] using
      rayleigh_inequality (hasH1Gradient u) hm hp


def one (hb : Bornology.IsBounded Ω) : Lp ℝ 2 (volume.restrict Ω) := by
  letI : IsFiniteMeasure (volume.restrict Ω) := ⟨by
    simpa using hb.measure_lt_top (μ := (volume : Measure Plane))⟩
  exact (memLp_const (1 : ℝ)).toLp (fun _ : Plane => (1 : ℝ))

lemma one_ae (hb : Bornology.IsBounded Ω) :
    one hb =ᵐ[volume.restrict Ω] fun _ : Plane => (1 : ℝ) :=
  MemLp.coeFn_toLp _

lemma mean_apply (hb : Bornology.IsBounded Ω) (u : H1 Ω) :
    mean hb u = ∫ x in Ω, value u x := mean_eq hb u

end H1


def meanZeroSubmodule {Ω : Set Plane} (hb : Bornology.IsBounded Ω) : Submodule ℝ (H1 Ω) :=
  (H1.mean hb).ker

abbrev N1 {Ω : Set Plane} (hb : Bornology.IsBounded Ω) := meanZeroSubmodule hb

instance N1.normedAddCommGroup {Ω : Set Plane} (hb : Bornology.IsBounded Ω) :
    NormedAddCommGroup (N1 hb) := (meanZeroSubmodule hb).normedAddCommGroup

instance N1.innerProductSpace {Ω : Set Plane} (hb : Bornology.IsBounded Ω) :
    InnerProductSpace ℝ (N1 hb) := (meanZeroSubmodule hb).innerProductSpace

instance N1.completeSpace {Ω : Set Plane} (hb : Bornology.IsBounded Ω) :
    CompleteSpace (N1 hb) := (H1.mean hb).isClosed_ker.completeSpace_coe

namespace N1
variable {Ω : Set Plane} (hb : Bornology.IsBounded Ω)

local instance : NormedSpace ℝ (N1 hb) := (N1.innerProductSpace hb).toNormedSpace

def value : N1 hb →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  H1.value.comp (meanZeroSubmodule hb).subtypeL

def grad : N1 hb →L[ℝ] Lp Plane 2 (volume.restrict Ω) :=
  H1.grad.comp (meanZeroSubmodule hb).subtypeL

lemma norm_sq (u : N1 hb) : ‖u‖ ^ 2 = ‖value hb u‖ ^ 2 + ‖grad hb u‖ ^ 2 :=
  H1.norm_sq u.val

lemma mean_zero (u : N1 hb) : (∫ x in Ω, value hb u x) = 0 := by
  have hu : H1.mean hb u.val = 0 := u.property
  change (∫ x in Ω, H1.value u.val x) = 0
  simpa only [H1.mean_apply] using hu

lemma rayleigh (u : N1 hb) :
    firstPositiveNeumannValue Ω * ‖value hb u‖ ^ 2 ≤ ‖grad hb u‖ ^ 2 :=
  H1.rayleigh u.val (mean_zero hb u)

def energy : N1 hb →L[ℝ] N1 hb →L[ℝ] ℝ := by
  let a : Lp Plane 2 (volume.restrict Ω) →L[ℝ]
      Lp Plane 2 (volume.restrict Ω) →L[ℝ] ℝ := innerSL ℝ
  let b : N1 hb →L[ℝ] Lp Plane 2 (volume.restrict Ω) →L[ℝ] ℝ := a.comp (grad hb)
  let c : Lp Plane 2 (volume.restrict Ω) →L[ℝ] N1 hb →L[ℝ] ℝ :=
    ContinuousLinearMap.flip (E := N1 hb) (F := Lp Plane 2 (volume.restrict Ω)) b
  let d : N1 hb →L[ℝ] N1 hb →L[ℝ] ℝ := c.comp (grad hb)
  exact ContinuousLinearMap.flip (E := N1 hb) (F := N1 hb) d

@[simp] lemma energy_apply (u v : N1 hb) :
    energy hb u v = inner ℝ (grad hb u) (grad hb v) := rfl

lemma energy_coercive (hμ : 0 < firstPositiveNeumannValue Ω) :
    @IsCoercive (N1 hb) (N1.normedAddCommGroup hb).toSeminormedAddCommGroup
      (N1.innerProductSpace hb).toNormedSpace (energy hb) := by
  let μ := firstPositiveNeumannValue Ω
  have hden : 0 < μ + 1 := by dsimp [μ]; positivity
  refine ⟨μ / (μ + 1), div_pos hμ hden, fun u => ?_⟩
  have hR := rayleigh hb u
  have hbound : μ * ‖u‖ ^ 2 ≤ (μ + 1) * ‖grad hb u‖ ^ 2 := by
    rw [norm_sq hb]
    nlinarith
  calc
    (μ / (μ + 1)) * ‖u‖ * ‖u‖ = (μ * ‖u‖ ^ 2) / (μ + 1) := by ring
    _ ≤ ‖grad hb u‖ ^ 2 := (div_le_iff₀ hden).mpr (by simpa [mul_comm] using hbound)
    _ = energy hb u u := (real_inner_self_eq_norm_sq _).symm




lemma existsUnique_energy_solution (hμ : 0 < firstPositiveNeumannValue Ω)
    (ℓ : N1 hb →L[ℝ] ℝ) :
    ∃! u : N1 hb, ∀ v : N1 hb, energy hb u v = ℓ v := by
  exact @existsUnique_of_coercive (N1 hb) (N1.normedAddCommGroup hb)
    (N1.innerProductSpace hb) (N1.completeSpace hb)
    (energy hb) (energy_coercive hb hμ) ℓ

end N1
end StrictHotSpots

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots
end StrictHotSpots
end ActualNeumannHilbertLayer

section HodgeOrthogonalityInteriorSupportLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots
namespace Hodge

lemma weakCurl_gradient {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane}
    (hv : HasH1Gradient Ω v g) : WeakCurlZero Ω g := by
  intro φ hφ hk hs
  have h0 := hv.2.2 (D 0 φ) (D_smooth hφ 0) (D_compact hk 0) ((D_support φ 0).trans hs) (e 1)
  have h1 := hv.2.2 (D 1 φ) (D_smooth hφ 1) (D_compact hk 1) ((D_support φ 1).trans hs) (e 0)
  change (∫ x in Ω, v x * D 1 (D 0 φ) x) = -(∫ x in Ω, c 1 (g x)*D 0 φ x) at h0
  change (∫ x in Ω, v x * D 0 (D 1 φ) x) = -(∫ x in Ω, c 0 (g x)*D 1 φ x) at h1
  simp_rw [D_D hφ 1 0] at h0
  have hi := (hv.2.1.inner_const (e 1)).integrable_mul (test_derivative_memLp hφ hk (e 0))
  have hj := (hv.2.1.inner_const (e 0)).integrable_mul (test_derivative_memLp hφ hk (e 1))
  change IntegrableOn (fun x => c 1 (g x)*D 0 φ x) Ω at hi
  change IntegrableOn (fun x => c 0 (g x)*D 1 φ x) Ω at hj
  simp_rw [inner_rot_gradient]
  rw [integral_sub hi hj]
  linarith

abbrev V2 (Ω : Set Plane) : Type := Lp Plane 2 (volume.restrict Ω)
def rotL (Ω : Set Plane) : V2 Ω →L[ℝ] V2 Ω := rot.compLpL 2 (volume.restrict Ω)
lemma rotL_ae {Ω : Set Plane} (u : V2 Ω) : rotL Ω u =ᵐ[volume.restrict Ω] fun x => rot (u x) :=
  rot.coeFn_compLpL u
lemma rotL_inner {Ω : Set Plane} (u v : V2 Ω) : inner ℝ (rotL Ω u) (rotL Ω v) = inner ℝ u v := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [rotL_ae u,rotL_ae v] with x hx hy
  rw [hx,hy,rot_inner]
lemma rotL_norm {Ω : Set Plane} (u : V2 Ω) : ‖rotL Ω u‖ = ‖u‖ := by
  have hh := rotL_inner u u
  simp only [real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (rotL Ω u),norm_nonneg u]

lemma weakCurl_iff {Ω : Set Plane} (ho : IsOpen Ω) (Z : V2 Ω) :
    WeakCurlZero Ω Z ↔ ∀ j : H10 ho, inner ℝ Z (rotL Ω (H10.grad ho j)) = 0 := by
  constructor
  · intro hz j
    apply isClosed_property (dense_smoothTestToH10 ho)
      (isClosed_eq (continuous_const.inner ((rotL Ω).continuous.comp (H10.grad ho).continuous)) continuous_const) _ j
    intro f
    rw [L2.inner_def]
    have he : H10.grad ho (smoothTestToH10 ho f) =ᵐ[volume.restrict Ω] gradient f.val :=
      (test_gradient_memLp f.property.1 f.property.2.1).coeFn_toLp
    calc
      _ = ∫ x in Ω, inner ℝ (Z x) (rot (gradient f.val x)) := by
        apply integral_congr_ae
        filter_upwards [rotL_ae (H10.grad ho (smoothTestToH10 ho f)),he] with x hx hy
        change inner ℝ (Z x) ((rotL Ω (H10.grad ho (smoothTestToH10 ho f))) x) = _
        rw [hx,hy]
      _ = 0 := hz f.val f.property.1 f.property.2.1 f.property.2.2
  · intro hz φ hφ hk hs
    let f : smoothTestSpace Ω := ⟨φ,hφ,hk,hs⟩
    have h := hz (smoothTestToH10 ho f)
    rw [L2.inner_def] at h
    have he : H10.grad ho (smoothTestToH10 ho f) =ᵐ[volume.restrict Ω] gradient φ :=
      (test_gradient_memLp hφ hk).coeFn_toLp
    convert h using 1
    apply integral_congr_ae
    filter_upwards [rotL_ae (H10.grad ho (smoothTestToH10 ho f)),he] with x hx hy
    rw [hx,hy]

lemma grad_rotGrad_orthogonal {Ω : Set Plane} (ho : IsOpen Ω) (v : H1 Ω) (j : H10 ho) :
    inner ℝ (H1.grad v) (rotL Ω (H10.grad ho j)) = 0 :=
  (weakCurl_iff ho (H1.grad v)).mp (weakCurl_gradient (H1.hasH1Gradient v)) j

lemma exists_meanZero_same_grad {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hb : Bornology.IsBounded Ω) (v : H1 Ω) :
    ∃ u : N1 hb, N1.grad hb u = H1.grad v := by
  let C : H1 Ω := (HasH1Gradient.const hb 1).toH1
  have hcG : H1.grad C = 0 := by
    apply Lp.ext
    exact ((HasH1Gradient.const hb 1).2.1.coeFn_toLp).trans (Lp.coeFn_zero _ _ _).symm
  have hcM : H1.mean hb C = (volume Ω).toReal := by
    rw [H1.mean_apply]
    calc
      _ = ∫ x in Ω, (1 : ℝ) := integral_congr_ae (HasH1Gradient.const hb 1).1.coeFn_toLp
      _ = _ := by simp [Measure.real]
  have hv : (volume Ω).toReal ≠ 0 :=
    (ENNReal.toReal_pos (ho.measure_pos volume hne).ne' hb.measure_lt_top.ne).ne'
  let u : H1 Ω := v - (H1.mean hb v/(volume Ω).toReal) • C
  have hm : H1.mean hb u = 0 := by
    simp only [u,map_sub,map_smul,smul_eq_mul,hcM]
    field_simp
    ring
  refine ⟨⟨u,hm⟩,?_⟩
  change H1.grad u = _
  simp only [u,map_sub,map_smul,hcG,smul_zero,sub_zero]

end Hodge
end StrictHotSpots

end HodgeOrthogonalityInteriorSupportLayer


section HodgeProjectionInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge
local instance {Ω : Set Plane} (hb : Bornology.IsBounded Ω) : NormedSpace ℝ (N1 hb) :=
  (N1.innerProductSpace hb).toNormedSpace
local instance {Ω : Set Plane} (ho : IsOpen Ω) : NormedSpace ℝ (H10 ho) :=
  (H10.innerProductSpace ho).toNormedSpace

def nFunctional {Ω : Set Plane} (hb : Bornology.IsBounded Ω) (X : Lp Plane 2 (volume.restrict Ω)) :
    N1 hb →L[ℝ] ℝ := (innerSL ℝ X).comp (N1.grad hb)
lemma nFunctional_apply {Ω : Set Plane} (hb : Bornology.IsBounded Ω)
    (X : Lp Plane 2 (volume.restrict Ω)) (v : N1 hb) :
    nFunctional hb X v = inner ℝ X (N1.grad hb v) := rfl
lemma nProjection {Ω : Set Plane} (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) (X : Lp Plane 2 (volume.restrict Ω)) :
    ∃ v : N1 hb, ∀ w : N1 hb, inner ℝ (N1.grad hb v) (N1.grad hb w) =
      inner ℝ X (N1.grad hb w) :=
  ExistsUnique.exists (N1.existsUnique_energy_solution hb hμ (nFunctional hb X))

lemma nProjection_extend {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hb : Bornology.IsBounded Ω) (X : Lp Plane 2 (volume.restrict Ω)) (v : N1 hb)
    (hv : ∀ w : N1 hb, inner ℝ (N1.grad hb v) (N1.grad hb w) = inner ℝ X (N1.grad hb w))
    (u : H1 Ω) : inner ℝ (N1.grad hb v) (H1.grad u) = inner ℝ X (H1.grad u) := by
  obtain ⟨w,hw⟩ := exists_meanZero_same_grad (Ω := Ω) ho hne hb u
  exact hw ▸ hv w

lemma neumann_projection {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hb : Bornology.IsBounded Ω) (hμ : 0 < firstPositiveNeumannValue Ω) (X : Lp Plane 2 (volume.restrict Ω)) :
    ∃ v : N1 hb, ∀ u : H1 Ω, inner ℝ (N1.grad hb v) (H1.grad u) = inner ℝ X (H1.grad u) :=
  (nProjection (Ω := Ω) hb hμ X).imp fun v hv => nProjection_extend ho hne hb X v hv

def jFunctional {Ω : Set Plane} (ho : IsOpen Ω) (X : Lp Plane 2 (volume.restrict Ω)) :
    H10 ho →L[ℝ] ℝ := (innerSL ℝ X).comp ((rotL Ω).comp (H10.grad ho))
lemma jProjection {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (X : Lp Plane 2 (volume.restrict Ω)) :
    ∃ j : H10 ho, ∀ k : H10 ho, inner ℝ (H10.grad ho j) (H10.grad ho k) =
      inner ℝ X (rotL Ω (H10.grad ho k)) :=
  ExistsUnique.exists (H10.existsUnique_energy_solution ho hb (jFunctional ho X))

lemma dirichlet_projection {Ω : Set Plane} (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (X : Lp Plane 2 (volume.restrict Ω)) :
    ∃ j : H10 ho, ∀ k : H10 ho,
      inner ℝ (rotL Ω (H10.grad ho j)) (rotL Ω (H10.grad ho k)) =
        inner ℝ X (rotL Ω (H10.grad ho k)) := by
  exact (jProjection (Ω := Ω) ho hb X).imp fun j hj k =>
    (rotL_inner (Ω := Ω) (H10.grad ho j) (H10.grad ho k)).trans (hj k)
end StrictHotSpots.Hodge

end HodgeProjectionInteriorSupportLayer


section HodgeResidualInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge

def residual {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (X : V2 Ω) (v : N1 hb) (j : H10 ho) : V2 Ω :=
  X - N1.grad hb v - rotL Ω (H10.grad ho j)

private lemma inner_sub_sub_normal_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (first second third test : E)
    (hsecond : inner ℝ second test = inner ℝ first test)
    (hthird : inner ℝ third test = 0) :
    inner ℝ (first - second - third) test = 0 := by
  rw [inner_sub_left, inner_sub_left, hsecond, hthird, sub_self, sub_zero]

lemma residual_normal {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (X : V2 Ω) (v : N1 hb) (j : H10 ho)
    (hn : ∀ u : H1 Ω, inner ℝ (N1.grad hb v) (H1.grad u) = inner ℝ X (H1.grad u))
    (u : H1 Ω) : inner ℝ (residual ho hb X v j) (H1.grad u) = 0 := by
  have he : inner ℝ (rotL Ω (H10.grad ho j)) (H1.grad u) = 0 :=
    (real_inner_comm _ _).trans (grad_rotGrad_orthogonal ho u j)
  exact inner_sub_sub_normal_zero X (N1.grad hb v) (rotL Ω (H10.grad ho j))
    (H1.grad u) (hn u) he

lemma inner_sub_sub_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X A B Y : E) (he : inner ℝ A Y = 0) (hj : inner ℝ B Y = inner ℝ X Y) :
    inner ℝ (X-A-B) Y = 0 := by
  rw [inner_sub_left,inner_sub_left,he,hj,sub_zero,sub_self]

lemma residual_curl {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (X : V2 Ω) (v : N1 hb) (j : H10 ho)
    (hj : ∀ k : H10 ho, inner ℝ (rotL Ω (H10.grad ho j)) (rotL Ω (H10.grad ho k)) =
      inner ℝ X (rotL Ω (H10.grad ho k))) (k : H10 ho) :
    inner ℝ (residual ho hb X v j) (rotL Ω (H10.grad ho k)) = 0 :=
  inner_sub_sub_zero X (N1.grad hb v) (rotL Ω (H10.grad ho j)) (rotL Ω (H10.grad ho k))
    (grad_rotGrad_orthogonal ho v.val k) (hj k)

lemma orthogonal_all_zero {Ω : Set Plane} (ho : IsOpen Ω) (hs : IsSimplyConnected Ω)
    (hb : Bornology.IsBounded Ω) (hμ : 0 < firstPositiveNeumannValue Ω) (Z : V2 Ω)
    (hzN : ∀ u : H1 Ω, inner ℝ Z (H1.grad u) = 0)
    (hzJ : ∀ k : H10 ho, inner ℝ Z (rotL Ω (H10.grad ho k)) = 0) : Z = 0 := by
  apply Lp.ext
  refine (weak_divCurl_zero ho hs hb hμ (Lp.memLp Z) ((weakCurl_iff ho Z).mpr hzJ) ?_).trans
    (Lp.coeFn_zero _ _ _).symm
  intro u g hh
  have h := hzN hh.toH1
  rw [L2.inner_def] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [hh.2.1.coeFn_toLp] with x hx
  change inner ℝ (Z x) (g x) = inner ℝ (Z x) (hh.2.1.toLp g x)
  rw [hx]

lemma sub_sub_zero_iff {E : Type*} [AddCommGroup E] (X A B : E) :
    X-A-B=0 ↔ X=A+B := by rw [sub_sub,sub_eq_zero]

lemma residual_zero_iff {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (X : V2 Ω) (v : N1 hb) (j : H10 ho) :
    residual ho hb X v j = 0 ↔ X = N1.grad hb v + rotL Ω (H10.grad ho j) :=
  sub_sub_zero_iff X (N1.grad hb v) (rotL Ω (H10.grad ho j))

lemma norm_add_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (h : inner ℝ a b = 0) : ‖a+b‖^2 = ‖a‖^2 + ‖b‖^2 := by
  rw [norm_add_sq_real,h]
  ring

lemma decomposition_norm {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (v : N1 hb) (j : H10 ho) :
    ‖N1.grad hb v + rotL Ω (H10.grad ho j)‖^2 =
      ‖N1.grad hb v‖^2 + ‖H10.grad ho j‖^2 := by
  exact (norm_add_orthogonal _ _ (grad_rotGrad_orthogonal ho v.val j)).trans
    (congrArg (fun r : ℝ => ‖N1.grad hb v‖^2 + r^2) (rotL_norm (H10.grad ho j)))
end StrictHotSpots.Hodge

end HodgeResidualInteriorSupportLayer


section HodgeDecompositionInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge

lemma projection_eq {Ω : Set Plane} (ho : IsOpen Ω) (hs : IsSimplyConnected Ω)
    (hb : Bornology.IsBounded Ω) (hμ : 0 < firstPositiveNeumannValue Ω)
    (X : V2 Ω) (v : N1 hb) (j : H10 ho)
    (hn : ∀ u : H1 Ω, inner ℝ (N1.grad hb v) (H1.grad u) = inner ℝ X (H1.grad u))
    (hj : ∀ k : H10 ho, inner ℝ (rotL Ω (H10.grad ho j)) (rotL Ω (H10.grad ho k)) =
      inner ℝ X (rotL Ω (H10.grad ho k))) :
    X = N1.grad hb v + rotL Ω (H10.grad ho j) :=
  (residual_zero_iff ho hb X v j).mp (orthogonal_all_zero ho hs hb hμ (residual ho hb X v j)
    (residual_normal ho hb X v j hn) (residual_curl ho hb X v j hj))

lemma projection_eq_exists {Ω : Set Plane} (ho : IsOpen Ω) (hs : IsSimplyConnected Ω)
    (hb : Bornology.IsBounded Ω) (hμ : 0 < firstPositiveNeumannValue Ω)
    (X : V2 Ω) (v : N1 hb)
    (hn : ∀ u : H1 Ω, inner ℝ (N1.grad hb v) (H1.grad u) = inner ℝ X (H1.grad u)) :
    ∃ j : H10 ho, X = N1.grad hb v + rotL Ω (H10.grad ho j) :=
  (dirichlet_projection ho hb X).imp fun j hj => projection_eq ho hs hb hμ X v j hn hj



theorem decomposition {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) (X : V2 Ω) :
    ∃ (v : N1 hb) (j : H10 ho), X = N1.grad hb v + rotL Ω (H10.grad ho j) :=
  (neumann_projection ho hne hb hμ X).imp fun v hn => projection_eq_exists ho hs hb hμ X v hn
end StrictHotSpots.Hodge

end HodgeDecompositionInteriorSupportLayer


section HodgeVectorEnergyInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge

lemma scalar_energy_bound {a b c θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ht : 0 ≤ θ) (hr : θ*b^2 ≤ a^2) (he : a^2 ≤ b*c) : θ*a^2 ≤ c^2 := by
  by_cases h : b = 0
  · subst b
    have hz : a = 0 := by nlinarith
    simp [hz,sq_nonneg]
  · have hp : 0 < b := lt_of_le_of_ne hb (Ne.symm h)
    have htc : θ*b ≤ c := (mul_le_mul_iff_of_pos_right hp).mp (by nlinarith)
    calc
      θ*a^2 ≤ θ*(b*c) := mul_le_mul_of_nonneg_left he ht
      _ = (θ*b)*c := by ring
      _ ≤ c*c := mul_le_mul_of_nonneg_right htc hc
      _ = c^2 := by ring

lemma scalar_rayleigh_eq {a b c θ : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (_hc : 0 ≤ c)
    (ht : 0 < θ) (hr : θ*b^2 ≤ a^2) (he : a^2 ≤ b*c) (heq : θ*a^2 = c^2) :
    θ*b^2 = a^2 := by
  by_cases hz : a = 0
  · subst a
    nlinarith
  · have hp : 0 < a^2 := sq_pos_of_ne_zero hz
    have hh : (a^2)^2 ≤ (b*c)^2 := by nlinarith [mul_nonneg _hb _hc]
    have hh' : (a^2)*a^2 ≤ (θ*b^2)*a^2 := by nlinarith [sq_nonneg (b*c-a^2)]
    exact le_antisymm hr ((mul_le_mul_iff_of_pos_right hp).mp hh')



def WeakNormalDiv {Ω : Set Plane} (X : Lp Plane 2 (volume.restrict Ω)) (F : Lp ℝ 2 (volume.restrict Ω)) : Prop :=
  ∀ u : H1 Ω, inner ℝ X (H1.grad u) = -inner ℝ F (H1.value u)

def WeakCurl {Ω : Set Plane} (ho : IsOpen Ω) (X : Lp Plane 2 (volume.restrict Ω))
    (G : Lp ℝ 2 (volume.restrict Ω)) : Prop :=
  ∀ j : H10 ho, inner ℝ X (rotL Ω (H10.grad ho j)) = -inner ℝ G (H10.value ho j)

lemma pair_add_orthogonal_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (h : inner ℝ a b = 0) : inner ℝ (a+b) a = ‖a‖^2 := by
  rw [inner_add_left,real_inner_comm a b,h,add_zero,real_inner_self_eq_norm_sq]

lemma pair_add_orthogonal_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (h : inner ℝ a b = 0) : inner ℝ (a+b) b = ‖b‖^2 := by
  rw [inner_add_left,h,zero_add,real_inner_self_eq_norm_sq]

lemma neg_inner_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) : -inner ℝ a b ≤ ‖b‖*‖a‖ := by
  simpa only [inner_neg_left,norm_neg,mul_comm] using real_inner_le_norm (-a) b

lemma energy_pair_normal {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (v : N1 hb) (j : H10 ho) (F : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv (N1.grad hb v + rotL Ω (H10.grad ho j)) F) :
    ‖N1.grad hb v‖^2 = -inner ℝ F (N1.value hb v) :=
  (pair_add_orthogonal_left _ _ (grad_rotGrad_orthogonal ho v.val j)).symm.trans (hF v.val)

lemma energy_pair_curl {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (v : N1 hb) (j : H10 ho) (G : Lp ℝ 2 (volume.restrict Ω))
    (hG : WeakCurl ho (N1.grad hb v + rotL Ω (H10.grad ho j)) G) :
    ‖H10.grad ho j‖^2 = -inner ℝ G (H10.value ho j) :=
  (congrArg (fun r : ℝ => r^2) (rotL_norm (H10.grad ho j))).symm.trans
    ((pair_add_orthogonal_right _ _ (grad_rotGrad_orthogonal ho v.val j)).symm.trans (hG j))

lemma energy_bound_normal {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (v : N1 hb) (j : H10 ho) (F : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv (N1.grad hb v + rotL Ω (H10.grad ho j)) F) :
    firstPositiveNeumannValue Ω * ‖N1.grad hb v‖^2 ≤ ‖F‖^2 := by
  apply scalar_energy_bound (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (firstPositiveNeumannValue_nonneg Ω) (N1.rayleigh hb v)
  exact (energy_pair_normal ho hb v j F hF).trans_le (neg_inner_bound F (N1.value hb v))

lemma energy_bound_curl {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (v : N1 hb) (j : H10 ho) (G : Lp ℝ 2 (volume.restrict Ω)) {L : ℝ} (hl : 0 ≤ L)
    (hD : L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (hG : WeakCurl ho (N1.grad hb v + rotL Ω (H10.grad ho j)) G) :
    L * ‖H10.grad ho j‖^2 ≤ ‖G‖^2 := by
  apply scalar_energy_bound (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hl hD
  exact (energy_pair_curl ho hb v j G hG).trans_le (neg_inner_bound G (H10.value ho j))

lemma energy_decomposition_of_eq {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {L : ℝ} (hl : 0 ≤ L) (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X : V2 Ω) (F G : Lp ℝ 2 (volume.restrict Ω)) (v : N1 hb) (j : H10 ho)
    (hX : X = N1.grad hb v + rotL Ω (H10.grad ho j))
    (hF : WeakNormalDiv X F) (hG : WeakCurl ho X G) :
    X = N1.grad hb v + rotL Ω (H10.grad ho j) ∧
      firstPositiveNeumannValue Ω * ‖N1.grad hb v‖^2 ≤ ‖F‖^2 ∧
      L * ‖H10.grad ho j‖^2 ≤ ‖G‖^2 :=
  ⟨hX,energy_bound_normal ho hb v j F (by rwa [← hX]),
    energy_bound_curl ho hb v j G hl (hD j) (by rwa [← hX])⟩


theorem energy_decomposition {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) {L : ℝ}
    (hl : firstPositiveNeumannValue Ω < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X : V2 Ω) (F G : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv X F) (hG : WeakCurl ho X G) :
    ∃ (v : N1 hb) (j : H10 ho),
      X = N1.grad hb v + rotL Ω (H10.grad ho j) ∧
      firstPositiveNeumannValue Ω * ‖N1.grad hb v‖^2 ≤ ‖F‖^2 ∧
      L * ‖H10.grad ho j‖^2 ≤ ‖G‖^2 :=
  (decomposition ho hne hs hb hμ X).imp fun v hv => hv.imp fun j hj =>
    energy_decomposition_of_eq ho hb (hμ.trans hl).le hD X F G v j hj hF hG

theorem vector_inequality {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) {L : ℝ}
    (hl : firstPositiveNeumannValue Ω < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X : Lp Plane 2 (volume.restrict Ω)) (F G : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv X F) (hG : WeakCurl ho X G) :
    firstPositiveNeumannValue Ω * ‖X‖^2 ≤ ‖F‖^2 + ‖G‖^2 := by
  obtain ⟨v,j,hX,hv,hj⟩ := energy_decomposition ho hne hs hb hμ hl hD X F G hF hG
  rw [hX,decomposition_norm ho hb]
  nlinarith [sq_nonneg ‖H10.grad ho j‖]

end StrictHotSpots.Hodge

end HodgeVectorEnergyInteriorSupportLayer


section HodgeEqualityInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge

lemma scalar_surplus_eq {a b f g μ L : ℝ} (hl : μ < L)
    (hv : μ*a^2 ≤ f^2) (hj : L*b^2 ≤ g^2)
    (he : μ*(a^2+b^2) = f^2+g^2) : b=0 ∧ g=0 ∧ μ*a^2=f^2 := by
  have hh : (L-μ)*b^2 ≤ 0 := by nlinarith
  have hb : b^2 = 0 := le_antisymm
    ((mul_le_mul_iff_of_pos_left (sub_pos.mpr hl)).mp (by simpa using hh)) (sq_nonneg _)
  have hb' : b = 0 := sq_eq_zero_iff.mp hb
  simp only [hb',zero_pow (by decide : 2 ≠ 0),add_zero] at he
  have hg : g^2 = 0 := by linarith [sq_nonneg g]
  exact ⟨hb',sq_eq_zero_iff.mp hg,by linarith⟩

lemma equality_norms {E F G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    (X A B : E) (f : F) (g : G) {μ L : ℝ} (hl : μ < L)
    (hn : ‖X‖^2 = ‖A‖^2+‖B‖^2) (hv : μ*‖A‖^2 ≤ ‖f‖^2)
    (hj : L*‖B‖^2 ≤ ‖g‖^2) (he : μ*‖X‖^2 = ‖f‖^2+‖g‖^2) :
    B=0 ∧ g=0 ∧ μ*‖A‖^2 = ‖f‖^2 := by
  obtain ⟨hB,hg,ha⟩ := scalar_surplus_eq hl hv hj (by rwa [hn] at he)
  exact ⟨norm_eq_zero.mp hB,norm_eq_zero.mp hg,ha⟩

lemma add_map_zero {E F : Type*} [AddCommMonoid E] [AddCommMonoid F]
    (T : E →+ F) {X A : F} {B : E} (hX : X=A+T B) (hB : B=0) : X=A := by
  simpa only [hB,map_zero,add_zero] using hX

lemma equality_minimizer {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) (v : N1 hb) (j : H10 ho)
    (F : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv (N1.grad hb v + rotL Ω (H10.grad ho j)) F)
    (he : firstPositiveNeumannValue Ω * ‖N1.grad hb v‖^2 = ‖F‖^2) :
    firstPositiveNeumannValue Ω * ‖N1.value hb v‖^2 = ‖N1.grad hb v‖^2 :=
  scalar_rayleigh_eq (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hμ (N1.rayleigh hb v)
    ((energy_pair_normal ho hb v j F hF).trans_le (neg_inner_bound F (N1.value hb v))) he

lemma equality_of_decomposition {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
    (X : V2 Ω) (F G : Lp ℝ 2 (volume.restrict Ω)) (v : N1 hb) (j : H10 ho)
    (hX : X = N1.grad hb v + rotL Ω (H10.grad ho j))
    (hv : firstPositiveNeumannValue Ω * ‖N1.grad hb v‖^2 ≤ ‖F‖^2)
    (hj : L * ‖H10.grad ho j‖^2 ≤ ‖G‖^2)
    (hF : WeakNormalDiv X F)
    (he : firstPositiveNeumannValue Ω * ‖X‖^2 = ‖F‖^2+‖G‖^2) :
    X = N1.grad hb v ∧ G = 0 ∧
      firstPositiveNeumannValue Ω * ‖N1.value hb v‖^2 = ‖N1.grad hb v‖^2 := by
  have hn : ‖X‖^2 = ‖N1.grad hb v‖^2 + ‖H10.grad ho j‖^2 :=
    (congrArg (fun x : V2 Ω => ‖x‖^2) hX).trans (decomposition_norm ho hb v j)
  exact (equality_norms X (N1.grad hb v) (H10.grad ho j) F G hl hn hv hj he).elim
    fun hj0 hh => ⟨add_map_zero (rotL Ω).toAddMonoidHom hX hj0,hh.1,
      equality_minimizer ho hb hμ v j F (hX ▸ hF) hh.2⟩




theorem vector_equality {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) {L : ℝ}
    (hl : firstPositiveNeumannValue Ω < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X : V2 Ω) (F G : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv X F) (hG : WeakCurl ho X G)
    (he : firstPositiveNeumannValue Ω * ‖X‖^2 = ‖F‖^2+‖G‖^2) :
    ∃ v : N1 hb, X = N1.grad hb v ∧ G = 0 ∧
      firstPositiveNeumannValue Ω * ‖N1.value hb v‖^2 = ‖N1.grad hb v‖^2 := by
  exact (energy_decomposition ho hne hs hb hμ hl hD X F G hF hG).imp fun v hv =>
    hv.elim fun j hj => equality_of_decomposition ho hb hμ hl X F G v j hj.1 hj.2.1 hj.2.2 hF he

lemma norm_minimizer_integral {Ω : Set Plane} (u : H1 Ω)
    (he : firstPositiveNeumannValue Ω * ‖H1.value u‖^2 = ‖H1.grad u‖^2) :
    (∫ x in Ω, ‖H1.grad u x‖^2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, (H1.value u x)^2) :=
  (H1.norm_grad_sq u).symm.trans (he.symm.trans
    (congrArg (fun t : ℝ => firstPositiveNeumannValue Ω*t) (H1.norm_value_sq u)))

lemma real_L2_pair {α : Type*} [MeasurableSpace α] (ν : Measure α) (f g : Lp ℝ 2 ν) :
    inner ℝ f g = ∫ x, f x*g x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [RCLike.inner_apply,RCLike.conj_to_real]
    exact mul_comm _ _

lemma minimizer_euler_H1 {Ω : Set Plane} (hb : Bornology.IsBounded Ω)
    (hvol : 0 < (volume Ω).toReal) (u : H1 Ω) (hm : (∫ x in Ω, H1.value u x)=0)
    (he : firstPositiveNeumannValue Ω * ‖H1.value u‖^2 = ‖H1.grad u‖^2)
    (w : H1 Ω) : inner ℝ (H1.grad u) (H1.grad w) =
      firstPositiveNeumannValue Ω * inner ℝ (H1.value u) (H1.value w) :=
  (L2.inner_def _ _).trans ((minimizer_euler hb hvol (H1.hasH1Gradient u)
    (H1.hasH1Gradient w) hm (norm_minimizer_integral u he)).trans
      (congrArg (fun t : ℝ => firstPositiveNeumannValue Ω*t)
        (real_L2_pair (volume.restrict Ω) (H1.value u) (H1.value w)).symm))

lemma minimizer_euler_L2 {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hb : Bornology.IsBounded Ω) (v : N1 hb)
    (he : firstPositiveNeumannValue Ω * ‖N1.value hb v‖^2 = ‖N1.grad hb v‖^2)
    (w : H1 Ω) : inner ℝ (N1.grad hb v) (H1.grad w) =
      firstPositiveNeumannValue Ω * inner ℝ (N1.value hb v) (H1.value w) :=
  minimizer_euler_H1 hb
    (ENNReal.toReal_pos (ho.measure_pos volume hne).ne' hb.measure_lt_top.ne)
    v.val (N1.mean_zero hb v) he w

end StrictHotSpots.Hodge

end HodgeEqualityInteriorSupportLayer


end

end ActualVectorSupport

end OAI
