import OAI.MathematicalPhysics.Elasticity.Regularity

namespace OAI

noncomputable section

/-! The Hahn--Banach / Riesz step used by the physical solvability argument.
This proves the functional-analytic implication, rather than postulating
existence of a right inverse. The physical test estimate is proved separately. -/
namespace ElasticityDualSolvability

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A lower norm estimate on an (unbounded) test operator gives a weak solution
for every Hilbert-space forcing, with precisely the same constant. No density
or completeness of the test space, or closedness of the range, is assumed. -/
theorem exists_weak_solution (D : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ v : D, ‖(v : H)‖ ≤ C * ‖A v‖) (f : H) :
    ∃ z : H, ‖z‖ ≤ C * ‖f‖ ∧ ∀ v : D, inner ℂ z (A v) = inner ℂ f (v : H) := by
  have hinj : Function.Injective A := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply Subtype.val_injective
    apply norm_eq_zero.mp
    have ht := hA (v-w)
    rw [map_sub, hvw, sub_self, norm_zero, mul_zero] at ht
    exact le_antisymm ht (norm_nonneg _)
  let T := (LinearEquiv.ofInjective A hinj).symm
  let l : A.range →ₗ[ℂ] ℂ :=
    ((innerSL ℂ f).toLinearMap.comp D.subtype).comp T.toLinearMap
  have hT (y : A.range) : A (T y) = (y : H) := by
    exact congrArg Subtype.val ((LinearEquiv.ofInjective A hinj).apply_symm_apply y)
  have hl : ∀ y : A.range, ‖l y‖ ≤ (C*‖f‖)*‖y‖ := by
    intro y
    change ‖inner ℂ f ((T y : D) : H)‖ ≤ _
    calc
      _ ≤ ‖f‖ * ‖((T y : D) : H)‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * (C*‖A (T y)‖) := mul_le_mul_of_nonneg_left (hA (T y)) (norm_nonneg _)
      _ = _ := by rw [hT]; change ‖f‖ * (C * ‖y‖) = _; ring
  let L : A.range →L[ℂ] ℂ := l.mkContinuous (C*‖f‖) hl
  obtain ⟨G, hG, hnorm⟩ := exists_extension_norm_eq A.range L
  let z : H := (InnerProductSpace.toDual ℂ H).symm G
  refine ⟨z, ?_, fun v => ?_⟩
  · calc
      ‖z‖ = ‖G‖ := (InnerProductSpace.toDual ℂ H).symm.norm_map _
      _ = ‖L‖ := hnorm
      _ ≤ C*‖f‖ := l.mkContinuous_norm_le (mul_nonneg hC (norm_nonneg _)) hl
  · change inner ℂ ((InnerProductSpace.toDual ℂ H).symm G) (A v) = _
    rw [InnerProductSpace.toDual_symm_apply]
    change G ((LinearEquiv.ofInjective A hinj v : A.range) : H) = _
    rw [hG]
    change inner ℂ f ((T (LinearEquiv.ofInjective A hinj v) : D) : H) = _
    rw [LinearEquiv.symm_apply_apply]

end ElasticityDualSolvability

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalDual
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
open ElasticityPhysicalAlgebra ElasticityPhysicalEstimate
abbrev X := ElasticityBessel.X
abbrev H := PiLp 2 (fun _ : Fin 3 => Lp ℂ 2 (volume : Measure X))

def embed : (Fin 3 → S) →ₗ[ℂ] H where
  toFun u := WithLp.toLp 2 (fun i => L2 (u i))
  map_add' u v := by apply PiLp.ext; intro i; exact map_add L2 _ _
  map_smul' a u := by apply PiLp.ext; intro i; exact map_smul L2 _ _

lemma embed_apply (u : Fin 3 → S) (i : Fin 3) : embed u i = L2 (u i) := rfl

lemma embed_injective : Function.Injective embed := by
  intro u v h
  funext i
  apply SchwartzMap.injective_toLp 2 volume
  exact congrArg (fun w : H => w i) h

lemma norm_embed (h : ℝ) (u : Fin 3 → S) : ‖embed u‖ = sobNorm h 0 u := by
  rw [PiLp.norm_eq_of_L2]
  simp only [embed_apply, sobNorm, J_zero, norm2]

lemma inner_embed (u v : Fin 3 → S) :
    inner ℂ (embed u) (embed v) = ∑ i, pair (u i) (v i) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact ip_integral _ _

def adjPhase (z : Fin 3 → ℂ) (i : Fin 3) : ℂ := -star (z i)

lemma pair_neg_left (f g : S) : pair (-f) g = -pair f g := by
  simpa only [neg_one_smul, star_neg, star_one, neg_mul, one_mul] using pair_smul_left f g (-1)

lemma pair_neg_right (f g : S) : pair f (-g) = -pair f g := by
  simpa only [neg_one_smul, neg_mul, one_mul] using pair_smul_right f g (-1)

lemma pair_shift (z : Fin 3 → ℂ) (i : Fin 3) (f g : S) :
    pair f (shiftD z i g) = -pair (shiftD (adjPhase z) i f) g := by
  simp only [shiftD_apply, pair_add_right, pair_add_left, pair_smul_left,
    pair_smul_right, pair_d, adjPhase, star_neg, star_star]
  ring

lemma pair_mult (a : X → ℂ) (ha : a.HasTemperateGrowth) (hr : ∀ x, star (a x) = a x)
    (f g : S) : pair f (mult a g) = pair (mult a f) g := by
  unfold pair
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [mult_apply a ha, star_mul, hr]
  ring

lemma pair_two_shift (z : Fin 3 → ℂ) (i j : Fin 3) (a : X → ℂ)
    (ha : a.HasTemperateGrowth) (hr : ∀ x, star (a x) = a x) (f g : S) :
    pair f (shiftD z i (mult a (shiftD z j g))) =
      pair (shiftD (adjPhase z) j (mult a (shiftD (adjPhase z) i f))) g := by
  rw [pair_shift, pair_mult a ha hr, pair_shift, neg_neg]

lemma pair_eq_ip (f g : S) : pair f g = ip f g := (ip_integral f g).symm

lemma pair_sum_left {ι : Type*} (s : Finset ι) (f : ι → S) (g : S) :
    pair (∑ i ∈ s, f i) g = ∑ i ∈ s, pair (f i) g := by
  simpa only [pair_eq_ip, ip, map_sum] using
    (sum_inner (𝕜 := ℂ) (s := s) (f := fun i => L2 (f i)) (L2 g))

lemma pair_sum_right {ι : Type*} (s : Finset ι) (f : S) (g : ι → S) :
    pair f (∑ i ∈ s, g i) = ∑ i ∈ s, pair f (g i) := by
  simpa only [pair_eq_ip, ip, map_sum] using
    (inner_sum (𝕜 := ℂ) (s := s) (f := fun i => L2 (g i)) (L2 f))

lemma physical_adjoint (z : Fin 3 → ℂ) (lam m : X → ℂ)
    (hl : lam.HasTemperateGrowth) (hm : m.HasTemperateGrowth)
    (hrl : ∀ x, star (lam x) = lam x) (hrm : ∀ x, star (m x) = m x)
    (u v : Fin 3 → S) :
    inner ℂ (embed v) (embed (physical z lam m u)) =
      inner ℂ (embed (physical (adjPhase z) lam m v)) (embed u) := by
  simp only [inner_embed, physical, map_sum, map_add, pair_add_left, pair_add_right,
    pair_sum_left, pair_sum_right, pair_two_shift z _ _ lam hl hrl,
    pair_two_shift z _ _ m hm hrm, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
  · congr 1
    rw [Finset.sum_comm]

/-- Supported Schwartz vectors, regarded as an actual subspace of L2. -/
def supported (R : ℝ) : Submodule ℂ (Fin 3 → S) where
  carrier := {u | ∀ i, BallSupported R (u i)}
  zero_mem' _i := BallSupported.zero R
  add_mem' hu hv i := (hu i).add (hv i)
  smul_mem' a _u hu i := (hu i).smul a

lemma physical_add (z : Fin 3 → ℂ) (lam m : X → ℂ) (u v : Fin 3 → S) :
    physical z lam m (u+v) = physical z lam m u + physical z lam m v := by
  funext i
  simp only [physical, Pi.add_apply, map_add, Finset.sum_add_distrib]
  abel

lemma physical_smul (z : Fin 3 → ℂ) (lam m : X → ℂ) (a : ℂ) (u : Fin 3 → S) :
    physical z lam m (a • u) = a • physical z lam m u := by
  funext i
  simp only [physical, Pi.smul_apply, map_smul, ← smul_add, ← Finset.smul_sum]

/-- Exact shifted stress-divergence as a linear map, for duality on its range. -/
def physicalLM (z : Fin 3 → ℂ) (lam m : X → ℂ) : (Fin 3 → S) →ₗ[ℂ] (Fin 3 → S) where
  toFun := physical z lam m
  map_add' := physical_add z lam m
  map_smul' := physical_smul z lam m

/-- The physical weak equation follows from the actual uniform test estimate.
The forcing and unknown belong to the genuine vector-valued L2 Hilbert space. -/
theorem weak_physical_from_test (R h : ℝ) (z : Fin 3 → ℂ) (lam m : X → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (htest : ∀ u : Fin 3 → S, (∀ i, BallSupported R (u i)) →
      sobNorm h 0 u ≤ C*sobNorm h 0 (physical (adjPhase z) lam m u)) (F : H) :
    ∃ w : H, ‖w‖ ≤ C*‖F‖ ∧ ∀ v : Fin 3 → S, (∀ i, BallSupported R (v i)) →
      inner ℂ w (embed (physical (adjPhase z) lam m v)) = inner ℂ F (embed v) := by
  let V := supported R
  let T : V →ₗ[ℂ] H := embed.comp V.subtype
  have hinj : Function.Injective T := by
    intro v w hvw
    exact Subtype.val_injective (embed_injective hvw)
  let E := LinearEquiv.ofInjective T hinj
  let B : T.range →ₗ[ℂ] H :=
    (((embed.comp (physicalLM (adjPhase z) lam m)).comp V.subtype).comp E.symm.toLinearMap)
  have hT (y : T.range) : T (E.symm y) = (y : H) :=
    congrArg Subtype.val (E.apply_symm_apply y)
  have hB (y : T.range) : ‖(y : H)‖ ≤ C*‖B y‖ := by
    rw [← hT y]
    change ‖embed ((E.symm y : V) : Fin 3 → S)‖ ≤
      C * ‖embed (physical (adjPhase z) lam m ((E.symm y : V) : Fin 3 → S))‖
    rw [norm_embed h, norm_embed h]
    exact htest _ (E.symm y).property
  obtain ⟨w, hw, heq⟩ := ElasticityDualSolvability.exists_weak_solution T.range B C hC hB F
  refine ⟨w, hw, fun v hv => ?_⟩
  let v' : V := ⟨v, hv⟩
  have hh := heq (E v')
  change inner ℂ w (embed (physical (adjPhase z) lam m ((E.symm (E v') : V) : Fin 3 → S))) =
    inner ℂ F (T v') at hh
  rw [E.symm_apply_apply] at hh
  exact hh

lemma adjPhase_phase (h : ℝ) (α β : X) :
    adjPhase (phase h α β) = phase h (-α) β := by
  funext i
  simp only [adjPhase, phase, Complex.star_def, map_div₀, map_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I, PiLp.neg_apply, Complex.ofReal_neg]
  ring

end ElasticityPhysicalDual

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
namespace ElasticityDistribution

section

open ElasticityPhysicalAlgebra ElasticityPhysicalDual ElasticityNegativeOrder
abbrev S := 𝓢(X,ℂ)
def cj (φ : S) : S := φ.postcompCLM Complex.conjCLE.toContinuousLinearMap
@[simp] lemma cj_apply (φ : S) (x : X) : cj φ x = star (φ x) := rfl
lemma cj_add (φ ψ : S) : cj (φ+ψ) = cj φ+cj ψ := by ext x; simp
lemma cj_smul (c : ℂ) (φ : S) : cj (c • φ) = star c • cj φ := by ext x; simp
lemma cj_sum {ι : Type*} (s : Finset ι) (φ : ι → S) : cj (∑ i ∈ s, φ i) = ∑ i ∈ s, cj (φ i) := by
  ext x
  simp
lemma cj_cj (φ : S) : cj (cj φ) = φ := by ext x; simp
lemma cj_deriv (i : Fin 3) (φ : S) : cj (∂_{ElasticityAugmented.e i} φ) = ∂_{ElasticityAugmented.e i} (cj φ) := by
  ext x
  change star (fderiv ℝ φ x (ElasticityAugmented.e i)) = fderiv ℝ (cj φ) x (ElasticityAugmented.e i)
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x (φ.hasFDerivAt x)
  exact (congrArg (fun T : X →L[ℝ] ℂ => T (ElasticityAugmented.e i)) h.fderiv).symm
lemma cj_shift (z : Fin 3 → ℂ) (i : Fin 3) (φ : S) :
    cj (shiftD z i φ) = shiftD (fun i => star (z i)) i (cj φ) := by
  simp only [shiftD_apply,cj_add,cj_smul]
  congr 1
  exact cj_deriv i φ
lemma cj_mult (a : X → ℂ) (ha : a.HasTemperateGrowth) (hr : ∀ x, star (a x)=a x) (φ : S) :
    cj (mult a φ) = mult a (cj φ) := by
  ext x
  simp only [cj_apply,mult_apply a ha,star_mul,hr]
  exact mul_comm _ _
lemma cj_physical (z : Fin 3 → ℂ) (lam m : X → ℂ)
    (hl : lam.HasTemperateGrowth) (hm : m.HasTemperateGrowth)
    (hrl : ∀ x, star (lam x)=lam x) (hrm : ∀ x, star (m x)=m x) (φ : Fin 3 → S)
    {index : Fin 3} :
    cj (physical z lam m φ index) =
      physical (fun i => star (z i)) lam m (fun i => cj (φ i)) index := by
  simp only [physical,cj_add,cj_shift,cj_mult lam hl hrl,cj_mult m hm hrm,cj_sum]
lemma cj_supported {R : ℝ} {φ : S} (h : BallSupported R φ) : BallSupported R (cj φ) := by
  intro x hx
  exact h x (fun h0 => hx (by simp [h0]))
lemma Lp_test (w : Lp ℂ 2 (volume : Measure X)) (φ : S) :
    (w : Dist) φ = inner ℂ (ElasticityBessel.L2 (cj φ)) w := by
  rw [Lp.toTemperedDistribution_apply,MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cj φ).coeFn_toLp 2 volume] with x hx
  change φ x • w x = inner ℂ ((ElasticityBessel.L2 (cj φ)) x) (w x)
  change (ElasticityBessel.L2 (cj φ) : X → ℂ) x = cj φ x at hx
  rw [hx]
  simp only [cj_apply,RCLike.inner_apply',starRingEnd_apply,star_star,smul_eq_mul,mul_comm]

open ElasticityAugmented TemperedDistribution
open ElasticityPhysicalAlgebra (shiftD shiftD_apply)
open ElasticityNegativeOrder (mult)

lemma sd_test (z : Fin 3 → ℂ) (i : Fin 3) (u : Dist) (φ : S) :
    (sd z i u) φ = -u (shiftD (-z) i φ) := by
  simp only [sd_apply,dd_apply,lineDerivOp_apply_apply,add_apply,smul_apply,
    shiftD_apply,map_neg,map_add,map_smul,Pi.neg_apply,neg_smul]
  change -u (∂_{e i} φ)+z i • u φ = -(u (∂_{e i} φ)+ -(z i • u φ))
  abel
lemma coeff_test (a : Coeff) (u : Dist) (φ : S) :
    (a • u) φ = u (mult (eval a) φ) := rfl
lemma coeff_smul_add (a : Coeff) (u v : Dist) : a • (u+v)=a•u+a•v :=
  (TemperedDistribution.smulLeftCLM ℂ (eval a)).map_add u v
lemma two_sd_test (z : Fin 3 → ℂ) (i j : Fin 3) (a : Coeff) (u : Dist) (φ : S) :
    (sd z i (a • sd z j u)) φ =
      u (shiftD (-z) j (mult (eval a) (shiftD (-z) i φ))) := by
  rw [sd_test,coeff_test,sd_test,neg_neg]

/-- Formal transpose of the actual complex physical distribution operator.
It is proved by evaluation on Schwartz tests, so no integration-by-parts
regularity of the unknown is assumed. -/
theorem physical_transpose (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (φ : Fin 3 → S) :
    (∑ i, phys z lam m u i (φ i)) =
      ∑ i, u i (ElasticityPhysicalAlgebra.physical (-z) (eval lam) (eval m) φ i) := by
  have h_lam : (∑ i, ∑ j, u j (shiftD (-z) j (mult (eval lam) (shiftD (-z) i (φ i))))) =
      ∑ i, ∑ j, u i (shiftD (-z) i (mult (eval lam) (shiftD (-z) j (φ j)))) :=
    Finset.sum_comm
  have hm : (∑ i, ∑ j, u j (shiftD (-z) i (mult (eval m) (shiftD (-z) j (φ i))))) =
      ∑ i, ∑ j, u i (shiftD (-z) j (mult (eval m) (shiftD (-z) i (φ j)))) :=
    Finset.sum_comm
  simp only [phys,divd,Finset.smul_sum,map_sum,coeff_smul_add,map_add,sum_apply,add_apply,
    two_sd_test,Finset.sum_add_distrib,
    ElasticityPhysicalAlgebra.physical]
  rw [h_lam,hm]

end

open ElasticityPhysicalAlgebra ElasticityPhysicalDual ElasticityNegativeOrder

/-- The actual Hilbert weak equation is the actual physical distribution equation.
This lemma does not assume regularity of the unknown and does not replace the
physical stress-divergence operator by an abstract PDE hypothesis. -/
theorem weak_to_vector_distribution (R : ℝ) (z : Fin 3 → ℂ) (lam m : Coeff)
    (hrl : ∀ x, star (eval lam x)=eval lam x) (hrm : ∀ x, star (eval m x)=eval m x)
    (w F : H)
    (heq : ∀ v : Fin 3 → S, (∀ i, BallSupported R (v i)) →
      inner ℂ w (embed (physical (adjPhase z) (eval lam) (eval m) v)) = inner ℂ F (embed v))
    (φ : Fin 3 → S) (hφ : ∀ i, BallSupported R (φ i)) :
    (∑ i, phys z lam m (fun j => (w j : Dist)) i (φ i)) =
      ∑ i, (F i : Dist) (φ i) := by
  rw [physical_transpose]
  simp only [Lp_test]
  have h := congrArg star (heq (fun i => cj (φ i)) (fun i => cj_supported (hφ i)))
  have hs (a b : H) : star (inner ℂ a b)=inner ℂ b a :=
    inner_conj_symm (𝕜 := ℂ) b a
  simp only [hs] at h
  rw [PiLp.inner_apply,PiLp.inner_apply] at h
  have hh (i : Fin 3) : physical (adjPhase z) (eval lam) (eval m) (fun j => cj (φ j)) i =
      cj (physical (-z) (eval lam) (eval m) φ i) := by
    rw [cj_physical _ _ _ (growth lam) (growth m) hrl hrm]
    rfl
  simpa only [embed_apply,hh] using h

theorem weak_to_local_physical (Ω : Set X) (R : ℝ) (hΩ : Ω ⊆ Metric.closedBall 0 R)
    (z : Fin 3 → ℂ) (lam m : Coeff)
    (hrl : ∀ x, star (eval lam x)=eval lam x) (hrm : ∀ x, star (eval m x)=eval m x)
    (w F : H)
    (heq : ∀ v : Fin 3 → S, (∀ i, BallSupported R (v i)) →
      inner ℂ w (embed (physical (adjPhase z) (eval lam) (eval m) v)) = inner ℂ F (embed v)) :
    ∀ i, LocalEq Ω (phys z lam m (fun j => (w j : Dist)) i) (F i : Dist) := by
  classical
  intro i φ _hc hs
  let ψ : Fin 3 → S := fun j => if j=i then φ else 0
  have hψ : ∀ j, BallSupported R (ψ j) := by
    intro j
    by_cases hji : j=i
    · intro x hx
      have hx' : φ x ≠ 0 := by simpa only [ψ,ite_eq_left hji] using hx
      have hxx := hΩ (hs (subset_tsupport _ hx'))
      simpa only [Metric.mem_closedBall,dist_zero_right] using hxx
    · simpa only [ψ,ite_eq_right hji] using BallSupported.zero R
  have h := weak_to_vector_distribution R z lam m hrl hrm w F heq ψ hψ
  simpa only [ψ,apply_ite,map_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h
end ElasticityDistribution

open scoped BigOperators
namespace ElasticityCoeffBounds
open ElasticityAugmented ElasticityPhysicalEstimate
abbrev X := ElasticityAugmented.X

def ExteriorConstant (f : Smooth) : Prop :=
  ∃ c : ℂ, HasCompactSupport (fun x => (f : X → ℂ) x - c)

lemma ExteriorConstant.growth {f : Smooth} (hf : ExteriorConstant f) :
    (f : X → ℂ).HasTemperateGrowth := by
  obtain ⟨c, hc⟩ := hf
  have hg := hc.hasTemperateGrowth ((smooth_coe f).sub contDiff_const)
  convert hg.add (Function.HasTemperateGrowth.const c) using 1
  funext x
  simp

lemma ExteriorConstant.bound {f : Smooth} (hf : ExteriorConstant f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖(f : X → ℂ) x‖ ≤ C := by
  obtain ⟨c, hc⟩ := hf
  have hcont : Continuous (fun x => ‖(f : X → ℂ) x - c‖) :=
    ((smooth_coe f).continuous.sub continuous_const).norm
  obtain ⟨x₀, hx⟩ := hcont.exists_forall_ge_of_hasCompactSupport hc.norm
  refine ⟨‖(f : X → ℂ) x₀ - c‖ + ‖c‖, by positivity, fun x => ?_⟩
  calc
    ‖(f : X → ℂ) x‖ = ‖((f : X → ℂ) x-c)+c‖ := by rw [sub_add_cancel]
    _ ≤ ‖(f : X → ℂ) x-c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ ‖(f : X → ℂ) x₀-c‖ + ‖c‖ := by linarith [hx x]

lemma ExteriorConstant.const (c : ℂ) : ExteriorConstant (algebraMap ℂ Smooth c) := by
  refine ⟨c, ?_⟩
  change HasCompactSupport (fun _ : X => c-c)
  exact HasCompactSupport.intro isCompact_empty (fun _ _ => sub_self c)

lemma ExteriorConstant.add {f g : Smooth} (hf : ExteriorConstant f) (hg : ExteriorConstant g) :
    ExteriorConstant (f+g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨c+d, ?_⟩
  have he : (fun x => ((f+g : Smooth) : X → ℂ) x - (c+d)) =
      (fun x => (f : X → ℂ) x-c) + (fun x => (g : X → ℂ) x-d) := by
    funext x
    change (f : X → ℂ) x + (g : X → ℂ) x - (c+d) = _
    dsimp
    ring
  rw [he]
  exact hc.add hd

lemma ExteriorConstant.mul {f g : Smooth} (hf : ExteriorConstant f) (hg : ExteriorConstant g) :
    ExteriorConstant (f*g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨c*d, ?_⟩
  have h1 : HasCompactSupport ((fun x => (f : X → ℂ) x-c) * (g : X → ℂ)) := hc.mul_right
  have h2 : HasCompactSupport ((fun _ : X => c) * (fun x => (g : X → ℂ) x-d)) := hd.mul_left
  have he : (fun x => ((f*g : Smooth) : X → ℂ) x - c*d) =
      ((fun x => (f : X → ℂ) x-c) * (g : X → ℂ)) +
        ((fun _ : X => c) * (fun x => (g : X → ℂ) x-d)) := by
    funext x
    change (f : X → ℂ) x * (g : X → ℂ) x - c*d = _
    dsimp
    ring
  rw [he]
  exact h1.add h2

lemma ExteriorConstant.neg {f : Smooth} (hf : ExteriorConstant f) : ExteriorConstant (-f) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨-c, ?_⟩
  have he : (fun x => ((-f : Smooth) : X → ℂ) x - (-c)) = -(fun x => (f : X → ℂ) x-c) := by
    funext x
    change -(f : X → ℂ) x - (-c) = -((f : X → ℂ) x-c)
    ring
  rw [he]
  exact hc.neg

lemma ExteriorConstant.sub {f g : Smooth} (hf : ExteriorConstant f) (hg : ExteriorConstant g) :
    ExteriorConstant (f-g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma ExteriorConstant.coord {f : Smooth} (hf : ExteriorConstant f) (i : Fin 3) :
    ExteriorConstant (coord i f) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨0, ?_⟩
  have hs : HasCompactSupport (fun x => fderiv ℝ (fun y => (f : X → ℂ) y-c) x (e i)) :=
    hc.fderiv_apply (𝕜 := ℝ) (e i)
  convert hs using 1
  funext x
  simp only [sub_zero, coord_apply, fderiv_sub_const]

lemma ExteriorConstant.zero : ExteriorConstant (0 : Smooth) := by
  simpa only [map_zero] using ExteriorConstant.const 0

lemma ExteriorConstant.natCast (n : ℕ) : ExteriorConstant (n : Smooth) := by
  simpa only [map_natCast] using ExteriorConstant.const (n : ℂ)

lemma ExteriorConstant.sum {ι : Type*} (s : Finset ι) (f : ι → Smooth)
    (hf : ∀ i ∈ s, ExteriorConstant (f i)) : ExteriorConstant (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using ExteriorConstant.zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma exterior_coeffA {lam m n o : Smooth} (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hn : ExteriorConstant n) (ho : ExteriorConstant o) (k : Fin 3) (i j : Fin 4) :
    ExteriorConstant (coeffA coord lam m n o k i j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact ((ExteriorConstant.natCast 2).mul ho).mul
        (((hl.add hm).coord k).sub (((hl.add hm).mul hn).mul (hm.coord k)))
    · exact ((ExteriorConstant.natCast 2).mul ho).mul
        (((hm.coord j).coord k).sub
          ((((ExteriorConstant.natCast 2).mul hn).mul (hm.coord k)).mul (hm.coord j)))
  · refine Fin.cases ?_ (fun j => ?_) j
    · change ExteriorConstant (if k=i then (lam+m)*n else 0)
      split
      · exact (hl.add hm).mul hn
      · exact ExteriorConstant.zero
    · change ExteriorConstant ((if j=i then n*coord k m else 0) +
        (if k=i then n*coord j m else 0))
      apply ExteriorConstant.add
      · split
        · exact hn.mul (hm.coord k)
        · exact ExteriorConstant.zero
      · split
        · exact hn.mul (hm.coord j)
        · exact ExteriorConstant.zero

lemma exterior_coeffV {lam m n o : Smooth} (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hn : ExteriorConstant n) (ho : ExteriorConstant o) (i j : Fin 4) :
    ExteriorConstant (coeffV coord lam m n o i j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun _ => ExteriorConstant.zero) j
    exact ho.mul ((ExteriorConstant.sum Finset.univ _ (fun i _ => (hl.coord i).coord i)).sub
      (((ExteriorConstant.natCast 2).mul hn).mul
        (ExteriorConstant.sum Finset.univ _ (fun i _ => (hm.coord i).mul (hl.coord i)))))
  · refine Fin.cases ?_ (fun _ => ExteriorConstant.zero) j
    exact hn.mul (hl.coord i)

lemma exterior_cPhys {m n : Smooth} (hm : ExteriorConstant m) (hn : ExteriorConstant n)
    (i : Fin 3) : ExteriorConstant (-2*n*coord i m) :=
  (((ExteriorConstant.natCast 2).neg).mul hn).mul (hm.coord i)

lemma ExteriorConstant.uniform_bound {ι : Type*} [Fintype ι] (f : ι → Smooth)
    (hf : ∀ i, ExteriorConstant (f i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, ‖(f i : X → ℂ) x‖ ≤ C := by
  classical
  choose C hC hb using (fun i => (hf i).bound)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun i x => ?_⟩
  exact (hb i x).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

/-- The reciprocal is the pointwise reciprocal, not an abstract inverse assumption. -/
def reciprocal (f : Smooth) (hf : ∀ x, (f : X → ℂ) x ≠ 0) : Smooth :=
  ⟨fun x => ((f : X → ℂ) x)⁻¹, (smooth_coe f).inv hf⟩

lemma reciprocal_mul (f : Smooth) (hf : ∀ x, (f : X → ℂ) x ≠ 0) :
    reciprocal f hf * f = 1 := by
  apply Subtype.ext
  funext x
  exact inv_mul_cancel₀ (hf x)

lemma ExteriorConstant.reciprocal {f : Smooth} (hf : ExteriorConstant f)
    (hn : ∀ x, (f : X → ℂ) x ≠ 0) : ExteriorConstant (reciprocal f hn) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨c⁻¹, hc.mono' ?_⟩
  intro x hx
  change ((f : X → ℂ) x)⁻¹-c⁻¹ ≠ 0 at hx
  apply subset_tsupport (fun x => (f : X → ℂ) x-c)
  change (f : X → ℂ) x-c ≠ 0
  intro h
  apply hx
  exact sub_eq_zero.mpr (congrArg Inv.inv (sub_eq_zero.mp h))

open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
open ElasticityPhysicalAlgebra (physical phase)

theorem physical_test_exterior (R : ℝ) (hR : 1 ≤ R) (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ u : Fin 3 → S, (∀ i, BallSupported R (u i)) →
        sobNorm h 0 u ≤ C*sobNorm h 0 (physical (phase h α β) lam m u) := by
  let n := reciprocal m hm0
  let o := reciprocal (lam+m+m) he0
  have hn : ExteriorConstant n := hm.reciprocal hm0
  have ho : ExteriorConstant o := ((hl.add hm).add hm).reciprocal he0
  have ha := exterior_coeffA hl hm hn ho
  have hv := exterior_coeffV hl hm hn ho
  have hc := exterior_cPhys hm hn
  obtain ⟨M, hM, hbM⟩ := ExteriorConstant.uniform_bound
    (fun ij : Fin 3 × Fin 4 × Fin 4 => coeffA coord lam m n o ij.1 ij.2.1 ij.2.2)
    (fun ij => ha ij.1 ij.2.1 ij.2.2)
  obtain ⟨V, hV, hbV⟩ := ExteriorConstant.uniform_bound
    (fun ij : Fin 4 × Fin 4 => coeffV coord lam m n o ij.1 ij.2)
    (fun ij => hv ij.1 ij.2)
  obtain ⟨A₁, hA₁, hnA⟩ := hn.bound
  obtain ⟨A₂, hA₂, hoA⟩ := ho.bound
  obtain ⟨A₃, hA₃, hcA⟩ := ExteriorConstant.uniform_bound (fun i => -2*n*coord i m) hc
  obtain ⟨D, hD, hod⟩ := ExteriorConstant.uniform_bound (fun i => coord i o) (fun i => ho.coord i)
  let Z : ℝ := ∑ i, ‖((α i : ℂ)+Complex.I*(β i : ℂ))‖
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hbZ (i : Fin 3) : ‖((α i : ℂ)+Complex.I*(β i : ℂ))‖ ≤ Z :=
    Finset.single_le_sum (fun j _ => norm_nonneg ((α j : ℂ)+Complex.I*(β j : ℂ))) (Finset.mem_univ i)
  apply physical_test_estimate R hR α β hα lam m n o (reciprocal_mul m hm0)
    (reciprocal_mul (lam+m+m) he0) hl.growth hm.growth hn.growth ho.growth
    (fun k i j => (ha k i j).growth) (fun i j => (hv i j).growth) (fun i => (hc i).growth)
    M V (A₁+A₂+A₃) D Z hM hV (by positivity) hD hZ
  · intro k i j x
    simpa only [aPhys, Pi.neg_apply, norm_neg] using hbM (k, i, j) x
  · intro i j x
    simpa only [vPhys, Pi.neg_apply, norm_neg] using hbV (i, j) x
  · intro x
    linarith [hnA x]
  · intro x
    linarith [hoA x]
  · intro i x
    have hh := hcA i x
    change ‖((-2*n*coord i m : Smooth) : X → ℂ) x‖ ≤ _
    linarith
  · exact fun x i => hod i x
  · exact hbZ

end ElasticityCoeffBounds

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalSolvability
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
open ElasticityAugmented
open ElasticityPhysicalAlgebra (physical phase)
open ElasticityPhysicalDual ElasticityCoeffBounds
abbrev X := ElasticityAugmented.X

theorem weak_solvability (R : ℝ) (hR : 1 ≤ R) (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ F : H, ∃ w : H, ‖w‖ ≤ C*‖F‖ ∧ ∀ v : Fin 3 → S,
        (∀ i, BallSupported R (v i)) →
        inner ℂ w (embed (physical (adjPhase (phase h α β)) lam m v)) =
          inner ℂ F (embed v) := by
  obtain ⟨C, h₀, hC, hh₀, hest⟩ := physical_test_exterior R hR (-α) β
    (neg_ne_zero.mpr hα) lam m hl hm hm0 he0
  refine ⟨C, h₀, hC, hh₀, fun h hh hsmall F => ?_⟩
  apply weak_physical_from_test R h (phase h α β) lam m C hC.le ?_ F
  intro u hu
  rw [adjPhase_phase]
  exact hest h hh hsmall u hu

/-- The real smooth coefficients are embedded pointwise, not abstractly. -/
def realSmooth (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Smooth :=
  ⟨fun x => (f x : ℂ), Complex.ofRealCLM.contDiff.comp hf⟩

lemma realSmooth_real (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : X) :
    star ((realSmooth f hf : X → ℂ) x) = (realSmooth f hf : X → ℂ) x := by
  exact Complex.conj_ofReal _

lemma exterior_of_ball (f : Smooth) (R : ℝ) (c : ℂ)
    (hf : ∀ x, R ≤ ‖x‖ → (f : X → ℂ) x = c) : ExteriorConstant f := by
  refine ⟨c, HasCompactSupport.intro (isCompact_closedBall (0 : X) R) ?_⟩
  intro x hx
  have hx' : R < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  exact sub_eq_zero.mpr (hf x hx'.le)

/-- Coefficient assumptions for this PDE lemma: smooth, strongly
convex, constant outside a ball. No bounds on their derivatives are assumed. -/
theorem real_weak_solvability (R : ℝ) (hR : 1 ≤ R) (α β : X) (hα : α ≠ 0)
    (lam m : X → ℝ) (hl : ContDiff ℝ (⊤ : ℕ∞) lam) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hpos : ∀ x, 0 < m x ∧ 0 < 3*lam x+2*m x)
    (Rext cl cm : ℝ) (hext : ∀ x, Rext ≤ ‖x‖ → lam x=cl ∧ m x=cm) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ F : H, ∃ w : H, ‖w‖ ≤ C*‖F‖ ∧ ∀ v : Fin 3 → S,
        (∀ i, BallSupported R (v i)) →
        inner ℂ w (embed (physical (adjPhase (phase h α β))
          (realSmooth lam hl) (realSmooth m hm) v)) = inner ℂ F (embed v) := by
  apply weak_solvability R hR α β hα
    (realSmooth lam hl) (realSmooth m hm)
  · exact exterior_of_ball _ Rext (cl : ℂ) (fun x hx => congrArg Complex.ofReal (hext x hx).1)
  · exact exterior_of_ball _ Rext (cm : ℂ) (fun x hx => congrArg Complex.ofReal (hext x hx).2)
  · intro x
    change (m x : ℂ) ≠ 0
    exact_mod_cast (hpos x).1.ne'
  · intro x
    have hh : lam x+m x+m x ≠ 0 := by linarith [(hpos x).1, (hpos x).2]
    change (lam x : ℂ)+(m x : ℂ)+(m x : ℂ) ≠ 0
    exact_mod_cast hh

end ElasticityPhysicalSolvability

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
namespace ElasticityDistribution
open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds
open ElasticityPhysicalAlgebra (phase)
open ElasticityPhysicalDual

lemma lp_local_zero (Ω : Set X) (u : Lp ℂ 2 (volume : Measure X)) :
    ElasticityRegularity.LocalSobolev Ω 0 (u : Dist) :=
  ElasticityRegularity.MemSobolev.local_zero (memSobolev_zero_iff.mpr ⟨u,rfl⟩) Ω
lemma schwartz_local_nat (Ω : Set X) (u : S) (N : ℕ) :
    ElasticityRegularity.LocalSobolev Ω N (u : Dist) := by
  intro g hg hc _
  exact sobolev_nat_product (EuclideanSpace.basisFun (Fin 3) ℝ) N hg hc u.memSobolev

/-- Real physical coefficients and pointwise inverses are the actual smooth
coefficients in the distribution formulation. -/
def exteriorCoeff (f : Smooth) (hf : ExteriorConstant f) : Coeff := ⟨f,hf.growth⟩
def inverseCoeff (f : Smooth) (hf : ExteriorConstant f) (hn : ∀ x, (f : X → ℂ) x ≠ 0) : Coeff :=
  exteriorCoeff (reciprocal f hn) (hf.reciprocal hn)
lemma inverseCoeff_mul (f : Smooth) (hf : ExteriorConstant f) (hn : ∀ x, (f : X → ℂ) x ≠ 0) :
    inverseCoeff f hf hn*exteriorCoeff f hf=1 := by
  apply Subtype.ext
  exact reciprocal_mul f hn

/-- Actual uniform physical weak solvability together with proved interior
smoothness of every cutoff of the physical displacement and shifted divergence.
This combines the supported Carleman/Hahn--Banach construction with the true
augmented distribution identity rather than assuming elliptic regularity. -/
theorem weak_smooth_solvability (R : ℝ) (hR : 1 ≤ R)
    (Ω : Set X) (hΩ : Ω ⊆ Metric.closedBall 0 R) (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x, star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x, star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ f : Fin 3 → S, ∃ w : H, ‖w‖ ≤ C*‖embed f‖ ∧
        (∀ i, LocalEq Ω (phys (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm)
          (fun j => (w j : Dist)) i) (f i : Dist)) ∧
        ∀ i : Fin 4, ∀ g : X → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ Ω →
          ∃ v : BoundedContinuousFunction X ℂ, ContDiff ℝ (⊤ : ℕ∞) (v : X → ℂ) ∧
            smulLeftCLM ℂ g ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
              (fun j => (w j : Dist)) : Fin 4 → Dist) i) =
              ((v.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure X)) : Dist) := by
  obtain ⟨C,h₀,hC,hh₀,hsol⟩ := ElasticityPhysicalSolvability.weak_solvability R hR α β hα lam m hl hm hm0 he0
  refine ⟨C,h₀,hC,hh₀,fun h hh hs f => ?_⟩
  obtain ⟨w,hw,hwe⟩ := hsol h hh hs (embed f)
  have heq := weak_to_local_physical Ω R hΩ (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm)
    hrl hrm w (embed f) hwe
  have heq' : ∀ i, LocalEq Ω (phys (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm)
      (fun j => (w j : Dist)) i) (f i : Dist) := by
    intro i
    simpa only [embed_apply,ElasticityBessel.L2,SchwartzMap.toLpCLM_apply,Lp.toTemperedDistribution_toLp_eq] using heq i
  refine ⟨w,hw,heq',fun i g hg hc hgs => ?_⟩
  let n := inverseCoeff m hm hm0
  let o := inverseCoeff (lam+m+m) ((hl.add hm).add hm) he0
  have hn : n*exteriorCoeff m hm=1 := inverseCoeff_mul m hm hm0
  have ho : o*(exteriorCoeff lam hl+exteriorCoeff m hm+exteriorCoeff m hm)=1 := by
    apply Subtype.ext
    exact reciprocal_mul (lam+m+m) he0
  exact physical_cutoff_smooth (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm) n o hn ho
    (fun j => (w j : Dist)) (fun j => (f j : Dist)) heq' (fun j => lp_local_zero Ω (w j))
    (fun N j => schwartz_local_nat Ω (f j) N) i hg hc hgs
end ElasticityDistribution

end

end OAI
