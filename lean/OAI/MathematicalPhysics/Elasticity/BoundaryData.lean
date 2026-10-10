import OAI.MathematicalPhysics.Elasticity.Restriction
import OAI.MathematicalPhysics.Elasticity.BoundaryPackets

namespace OAI

noncomputable section

namespace Elasticity

section
/-! Mixed physical quasimodes. Unlike a quadratic same-system remainder,
this controls the coefficient-difference energy of a trial for each system.
It is the precise physical-DN bridge for the normal-jet induction. -/
open Set MeasureTheory
variable {Ω : Set X} {lam mu : X → ℝ}

lemma DN_trace_symm (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u v : H1Hilbert Ω) :
    DN Ω lam mu (trace Ω (h1Equiv Ω u)) (trace Ω (h1Equiv Ω v)) =
      DN Ω lam mu (trace Ω (h1Equiv Ω v)) (trace Ω (h1Equiv Ω u)) := by
  have huv := DN_quasimode_identity ha hO hB u v
  have hvu := DN_quasimode_identity ha hO hB v u
  have he := energy_symm (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) (h1Equiv Ω u) (h1Equiv Ω v)
  have hz : zeroTraceEnergy (ha.1.boundedCoefficient hO hB)
      (ha.2.1.boundedCoefficient hO hB) (physicalError ha hO hB u)
        (physicalError ha hO hB v) =
      zeroTraceEnergy (ha.1.boundedCoefficient hO hB)
      (ha.2.1.boundedCoefficient hO hB) (physicalError ha hO hB v)
        (physicalError ha hO hB u) := jetEnergy_symm _ _ _ _
  linarith

lemma DN_one_sided_error (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u v : H1Hilbert Ω) :
    energy Ω lam mu (h1Equiv Ω u) (h1Equiv Ω v) -
      DN Ω lam mu (trace Ω (h1Equiv Ω u)) (trace Ω (h1Equiv Ω v)) =
      jetEnergy (ha.1.boundedCoefficient hO hB) (ha.2.1.boundedCoefficient hO hB)
        (physicalError ha hO hB u).val v.val := by
  let U := physicalProjection (lam := lam) (mu := mu) u
  let hl := ha.1.boundedCoefficient hO hB
  let hm := ha.2.1.boundedCoefficient hO hB
  rw [DN_eq_energy ha hO hB]
  have hU : dirichletSolution Ω lam mu (trace Ω (h1Equiv Ω u)) = h1Equiv Ω U :=
    (Equiv.apply_symm_apply _ _).symm
  rw [hU, ← jetEnergy_eq_energy hl hm u v, ← jetEnergy_eq_energy hl hm U v]
  exact (congrArg (fun f : JetH Ω →L[ℝ] ℝ => f v.val)
    ((jetEnergy hl hm).map_sub u.val U.val)).symm

lemma mixed_error_identity {l₁ m₁ l₂ m₂ : X → ℝ}
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hDN : DN Ω l₁ m₁ = DN Ω l₂ m₂) (u v : H1Hilbert Ω) :
    energy Ω l₁ m₁ (h1Equiv Ω u) (h1Equiv Ω v) -
      energy Ω l₂ m₂ (h1Equiv Ω u) (h1Equiv Ω v) =
    jetEnergy (ha₁.1.boundedCoefficient hO hB) (ha₁.2.1.boundedCoefficient hO hB)
      (physicalError ha₁ hO hB u).val v.val -
    jetEnergy (ha₂.1.boundedCoefficient hO hB) (ha₂.2.1.boundedCoefficient hO hB)
      u.val (physicalError ha₂ hO hB v).val := by
  have h₁ := DN_one_sided_error ha₁ hO hB u v
  have h₂ := DN_one_sided_error ha₂ hO hB v u
  rw [energy_symm (ha₂.1.boundedCoefficient hO hB)
      (ha₂.2.1.boundedCoefficient hO hB), DN_trace_symm ha₂ hO hB v u,
      jetEnergy_symm] at h₂
  rw [hDN] at h₁
  linarith

/-- Equal physical DN maps control the *same mixed fields* in the two
coefficient energies, using only the residual in its own system. -/
theorem equal_DN_mixed_quasimode_bound {l₁ m₁ l₂ m₂ : X → ℝ}
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hDN : DN Ω l₁ m₁ = DN Ω l₂ m₂) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ u v : H1Hilbert Ω,
      |energy Ω l₁ m₁ (h1Equiv Ω u) (h1Equiv Ω v) -
        energy Ω l₂ m₂ (h1Equiv Ω u) (h1Equiv Ω v)| ≤
      C₁ * ‖physicalResidual (ha₁.1.boundedCoefficient hO hB)
        (ha₁.2.1.boundedCoefficient hO hB) u‖ * ‖v‖ +
      C₂ * ‖u‖ * ‖physicalResidual (ha₂.1.boundedCoefficient hO hB)
        (ha₂.2.1.boundedCoefficient hO hB) v‖ := by
  obtain ⟨c₁, hc₁, hb₁⟩ := physicalError_bound ha₁ hO hB
  obtain ⟨c₂, hc₂, hb₂⟩ := physicalError_bound ha₂ hO hB
  let E₁ := jetEnergy (ha₁.1.boundedCoefficient hO hB) (ha₁.2.1.boundedCoefficient hO hB)
  let E₂ := jetEnergy (ha₂.1.boundedCoefficient hO hB) (ha₂.2.1.boundedCoefficient hO hB)
  refine ⟨(‖E₁‖+1)/c₁, (‖E₂‖+1)/c₂, by positivity, by positivity, ?_⟩
  intro u v
  rw [mixed_error_identity ha₁ ha₂ hO hB hDN]
  let r₁ := physicalResidual (ha₁.1.boundedCoefficient hO hB)
    (ha₁.2.1.boundedCoefficient hO hB) u
  let r₂ := physicalResidual (ha₂.1.boundedCoefficient hO hB)
    (ha₂.2.1.boundedCoefficient hO hB) v
  have h₁ : |E₁ (physicalError ha₁ hO hB u).val v.val| ≤
      ((‖E₁‖+1)/c₁) * ‖r₁‖ * ‖v‖ := by
    calc
      _ ≤ ‖E₁‖ * ‖physicalError ha₁ hO hB u‖ * ‖v‖ := E₁.le_opNorm₂ _ _
      _ ≤ (‖E₁‖+1) * (‖r₁‖/c₁) * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (by linarith) (hb₁ u) (by positivity) (by positivity))
          (norm_nonneg v)
      _ = _ := by ring
  have h₂ : |E₂ u.val (physicalError ha₂ hO hB v).val| ≤
      ((‖E₂‖+1)/c₂) * ‖u‖ * ‖r₂‖ := by
    calc
      _ ≤ ‖E₂‖ * ‖u‖ * ‖physicalError ha₂ hO hB v‖ := E₂.le_opNorm₂ _ _
      _ ≤ ((‖E₂‖+1) * ‖u‖) * (‖r₂‖/c₂) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg u))
          (hb₂ v) (by positivity) (by positivity)
      _ = _ := by ring
  exact (abs_sub _ _).trans (add_le_add h₁ h₂)

end
/-! Complex boundary tests use only the real physical DN map. The following
is derived from four real identities; no equality of an augmented or assumed
complex DN map is introduced. -/
open Set
variable {Ω : Set X}

abbrev ComplexTrial (Ω : Set X) := H1Hilbert Ω × H1Hilbert Ω

def complexTrialSize (u : ComplexTrial Ω) : ℝ := ‖u.1‖+‖u.2‖

def complexTrialEnergy (l m : X → ℝ) (u v : ComplexTrial Ω) : ℂ :=
  (energy Ω l m (h1Equiv Ω u.1) (h1Equiv Ω v.1):ℂ)+
  (energy Ω l m (h1Equiv Ω u.2) (h1Equiv Ω v.2):ℂ)+
  Complex.I*((energy Ω l m (h1Equiv Ω u.2) (h1Equiv Ω v.1):ℂ)-
    (energy Ω l m (h1Equiv Ω u.1) (h1Equiv Ω v.2):ℂ))

def complexResidualSize {l m : X → ℝ} (hl : BoundedCoefficient Ω l)
    (hm : BoundedCoefficient Ω m) (u : ComplexTrial Ω) : ℝ :=
  ‖physicalResidual hl hm u.1‖+‖physicalResidual hl hm u.2‖

lemma norm_complex_four (a b c d : ℝ) :
    ‖(a:ℂ)+b+Complex.I*((c:ℂ)-d)‖≤|a|+|b|+|c|+|d| := by
  calc
    _ ≤ ‖(a:ℂ)+b‖+‖Complex.I*((c:ℂ)-d)‖ := norm_add_le _ _
    _ ≤ (‖(a:ℂ)‖+‖(b:ℂ)‖)+(‖(c:ℂ)‖+‖(d:ℂ)‖) := by
      rw [norm_mul,Complex.norm_I,one_mul]
      exact add_le_add (norm_add_le _ _) (norm_sub_le _ _)
    _ = _ := by simp only [Complex.norm_real,Real.norm_eq_abs]; ring

/-- Genuine sesquilinear mixed energy from equality of the real physical DN
maps. Each of the four trial components may have its own arbitrary trace. -/
theorem equal_DN_complex_mixed_bound {l₁ m₁ l₂ m₂ : X → ℝ}
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) :
    ∃ C₁ C₂ : ℝ, 0<C₁ ∧ 0<C₂ ∧ ∀ u v : ComplexTrial Ω,
      ‖complexTrialEnergy l₁ m₁ u v-complexTrialEnergy l₂ m₂ u v‖≤
      C₁*complexResidualSize (ha₁.1.boundedCoefficient hO hB)
        (ha₁.2.1.boundedCoefficient hO hB) u*complexTrialSize v+
      C₂*complexTrialSize u*complexResidualSize (ha₂.1.boundedCoefficient hO hB)
        (ha₂.2.1.boundedCoefficient hO hB) v := by
  obtain ⟨C₁,C₂,hC₁,hC₂,h⟩ := equal_DN_mixed_quasimode_bound ha₁ ha₂ hO hB hDN
  refine ⟨C₁,C₂,hC₁,hC₂,fun u v => ?_⟩
  let E (a b : H1Hilbert Ω) := energy Ω l₁ m₁ (h1Equiv Ω a) (h1Equiv Ω b)-
    energy Ω l₂ m₂ (h1Equiv Ω a) (h1Equiv Ω b)
  have he : complexTrialEnergy l₁ m₁ u v-complexTrialEnergy l₂ m₂ u v=
      (E u.1 v.1:ℂ)+E u.2 v.2+Complex.I*((E u.2 v.1:ℂ)-E u.1 v.2) := by
    unfold complexTrialEnergy E
    push_cast
    ring
  rw [he]
  refine (norm_complex_four _ _ _ _).trans ?_
  have hh := add_le_add
    (add_le_add (add_le_add (h u.1 v.1) (h u.2 v.2)) (h u.2 v.1)) (h u.1 v.2)
  change |E u.1 v.1|+|E u.2 v.2|+|E u.2 v.1|+|E u.1 v.2|≤_ at hh
  refine hh.trans_eq ?_
  unfold complexResidualSize complexTrialSize
  ring

end Elasticity
namespace Elasticity
/-! Genuine strong-to-variational residual estimate for boundary trial fields.
All pairings are on the actual physical H10 space, extended by its defining
density, not a separately assumed boundary test class. -/
open MeasureTheory Set
open scoped BigOperators
variable {Ω : Set X} {lam mu : X → ℝ}

def jetStress (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : JetH Ω) (i j : Fin 3) : ScalarL2 Ω :=
  (if i=j then hl.mulL (jetDiv Ω u) else 0) + (2 : ℝ) • hm.mulL (jetStrain Ω i j u)

lemma jetStrain_symm (u : JetH Ω) (i j : Fin 3) :
    jetStrain Ω i j u = jetStrain Ω j i u := by
  simp only [jetStrain, add_comm]

lemma jetEnergy_stress (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u v : JetH Ω) :
    jetEnergy hl hm u v = ∑ i, ∑ j, inner ℝ (jetStress hl hm u i j) (jetEntry Ω i j v) := by
  have hv (i j : Fin 3) : jetStrain Ω i j v =
      (1/2 : ℝ) • (jetEntry Ω i j v + jetEntry Ω j i v) := rfl
  have hs : (∑ i, ∑ j, inner ℝ (hm.mulL (jetStrain Ω i j u)) (jetEntry Ω j i v)) =
      ∑ i, ∑ j, inner ℝ (hm.mulL (jetStrain Ω i j u)) (jetEntry Ω i j v) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [jetStrain_symm u j i]
  have hd (i j : Fin 3) :
      inner ℝ (if i = j then hl.mulL (jetDiv Ω u) else 0) (jetEntry Ω i j v) =
        if i = j then inner ℝ (hl.mulL (jetDiv Ω u)) (jetEntry Ω i j v) else 0 := by
    by_cases h : i = j <;> simp [h]
  rw [jetEnergy_apply]
  simp only [hv, inner_smul_right, inner_add_right, mul_add, Finset.sum_add_distrib,
    ← Finset.mul_sum, hs]
  simp only [jetStress, inner_add_left, real_inner_smul_left,
    Finset.sum_add_distrib, ← Finset.mul_sum, hd,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [jetDiv, sum_apply, inner_sum]
  ring

/-- Smooth scalar integration by parts with a compactly supported interior test. -/
lemma boundary_smooth_ibp {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ) ⊆ Ω) (j : Fin 3) :
    (∫ x, f x*ElasticityKorn.d (coordVector j) g x ∂(volume.restrict Ω)) =
    -(∫ x, fderiv ℝ f x (coordVector j)*g x ∂(volume.restrict Ω)) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (g : X → ℝ) := g.smooth _
  have hd : Continuous (fun x => fderiv ℝ f x (coordVector j)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgd : Continuous (fun x => fderiv ℝ (g : X → ℝ) x (coordVector j)) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hz := image_eq_zero_of_notMem_tsupport (f := (ElasticityKorn.d (coordVector j) g : X → ℝ))
      (fun ht => hx (hs ((tsupport_fderiv_apply_subset ℝ (coordVector j)) ht)))
    rw [hz,mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (f := (g : X → ℝ)) (fun ht => hx (hs ht)),mul_zero])]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hd.mul hg.continuous).integrable_of_hasCompactSupport (hc.mul_left))
    ((hf.continuous.mul hgd).integrable_of_hasCompactSupport ((hc.fderiv_apply ℝ _).mul_left))
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hc.mul_left))
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x)

lemma boundary_L2_schwartz_pair (f : ScalarL2 Ω) (g : SchwartzMap X ℝ) :
    inner ℝ f (schwartzR Ω g) = ∫ x, f x*g x ∂(volume.restrict Ω) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp 2 (volume.restrict Ω)] with x hx
  change inner ℝ (f x) (g.toLp 2 (volume.restrict Ω) x)=_
  rw [hx, real_inner_comm]
  rfl

/-- The actual L2 force pairing, with no regularity required of the test. -/
def boundaryForcePair (F : Fin 3 → ScalarL2 Ω) : JetH Ω →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ (F i)).comp (jetScalar Ω none i)

lemma boundaryForcePair_apply (F : Fin 3 → ScalarL2 Ω) (v : JetH Ω) :
    boundaryForcePair F v = ∑ i, inner ℝ (F i) (jetScalar Ω none i v) := by
  simp [boundaryForcePair, sum_apply]

/-- Smooth stresses with their literal divergence give exactly the physical
variational residual. The same statement permits local coefficient extensions:
only equality to the actual stress on Ω is required. -/
theorem physicalResidual_of_smooth_stress
    (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) (s : Fin 3 → Fin 3 → X → ℝ)
    (hs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (s i j))
    (hes : ∀ i j, jetStress hl hm u.val i j =ᵐ[volume.restrict Ω] s i j)
    (hd : ∀ i j, MemLp (fun x => fderiv ℝ (s i j) x (coordVector j)) 2 (volume.restrict Ω)) :
    physicalResidual hl hm u =
      -(boundaryForcePair (fun i => ∑ j, (hd i j).toLp _)).comp (H10Hilbert Ω).subtypeL := by
  apply ContinuousLinearMap.ext
  intro v
  change jetEnergy hl hm u.val v.val =
    -boundaryForcePair (fun i => ∑ j, (hd i j).toLp _) v.val
  apply h10_induction_closed (P := fun w => jetEnergy hl hm u.val w =
    -boundaryForcePair (fun i => ∑ j, (hd i j).toLp _) w)
  · exact isClosed_eq (jetEnergy hl hm u.val).continuous
      (boundaryForcePair (fun i => ∑ j, (hd i j).toLp _)).continuous.neg
  · intro w hw
    obtain ⟨G, hG, h0, h1⟩ := jet_test_representation w hw
    rw [jetEnergy_stress, boundaryForcePair_apply]
    simp only [h0, h1, sum_inner, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [boundary_L2_schwartz_pair, boundary_L2_schwartz_pair]
    have hab := boundary_smooth_ibp (hs i j) (G i)
      (Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport _, hB.subset (hG i)⟩) (hG i) j
    calc
      _ = ∫ x, s i j x * ElasticityKorn.d (coordVector j) (G i) x ∂(volume.restrict Ω) := by
        apply integral_congr_ae
        filter_upwards [hes i j] with x hx
        rw [hx]
        rfl
      _ = _ := hab
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [(hd i j).coeFn_toLp] with x hx
        rw [hx]

lemma jetScalar_value_norm_le (v : JetH Ω) (i : Fin 3) :
    ‖jetScalar Ω none i v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [jet_norm_sq]
  have h1 : ‖jetScalar Ω none i v‖ ^ 2 ≤ jetValueSq Ω v := by
    apply Finset.single_le_sum (f := fun j => ‖jetScalar Ω none j v‖ ^ 2)
    · intro j _; exact sq_nonneg _
    · exact Finset.mem_univ i
  have h2 : 0 ≤ jetGradSq Ω v :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  linarith

lemma boundaryForcePair_norm_le (F : Fin 3 → ScalarL2 Ω) :
    ‖boundaryForcePair F‖ ≤ ∑ i, ‖F i‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  rw [boundaryForcePair_apply]
  calc
    ‖∑ i, inner ℝ (F i) (jetScalar Ω none i v)‖ ≤
        ∑ i, ‖inner ℝ (F i) (jetScalar Ω none i v)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖F i‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (jetScalar_value_norm_le v i) (norm_nonneg _))
    _ = _ := by rw [Finset.sum_mul]

/-- The actual dual residual obeys an L2 strong-residual bound; no boundary
regularity of the test space or unproved trace density is used. -/
theorem physicalResidual_norm_le_of_smooth_stress
    (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) (s : Fin 3 → Fin 3 → X → ℝ)
    (hs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (s i j))
    (hes : ∀ i j, jetStress hl hm u.val i j =ᵐ[volume.restrict Ω] s i j)
    (hd : ∀ i j, MemLp (fun x => fderiv ℝ (s i j) x (coordVector j)) 2 (volume.restrict Ω)) :
    ‖physicalResidual hl hm u‖ ≤ ∑ i, ‖∑ j, (hd i j).toLp _‖ := by
  rw [physicalResidual_of_smooth_stress hl hm hB u s hs hes hd]
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  change ‖-boundaryForcePair (fun i => ∑ j, (hd i j).toLp _) v.val‖ ≤ _
  rw [norm_neg]
  exact ((boundaryForcePair (fun i => ∑ j, (hd i j).toLp _)).le_opNorm v.val).trans
    (mul_le_mul_of_nonneg_right (boundaryForcePair_norm_le _) (norm_nonneg _))

end Elasticity
namespace Elasticity
/-! Actual smooth physical displacements give the exact H1 trial objects used
 by the physical DN map. This is a constructor, not a trace assumption. -/
open Set MeasureTheory
open scoped BigOperators
variable {Ω : Set X}

def smoothTrial (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) : H1Hilbert Ω :=
  (h1Equiv Ω).symm ⟨(hf.toLp f,fun j => (hd j).toLp _),
    subset_closure ⟨f,hf,hd,hs,rfl,rfl⟩⟩

@[simp] lemma smoothTrial_value (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) :
    (smoothTrial f hs hf hd).val none=hf.toLp f := rfl

@[simp] lemma smoothTrial_deriv (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) (j : Fin 3) :
    (smoothTrial f hs hf hd).val (some j)=(hd j).toLp _ := rfl

lemma smoothTrial_entry_ae (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) (i j : Fin 3) :
    jetEntry Ω i j (smoothTrial f hs hf hd).val =ᵐ[volume.restrict Ω]
      fun x => (coordDeriv f j x) i := by
  filter_upwards [jetEntry_ae (smoothTrial f hs hf hd).val i j,(hd j).coeFn_toLp] with x hx hy
  exact hx.trans (congrArg (fun v : V => v i) hy)

lemma smoothTrial_stress_ae {l m : X → ℝ} (hl : BoundedCoefficient Ω l) (hm : BoundedCoefficient Ω m)
    (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) (i j : Fin 3) :
    jetStress hl hm (smoothTrial f hs hf hd).val i j =ᵐ[volume.restrict Ω]
      fun x => (if i=j then l x*(∑ k, (coordDeriv f k x) k) else 0)+
        m x*((coordDeriv f j x) i+(coordDeriv f i x) j) := by
  let u := (smoothTrial f hs hf hd).val
  have hda : ∀ᵐ x ∂(volume.restrict Ω),∀ k, u (some k) x=coordDeriv f k x :=
    Filter.eventually_all.mpr (fun k => (hd k).coeFn_toLp)
  have hzero : (0 : ScalarL2 Ω) =ᵐ[volume.restrict Ω] fun _ => 0 := Lp.coeFn_zero _ _ _
  by_cases hij : i=j
  · filter_upwards [Lp.coeFn_add (hl.mulL (jetDiv Ω u)) ((2:ℝ) • hm.mulL (jetStrain Ω i j u)),
        Lp.coeFn_smul (2:ℝ) (hm.mulL (jetStrain Ω i j u)), hl.mulL_ae (jetDiv Ω u),
        hm.mulL_ae (jetStrain Ω i j u), jetDiv_ae u,jetStrain_ae u i j,hda] with x h0 h1 h2 h3 h4 h5 h6
    change ((if i=j then hl.mulL (jetDiv Ω u) else 0)+(2:ℝ) • hm.mulL (jetStrain Ω i j u)) x=_
    simp only [hij,ite_true] at *
    rw [h0]
    simp only [Pi.add_apply]
    rw [h1]
    simp only [Pi.smul_apply,smul_eq_mul,h2,h3,h4,h5,h6]
    ring
  · filter_upwards [Lp.coeFn_add (0 : ScalarL2 Ω) ((2:ℝ) • hm.mulL (jetStrain Ω i j u)),
        Lp.coeFn_smul (2:ℝ) (hm.mulL (jetStrain Ω i j u)),hzero,
        hm.mulL_ae (jetStrain Ω i j u),jetStrain_ae u i j,hda] with x h0 h1 hz h3 h5 h6
    change ((if i=j then hl.mulL (jetDiv Ω u) else 0)+(2:ℝ) • hm.mulL (jetStrain Ω i j u)) x=_
    simp only [hij,ite_false]
    rw [h0]
    simp only [Pi.add_apply]
    rw [h1]
    simp only [Pi.smul_apply,smul_eq_mul,hz,h3,h5,h6]
    ring

lemma smooth_compact_coordDeriv {f : X → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (coordDeriv f j) ∧ HasCompactSupport (coordDeriv f j) := by
  exact ⟨(hf.fderiv_right (by simp)).clm_apply contDiff_const,hc.fderiv_apply ℝ _⟩

lemma smooth_compact_memLp {f : X → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    MemLp f 2 (volume.restrict Ω) ∧ ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω) := by
  refine ⟨(hf.continuous.memLp_of_hasCompactSupport hc).restrict _,fun j => ?_⟩
  obtain ⟨hs,hc'⟩ := smooth_compact_coordDeriv hf hc j
  exact (hs.continuous.memLp_of_hasCompactSupport hc').restrict _

end Elasticity
namespace Elasticity
/-! Exact agreement of the variational trial energy with classical smooth
physical fields and their literal derivatives. -/
open Set MeasureTheory
open scoped BigOperators
variable {Ω : Set X}

lemma smoothTrial_gradient_ae (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) :
    gradient (h1Equiv Ω (smoothTrial f hs hf hd)).val =ᵐ[volume.restrict Ω]
      (fun x j => coordDeriv f j x) := by
  have hh := Filter.eventually_all.mpr (fun j => (hd j).coeFn_toLp)
  filter_upwards [hh] with x hx
  exact funext hx

lemma smoothTrial_energy (l m : X → ℝ) (f g : X → V)
    (hsf : ContDiff ℝ (⊤ : ℕ∞) f) (hsg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hf : MemLp f 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (hdf : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω))
    (hdg : ∀ j, MemLp (coordDeriv g j) 2 (volume.restrict Ω)) :
    energy Ω l m (h1Equiv Ω (smoothTrial f hsf hf hdf)) (h1Equiv Ω (smoothTrial g hsg hg hdg))=
      ∫ x in Ω, elasticDensity (l x) (m x) (fun j => coordDeriv f j x) (fun j => coordDeriv g j x) := by
  rw [energy_eq_ambient]
  apply integral_congr_ae
  filter_upwards [smoothTrial_gradient_ae f hsf hf hdf,smoothTrial_gradient_ae g hsg hg hdg] with x h1 h2
  exact congrArg₂ (elasticDensity (l x) (m x)) h1 h2

/-- Projection of a complex physical displacement to an actual real trial
field. The map `w` will be real or imaginary part. -/
def realField (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ) (x : X) : V :=
  WithLp.toLp 2 (fun i => w (u i x))

lemma smooth_realField (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ)
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) : ContDiff ℝ (⊤ : ℕ∞) (realField w u) := by
  exact PiLp.contDiff_toLp.comp (contDiff_pi.mpr (fun i => w.contDiff.comp (hu i)))

lemma realField_derivative (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ)
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) (i j : Fin 3) (x : X) :
    coordDeriv (realField w u) j x i=
      w (ElasticityBoundaryChainRule.dd (u i) (coordVector j) x) := by
  have h1 := (EuclideanSpace.proj i : V →L[ℝ] ℝ).hasFDerivAt.comp x
    (((smooth_realField w u hu).differentiable (by simp)) x).hasFDerivAt
  have h2 := w.hasFDerivAt.comp x (((hu i).differentiable (by simp)) x).hasFDerivAt
  have he : (EuclideanSpace.proj i : V →L[ℝ] ℝ) ∘ realField w u=w ∘ u i := rfl
  rw [he] at h1
  have hh := congrArg (fun A : X →L[ℝ] ℝ => A (coordVector j)) (h1.unique h2)
  exact hh

lemma realField_support (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ) {K : Set X}
    (hu : ∀ i, Function.support (u i)⊆K) : Function.support (realField w u)⊆K := by
  intro x hx
  by_contra hn
  apply hx
  ext i
  have hz : u i x=0 := Function.notMem_support.mp (fun h => hn (hu i h))
  simp [realField,hz]

lemma compact_realField (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ) {K : Set X}
    (hK : IsCompact K) (hu : ∀ i, Function.support (u i)⊆K) : HasCompactSupport (realField w u) := by
  exact hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (realField_support w u hu) hK.isClosed)

end Elasticity
namespace ElasticityBoundaryProjectedStress
/-! The complex quasimode's real and imaginary stresses are the literal real
physical stresses used by the DN map. -/
open Set MeasureTheory
open scoped BigOperators
open Elasticity ElasticityBoundaryChainRule ElasticityBoundaryPhysicalStrong
  ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalTransfer
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

def realStress (w : ℂ →L[ℝ] ℝ) (l m : X → ℝ) (u : I → X → ℂ) (i j : I) : X → ℝ :=
  fun x => w (stress basis (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) u i j x)

lemma smooth_stress {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → X → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i j : I) :
    ContDiff ℝ (⊤ : ℕ∞) (stress basis l m u i j) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x =>
    (if i=j then l x*divergence basis u x else 0)+
      m x*(dd (u i) (basis j) x+dd (u j) (basis i) x))
  by_cases hij : i=j
  · simp only [hij,ite_true]
    exact (hl.mul (smooth_divergence basis u hu)).add
      (hm.mul ((smooth_dd (hu j) _).add (smooth_dd (hu j) _)))
  · simp only [hij,ite_false,zero_add]
    exact hm.mul ((smooth_dd (hu i) _).add (smooth_dd (hu j) _))

lemma compact_stress (l m : X → ℂ) (u : I → X → ℂ)
    (hu : ∀ j, HasCompactSupport (u j)) (i j : I) :
    HasCompactSupport (stress basis l m u i j) := by
  have hd : HasCompactSupport (divergence basis u) := by
    change HasCompactSupport (fun x => ∑ k, dd (u k) (basis k) x)
    simp only [Fin.sum_univ_three]
    exact (((hu 0).fderiv_apply ℝ _).add ((hu 1).fderiv_apply ℝ _)).add ((hu 2).fderiv_apply ℝ _)
  have hs : HasCompactSupport (fun x => m x*(dd (u i) (basis j) x+dd (u j) (basis i) x)) :=
    ((hu i).fderiv_apply ℝ _ |>.add ((hu j).fderiv_apply ℝ _)).mul_left
  change HasCompactSupport (fun x => (if i=j then l x*divergence basis u x else 0)+
    m x*(dd (u i) (basis j) x+dd (u j) (basis i) x))
  by_cases hij : i=j
  · simp only [hij,ite_true]
    have hl : HasCompactSupport (fun x => l x*divergence basis u x) := hd.mul_left
    convert hl.add hs using 1
    subst i
    rfl
  · simpa only [hij,ite_false,zero_add] using hs

lemma project_mul (w : ℂ →L[ℝ] ℝ) (c : ℝ) (z : ℂ) : w ((c:ℂ)*z)=c*w z := by
  rw [← Complex.real_smul,map_smul,smul_eq_mul]

lemma realStress_eq (w : ℂ →L[ℝ] ℝ) (l m : X → ℝ) (u : I → X → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i j : I) (x : X) :
    realStress w l m u i j x=
      (if i=j then l x*(∑ k, coordDeriv (realField w u) k x k) else 0)+
        m x*(coordDeriv (realField w u) j x i+coordDeriv (realField w u) i x j) := by
  simp only [realStress,stress,map_add,project_mul,divergence,
    realField_derivative w u hu]
  by_cases hij : i=j <;> simp only [hij,ite_true,ite_false,map_zero,project_mul,map_sum]
  all_goals rfl

lemma smooth_realStress (w : ℂ →L[ℝ] ℝ) {l m : X → ℝ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → X → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i j : I) :
    ContDiff ℝ (⊤ : ℕ∞) (realStress w l m u i j) :=
  w.contDiff.comp (smooth_stress (Complex.ofRealCLM.contDiff.comp hl)
    (Complex.ofRealCLM.contDiff.comp hm) u hu i j)

lemma compact_realStress (w : ℂ →L[ℝ] ℝ) (l m : X → ℝ) (u : I → X → ℂ)
    (hu : ∀ j, HasCompactSupport (u j)) (i j : I) :
    HasCompactSupport (realStress w l m u i j) :=
  (compact_stress _ _ u hu i j).comp_left (g := w) (map_zero w)

lemma derivative_project {f : X → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (w : ℂ →L[ℝ] ℝ) (v x : X) :
    fderiv ℝ (fun z => w (f z)) x v=w (dd f v x) := by
  rw [show (fun z => w (f z))=w ∘ f from rfl,
    (w.hasFDerivAt.comp x (hf.differentiable (by simp) x).hasFDerivAt).fderiv]
  rfl

lemma realStress_divergence (w : ℂ →L[ℝ] ℝ) {l m : X → ℝ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → X → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) (x : X) :
    (∑ j, fderiv ℝ (realStress w l m u i j) x (coordVector j))=
      w (force (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) u i x) := by
  have hlc := Complex.ofRealCLM.contDiff.comp hl
  have hmc := Complex.ofRealCLM.contDiff.comp hm
  have he (j : I) : fderiv ℝ (realStress w l m u i j) x (coordVector j)=
      w (dd (stress basis (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) u i j) (basis j) x) :=
    derivative_project (smooth_stress hlc hmc u hu i j) w _ x
  simp only [he]
  rw [← map_sum]
  exact congrArg w (stress_divergence basis hlc hmc u hu i x)

end ElasticityBoundaryProjectedStress
/-! Squared physical H10-dual residual estimates in terms of the genuine
strong-force mass. This is the bridge from chart quasimodes to the DN map. -/
section
open Set MeasureTheory
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}

lemma L2_norm_sq_mass (v : ScalarL2 Ω) : ‖v‖^2=∫ x in Ω, ‖v x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma sum_toLp_norm_sq (f : Fin 3 → X → ℝ) (hf : ∀ j, MemLp (f j) 2 (volume.restrict Ω)) :
    ‖∑ j, (hf j).toLp (f j)‖^2=∫ x in Ω, ‖∑ j, f j x‖^2 := by
  rw [L2_norm_sq_mass]
  apply integral_congr_ae
  have hall := Filter.eventually_all.mpr (fun j => (hf j).coeFn_toLp)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => (hf j).toLp (f j)),hall] with x hx hy
  simp only [hx,Finset.sum_apply,hy]

lemma sum_three_sq (v : Fin 3 → ℝ) : (∑ i, v i)^2≤3*∑ i, (v i)^2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (v 0-v 1),sq_nonneg (v 0-v 2),sq_nonneg (v 1-v 2)]

lemma physicalResidual_sq_mass {l m : X → ℝ}
    (hl : BoundedCoefficient Ω l) (hm : BoundedCoefficient Ω m)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) (s : Fin 3 → Fin 3 → X → ℝ)
    (hs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (s i j))
    (hes : ∀ i j, jetStress hl hm u.val i j =ᵐ[volume.restrict Ω] s i j)
    (hd : ∀ i j, MemLp (fun x => fderiv ℝ (s i j) x (coordVector j)) 2 (volume.restrict Ω)) :
    ‖physicalResidual hl hm u‖^2≤3*∑ i,
      (∫ x in Ω, ‖∑ j, fderiv ℝ (s i j) x (coordVector j)‖^2) := by
  have h := physicalResidual_norm_le_of_smooth_stress hl hm hB u s hs hes hd
  have h0 : 0≤∑ i, ‖∑ j, (hd i j).toLp _‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  apply ((sq_le_sq₀ (norm_nonneg (physicalResidual hl hm u)) h0).mpr h).trans
  have hsq := sum_three_sq (fun i => ‖∑ j, (hd i j).toLp _‖)
  simpa only [sum_toLp_norm_sq] using hsq

end Elasticity
namespace ElasticityBoundaryResidualMass
open Elasticity ElasticityBoundaryProjectedStress ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalStrong ElasticityBoundaryChainRule
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

lemma projected_force_mass_le {Ω : Set X} (w : ℂ →L[ℝ] ℝ) {F : X → ℂ}
    (hF : MemLp F 2 (volume.restrict Ω)) :
    (∫ x in Ω, ‖w (F x)‖^2)≤‖w‖^2*(∫ x in Ω, ‖F x‖^2) := by
  have hInt := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hwF : MemLp (fun x => w (F x)) 2 (volume.restrict Ω) := hF.continuousLinearMap_comp w
  rw [← integral_const_mul]
  apply integral_mono ((memLp_two_iff_integrable_sq_norm hwF.aestronglyMeasurable).mp hwF)
    (hInt.const_mul _)
  intro x
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (w.le_opNorm (F x)) 2

/-- Each real projection is an actual finite-energy smooth trial and its
physical variational residual is controlled by the literal complex force. -/
theorem projected_trial_residual {Ω : Set X} (w : ℂ →L[ℝ] ℝ) {l m : X → ℝ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hbl : BoundedCoefficient Ω l) (hbm : BoundedCoefficient Ω m)
    (hB : Bornology.IsBounded Ω)
    (u : I → X → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (hcu : ∀ j, HasCompactSupport (u j))
    (hf : MemLp (realField w u) 2 (volume.restrict Ω))
    (hdf : ∀ j, MemLp (coordDeriv (realField w u) j) 2 (volume.restrict Ω))
    (hF : ∀ i, MemLp (force (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) u i) 2 (volume.restrict Ω)) :
    ‖physicalResidual hbl hbm (smoothTrial (realField w u) (smooth_realField w u hu) hf hdf)‖^2≤
      3*‖w‖^2*∑ i, (∫ x in Ω, ‖force (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) u i x‖^2) := by
  have hs := smooth_realStress w hl hm u hu
  have hc := compact_realStress w l m u hcu
  have hd (i j : I) : MemLp (fun x => fderiv ℝ (realStress w l m u i j) x (coordVector j)) 2
      (volume.restrict Ω) :=
    (((hs i j).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hc i j).fderiv_apply ℝ _) |>.restrict _
  have hes (i j : I) : jetStress hbl hbm
      (smoothTrial (realField w u) (smooth_realField w u hu) hf hdf).val i j =ᵐ[volume.restrict Ω]
      realStress w l m u i j := by
    filter_upwards [smoothTrial_stress_ae hbl hbm (realField w u) (smooth_realField w u hu) hf hdf i j]
      with x hx
    exact hx.trans (realStress_eq w l m u hu i j x).symm
  apply (physicalResidual_sq_mass hbl hbm hB _ (realStress w l m u) hs hes hd).trans
  simp only [realStress_divergence w hl hm u hu]
  calc
    _ ≤ 3*∑ i, (‖w‖^2*(∫ x in Ω, ‖force (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) u i x‖^2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => projected_force_mass_le w (hF i))) (by norm_num)
    _ = _ := by rw [← Finset.mul_sum,mul_assoc]

end ElasticityBoundaryResidualMass

end
/-! Exact H1 masses of the physical complex trial projections, and bounds by
literal scalar component derivatives. -/
section
open Set MeasureTheory
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}

lemma vector_toLp_norm_sq (f : X → V) (hf : MemLp f 2 (volume.restrict Ω)) :
    ‖hf.toLp f‖^2=∑ i, (∫ x in Ω, ‖f x i‖^2) := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  have hi (i : Fin 3) : IntegrableOn (fun x => ‖f x i‖^2) Ω := by
    have hh := hf.continuousLinearMap_comp (EuclideanSpace.proj i : V →L[ℝ] ℝ)
    exact (memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mp hh
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx,real_inner_self_eq_norm_sq,PiLp.norm_sq_eq_of_L2]

lemma smoothTrial_norm_sq (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) :
    ‖smoothTrial f hs hf hd‖^2=(∑ i, (∫ x in Ω, ‖f x i‖^2))+
      ∑ j, ∑ i, (∫ x in Ω, ‖coordDeriv f j x i‖^2) := by
  change ‖(smoothTrial f hs hf hd).val‖^2=_
  rw [PiLp.norm_sq_eq_of_L2,Fintype.sum_option]
  simp only [smoothTrial_value,smoothTrial_deriv,vector_toLp_norm_sq]

end Elasticity
namespace ElasticityBoundaryTrialMass
open Elasticity ElasticityBoundaryResidualMass ElasticityBoundaryChainRule
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

lemma projected_trial_mass {Ω : Set X} (w : ℂ →L[ℝ] ℝ)
    (u : I → X → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (hm : ∀ j, MemLp (u j) 2 (volume.restrict Ω))
    (hdm : ∀ i j, MemLp (dd (u i) (coordVector j)) 2 (volume.restrict Ω))
    (hf : MemLp (realField w u) 2 (volume.restrict Ω))
    (hdf : ∀ j, MemLp (coordDeriv (realField w u) j) 2 (volume.restrict Ω)) :
    ‖smoothTrial (realField w u) (smooth_realField w u hu) hf hdf‖^2≤
      ‖w‖^2*((∑ i, (∫ x in Ω, ‖u i x‖^2))+
        ∑ j, ∑ i, (∫ x in Ω, ‖dd (u i) (coordVector j) x‖^2)) := by
  rw [smoothTrial_norm_sq,mul_add]
  simp only [Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    exact projected_force_mass_le w (hm i)
  · apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro i _
    simp only [realField_derivative w u hu]
    exact projected_force_mass_le w (hdm i j)

end ElasticityBoundaryTrialMass

end
namespace Elasticity
/-! Complex geometric displacements as genuine pairs of real H1 trials. -/
open Set MeasureTheory
open scoped BigOperators
variable {Ω : Set X}

lemma classicalDensity_integrable {l m : X → ℝ} (hl : BoundedCoefficient Ω l)
    (hm : BoundedCoefficient Ω m) (P Q : X → Fin 3 → V)
    (hP : ∀ j, MemLp (fun x => P x j) 2 (volume.restrict Ω))
    (hQ : ∀ j, MemLp (fun x => Q x j) 2 (volume.restrict Ω)) :
    IntegrableOn (fun x => elasticDensity (l x) (m x) (P x) (Q x)) Ω := by
  have hp (i j : Fin 3) : MemLp (fun x => P x j i) 2 (volume.restrict Ω) := (hP j).continuousLinearMap_comp (EuclideanSpace.proj i : V →L[ℝ] ℝ)
  have hq (i j : Fin 3) : MemLp (fun x => Q x j i) 2 (volume.restrict Ω) := (hQ j).continuousLinearMap_comp (EuclideanSpace.proj i : V →L[ℝ] ℝ)
  have hdP : MemLp (fun x => ∑ i, P x i i) 2 (volume.restrict Ω) :=
    memLp_finsetSum _ (fun i _ => hp i i)
  have hdQ : MemLp (fun x => ∑ i, Q x i i) 2 (volume.restrict Ω) :=
    memLp_finsetSum _ (fun i _ => hq i i)
  have hsP (i j : Fin 3) : MemLp (fun x => (P x j i+P x i j)/2) 2 (volume.restrict Ω) := by
    simpa only [div_eq_mul_inv,Pi.add_apply] using ((hp i j).add (hp j i)).mul_const (2:ℝ)⁻¹
  have hsQ (i j : Fin 3) : MemLp (fun x => (Q x j i+Q x i j)/2) 2 (volume.restrict Ω) := by
    simpa only [div_eq_mul_inv,Pi.add_apply] using ((hq i j).add (hq j i)).mul_const (2:ℝ)⁻¹
  have hL := (hl.mul_memLp_fun hdP).integrable_mul hdQ
  have hS (i j) := (hm.mul_memLp_fun (hsP i j)).integrable_mul (hsQ i j)
  have hsum := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hS i j))
  apply (hL.add (hsum.const_mul 2)).congr
  exact Filter.Eventually.of_forall (fun x => by
    simp only [elasticDensity,Pi.mul_apply,Pi.add_apply,Finset.mul_sum,mul_assoc])

def projectedTrial (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) {K : Set X} (hK : IsCompact K)
    (hus : ∀ j, Function.support (u j)⊆K) : H1Hilbert Ω :=
  smoothTrial (realField w u) (smooth_realField w u hu)
    (smooth_compact_memLp (smooth_realField w u hu) (compact_realField w u hK hus)).1
    (smooth_compact_memLp (smooth_realField w u hu) (compact_realField w u hK hus)).2

def complexFieldTrial (u : Fin 3 → X → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) {K : Set X} (hK : IsCompact K)
    (hus : ∀ j, Function.support (u j)⊆K) : ComplexTrial Ω :=
  (projectedTrial Complex.reCLM u hu hK hus,projectedTrial Complex.imCLM u hu hK hus)

def realMatrix (w : ℂ →L[ℝ] ℝ) (P : Fin 3 → Fin 3 → ℂ) : Fin 3 → V :=
  fun j => WithLp.toLp 2 (fun i => w (P i j))

def complexDensity (l m : ℝ) (P Q : Fin 3 → Fin 3 → ℂ) : ℂ :=
  (elasticDensity l m (realMatrix Complex.reCLM P) (realMatrix Complex.reCLM Q):ℂ)+
  (elasticDensity l m (realMatrix Complex.imCLM P) (realMatrix Complex.imCLM Q):ℂ)+
  Complex.I*((elasticDensity l m (realMatrix Complex.imCLM P) (realMatrix Complex.reCLM Q):ℂ)-
    (elasticDensity l m (realMatrix Complex.reCLM P) (realMatrix Complex.imCLM Q):ℂ))

def fieldGradient (u : Fin 3 → X → ℂ) (x : X) (i j : Fin 3) : ℂ :=
  ElasticityBoundaryChainRule.dd (u i) (coordVector j) x

lemma realMatrix_gradient (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (x : X) :
    realMatrix w (fieldGradient u x)=(fun j => coordDeriv (realField w u) j x) := by
  funext j
  ext i
  exact (realField_derivative w u hu i j x).symm

lemma complexFieldTrial_energy {l m : X → ℝ} (hl : BoundedCoefficient Ω l)
    (hm : BoundedCoefficient Ω m) (u v : Fin 3 → X → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j))
    {K L : Set X} (hK : IsCompact K) (hL : IsCompact L)
    (hus : ∀ j, Function.support (u j)⊆K) (hvs : ∀ j, Function.support (v j)⊆L) :
    complexTrialEnergy (Ω := Ω) l m (complexFieldTrial u hu hK hus) (complexFieldTrial v hv hL hvs)=
      ∫ x in Ω, complexDensity (l x) (m x) (fieldGradient u x) (fieldGradient v x) := by
  have hi (w z : ℂ →L[ℝ] ℝ) : Integrable (fun x =>
      elasticDensity (l x) (m x) (realMatrix w (fieldGradient u x))
        (realMatrix z (fieldGradient v x))) (volume.restrict Ω) := by
    simp only [realMatrix_gradient w u hu,realMatrix_gradient z v hv]
    exact classicalDensity_integrable hl hm _ _
      (smooth_compact_memLp (smooth_realField w u hu) (compact_realField w u hK hus)).2
      (smooth_compact_memLp (smooth_realField z v hv) (compact_realField z v hL hvs)).2
  have he (w z : ℂ →L[ℝ] ℝ) := smoothTrial_energy (Ω := Ω) l m (realField w u) (realField z v)
    (smooth_realField w u hu) (smooth_realField z v hv)
    (smooth_compact_memLp (smooth_realField w u hu) (compact_realField w u hK hus)).1
    (smooth_compact_memLp (smooth_realField z v hv) (compact_realField z v hL hvs)).1
    (smooth_compact_memLp (smooth_realField w u hu) (compact_realField w u hK hus)).2
    (smooth_compact_memLp (smooth_realField z v hv) (compact_realField z v hL hvs)).2
  simp only [complexTrialEnergy,complexFieldTrial,projectedTrial,he,complexDensity]
  simp only [← realMatrix_gradient _ u hu,← realMatrix_gradient _ v hv]
  rw [integral_add ((hi _ _).ofReal.add (hi _ _).ofReal)
    (((hi _ _).ofReal.sub (hi _ _).ofReal).const_mul _),
    integral_add (hi _ _).ofReal (hi _ _).ofReal,integral_const_mul,
    integral_sub (hi _ _).ofReal (hi _ _).ofReal]
  simp only [integral_complex_ofReal]

end Elasticity
namespace ElasticityBoundaryPacket
/-! Actual smooth compact physical fields selected from the curved boundary
parametrix, on an arbitrary honest smooth domain. -/
open Set MeasureTheory Filter
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryCutoffLayer ElasticityBoundaryCutoffParametrix ElasticityBoundaryPacketMass
  ElasticityBoundaryGradientMass ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalMass
  ElasticityBoundaryChainRule ElasticityBoundaryChartOperator ElasticityBoundaryStrongLayer
  ElasticityBoundaryLocalParametrix ElasticityBoundaryMVNormal ElasticityBoundaryActualTower
  ElasticityBoundaryProfileBounds ElasticityBoundaryLayerOperator

variable {Ω : Set X} {x : X}

def Setup.field (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) : I → X → ℂ :=
  transferred s.e s.η s.Q (cutoffLayer s.cutoff q δ)

lemma Setup.cutoff_layer_support (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) (j : I) :
    Function.support (fun y : X => cutoffLayer s.cutoff q δ j y.ofLp)⊆s.K := by
  intro y hy
  apply s.cutoff_support
  intro hz
  exact hy (by simp [cutoffLayer,hz])

lemma Setup.field_smooth (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (s.field q δ i) :=
  smooth_transferred s.e s.inverse_smooth s.η_smooth s.η_support s.Q _
    (smooth_cutoffLayer s.cutoff_smooth q δ) i

lemma Setup.field_support (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) (i : I) :
    Function.support (s.field q δ i)⊆s.e '' s.K :=
  support_transferred s.e s.η_support s.Q _ (s.cutoff_layer_support q δ) i

lemma Setup.image_compact (s : Setup Ω x) : IsCompact (s.e '' s.K) :=
  compact_image s.e s.compact s.source

lemma Setup.field_compact (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) (i : I) :
    HasCompactSupport (s.field q δ i) :=
  s.image_compact.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (s.field_support q δ i) s.image_compact.isClosed)

lemma Setup.field_value_mass (s : Setup Ω x) (hΩ : MeasurableSet Ω) (q : Polynomial W) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 → ∀ i,
      (∫ z in Ω, ‖s.field q δ i z‖^2)≤C := by
  obtain ⟨A,hA,hbound⟩ := transferred_value_mass s.e s.smooth s.compact s.source
    hΩ measurable_H s.inside s.η_support s.η_one s.Q s.Φ s.Φ_smooth s.Φ_germ
  choose B hB hBbound using cutoff_value_bound s.cutoff_smooth s.cutoff_compact q
  refine ⟨A*∑ j, B j,mul_nonneg hA (Finset.sum_nonneg (fun j _ => hB j)),fun δ hδ hδ1 i => ?_⟩
  apply (hbound _ (smooth_cutoffLayer s.cutoff_smooth q δ) (s.cutoff_layer_support q δ) i).trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply Finset.sum_le_sum
  intro j _
  rw [integral_ofLp (fun y => ‖cutoffLayer s.cutoff q δ j y‖^2)]
  exact ((hBbound j δ hδ hδ1).2).trans (mul_le_of_le_one_right (hB j) (pow_le_one₀ hδ.le hδ1))

lemma Setup.field_gradient_mass (s : Setup Ω x) (hΩ : MeasurableSet Ω) (q : Polynomial W) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 → ∀ i d,
      (∫ z in Ω, ‖dd (s.field q δ i) (basis d) z‖^2)≤C := by
  obtain ⟨A,hA,hbound⟩ := transferred_gradient_mass s.e s.smooth s.compact s.source
    hΩ measurable_H s.inside s.η_support s.η_one s.Q s.Φ s.Ψ s.Φ_smooth s.Ψ_smooth s.Φ_germ s.Ψ_germ
  choose B hB hBbound using cutoff_gradient_bound s.cutoff_smooth s.cutoff_compact q
  refine ⟨A*∑ j, ∑ α, B j α,mul_nonneg hA
    (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun α _ => hB j α))),fun δ hδ hδ1 i d => ?_⟩
  apply (hbound _ (smooth_cutoffLayer s.cutoff_smooth q δ) (s.cutoff_layer_support q δ) i d).trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply Finset.sum_le_sum; intro j _
  apply Finset.sum_le_sum; intro α _
  rw [integral_ofLp (fun y => ‖dpart (cutoffLayer s.cutoff q δ j) α y‖^2)]
  exact (hBbound j α δ hδ hδ1).2

/-- Uniform strong force of arbitrary order for the literal physical Lamé
operator; its lower terms and the actual curved chart are retained. -/
lemma Setup.field_force_mass (s : Setup Ω x) (hΩ : MeasurableSet Ω)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hm0 : m x≠0) (he0 : l x+2*m x≠0) (hp0 : l x+3*m x≠0)
    (p₀ : W) (h₀ : normal (l x) (m x) p₀=0) (N : ℕ) :
    ∃ p : ℕ → W, p 0=p₀ ∧ (∀ n, 0<n → boundary (p n)=0) ∧
      ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 → ∀ i,
        (∫ z in Ω, ‖force l m (s.field (amplitude p (N+1)) δ) i z‖^2)≤C*δ^(2*N) := by
  have ha := smooth_chartPrincipal s.Q (s.Φ_smooth.comp PiLp.contDiff_toLp)
    (PiLp.contDiff_ofLp.comp s.Ψ_smooth) hl hm
  have hb := smooth_chartLower s.Q (s.Φ_smooth.comp PiLp.contDiff_toLp)
    (PiLp.contDiff_ofLp.comp s.Ψ_smooth) hl hm
  obtain ⟨p,hp,hpb,hbound⟩ := finite_local_layer _ _ ha hb s.cutoff_smooth s.cutoff_compact
    s.cutoff_one (l x) (m x) hm0 he0 hp0 (s.frozen l m) p₀ h₀ N
  obtain ⟨A,hA,hAbound⟩ := transferred_mass_bound s.e s.smooth s.compact s.source
    hΩ measurable_H s.inside s.η_support s.η_one s.Q s.Φ s.Ψ s.Φ_smooth s.Ψ_smooth s.Φ_germ s.Ψ_germ hl hm
  choose B hB hBbound using hbound
  refine ⟨p,hp,hpb,A*∑ i, B i,mul_nonneg hA (Finset.sum_nonneg (fun i _ => hB i)),
    fun δ hδ hδ1 i => ?_⟩
  apply (hAbound _ (smooth_cutoffLayer s.cutoff_smooth _ δ) (s.cutoff_layer_support _ δ) i).trans
  calc
    _ ≤ A*∑ j, (B j*δ^(2*N)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum; intro j _
      rw [integral_ofLp (fun y => ‖strong (ElasticityBoundaryPhysicalMass.principal s.Q s.Φ s.Ψ l m)
        (ElasticityBoundaryPhysicalMass.lower s.Q s.Φ s.Ψ l m) (cutoffLayer s.cutoff (amplitude p (N+1)) δ) j y‖^2)]
      exact (hBbound j δ hδ hδ1).2
    _ = _ := by rw [← Finset.sum_mul,mul_assoc]

end ElasticityBoundaryPacket
namespace ElasticityBoundaryPacket
/-! The physical quasimodes are genuine elements of the H1/trace construction
used by the real DN map, with uniform norm and arbitrary dual-residual decay. -/
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal
open Elasticity ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryProjectedStress ElasticityBoundaryPhysicalStrong ElasticityBoundaryChainRule
  ElasticityBoundaryResidualMass ElasticityBoundaryTrialMass ElasticityBoundaryActualTower
  ElasticityBoundaryMVNormal ElasticityBoundaryChartOperator

variable {Ω : Set X} {x : X}

lemma smooth_force {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (u : I → X → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (force l m u i) := by
  have he : force l m u i=(fun z => ∑ j, dd (stress basis l m u i j) (basis j) z) :=
    funext (fun z => (stress_divergence basis hl hm u hu i z).symm)
  rw [he]
  exact ContDiff.sum (fun j _ => smooth_dd (smooth_stress hl hm u hu i j) _)

lemma compact_force (l m : X → ℂ) (u : I → X → ℂ) {K : Set X}
    (hK : IsCompact K) (hus : ∀ j, Function.support (u j)⊆K) (i : I) :
    HasCompactSupport (force l m u i) :=
  hK.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (force_support l m u hK.isClosed hus i) hK.isClosed)

lemma coarse_sq_bound {A t r : ℝ} (hA : 0≤A) (ht : 0≤t) (hr : 0≤r)
    (h : r^2≤A*t^2) : r≤(A+1)*t := by
  apply (sq_le_sq₀ hr (mul_nonneg (by positivity) ht)).mp
  have hC : A≤(A+1)^2 := by nlinarith [sq_nonneg A]
  calc
    _ ≤ A*t^2 := h
    _ ≤ (A+1)^2*t^2 := mul_le_mul_of_nonneg_right hC (sq_nonneg t)
    _ = _ := (mul_pow _ _ _).symm

def Setup.trial (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) : ComplexTrial Ω :=
  complexFieldTrial (s.field q δ) (s.field_smooth q δ) s.image_compact (s.field_support q δ)

lemma Setup.trial_size (s : Setup Ω x) (hΩ : MeasurableSet Ω) (q : Polynomial W) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 → complexTrialSize (s.trial q δ)≤C := by
  obtain ⟨A,hA,hAb⟩ := s.field_value_mass hΩ q
  obtain ⟨B,hB,hBb⟩ := s.field_gradient_mass hΩ q
  let T := 3*A+9*B
  have hT : 0≤T := by dsimp [T]; positivity
  have hb (w : ℂ →L[ℝ] ℝ) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
      ‖projectedTrial (Ω := Ω) w (s.field q δ) (s.field_smooth q δ) s.image_compact (s.field_support q δ)‖≤
        (T+1)*‖w‖ := by
    apply coarse_sq_bound hT (norm_nonneg _) (norm_nonneg _)
    have hu := s.field_smooth q δ
    have hc := s.field_compact q δ
    have hm (i) := (hu i).continuous.memLp_of_hasCompactSupport (hc i) (p := (2:ℝ≥0∞)) (μ := volume) |>.restrict Ω
    have hdm (i j) := (smooth_dd (hu i) (coordVector j)).continuous.memLp_of_hasCompactSupport
      ((hc i).fderiv_apply ℝ _) (p := (2:ℝ≥0∞)) (μ := volume) |>.restrict Ω
    apply (projected_trial_mass w _ hu hm hdm _ _).trans
    have hreal : (∑ i, (∫ z in Ω, ‖s.field q δ i z‖^2))+
        (∑ j, ∑ i, (∫ z in Ω, ‖dd (s.field q δ i) (coordVector j) z‖^2))≤T := by
      have h1 := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset I)) => hAb δ hδ hδ1 i)
      have h2 := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset I)) =>
        Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset I)) => hBb δ hδ hδ1 i j))
      have h1' : (∑ i, (∫ z in Ω, ‖s.field q δ i z‖^2))≤3*A := by simpa using h1
      have h2' : (∑ j, ∑ i, (∫ z in Ω, ‖dd (s.field q δ i) (coordVector j) z‖^2))≤9*B := by
        have hh : (∑ j, ∑ i, (∫ z in Ω, ‖dd (s.field q δ i) (coordVector j) z‖^2))≤(3:ℝ)*(3*B) := by
          simpa [basis,coordVector] using h2
        exact hh.trans_eq (by ring)
      exact add_le_add h1' h2'
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hreal (sq_nonneg ‖w‖)
  refine ⟨(T+1)*(‖Complex.reCLM‖+‖Complex.imCLM‖),mul_nonneg (by positivity) (by positivity),
    fun δ hδ hδ1 => ?_⟩
  exact (add_le_add (hb Complex.reCLM δ hδ hδ1) (hb Complex.imCLM δ hδ hδ1)).trans_eq (mul_add _ _ _).symm

lemma Setup.trial_residual (s : Setup Ω x) (hB : Bornology.IsBounded Ω)
    {l m : X → ℝ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hbl : BoundedCoefficient Ω l) (hbm : BoundedCoefficient Ω m)
    (q : Polynomial W) (N : ℕ) {C : ℝ} (hC : 0≤C)
    (hforce : ∀ δ : ℝ, 0<δ → δ≤1 → ∀ i,
      (∫ z in Ω, ‖force (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) (s.field q δ) i z‖^2)≤C*δ^(2*N)) :
    ∃ A : ℝ, 0≤A ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
      complexResidualSize hbl hbm (s.trial q δ)≤A*δ^N := by
  have hb (w : ℂ →L[ℝ] ℝ) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
      ‖physicalResidual hbl hbm
        (projectedTrial w (s.field q δ) (s.field_smooth q δ) s.image_compact (s.field_support q δ))‖≤
        (9*C+1)*(‖w‖*δ^N) := by
    refine coarse_sq_bound (A := 9*C) (t := ‖w‖*δ^N) (mul_nonneg (by norm_num) hC) (mul_nonneg (norm_nonneg _) (pow_nonneg hδ.le _))
      (norm_nonneg (physicalResidual hbl hbm
        (projectedTrial w (s.field q δ) (s.field_smooth q δ) s.image_compact (s.field_support q δ)))) ?_
    have hu := s.field_smooth q δ
    have hc := s.field_compact q δ
    have hlc := Complex.ofRealCLM.contDiff.comp hl
    have hmc := Complex.ofRealCLM.contDiff.comp hm
    have hf (i) := (smooth_force hlc hmc _ hu i).continuous.memLp_of_hasCompactSupport
      (compact_force _ _ _ s.image_compact (s.field_support q δ) i) (p := (2:ℝ≥0∞)) (μ := volume) |>.restrict Ω
    apply (projected_trial_residual w hl hm hbl hbm hB _ hu hc _ _ hf).trans
    calc
      _ ≤ 3*‖w‖^2*∑ i : I, (C*δ^(2*N)) := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => hforce δ hδ hδ1 i)) (by positivity)
      _ = _ := by simp only [Fin.sum_univ_three]; rw [pow_mul]; ring
  refine ⟨(9*C+1)*(‖Complex.reCLM‖+‖Complex.imCLM‖),by positivity,fun δ hδ hδ1 => ?_⟩
  apply (add_le_add (hb Complex.reCLM δ hδ hδ1) (hb Complex.imCLM δ hδ hδ1)).trans_eq
  ring

end ElasticityBoundaryPacket
namespace ElasticityBoundaryPacket

section
/-! Arbitrary-order actual physical boundary packets. All coefficient and
ellipticity assumptions here follow from the admissibility. -/
open Set MeasureTheory
open scoped BigOperators
open Elasticity ElasticityBoundaryMVNormal ElasticityBoundaryActualTower

variable {Ω : Set X} {x : X}

lemma amplitude_zero (p : ℕ → W) (N : ℕ) : (amplitude p N).coeff 0=p 0 := by
  simp [amplitude,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]

lemma ellipticity_at {l m : X → ℝ} (ha : Admissible Ω l m) (hx : x∈closure Ω) :
    (m x:ℂ)≠0 ∧ (l x:ℂ)+2*m x≠0 ∧ (l x:ℂ)+3*m x≠0 := by
  obtain ⟨hm,he⟩ := ha.2.2 x hx
  have h2 : 0<l x+2*m x := by linarith
  have h3 : 0<l x+3*m x := by linarith
  exact ⟨Complex.ofReal_ne_zero.mpr hm.ne',
    by exact_mod_cast h2.ne',by exact_mod_cast h3.ne'⟩

/-- Genuine physical trace-space test, prescribed leading frozen solution,
uniform H1 norm and arbitrarily small dual Lamé residual. -/
lemma Setup.packet (s : Setup Ω x) {l m : X → ℝ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (ha : Admissible Ω l m) (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hx : x∈closure Ω) (p₀ : W) (h₀ : normal (l x) (m x) p₀=0) (N : ℕ) :
    ∃ q : Polynomial W, q.coeff 0=p₀ ∧ ∃ A B : ℝ, 0≤A ∧ 0≤B ∧
      ∀ δ : ℝ, 0<δ → δ≤1 → complexTrialSize (s.trial q δ)≤A ∧
      complexResidualSize (ha.1.boundedCoefficient hO hB)
        (ha.2.1.boundedCoefficient hO hB) (s.trial q δ)≤B*δ^N := by
  obtain ⟨hm0,he0,hp0⟩ := ellipticity_at ha hx
  obtain ⟨p,hp,_hpb,C,hC,hf⟩ := s.field_force_mass hO.measurableSet
    (Complex.ofRealCLM.contDiff.comp hl) (Complex.ofRealCLM.contDiff.comp hm)
    hm0 he0 hp0 p₀ h₀ N
  obtain ⟨A,hA,hAb⟩ := s.trial_size hO.measurableSet (amplitude p (N+1))
  obtain ⟨B,hB0,hBb⟩ := s.trial_residual hB hl hm (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) _ N hC hf
  refine ⟨amplitude p (N+1),(amplitude_zero p _).trans hp,A,B,hA,hB0,fun δ hδ hδ1 => ?_⟩
  exact ⟨hAb δ hδ hδ1,hBb δ hδ hδ1⟩

end
/-! Equal full real physical DN maps control two genuine, independently
corrected physical packets; the traces need not coincide. -/
open Set
open scoped BigOperators
open Elasticity ElasticityBoundaryMVNormal
variable {Ω : Set X} {x : X}

lemma Setup.paired_packets (s : Setup Ω x) {l₁ m₁ l₂ m₂ : X → ℝ}
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω) (hx : x∈closure Ω)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂)
    (p₀ q₀ : W) (hp₀ : normal (l₁ x) (m₁ x) p₀=0) (hq₀ : normal (l₂ x) (m₂ x) q₀=0)
    (N : ℕ) :
    ∃ p q : Polynomial W, p.coeff 0=p₀ ∧ q.coeff 0=q₀ ∧
      ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
      ‖complexTrialEnergy l₁ m₁ (s.trial p δ) (s.trial q δ)-
        complexTrialEnergy l₂ m₂ (s.trial p δ) (s.trial q δ)‖≤C*δ^N := by
  obtain ⟨p,hp,A₁,B₁,hA₁,hB₁,hpB⟩ := s.packet hl₁ hm₁ ha₁ hO hB hx p₀ hp₀ N
  obtain ⟨q,hq,A₂,B₂,hA₂,hB₂,hqB⟩ := s.packet hl₂ hm₂ ha₂ hO hB hx q₀ hq₀ N
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := equal_DN_complex_mixed_bound ha₁ ha₂ hO hB hDN
  refine ⟨p,q,hp,hq,C₁*B₁*A₂+C₂*A₁*B₂,by positivity,fun δ hδ hδ1 => ?_⟩
  apply (hE _ _).trans
  obtain ⟨hpS,hpR⟩ := hpB δ hδ hδ1
  obtain ⟨hqS,hqR⟩ := hqB δ hδ hδ1
  have hRS₂ : 0≤complexResidualSize (ha₂.1.boundedCoefficient hO hB)
      (ha₂.2.1.boundedCoefficient hO hB) (s.trial q δ) := add_nonneg (ContinuousLinearMap.opNorm_nonneg _) (ContinuousLinearMap.opNorm_nonneg _)
  have hS₂ : 0≤complexTrialSize (s.trial q δ) := add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    _ ≤ C₁*(B₁*δ^N)*A₂+C₂*A₁*(B₂*δ^N) := add_le_add
      (mul_le_mul (mul_le_mul_of_nonneg_left hpR hC₁.le) hqS hS₂
        (mul_nonneg hC₁.le (mul_nonneg hB₁ (pow_nonneg hδ.le _))))
      (mul_le_mul (mul_le_mul_of_nonneg_left hpS hC₂.le) hqR hRS₂
        (mul_nonneg hC₂.le hA₁))
    _ = _ := by ring

end ElasticityBoundaryPacket

end

end OAI
