import OAI.Dynamics.ThreeTorus.Preparation

namespace OAI

/-! Good-arc cutoffs, scalar and tensor packet constructors, fiber insertion, and initial dense tests. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace ThreeTorus

lemma sharp_cutoff_integral_bound {δ t : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ)
    (hu : δ+t < 1/2) {b : ℝ → ℝ} (hbc : Continuous b) (_hbs : HasCompactSupport b)
    (hb : ∀ x, 0 ≤ b x ∧ b x ≤ 1)
    (hone : ∀ x ∈ Icc (δ+t) (1-δ-t), b x = 1) :
    (∫ x in Ioo (0:ℝ) 1, (1-b x)^2) ≤ 2*δ+2*t := by
  have hbint : IntegrableOn (fun x : ℝ => b x^2) (Ioo (0:ℝ) 1) :=
    (hbc.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hlower : 1-2*δ-2*t ≤ ∫ x in Ioo (0:ℝ) 1, b x^2 := by
    calc
      _ = ∫ x in Icc (δ+t) (1-δ-t), (1:ℝ) := by
        simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,
          Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-δ-t-(δ+t))]
        ring
      _ = ∫ x in Icc (δ+t) (1-δ-t), b x^2 := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        dsimp only
        rw [hone x hx,one_pow]
      _ ≤ ∫ x in Ioo (0:ℝ) 1, b x^2 := by
        apply setIntegral_mono_set hbint (.of_forall fun _ => sq_nonneg _)
        exact .of_forall fun x hx => ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo (0:ℝ) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  calc
    _ ≤ ∫ x in Ioo (0:ℝ) 1, 1-b x^2 := by
      apply setIntegral_mono_on
        ((continuous_const.sub hbc).pow 2 |>.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
        (hi.sub hbint) measurableSet_Ioo
      intro x _
      change (1-b x)^2 ≤ 1-b x^2
      nlinarith [(hb x).1,(hb x).2]
    _ = 1-∫ x in Ioo (0:ℝ) 1, b x^2 := by rw [integral_sub hi hbint]; simp
    _ ≤ _ := by linarith

/-- Smooth compact arc cutoffs with arbitrarily small excess over the ACTUAL
complement length. The standard neutral 4δ estimate is not sharp enough here. -/
theorem exists_sharp_arc_cutoff {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t)
    (hu : δ+t < 1/2) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Ioo δ (1-δ) ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ Icc (δ+t) (1-δ-t), χ x = 1) ∧
      (∫ x in Ioo (0:ℝ) 1, (1-χ x)^2) ≤ 2*δ+2*t := by
  let b : ContDiffBump (1/2:ℝ) := ⟨1/2-δ-t,1/2-δ-t/2,by linarith,by linarith⟩
  have hs : tsupport (b : ℝ → ℝ) ⊆ Ioo δ (1-δ) := by
    intro x hx
    rw [b.tsupport_eq] at hx
    change |x-1/2| ≤ 1/2-δ-t/2 at hx
    have hh := abs_le.mp hx
    constructor <;> linarith
  have hone : ∀ x ∈ Icc (δ+t) (1-δ-t), b x = 1 := by
    intro x hx
    apply b.one_of_mem_closedBall
    change |x-1/2| ≤ 1/2-δ-t
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  refine ⟨b,b.contDiff,b.hasCompactSupport,hs,fun x => ⟨b.nonneg,b.le_one⟩,hone,?_⟩
  exact sharp_cutoff_integral_bound ht hδ hu b.continuous b.hasCompactSupport
    (fun _ => ⟨b.nonneg,b.le_one⟩) hone

lemma circle_cutoff_squared_error {χ : ℝ → ℝ}
    (_hc : HasCompactSupport χ) (hs : support χ ⊆ Ioo (0:ℝ) 1)
    (_hb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    (∫ x, (1-(periodize_periodic χ).lift x)^2 ∂AddCircle.haarAddCircle) =
      ∫ x in Ioo (0:ℝ) 1, (1-χ x)^2 := by
  have he := AddCircle.integral_preimage 1 0
    (fun x : UnitAddCircle => (1-(periodize_periodic χ).lift x)^2)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,one_smul] at he
  rw [← he,integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  change (1-periodize χ x)^2 = (1-χ x)^2
  rw [periodize_eq_on_unit hs ⟨hx.1.le,hx.2.le⟩]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma cylinderTorusCutoff_scalar (χ : ℝ → ℝ) (p : UnitAddCircle × UnitAddCircle) :
    cylinderTorusCutoff (fun q => χ q.1) p = (periodize_periodic χ).lift p.1 := by
  rcases p with ⟨p,q⟩
  obtain ⟨x,hx⟩ := QuotientAddGroup.mk_surjective p
  subst p
  rfl

/-- A common scalar good-arc cutoff produces literal smooth input packets;
all data are fixed before any passage integer is chosen. -/
theorem exists_scalar_cutoff_packets {ι : Type*}
    (m : ι → ℤ) (hm : ∀ i, m i ≠ 0)
    (C : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (hCc : ∀ i, Continuous (C i))
    (hCs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => C i (p.1,p.2)))
    {χ : ℝ → ℝ} (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) {δ : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2)
    (hχI : tsupport χ ⊆ Ioo δ (1-δ))
    (V : ℝ → ℝ) (hVp : Periodic V 1)
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVd : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x) :
    ∃ F : PassagePackets ι, F.m=m ∧ F.V=V ∧ F.GoodArc δ ∧
      (∀ i p, F.A i p = ((periodize_periodic χ).lift p.1:ℂ)*C i p) ∧
      ∀ i a x, F.A₀ i a x = (χ x:ℂ)*C i ((x:UnitAddCircle),a) := by
  obtain ⟨l,u,R,hdl,hlu,hud,hR,hKI,hbuffer⟩ := compact_inside_buffered_interval
    hχc (by linarith : δ < 1-δ) hχI
  have hs : CylinderSmooth (fun p : ℝ × UnitAddCircle => χ p.1) := hχs.comp contDiff_fst
  have hc : HasCompactSupport (fun p : ℝ × UnitAddCircle => χ p.1) := scalar_cylinder_compact hχc
  have hso : support (fun p : ℝ × UnitAddCircle => χ p.1) ⊆ Ioo (0:ℝ) (0+1) ×ˢ univ := by
    intro p hp
    have h := hχI (subset_tsupport χ hp)
    exact ⟨⟨hδ.trans_lt h.1,by linarith [h.2]⟩,mem_univ _⟩
  have hsi : support (fun p : ℝ × UnitAddCircle => χ p.1) ⊆ Ioc l u ×ˢ univ :=
    fun p hp => ⟨hKI (subset_tsupport χ hp),mem_univ _⟩
  let F := cutoffPackets m hm C hCc hCs (fun _ p => χ p.1) (fun _ => hs) (fun _ => hc)
    0 l u R (fun _ => hso) (fun _ => hsi) (hδ.trans hdl.le) (by linarith) hlu.le hR
    V hVp hVs (fun x hx => hVd x (hbuffer hx))
  refine ⟨F,rfl,rfl,⟨rfl,hdl,hud,hVd⟩,?_,fun _ _ _ => rfl⟩
  intro i p
  change (cylinderTorusCutoff (fun q => χ q.1) p:ℂ)*C i p = _
  rw [cylinderTorusCutoff_scalar]

lemma scalar_packets_reflection {ι : Type*} (F : PassagePackets ι)
    {τ : ι → ι} {m : ι → ℤ} {C : ι → UnitAddCircle × UnitAddCircle → ℂ}
    {χ : ℝ → ℝ} (hm : F.m=m) (hmi : ∀ i, m (τ i) = -m i)
    (hc : ∀ i p, C (τ i) p = conj (C i p))
    (hA : ∀ i p, F.A i p = ((periodize_periodic χ).lift p.1:ℂ)*C i p)
    (hA₀ : ∀ i a x, F.A₀ i a x = (χ x:ℂ)*C i ((x:UnitAddCircle),a)) :
    F.Reflection τ := by
  constructor
  · simpa only [hm] using hmi
  · intro i p; rw [hA,hA,hc]; simp only [map_mul,Complex.conj_ofReal]
  · intro i a x; rw [hA₀,hA₀,hc]; simp only [map_mul,Complex.conj_ofReal]

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate
namespace ThreeTorus

lemma tensor_filter_reflection {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k))
    (P : TensorIndex → Prop) [DecidablePred P] (hP : ∀ k, P (-k) ↔ P k) :
    ∀ k, (c.filter P) (-k)=conj ((c.filter P) k) := by
  intro k
  simp only [Finsupp.filter_apply,hP,hc,apply_ite,map_zero]
  split_ifs <;> rfl

lemma tensorAngular_reflection {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k)) :
    ∀ k, tensorAngular c (-k)=conj (tensorAngular c k) :=
  tensor_filter_reflection hc _ (fun _ => by simp)
lemma tensorMiddle_reflection {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k)) :
    ∀ k, tensorMiddle c (-k)=conj (tensorMiddle c k) :=
  tensor_filter_reflection hc _ (fun _ => by simp)
lemma tensorLast_reflection {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k)) :
    ∀ k, tensorLast c (-k)=conj (tensorLast c k) :=
  tensor_filter_reflection hc _ (fun _ => by simp)

def tensorSupportNeg {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k)) :
    ↥c.support → ↥c.support := fun k => ⟨-k.val,by
      rw [Finsupp.mem_support_iff,hc]
      exact (map_ne_zero (starRingEnd ℂ)).mpr (Finsupp.mem_support_iff.mp k.property)⟩

lemma tensorSupportNeg_involutive {c : TensorIndex →₀ ℂ} (hc : ∀ k, c (-k)=conj (c k)) :
    Involutive (tensorSupportNeg hc) := fun _ => Subtype.ext (neg_neg _)

/-- Literal smooth packets of a finite tensor polynomial after a cyclic
coordinate change. The unused old coordinate is not silently discarded. -/
theorem exists_rotated_tensor_packets (c : TensorIndex →₀ ℂ)
    (hc : ∀ k, c (-k)=conj (c k)) (a b d : Fin 3)
    (hn : ∀ k ∈ c.support, k a ≠ 0)
    {χ : ℝ → ℝ} (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) {δ : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2)
    (hχI : tsupport χ ⊆ Ioo δ (1-δ))
    (V : ℝ → ℝ) (hVp : Periodic V 1)
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVd : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x) :
    ∃ F : PassagePackets ↥c.support, F.V=V ∧ F.GoodArc δ ∧
      F.Reflection (tensorSupportNeg hc) ∧
      (∀ k, F.m k=k.val a) ∧
      ∀ x, finitePacketVector F.m F.A x = ((periodize_periodic χ).lift x.2.1:ℂ)*
        ∑ k ∈ c.support, c k*(fourier (k a) x.1*fourier (k b) x.2.1*fourier (k d) x.2.2) := by
  let C : ↥c.support → UnitAddCircle × UnitAddCircle → ℂ :=
    fun k ua => c k.val*fourier (k.val b) ua.1*fourier (k.val d) ua.2
  have hCc k : Continuous (C k) := by dsimp [C]; fun_prop
  have hCs k : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => C k (p.1,p.2)) :=
    (contDiff_const.mul ((smooth_fourier_lift (k.val b)).comp contDiff_fst)).mul
      ((smooth_fourier_lift (k.val d)).comp contDiff_snd)
  obtain ⟨F,hFm,hFV,hFg,hFA,hFA₀⟩ := exists_scalar_cutoff_packets
    (fun k : ↥c.support => k.val a) (fun k => hn k.val k.property) C hCc hCs
    hχs hχc hδ hd hχI V hVp hVs hVd
  have hCr k p : C (tensorSupportNeg hc k) p=conj (C k p) := by
    simp only [C,tensorSupportNeg,hc,Pi.neg_apply,fourier_neg,map_mul]
  have hFr := scalar_packets_reflection F hFm (fun _ => rfl) hCr hFA hFA₀
  refine ⟨F,hFV,hFg,hFr,fun _ => congrFun hFm _,?_⟩
  intro x
  simp only [finitePacketVector,packet,hFA,hFm,C]
  rw [Finset.mul_sum]
  change (∑ k ∈ c.support.attach, _) = _
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans
    (Finset.sum_attach c.support (fun k => ((periodize_periodic χ).lift x.2.1:ℂ)*
      (c k*(fourier (k a) x.1*fourier (k b) x.2.1*fourier (k d) x.2.2))))
  ring

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma tensorPolynomial_add (c d : TensorIndex →₀ ℂ) :
    tensorPolynomial (c+d) = fun x => tensorPolynomial c x+tensorPolynomial d x := by
  funext x
  simp only [tensorPolynomial_eq,comp_apply,multiTrigPolynomial_add]
  rfl

lemma tensorPolynomial_filter (c : TensorIndex →₀ ℂ) (p : TensorIndex → Prop)
    [DecidablePred p] (x : TripleTorus) :
    tensorPolynomial (c.filter p) x = ∑ k ∈ c.support, if p k then c k*tensorCharacter k x else 0 := by
  classical
  simp only [tensorPolynomial,Finsupp.sum,Finsupp.support_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : p k <;> simp [h]

lemma tensorCharacter_angular_integral (k : TensorIndex) (ua : UnitAddCircle × UnitAddCircle) :
    (∫ θ, tensorCharacter k (θ,ua) ∂phaseHaar) =
      if k 0=0 then fourier (k 1) ua.1*fourier (k 2) ua.2 else 0 := by
  simp only [tensorCharacter,integral_mul_const,integral_fourier_haar]
  split_ifs <;> simp_all

lemma tensorAngular_eq_remove_mean (c : TensorIndex →₀ ℂ) (x : TripleTorus) :
    tensorPolynomial (tensorAngular c) x =
      tensorPolynomial c x-∫ θ, tensorPolynomial c (θ,x.2) ∂phaseHaar := by
  classical
  have hsplit : ∀ k, (if k 0≠0 then c k*tensorCharacter k x else 0) =
      c k*tensorCharacter k x-c k*(if k 0=0 then fourier (k 1) x.2.1*fourier (k 2) x.2.2 else 0) := by
    intro k
    by_cases hk : k 0=0
    · simp [hk,tensorCharacter]
    · simp [hk]
  rw [tensorAngular,tensorPolynomial_filter]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib]
  congr 1
  change _ = ∫ θ, ∑ k ∈ c.support, c k*tensorCharacter k (θ,x.2) ∂phaseHaar
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul,tensorCharacter_angular_integral]
  · intro k _
    exact (continuous_const.mul ((tensorCharacter_continuous k).comp
      (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

lemma tensorAngular_fiber_energy_le (c : TensorIndex →₀ ℂ) {B : ℝ} (_hB : 0 ≤ B)
    (hc : ∀ x, ‖tensorPolynomial c x‖ ≤ B) (ua : UnitAddCircle × UnitAddCircle) :
    (∫ θ, ‖tensorPolynomial (tensorAngular c) (θ,ua)‖^2 ∂phaseHaar) ≤ B^2 := by
  have hcont : Continuous (fun θ => tensorPolynomial c (θ,ua)) :=
    (tensorPolynomial_continuous c).comp (continuous_id.prodMk continuous_const)
  simp_rw [tensorAngular_eq_remove_mean]
  have hf := hcont.memLp_of_hasCompactSupport (p := 2) (μ := phaseHaar) (HasCompactSupport.of_compactSpace _)
  refine (integral_sq_sub_mean_le hf).trans ?_
  have he : (∫ θ : UnitAddCircle, B^2 ∂phaseHaar) = B^2 := by simp
  rw [← he]
  apply integral_mono (hcont.norm.pow 2 |>.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (integrable_const _)
  intro θ
  exact pow_le_pow_left₀ (norm_nonneg _) (hc (θ,ua)) 2

/-- Exact constant-one angular cutoff bound; it is the actual lost arc length,
not four times that length, which appears in the preparation error. -/
lemma tensorAngular_cutoff_energy (c : TensorIndex →₀ ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ x, ‖tensorPolynomial c x‖ ≤ B) {χ : UnitAddCircle → ℝ} (hχ : Continuous χ) :
    (∫ x : TripleTorus, ‖tensorPolynomial (tensorAngular c) x-
      (χ x.2.1:ℂ)*tensorPolynomial (tensorAngular c) x‖^2 ∂tripleVolume) ≤
      B^2 * ∫ u, (1-χ u)^2 ∂phaseHaar := by
  let f := tensorPolynomial (tensorAngular c)
  have hfc : Continuous f := tensorPolynomial_continuous _
  have he (x : TripleTorus) : ‖f x-(χ x.2.1:ℂ)*f x‖^2 = (1-χ x.2.1)^2*‖f x‖^2 := by
    rw [show f x-(χ x.2.1:ℂ)*f x = ((1-χ x.2.1:ℝ):ℂ)*f x by push_cast; ring,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  change (∫ x : TripleTorus, ‖f x-(χ x.2.1:ℂ)*f x‖^2 ∂tripleVolume) ≤ _
  simp_rw [he]
  have hi : Integrable (fun x : TripleTorus => (1-χ x.2.1)^2*‖f x‖^2) tripleVolume :=
    (((continuous_const.sub (hχ.comp (continuous_fst.comp continuous_snd))).pow 2).mul
      (hfc.norm.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_prod_symm _ hi]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∫ ua, (1-χ ua.1)^2*B^2 ∂slowVolume := by
      apply integral_mono (by simpa only [integral_const_mul] using hi.integral_prod_right)
        ((((continuous_const.sub (hχ.comp continuous_fst)).pow 2).mul continuous_const).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
      intro ua
      exact mul_le_mul_of_nonneg_left (tensorAngular_fiber_energy_le c hB hc ua) (sq_nonneg _)
    _ = _ := by
      rw [integral_prod]
      · simp only [integral_const,probReal_univ,one_smul]
        rw [integral_mul_const,mul_comm]
      · exact (((continuous_const.sub (hχ.comp continuous_fst)).pow 2).mul continuous_const).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma neutralCircleCutoff_squared_error {δ : ℝ} (cut : LawCutoffs δ)
    (hδ : 0 < δ) (hd : δ < 1/8) :
    (∫ a, (1-neutralCircleCutoff cut a)^2 ∂phaseHaar) ≤ 4*δ := by
  have hs : support cut.ψ ⊆ Ioo (0:ℝ) 1 := fun x hx => by
    have hh := cut.ψ_support (subset_tsupport _ hx)
    exact ⟨hδ.trans hh.1,by linarith [hh.2]⟩
  change (∫ a, (1-(periodize_periodic cut.ψ).lift a)^2 ∂phaseHaar) ≤ _
  rw [circle_cutoff_squared_error cut.ψ_compact hs (fun x => ⟨cut.ψ_nonneg x,cut.ψ_le_one x⟩)]
  have hh := sharp_cutoff_integral_bound hδ hδ.le (by linarith : δ+δ < 1/2)
    cut.ψ_smooth.continuous cut.ψ_compact (fun x => ⟨cut.ψ_nonneg x,cut.ψ_le_one x⟩)
    (by simpa only [two_mul,sub_sub] using cut.ψ_one)
  linarith

lemma uniform_slow_cutoff_energy {f : TripleTorus → ℂ} (hf : Continuous f)
    {B : ℝ} (_hB : 0 ≤ B) (hb : ∀ x, ‖f x‖ ≤ B)
    {χ : UnitAddCircle → ℝ} (hχ : Continuous χ) :
    physicalError f (fun x => (χ x.2.1:ℂ)*f x) ≤
      B^2*(∫ u, (1-χ u)^2 ∂phaseHaar) := by
  have he (x : TripleTorus) : ‖f x-(χ x.2.1:ℂ)*f x‖^2 = (1-χ x.2.1)^2*‖f x‖^2 := by
    rw [show f x-(χ x.2.1:ℂ)*f x = ((1-χ x.2.1:ℝ):ℂ)*f x by push_cast; ring,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  unfold physicalError
  simp_rw [he]
  calc
    _ ≤ ∫ x : TripleTorus, (1-χ x.2.1)^2*B^2 ∂tripleVolume := by
      apply integral_mono
        (((continuous_const.sub (hχ.comp (continuous_fst.comp continuous_snd))).pow 2).mul (hf.norm.pow 2)
          |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (((continuous_const.sub (hχ.comp (continuous_fst.comp continuous_snd))).pow 2).mul continuous_const
          |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      intro x
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb x) 2) (sq_nonneg _)
    _ = _ := by
      rw [integral_prod]
      · simp only [integral_const,probReal_univ,one_smul]
        rw [integral_prod]
        · simp only [integral_const,probReal_univ,one_smul]
          rw [integral_mul_const,mul_comm]
        · exact (((continuous_const.sub (hχ.comp continuous_fst)).pow 2).mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact (((continuous_const.sub (hχ.comp (continuous_fst.comp continuous_snd))).pow 2).mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma tensorMiddle_coords {c : TensorIndex →₀ ℂ} (H : UnitAddCircle → UnitAddCircle) (x : TripleTorus) :
    (∑ k ∈ (tensorMiddle c).support, tensorMiddle c k*(fourier (k 1) (passageChart H x).1 *
      fourier (k 2) (passageChart H x).2.1 * fourier (k 0) (passageChart H x).2.2)) =
      tensorPolynomial (tensorMiddle c) x := by
  classical
  unfold tensorPolynomial Finsupp.sum
  apply Finset.sum_congr rfl
  intro k hk
  have hh := Finsupp.mem_support_iff.mp hk
  have hk0 : k 0=0 := by
    simpa only [tensorMiddle,Finsupp.filter_apply] using
      (show k 0=0 from by
        by_contra hn
        exact hh (by simp [tensorMiddle,hn]))
  simp only [tensorCharacter,passageChart,circleThetaShear,circleCycle,Equiv.trans_apply,Equiv.coe_fn_mk,hk0,fourier_zero,one_mul,mul_one]

lemma tensorLast_coords {c : TensorIndex →₀ ℂ} (H J : UnitAddCircle → UnitAddCircle) (x : TripleTorus) :
    (∑ k ∈ (tensorLast c).support, tensorLast c k*(fourier (k 2) (passageChart J (passageChart H x)).1 *
      fourier (k 0) (passageChart J (passageChart H x)).2.1 *
      fourier (k 1) (passageChart J (passageChart H x)).2.2)) = tensorPolynomial (tensorLast c) x := by
  classical
  unfold tensorPolynomial Finsupp.sum
  apply Finset.sum_congr rfl
  intro k hk
  have hh := Finsupp.mem_support_iff.mp hk
  have hk01 : k 0=0 ∧ k 1=0 := by
    by_contra hn
    exact hh (by simp [tensorLast,hn])
  simp only [tensorCharacter,passageChart,circleThetaShear,circleCycle,Equiv.trans_apply,Equiv.coe_fn_mk,hk01.1,hk01.2,fourier_zero,one_mul,mul_one]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def rotatedTensor (c : TensorIndex →₀ ℂ) (a b d : Fin 3) (x : TripleTorus) : ℂ :=
  ∑ k ∈ c.support, c k*(fourier (k a) x.1*fourier (k b) x.2.1*fourier (k d) x.2.2)
def tensorBudget (c : TensorIndex →₀ ℂ) : ℝ := ∑ k ∈ c.support, ‖c k‖
lemma tensorBudget_nonneg (c : TensorIndex →₀ ℂ) : 0 ≤ tensorBudget c :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)
lemma rotatedTensor_continuous (c : TensorIndex →₀ ℂ) (a b d : Fin 3) :
    Continuous (rotatedTensor c a b d) := by
  unfold rotatedTensor
  apply continuous_finsetSum
  intro k _
  fun_prop
lemma rotatedTensor_norm_le (c : TensorIndex →₀ ℂ) (a b d : Fin 3) (x : TripleTorus) :
    ‖rotatedTensor c a b d x‖ ≤ tensorBudget c := by
  apply (norm_sum_le _ _).trans_eq
  simp only [norm_mul,fourier_apply,Circle.norm_coe,mul_one,tensorBudget]

lemma exists_tensor_cutoff_family (c : TensorIndex →₀ ℂ)
    (hc : ∀ k, c (-k)=conj (c k)) (a b d : Fin 3)
    (hn : ∀ k ∈ c.support, k a ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hd : δ < 1/8) (cut : LawCutoffs δ)
    (V : ℝ → ℝ) (hp : Periodic V 1) (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hv : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x) :
    ∃ P : RealPacketFamily, P.data.V=V ∧ P.data.GoodArc δ ∧
      physicalError (rotatedTensor c a b d) P.vector ≤ 4*δ*(tensorBudget c)^2 := by
  obtain ⟨P,hPV,hPg,hPr,_hPm,hPv⟩ := exists_rotated_tensor_packets c hc a b d hn
    cut.ψ_smooth cut.ψ_compact hδ.le (by linarith : δ < 1/2) cut.ψ_support V hp hs hv
  let F : RealPacketFamily := ⟨↥c.support,inferInstance,P,tensorSupportNeg hc,
    tensorSupportNeg_involutive hc,hPr⟩
  refine ⟨F,hPV,hPg,?_⟩
  have he : F.vector = fun x => (neutralCircleCutoff cut x.2.1:ℂ)*rotatedTensor c a b d x := funext hPv
  rw [he]
  apply (uniform_slow_cutoff_energy (rotatedTensor_continuous c a b d)
    (tensorBudget_nonneg c) (rotatedTensor_norm_le c a b d) (continuous_neutralCircleCutoff cut)).trans
  have h := mul_le_mul_of_nonneg_left (neutralCircleCutoff_squared_error cut hδ hd)
    (sq_nonneg (tensorBudget c))
  nlinarith

lemma tensorAngular_nonzero {c : TensorIndex →₀ ℂ} {k : TensorIndex}
    (hk : k ∈ (tensorAngular c).support) : k 0 ≠ 0 := by
  have hh := Finsupp.mem_support_iff.mp hk
  intro hn
  exact hh (by simp [tensorAngular,hn])
lemma tensorMiddle_nonzero {c : TensorIndex →₀ ℂ} {k : TensorIndex}
    (hk : k ∈ (tensorMiddle c).support) : k 1 ≠ 0 := by
  classical
  have hh := Finsupp.mem_support_iff.mp hk
  intro hn
  exact hh (by simp [tensorMiddle,hn])

lemma tensor_split_vector (c : TensorIndex →₀ ℂ) (x : TripleTorus) :
    tensorPolynomial c x=tensorPolynomial (tensorAngular c) x+
      tensorPolynomial (tensorMiddle c) x+tensorPolynomial (tensorLast c) x := by
  have hs := congrArg (fun q => tensorPolynomial q x) (tensor_split c)
  unfold tensorPolynomial at hs
  rw [Finsupp.sum_add_index' (by simp) (by intros; ring),
    Finsupp.sum_add_index' (by simp) (by intros; ring)] at hs
  exact hs.symm
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma continuous_triple_memLp {f : TripleTorus → ℂ} (hf : Continuous f) : MemLp f 2 tripleVolume :=
  hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma exists_cutoff_loss_budget (B : ℝ) {ε : ℝ} (he : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, δ < η → 4*δ*B^2 < ε^2 := by
  refine ⟨ε^2/(4*(B^2+1)),by positivity,?_⟩
  intro δ hd
  have hh := (lt_div_iff₀ (by positivity : 0 < 4*(B^2+1))).1 hd
  by_cases hδ : 0 ≤ δ
  · nlinarith [sq_nonneg B]
  · have : δ < 0 := lt_of_not_ge hδ
    have : 4*δ*B^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg B)
    exact this.trans_lt (sq_pos_of_pos he)

/-- Two literal neutral passages convert both retained slow Fourier components
into nonzero angular packets. The F list alone is kept orthogonal. All objects,
cutoffs and bounds are fixed before their respective passage integer choices. -/
theorem exists_two_slow_insertions (F H : RealPacketFamily) (hmi : Injective F.data.m)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgF : F.data.GoodArc δ) (hgH : H.data.GoodArc δ) (hV : H.data.V=F.data.V)
    (c : TensorIndex →₀ ℂ) (hc0 : c 0=0) (hcr : ∀ k, c (-k)=conj (c k))
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ F' H' : RealPacketFamily, ∃ α : Equiv.Perm TripleTorus, ∃ frame' : PhysicalFrame,
      Continuous α ∧ MeasurePreserving α tripleVolume tripleVolume ∧
      frame'.chart=frame.chart.trans α ∧ H'.data.V=F'.data.V ∧ Injective F'.data.m ∧
      (∃ δ' : ℝ, 0 < δ' ∧ δ' < 1/8 ∧ δ' < κ ∧ F'.data.GoodArc δ' ∧ H'.data.GoodArc δ') ∧
      Q.Close ζ frame F.data.V frame' F'.data.V ∧
      physicalDist F.vector (F'.vector ∘ α) < ε ∧
      physicalDist (fun x => H.vector x+tensorPolynomial (tensorMiddle c) x+tensorPolynomial (tensorLast c) x)
        (H'.vector ∘ α) < ε ∧
      (∫ z, |F'.density z-F.density z| ∂phaseHaar) < ε := by
  classical
  let e := ε/4
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨η,hη,hηe⟩ := exists_cutoff_loss_budget (tensorBudget (tensorMiddle c)) he
  obtain ⟨s,F₁,H₁,hF₁V,hH₁V,hF₁g,hH₁g,hsδ,hsjet,hF₁i,hsF,hsH,hsp⟩ :=
    exists_neutral_families F H hmi hδ hgF hgH hV Q frame he hη (half_pos hζ)
  obtain ⟨P₁,hP₁V,hP₁g,hP₁e⟩ := exists_tensor_cutoff_family (tensorMiddle c)
    (tensorMiddle_reflection hcr) 1 2 0 (fun _ => tensorMiddle_nonzero)
    s.δpos s.δsmall s.cut s.final.V s.final.periodic s.final.smooth_speed s.good.2.2.2
  let K := H₁.append P₁ s.δpos.le hH₁g hP₁g (hP₁V.trans hH₁V.symm)
  have hKg : K.data.GoodArc s.δ := H₁.data.append_good P₁.data s.δpos.le hH₁g hP₁g (hP₁V.trans hH₁V.symm)
  have hKV : K.data.V=F₁.data.V := hH₁V.trans hF₁V.symm
  obtain ⟨η₂,hη₂,hη₂e⟩ := exists_cutoff_loss_budget (tensorBudget (tensorLast c)) he
  obtain ⟨t,F₂,H₂,hF₂V,hH₂V,hF₂g,hH₂g,htδ,htjet,hF₂i,htF,htH,htp⟩ :=
    exists_neutral_families F₁ K hF₁i s.δpos.le hF₁g hKg hKV Q (s.nextFrame frame)
      he (lt_min hκ hη₂) (half_pos hζ)
  obtain ⟨P₂,hP₂V,hP₂g,hP₂e⟩ := exists_tensor_cutoff_family (tensorLast c)
    (tensorLast_reflection hcr) 2 0 1 (fun _ => tensorLast_nonzero hc0)
    t.δpos t.δsmall t.cut t.final.V t.final.periodic t.final.smooth_speed t.good.2.2.2
  let H' := H₂.append P₂ t.δpos.le hH₂g hP₂g (hP₂V.trans hH₂V.symm)
  have hscont : Continuous s.chart := continuous_passageChart (s.geometry.Hcontinuous s.n)
  have htcont : Continuous t.chart := continuous_passageChart (t.geometry.Hcontinuous t.n)
  have hsmp : MeasurePreserving s.chart tripleVolume tripleVolume := measurePreserving_passageChart (s.geometry.Hcontinuous s.n).measurable
  have htmp : MeasurePreserving t.chart tripleVolume tripleVolume := measurePreserving_passageChart (t.geometry.Hcontinuous t.n).measurable
  refine ⟨F₂,H',s.chart.trans t.chart,t.nextFrame (s.nextFrame frame),htcont.comp hscont,htmp.comp hsmp,rfl,
    hH₂V.trans hF₂V.symm,hF₂i,⟨t.δ,t.δpos,t.δsmall,htδ.trans_le (min_le_left _ _),hF₂g,?_⟩,?_,?_,?_,?_⟩
  · exact H₂.data.append_good P₂.data t.δpos.le hH₂g hP₂g (hP₂V.trans hH₂V.symm)
  · have hh := hsjet.trans htjet
    convert hh using 1; simp [show ζ/2+ζ/2=ζ by ring]
  · have htF' : physicalDist (F₁.vector ∘ s.chart) (F₂.vector ∘ (s.chart.trans t.chart)) < e := by
      change physicalDist (F₁.vector ∘ s.chart) ((F₂.vector ∘ t.chart) ∘ s.chart) < e
      rwa [physicalDist_continuous_comp s.chart hscont hsmp]
    have hh := physicalDist_triangle F.vector_memLp (continuous_triple_memLp (F₁.continuous_vector.comp hscont))
      (continuous_triple_memLp (F₂.continuous_vector.comp (htcont.comp hscont)))
    exact (hh.trans_lt (add_lt_add hsF htF')).trans_le (by dsimp [e]; linarith)
  · have hm : (rotatedTensor (tensorMiddle c) 1 2 0 ∘ s.chart)=tensorPolynomial (tensorMiddle c) :=
      funext (tensorMiddle_coords (s.geometry.H s.n))
    have hl : (rotatedTensor (tensorLast c) 2 0 1 ∘ (s.chart.trans t.chart))=tensorPolynomial (tensorLast c) :=
      funext (tensorLast_coords (s.geometry.H s.n) (t.geometry.H t.n))
    have hP₁ : physicalDist (tensorPolynomial (tensorMiddle c)) (P₁.vector ∘ s.chart) < e := by
      rw [← hm,physicalDist_continuous_comp s.chart hscont hsmp]
      exact (physicalDist_lt_iff _ _ he).2 (hP₁e.trans_lt (hηe _ hsδ))
    have hP₂ : physicalDist (tensorPolynomial (tensorLast c)) (P₂.vector ∘ (s.chart.trans t.chart)) < e := by
      rw [← hl,physicalDist_continuous_comp (s.chart.trans t.chart) (htcont.comp hscont) (htmp.comp hsmp)]
      exact (physicalDist_lt_iff _ _ he).2 (hP₂e.trans_lt (hη₂e _ (htδ.trans_le (min_le_right _ _))))
    have hK : physicalDist (fun x => H.vector x+tensorPolynomial (tensorMiddle c) x) (K.vector ∘ s.chart) < e+e := by
      have hh := physicalDist_add_le H.vector_memLp (continuous_triple_memLp (H₁.continuous_vector.comp hscont))
        (continuous_triple_memLp (tensorPolynomial_continuous (tensorMiddle c))) (continuous_triple_memLp (P₁.continuous_vector.comp hscont))
      have hv := H₁.append_vector P₁ s.δpos.le hH₁g hP₁g (hP₁V.trans hH₁V.symm)
      change K.vector = _ at hv
      rw [hv]
      exact hh.trans_lt (add_lt_add hsH hP₁)
    have hT : physicalDist (K.vector ∘ s.chart) (H₂.vector ∘ (s.chart.trans t.chart)) < e := by
      change physicalDist (K.vector ∘ s.chart) ((H₂.vector ∘ t.chart) ∘ s.chart) < e
      rwa [physicalDist_continuous_comp s.chart hscont hsmp]
    have hKH : physicalDist (fun x => H.vector x+tensorPolynomial (tensorMiddle c) x)
        (H₂.vector ∘ (s.chart.trans t.chart)) < (e+e)+e :=
      (physicalDist_triangle (continuous_triple_memLp (H.continuous_vector.add (tensorPolynomial_continuous (tensorMiddle c))))
        (continuous_triple_memLp (K.continuous_vector.comp hscont))
        (continuous_triple_memLp (H₂.continuous_vector.comp (htcont.comp hscont)))).trans_lt (add_lt_add hK hT)
    have hh := physicalDist_add_le (continuous_triple_memLp (H.continuous_vector.add (tensorPolynomial_continuous (tensorMiddle c))))
      (continuous_triple_memLp (H₂.continuous_vector.comp (htcont.comp hscont)))
      (continuous_triple_memLp (tensorPolynomial_continuous (tensorLast c)))
      (continuous_triple_memLp (P₂.continuous_vector.comp (htcont.comp hscont)))
    have hv := H₂.append_vector P₂ t.δpos.le hH₂g hP₂g (hP₂V.trans hH₂V.symm)
    change H'.vector = _ at hv
    rw [hv]
    convert hh.trans_lt (add_lt_add hKH hP₂) using 1 <;> first | rfl | (simp only [e]; ring)
  · have hh := densityDist_triangle F₂.density_integrable F₁.density_integrable F.density_integrable
    have ht := hh.trans_lt (add_lt_add htp hsp)
    dsimp [e] at ht
    linarith
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma physicalDist_le_of_uniform {f g : TripleTorus → ℂ} (hf : Continuous f) (hg : Continuous g)
    {e : ℝ} (he : 0 ≤ e) (h : ∀ x, ‖f x-g x‖ ≤ e) : physicalDist f g ≤ e := by
  have hh : physicalDist f g^2 ≤ e^2 := by
    rw [physicalDist_sq,physicalError]
    calc
      _ ≤ ∫ _x : TripleTorus, e^2 ∂tripleVolume :=
        integral_mono (((hf.sub hg).norm.pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) (integrable_const _)
          (fun x => pow_le_pow_left₀ (norm_nonneg _) (h x) 2)
      _ = _ := by simp
  nlinarith [physicalDist_nonneg f g]

lemma small_angular_loss {δ e t : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2)
    (he : 0 < e) (hem : e ≤ 1/8) (ht : 0 < t) (htm : t ≤ e^2) :
    (1+e)^2*(2*δ+2*t) < (Real.sqrt (2*δ)+5*e)^2 := by
  have hs : 0 ≤ Real.sqrt (2*δ) := Real.sqrt_nonneg _
  have hss : (Real.sqrt (2*δ))^2=2*δ := Real.sq_sqrt (by positivity)
  have hs1 : Real.sqrt (2*δ) ≤ 1 := (Real.sqrt_le_iff).2 ⟨by norm_num,by linarith⟩
  have he2 : e^2 ≤ e/8 := by nlinarith
  have hm : (1+e)*(Real.sqrt (2*δ)+2*e) < Real.sqrt (2*δ)+5*e := by
    have hh := mul_le_mul_of_nonneg_left hs1 he.le
    nlinarith
  have hn : 0 ≤ (1+e)*(Real.sqrt (2*δ)+2*e) := by positivity
  have hb : 2*δ+2*t ≤ (Real.sqrt (2*δ)+2*e)^2 := by
    nlinarith [mul_nonneg hs he.le]
  have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg (1+e))
  have hsq := sq_lt_sq₀ hn (by positivity : 0 ≤ Real.sqrt (2*δ)+5*e) |>.2 hm
  rw [mul_pow] at hsq
  exact hmul.trans_lt hsq

/-- The INITIAL cutoff costs the exact old complement square root. Both slow
components are retained as the very same finite real tensor polynomial. -/
theorem exists_initial_tensor_test {h : TripleTorus → ℂ} (hh : Continuous h)
    (hr : ∀ x, conj (h x)=h x) (hc : ∫ x, h x ∂tripleVolume=0) (hb : ∀ x, ‖h x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2)
    (V : ℝ → ℝ) (hp : Periodic V 1) (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hv : ∀ x ∈ Ioo δ (1-δ), 0 < deriv V x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : TensorIndex →₀ ℂ, c 0=0 ∧ (∀ k, c (-k)=conj (c k)) ∧
      ∃ H : RealPacketFamily, H.data.V=V ∧ H.data.GoodArc δ ∧
      physicalDist h (fun x => H.vector x+tensorPolynomial (tensorMiddle c) x+tensorPolynomial (tensorLast c) x)
        < Real.sqrt (2*δ)+ε := by
  classical
  let e := min (ε/8) (1/8)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have hem : e ≤ 1/8 := min_le_right _ _
  have heε : 8*e ≤ ε := by have := min_le_left (ε/8) (1/8); dsimp [e]; linarith
  obtain ⟨c,hc0,hcr,hce⟩ := exists_real_centered_tensor hh hr hc he
  let t := min (e^2) ((1/2-δ)/2)
  have ht : 0 < t := lt_min (sq_pos_of_pos he) (by linarith)
  have hdt : δ+t < 1/2 := by have := min_le_right (e^2) ((1/2-δ)/2); dsimp [t]; linarith
  obtain ⟨χ,hχs,hχc,hχI,hχb,_hχ1,hχe⟩ := exists_sharp_arc_cutoff hδ ht hdt
  obtain ⟨P,hPV,hPg,hPr,_hPm,hPv⟩ := exists_rotated_tensor_packets (tensorAngular c)
    (tensorAngular_reflection hcr) 0 1 2 (fun _ => tensorAngular_nonzero)
    hχs hχc hδ hd hχI V hp hs hv
  let H : RealPacketFamily := ⟨_,inferInstance,P,tensorSupportNeg (tensorAngular_reflection hcr),
    tensorSupportNeg_involutive _,hPr⟩
  refine ⟨c,hc0,hcr,H,hPV,hPg,?_⟩
  have hχsupp : support χ ⊆ Ioo (0:ℝ) 1 := fun x hx => by
    have hx := hχI (subset_tsupport _ hx)
    exact ⟨hδ.trans_lt hx.1,by linarith [hx.2]⟩
  have hχcont : Continuous ((periodize_periodic χ).lift) :=
    continuous_of_continuous_lift (by simpa only [Periodic.lift_coe] using (contDiff_periodize hχs hχc).continuous)
  have hHv : H.vector = fun x => ((periodize_periodic χ).lift x.2.1:ℂ)*tensorPolynomial (tensorAngular c) x := by
    funext x
    exact hPv x
  have hcb (x : TripleTorus) : ‖tensorPolynomial c x‖ ≤ 1+e := by
    have ht := norm_le_norm_add_norm_sub (h x) (tensorPolynomial c x)
    linarith [hb x,hce x]
  have hA : physicalDist (tensorPolynomial (tensorAngular c)) H.vector < Real.sqrt (2*δ)+5*e := by
    apply (physicalDist_lt_iff _ _ (by positivity)).2
    rw [hHv]
    have htE := tensorAngular_cutoff_energy c (by positivity : 0 ≤ 1+e) hcb hχcont
    have hl := circle_cutoff_squared_error hχc hχsupp hχb
    rw [hl] at htE
    exact htE.trans_lt ((mul_le_mul_of_nonneg_left hχe (sq_nonneg (1+e))).trans_lt
      (small_angular_loss hδ hd he hem ht (min_le_left _ _)))
  have hpoly : physicalDist h (tensorPolynomial c) ≤ e := physicalDist_le_of_uniform hh
    (tensorPolynomial_continuous c) he.le (fun x => (hce x).le)
  let K := fun x => H.vector x+tensorPolynomial (tensorMiddle c) x+tensorPolynomial (tensorLast c) x
  have hKc : Continuous K := (H.continuous_vector.add (tensorPolynomial_continuous _)).add (tensorPolynomial_continuous _)
  have hAK : physicalDist (tensorPolynomial c) K = physicalDist (tensorPolynomial (tensorAngular c)) H.vector := by
    have hcFun := funext (tensor_split_vector c)
    rw [hcFun]
    change physicalDist (fun x => (tensorPolynomial (tensorAngular c) x+tensorPolynomial (tensorMiddle c) x)+tensorPolynomial (tensorLast c) x)
      (fun x => (H.vector x+tensorPolynomial (tensorMiddle c) x)+tensorPolynomial (tensorLast c) x) = _
    rw [physicalDist_add_right,physicalDist_add_right]
  have hsum := physicalDist_triangle (continuous_triple_memLp hh) (continuous_triple_memLp (tensorPolynomial_continuous c))
    (continuous_triple_memLp hKc)
  rw [hAK] at hsum
  have hh' := hsum.trans_lt (add_lt_add_of_le_of_lt hpoly hA)
  exact hh'.trans_le (by dsimp [e] at *; linarith)
end ThreeTorus
end
end

end OAI
