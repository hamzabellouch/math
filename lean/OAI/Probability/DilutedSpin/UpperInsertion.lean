import OAI.Probability.DilutedSpin.CavityRateLimits
import OAI.Probability.DilutedSpin.MixedEnergy
import OAI.Probability.DilutedSpin.PoissonInsertionLimit

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

lemma abs_integral_le_bound_ae {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} {B : ℝ}
    (h : ∀ᵐ x ∂μ, |f x|≤B) : |∫ x,f x ∂μ|≤B := by
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
      (h.mono (fun x hx => by simpa only [Real.norm_eq_abs] using hx))

namespace UniversalDictionary
open ConcreteReservoir

lemma randomInsertionOn_comparison_tendsto_ae {ι X : Type} [Fintype ι] [MeasurableSpace X]
    {p : ℕ} (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L,Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L,FullShapeControl M C H L (Ns L) (us L))
    (μ : Measure X) [IsProbabilityMeasure μ] (F : X → (ι → Spin) → ℝ)
    (hFm : Measurable F) {D : ℝ} (hD : 0≤D) (hF : ∀ᵐ x ∂μ,∀ s,|F x s|≤D) :
    Tendsto (fun L => limsup (fun n =>
      |(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (F x) ∂μ)-
        (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F x)) ∂μ)|) atTop) atTop (𝓝 0) := by
  let G := fun x s => clipReal D (F x s)
  have hm : Measurable G := Measurable.of_eval (fun s => (measurable_clipReal D).comp ((measurable_pi_apply s).comp hFm))
  have he : G =ᵐ[μ] F := hF.mono (fun x hx => funext (fun s => clipReal_eq (hx s)))
  have h := randomInsertionOn_comparison_tendsto M hα C H Ns hNs us hcontrol μ G hm hD
    (fun _ _ => clipReal_bound hD _)
  have hi (L n : ℕ) :
      (∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (G x) ∂μ)=
        ∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (F x) ∂μ := by
    apply integral_congr_ae; filter_upwards [he] with x hx; rw [hx]
  have hj (L n : ℕ) :
      (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (G x)) ∂μ)=
        ∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F x)) ∂μ := by
    apply integral_congr_ae; filter_upwards [he] with x hx; rw [hx]
  simpa only [hi,hj] using h

lemma poissonInsertionOn_comparison_tendsto_ae
    {ι X : ℕ → Type} [∀ k,Fintype (ι k)] [∀ k,MeasurableSpace (X k)]
    {p : ℕ} (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L,Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L,FullShapeControl M C H L (Ns L) (us L))
    (μ : (k : ℕ) → Measure (X k)) [∀ k,IsProbabilityMeasure (μ k)]
    (F : (k : ℕ) → X k → (ι k → Spin) → ℝ) (hFm : ∀ k,Measurable (F k))
    {B D : ℝ} (hB : 0≤B) (hD : 0≤D)
    (hF : ∀ k,∀ᵐ x ∂μ k,∀ s,|F k x s|≤B+D*k) (ρ : ℝ≥0) :
    Tendsto (fun L => limsup (fun n => ∫ k,
      |(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (F k x) ∂μ k)-
        (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F k x)) ∂μ k)|
      ∂poissonMeasure ρ) atTop) atTop (𝓝 0) := by
  apply poisson_mixture_double_limit ρ _ (B := 2*B) (C := 2*D)
  · intros; exact abs_nonneg _
  · intro k L n
    have h1 := abs_integral_le_bound_ae (μ k) ((hF k).mono (fun x hx =>
      reservoirInsertionOn_bound M C H (Ns L n+1) L (us L n) (F k x) hx))
    have h2 := abs_integral_le_bound_ae (μ k) ((hF k).mono (fun x hx =>
      (trialLog_continuous_bound L (FiniteLaw.spinLog (F k x))
        (FiniteLaw.spinLog_continuous (F k x)) (FiniteLaw.spinLog_bound (F k x) hx) _
        (fun i => gridExponents_pos L i.castSucc)).2
        (reservoirTrialLaw M C H (Ns L n+1) L (us L n))))
    exact (abs_sub _ _).trans (by linarith)
  · intro k
    exact randomInsertionOn_comparison_tendsto_ae M hα C H Ns hNs us hcontrol (μ k) (F k)
      (hFm k) (by positivity) (hF k)

end UniversalDictionary
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped BigOperators Topology
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    {n p N : ℕ} [NeZero N]

noncomputable def referenceD (z : InteractionSample p) : ℝ :=
  z.2.2.1*∏ l,z.2.2.2 l false

noncomputable def mixedNormalizedAvg (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (z : InteractionSample p) (sel : Fin p → Bool) (t : ℝ) : ℝ :=
  mixedLogAvg T Q U V x m z sel t-Real.log (1+t*referenceD z)

lemma mixedNormalizedAvg_bound (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ)
    (z : InteractionSample p)
    (hz : 0<z.2.1 ∧ ∀ s : Fin p → Spin,
      Real.exp (z.1 s)=z.2.1*(1+z.2.2.1*∏ l,z.2.2.2 l (s l)) ∧
      |z.2.2.1*∏ l,z.2.2.2 l (s l)|<1)
    (sel : Fin p → Bool) {t : ℝ} (ht0 : 0≤t) (ht : t<1) :
    |mixedNormalizedAvg T Q U V x m z sel t|≤2*‖z.1‖ := by
  unfold mixedNormalizedAvg mixedLogAvg
  rw [← FiniteLaw.expect_const (P := FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N))))
    (Real.log (1+t*referenceD z)),← FiniteLaw.expect_sub]
  apply FiniteLaw.abs_expect_le
  intro i
  rw [← FiniteLaw.expect_const (P := FiniteLaw.pi (fun _ : Fin p => Q)) (Real.log (1+t*referenceD z)),
    ← FiniteLaw.expect_sub]
  apply FiniteLaw.abs_expect_le
  intro r
  let P := fun w : FinitePath (Ω×(Fin p → Λ)) n => mixedSpinLaw sel
    (fun l => V (KernelTower.pathFst n w) (i l))
    (fun l => x (r l) (KernelTower.pathMap (fun a : Fin p → Λ => a l) n (KernelTower.pathSnd n w)))
  have hh := normalized_logInsertion_bound
    (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j)))) m hm P
    z.1 (fun s => z.2.2.1*∏ l,z.2.2.2 l (s l)) z.2.1 hz.1 (fun s => (hz.2 s).1)
    (fun _ => false) (fun s => (hz.2 s).2) (norm_nonneg z.1)
    (fun s => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z.1 s) ht0 ht
  simp only [P,mixedSpinLaw_factor] at hh
  convert hh using 1
  rfl

lemma mixedNormalizedAvg_limit (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hnz : ∀ j : Fin n,m j.succ≠0)
    (z : InteractionSample p)
    (hz : 0<z.2.1 ∧ ∀ s : Fin p → Spin,
      Real.exp (z.1 s)=z.2.1*(1+z.2.2.1*∏ l,z.2.2.2 l (s l)) ∧
      |z.2.2.1*∏ l,z.2.2.2 l (s l)|<1)
    (sel : Fin p → Bool) :
    Tendsto (mixedNormalizedAvg T Q U V x m z sel) (𝓝 1)
      (𝓝 (mixedEnergyAvg T Q U V x m z sel-z.1 (fun _ => false))) := by
  let I : FiniteLaw (Fin p → Fin N) := FiniteLaw.pi (fun _ => FiniteLaw.uniform)
  let P (i : Fin p → Fin N) (r : Fin p → R) (w : FinitePath (Ω×(Fin p → Λ)) n) := mixedSpinLaw sel
    (fun l => V (KernelTower.pathFst n w) (i l))
    (fun l => x (r l) (KernelTower.pathMap (fun a : Fin p → Λ => a l) n (KernelTower.pathSnd n w)))
  have hh (i : Fin p → Fin N) (r : Fin p → R) := normalized_logInsertion_limit
    (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j)))) m hnz (P i r)
    z.1 (fun s => z.2.2.1*∏ l,z.2.2.2 l (s l)) z.2.1 hz.1 (fun s => (hz.2 s).1)
    (fun _ => false) (fun s => (hz.2 s).2)
  have hl := I.tendsto_expect _ _ (fun i =>
    (FiniteLaw.pi (fun _ : Fin p => Q)).tendsto_expect _ _ (hh i))
  simp only [P,I,mixedSpinLaw_factor,FiniteLaw.expect_sub,FiniteLaw.expect_const] at hl
  convert hl using 1 <;> rfl

lemma measurable_mixedNormalizedAvg (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (sel : Fin p → Bool) (t : ℝ) :
    Measurable (fun z => mixedNormalizedAvg T Q U V x m z sel t) := by
  apply (measurable_mixedLogAvg T Q U V x m sel t).sub
  unfold referenceD
  fun_prop

lemma integrable_mixedNormalizedAvg (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ)
    (sel : Fin p → Bool) {t : ℝ} (ht0 : 0≤t) (ht : t<1) :
    Integrable (fun z => mixedNormalizedAvg T Q U V x m z sel t) M.disorder.toMeasure := by
  apply (hM.interaction_integrable.const_mul 2).mono'
    (measurable_mixedNormalizedAvg T Q U V x m sel t).aestronglyMeasurable
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs] using mixedNormalizedAvg_bound T Q U V x m hm z hz sel ht0 ht

noncomputable def regularization (k : ℕ) : ℝ := 1-1/(k+1)

lemma regularization_nonneg (k : ℕ) : 0≤regularization k := by
  unfold regularization
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  have hh : 1/((k:ℝ)+1)≤1 := (div_le_one (by positivity : (0:ℝ)<k+1)).mpr (by linarith)
  linarith
lemma regularization_lt_one (k : ℕ) : regularization k<1 := by
  unfold regularization
  have hh : (0:ℝ)<1/((k:ℝ)+1) := by positivity
  linarith
lemma regularization_limit : Tendsto regularization atTop (𝓝 1) := by
  unfold regularization
  simpa only [sub_zero] using
    (tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

lemma integral_mixedNormalizedAvg_limit (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n,0 < m j.succ) (sel : Fin p → Bool) :
    Tendsto (fun k => ∫ z,mixedNormalizedAvg T Q U V x m z sel (regularization k) ∂M.disorder.toMeasure)
      atTop (𝓝 ((∫ z,mixedEnergyAvg T Q U V x m z sel ∂M.disorder.toMeasure)-
        ∫ z,z.1 (fun _ => false) ∂M.disorder.toMeasure)) := by
  have href : Integrable (fun z : InteractionSample p => z.1 (fun _ => false)) M.disorder.toMeasure :=
    hM.interaction_integrable.mono' (by fun_prop) (ae_of_all _ (fun z => norm_le_pi_norm z.1 _))
  rw [← integral_sub (integrable_mixedEnergyAvg M hM T Q U V x m hm sel) href]
  apply tendsto_integral_of_dominated_convergence (fun z : InteractionSample p => 2*‖z.1‖)
  · intro k
    exact (measurable_mixedNormalizedAvg T Q U V x m sel _).aestronglyMeasurable
  · exact hM.interaction_integrable.const_mul 2
  · intro k
    filter_upwards [hM.factorization] with z hz
    simpa only [Real.norm_eq_abs] using mixedNormalizedAvg_bound T Q U V x m hm z hz sel
      (regularization_nonneg k) (regularization_lt_one k)
  · filter_upwards [hM.factorization] with z hz
    exact (mixedNormalizedAvg_limit T Q U V x m (fun j => ne_of_gt (hm j)) z hz sel).comp regularization_limit


/-- First-moment common-tree insertion inequality (unregularized). -/
lemma integral_mixedEnergy_combination_nonpos (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hstrict : ∀ j : Fin n,0 < m j.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) :
    (∫ z,mixedEnergyAvg T Q U V x m z (fun _ => true) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedEnergyAvg T Q U V x m z (fun l => decide (l=j)) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedEnergyAvg T Q U V x m z (fun _ => false) ∂M.disorder.toMeasure) ≤0 := by
  have hp : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by
    rw [Nat.cast_sub (by have h := hM.arity; omega : 1≤p)]; norm_num
  have hr (k : ℕ) :
      (∫ z,mixedNormalizedAvg T Q U V x m z (fun _ => true) (regularization k) ∂M.disorder.toMeasure)-
      (p:ℝ)*(∫ z,mixedNormalizedAvg T Q U V x m z (fun l => decide (l=j)) (regularization k) ∂M.disorder.toMeasure)+
      ((p-1:ℕ):ℝ)*(∫ z,mixedNormalizedAvg T Q U V x m z (fun _ => false) (regularization k) ∂M.disorder.toMeasure) ≤0 := by
    have ht0 := regularization_nonneg k
    have ht := regularization_lt_one k
    have ht' : |regularization k|<1 := by rwa [abs_of_nonneg ht0]
    have hi (sel : Fin p → Bool) := integrable_mixedLogAvg M hM T Q U V x m hm hpos (fun l => ne_of_gt (hstrict l)) hroot hend sel ht'
    have hn (sel : Fin p → Bool) := integrable_mixedNormalizedAvg M hM T Q U V x m hstrict sel ht0 ht
    have hd : Integrable (fun z => Real.log (1+regularization k*referenceD z)) M.disorder.toMeasure := by
      convert (hi (fun _ => false)).sub (hn (fun _ => false)) using 1
      funext z
      simp only [Pi.sub_apply,mixedNormalizedAvg]
      ring
    simp only [mixedNormalizedAvg]
    rw [integral_sub (hi _) hd,integral_sub (hi _) hd,integral_sub (hi _) hd]
    have hs := integral_mixedLog_combination_nonpos M hM T Q U V x m hm hpos
      (fun l => ne_of_gt (hstrict l)) hroot hend j ht0 ht
    rw [hp] at hs ⊢
    nlinarith only [hs]
  have hlim := ((integral_mixedNormalizedAvg_limit M hM T Q U V x m hstrict (fun _ => true)).sub
    ((integral_mixedNormalizedAvg_limit M hM T Q U V x m hstrict (fun l => decide (l=j))).const_mul (p:ℝ))).add
    ((integral_mixedNormalizedAvg_limit M hM T Q U V x m hstrict (fun _ => false)).const_mul ((p-1:ℕ):ℝ))
  have hs := le_of_tendsto hlim (Eventually.of_forall hr)
  rw [hp] at hs ⊢
  nlinarith only [hs]

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass
open scoped BigOperators

lemma mixedSpinLaw_single {p : ℕ} (j : Fin p) (s : Fin p → Spin) (x : Fin p → ℝ) :
    mixedSpinLaw (fun a => decide (a=j)) s x=
      mixedSpinLaw (fun a => decide (a=j)) (fun _ => s j) x := by
  unfold mixedSpinLaw
  congr 1
  funext a
  by_cases h : a=j
  · subst a; rfl
  · simp [h]

lemma mixedEnergy_single {p : ℕ} (z : InteractionSample p) (j : Fin p)
    (s : Fin p → Spin) (x : Fin p → ℝ) :
    mixedEnergy z (fun a => decide (a=j)) s x=
      mixedEnergy z (fun a => decide (a=j)) (fun _ => s j) x := by
  unfold mixedEnergy
  rw [mixedSpinLaw_single]

lemma mixedEnergy_last {q : ℕ} (z : InteractionSample (q+1))
    (s : Fin (q+1) → Spin) (x : Fin (q+1) → ℝ) :
    mixedEnergy z (fun a => decide (a=Fin.last q)) s x=
      message z.1 (fun i => x i.castSucc) (s (Fin.last q)) := by
  classical
  unfold mixedEnergy mixedSpinLaw FiniteLaw.logMean FiniteLaw.expMoment
  simp only [one_mul,div_one]
  apply congrArg Real.log
  unfold FiniteLaw.expect FiniteLaw.pi
  rw [← (Fin.snocEquiv (fun _ : Fin (q+1) => Spin)).sum_comp]
  simp only [Fintype.sum_prod_type,Fin.snocEquiv_apply,Fin.prod_univ_castSucc,
    Fin.snoc_castSucc,Fin.snoc_last,Fin.castSucc_ne_last,decide_false,Bool.false_eq_true,
    ↓reduceIte,decide_true,FiniteLaw.point]
  simp only [Finset.sum_ite_irrel,mul_ite,ite_mul,zero_mul,mul_zero,mul_one,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  have he : (Fin.snocEquiv (fun _ : Fin (q+1) => Spin)) (s (Fin.last q),a)=
      appendSpin (p := q+1) a (s (Fin.last q)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snocEquiv_apply,Fin.snoc_last] using (appendSpin_last a (s (Fin.last q))).symm
    · simpa only [Fin.snocEquiv_apply,Fin.snoc_castSucc] using (appendSpin_castSucc a (s (Fin.last q)) j).symm
  simp only [he,qLaw,mul_comm]
  rfl

end DilutedSpinGlass

end

end OAI
