import OAI.Probability.DilutedSpin.FirstMomentUpper

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
lemma integral_root_prod_finite_integrable {X J : Type} [MeasurableSpace X]
    [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ)
    (F : (Fin n → X) × (Fin n → J) → ℝ) (_hF : Measurable F)
    (hi : Integrable F ((Measure.pi (fun _ : Fin n => μ)).prod
      (Measure.pi (fun _ : Fin n => finiteUniform J)))) :
    (∫ z : RootPath (X×J) n,F ((fun i => (rootArray n z i).1),(fun i => (rootArray n z i).2))
      ∂rootLaw n (fun _ => μ.prod (finiteUniform J))) =
      ∫ x : Fin n → X,(FiniteLaw.uniform : FiniteLaw (Fin n → J)).expect (fun j => F (x,j))
        ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_root_prod μ (finiteUniform J) n F hi]
  simp only [finiteUniform_pi]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_finiteUniform,FiniteLaw.expect_uniform]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]
namespace PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]
omit [MeasurableSingletonClass R] in
lemma upperCountMean_real_firstMoment (M : Model p) (hM : Admissible M) (T : KernelTower Ω n) (Q : FiniteLaw R)
    (U : R → KernelTower Λ n) (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (m : Fin n → ℝ) (hm : ∀ d,0 < m d)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k : ℕ) :
    upperCountMean M T Q U V x m j f k 0 =
      ∫ z : Fin k → InteractionSample p,
       (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
        (fun i => backwardLog n T m (fun y => f y+∑ a,(z a).1 (fun b => V y (i a b))))
          ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  let F : RootPath (InteractionSample p × (Fin p → Fin N)) k → ℝ := fun z =>
    backwardLog n T m (fun y => f y+∑ a,(rootArray k z a).1.1 (fun b => V y ((rootArray k z a).2 b)))
  have hFm : Measurable F := by
    apply measurable_backwardLog
    intro y
    apply measurable_const.add
    apply Finset.measurable_sum
    intro a _
    exact (measurable_pi_apply (V y)).comp ((PhysicalRoot.measurable_indexedPotential (fun x : InteractionSample p => x)
      (fun σ => (measurable_pi_apply σ).comp measurable_fst)).comp (measurable_rootArray k a))
  have he : upperCountMean M T Q U V x m j f k 0 =
      ∫ z,F (rootMap (fun a : UpperDatum p N R => (a.1,a.2.1)) k z)
        ∂rootLaw k (fun _ => upperDatumLaw M Q) := by
    let : IsProbabilityMeasure (rootLaw 0 (fun _ : Fin 0 => upperDatumLaw (N := N) M Q)) := Measure.dirac.isProbabilityMeasure
    unfold upperCountMean
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [datumRoot,cavityRoot,cavityTower,cavityEnergy,realCountEnergy,
      rootArray_rootMap,F]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
    rfl
  rw [he,integral_rootMap (upperDatum_real_projection M Q) k F hFm]
  apply integral_root_prod_finite_integrable M.disorder.toMeasure k
    (fun z : (Fin k → InteractionSample p) × (Fin k → Fin p → Fin N) => backwardLog n T m (fun y => f y+∑ a,(z.1 a).1 (fun b => V y (z.2 a b))))
  · apply measurable_from_prod_countable_left
    intro i
    apply measurable_backwardLog
    intro y
    change Measurable (fun z : Fin k → InteractionSample p => f y+∑ a,(z a).1 (fun b => V y (i a b)))
    exact measurable_const.add (Finset.measurable_sum _ (fun a _ =>
      (measurable_pi_apply _).comp (measurable_fst.comp (measurable_pi_apply a))))
  · apply ((integrable_const ‖f‖).add ((integrable_finsetSum Finset.univ
        (fun (a : Fin k) _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) (i := a)
          hM.interaction_integrable)).comp_fst (Measure.pi (fun _ : Fin k => finiteUniform (Fin p → Fin N))))).mono'
    · apply Measurable.aestronglyMeasurable
      apply measurable_from_prod_countable_left
      intro i
      apply measurable_backwardLog
      intro y
      change Measurable (fun z : Fin k → InteractionSample p => f y+∑ a,(z a).1 (fun b => V y (i a b)))
      exact measurable_const.add (Finset.measurable_sum _ (fun a _ =>
        (measurable_pi_apply _).comp (measurable_fst.comp (measurable_pi_apply a))))
    · exact ae_of_all _ (fun z => backwardLog_bound n T m hm (fun y =>
        (abs_add_le _ _).trans (add_le_add (norm_le_pi_norm f y)
          ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum (fun a _ => norm_le_pi_norm (z.1 a).1 _))))))

end PrescribedTree
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

lemma integral_upperDatumLaw_integrable (M : Model p) (Q : FiniteLaw R)
    (g : UpperDatum p N R → ℝ) (hg : Measurable g) (hi : Integrable g (upperDatumLaw M Q)) :
    (∫ a,g a ∂upperDatumLaw M Q) =
      ∫ z,(FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
        (fun i => (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r => g (z,i,r))) ∂M.disorder.toMeasure := by
  rw [upperDatumLaw,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with z
  have hiz : Integrable (fun a : (Fin p → Fin N) × (Fin p → R) => g (z,a))
      (((FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).asProbability id).toMeasure.prod
        ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) :=
    Integrable.of_bound (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      ‖fun a : (Fin p → Fin N) × (Fin p → R) => g (z,a)‖
      (ae_of_all _ (fun a => norm_le_pi_norm (fun a => g (z,a)) a))
  rw [integral_prod _ hiz]
  rw [FiniteLaw.integral_asProbability]
  apply FiniteLaw.expect_congr
  intro i
  exact FiniteLaw.integral_asProbability _ _ _

lemma freshRoot_mean_sub_firstMoment (M : Model p) (hM : Admissible M)
    (Q : FiniteLaw R) (T : KernelTower Ω n)
    (U : R → KernelTower Λ n) (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (m : Fin (n+1) → ℝ) (hm : ∀ d : Fin n,0 < m d.succ)
    (f : FinitePath Ω n → ℝ) (sel : Fin p → Bool) {B : ℝ}
    (hf : ∀ y,|f y|≤B) :
    (∫ a,freshRoot T U V x (fun d => m d.succ) f sel a ∂upperDatumLaw M Q)-
      backwardLog n T (fun d => m d.succ) f =
      ∫ θ,mixedRootIncrement T Q U V x m f θ sel ∂M.disorder.toMeasure := by
  let g := freshRoot T U V x (fun d => m d.succ) f sel
  have hg := measurable_freshRoot T U V x (fun d => m d.succ) f sel
  have hb (a : InteractionSample p) (i : Fin p → Fin N) (r : Fin p → R) : |g (a,i,r)|≤B+‖a.1‖ :=
    freshRoot_bound T U V x _ hm f sel (a,i,r) hf
  have hi : Integrable g (upperDatumLaw M Q) := by
    apply ((integrable_const B).add (upperDatum_integrable_norm M hM Q)).mono' hg.aestronglyMeasurable
    exact ae_of_all _ (fun a => hb a.1 a.2.1 a.2.2)
  rw [integral_upperDatumLaw_integrable M Q g hg hi]
  let G := fun θ => (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
    (fun i => (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r => g (θ,i,r)))
  have hG : Measurable G := FiniteLaw.measurable_expect _ (fun i =>
    FiniteLaw.measurable_expect _ (fun r => hg.comp (measurable_id.prodMk measurable_const)))
  have hiG : Integrable G M.disorder.toMeasure := by
    apply ((integrable_const B).add hM.interaction_integrable).mono' hG.aestronglyMeasurable
    exact ae_of_all _ (fun a => FiniteLaw.abs_expect_le _ (fun i => FiniteLaw.abs_expect_le _ (hb a i)))
  change (∫ θ,G θ ∂M.disorder.toMeasure)-_=_
  have hc : backwardLog n T (fun d => m d.succ) f =
      ∫ _θ : InteractionSample p, backwardLog n T (fun d => m d.succ) f ∂M.disorder.toMeasure := by simp
  rw [hc,← integral_sub hiG (integrable_const _)]
  apply integral_congr_ae
  filter_upwards [] with θ
  simp only [mixedRootIncrement,FiniteLaw.expect_sub,FiniteLaw.expect_const]
  rfl

lemma freshRoot_replacement_firstMoment (M : Model p) (hM : Admissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (f : FinitePath Ω n → ℝ) (j : Fin p) {B : ℝ}
    (hf : ∀ y,|f y|≤B) :
    (∫ a,freshRoot T U V x (fun d => m d.succ) f (fun _ => true) a ∂upperDatumLaw M Q)+
      ((p-1:ℕ):ℝ)*backwardLog n T (fun d => m d.succ) f ≤
      (p:ℝ)*(∫ a,freshRoot T U V x (fun d => m d.succ) f (fun d => decide (d=j)) a ∂upperDatumLaw M Q)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  have h := integral_mixedRoot_combination_nonpos M hM T Q U V x m hm hpos hstrict hroot hend f j
  simp_rw [mixedRootIncrement_false] at h
  rw [← freshRoot_mean_sub_firstMoment M hM Q T U V x m hstrict f (fun _ => true) hf,
    ← freshRoot_mean_sub_firstMoment M hM Q T U V x m hstrict f (fun d => decide (d=j)) hf] at h
  have hp : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by have := hM.arity; omega : 1≤p),Nat.cast_one]
  rw [hp] at h ⊢
  nlinarith

end DilutedSpinGlass.PrescribedTree

end

end OAI
