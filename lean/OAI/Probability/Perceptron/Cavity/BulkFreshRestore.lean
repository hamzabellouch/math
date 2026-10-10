import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkModel
import OAI.Probability.Perceptron.Variational.GibbsRestoration

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

def bulkSeparateLast (N M : ℕ) (a : BulkDisorder N (M+1)) :
    BulkDisorder N M × EuclideanSpace ℝ (Fin N) :=
  ((fun i => a.1 i.castSucc,a.2),WithLp.toLp 2 (a.1 (Fin.last M)))

lemma bulkSeparateLast_preserving (N M : ℕ) :
    MeasurePreserving (bulkSeparateLast N M) (bulkDisorderLaw N (M+1))
      ((bulkDisorderLaw N M).prod (stdGaussian (EuclideanSpace ℝ (Fin N)))) := by
  let ρ : Measure (Fin N→ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let R := finitePatternRowsLaw N M
  let G := stdGaussian (EuclideanSpace ℝ (Fin N))
  let B := stdGaussian (BulkMark N)
  have hrow : MeasurePreserving (WithLp.toLp 2 : (Fin N→ℝ)→EuclideanSpace ℝ (Fin N)) ρ G :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hp := (((MeasurePreserving.id R).prod hrow).comp
    (Measure.measurePreserving_swap (μ:=ρ) (ν:=R))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (M+1) => ρ) (Fin.last M))
  have hr : MeasurePreserving (fun a : ((Fin M→Fin N→ℝ)×EuclideanSpace ℝ (Fin N))×BulkMark N =>
      ((a.1.1,a.2),a.1.2)) ((R.prod G).prod B) ((R.prod B).prod G) :=
    (measurePreserving_prodAssoc R B G).symm.comp
      (((MeasurePreserving.id R).prod (Measure.measurePreserving_swap (μ:=G) (ν:=B))).comp
        (measurePreserving_prodAssoc R G B))
  convert hr.comp (hp.prod (MeasurePreserving.id B)) using 1
  · funext a
    simp only [bulkSeparateLast,Function.comp_def,MeasurableEquiv.piFinSuccAbove_apply]
    apply Prod.ext
    · apply Prod.ext
      · funext i j; simp [Fin.init]
      · rfl
    · rfl
  · rfl
  · rfl

lemma bulkHamiltonian_last (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder N (M+1)) (x : NormalizedSpin N) :
    bulkHamiltonian N (M+1) f v a.1 a.2 x =
      bulkHamiltonian N M f v (bulkSeparateLast N M a).1.1 (bulkSeparateLast N M a).1.2 x+
        f (inner ℝ x.val (bulkSeparateLast N M a).2) := by
  unfold bulkHamiltonian normalizedPatternEnergy
  rw [Fin.sum_univ_castSucc]
  simp only [bulkSeparateLast,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  ring

lemma bulk_replica_restore_last (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) (M+1)) (r : ℕ) (F : (Fin r→NormalizedSpin (n+1))→ℝ) :
    gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) (M+1) f v a.1 a.2) r F =
      gibbsReplicaMean (unitSphereLaw (n+1))
        (bulkHamiltonian (n+1) M f v (bulkSeparateLast (n+1) M a).1.1 (bulkSeparateLast (n+1) M a).1.2) r
        (fun x => (∏ i, Real.exp (f (inner ℝ (x i).val (bulkSeparateLast (n+1) M a).2)))*F x) /
      (tiltMean (unitSphereLaw (n+1))
        (bulkHamiltonian (n+1) M f v (bulkSeparateLast (n+1) M a).1.1 (bulkSeparateLast (n+1) M a).1.2)
        (fun x => Real.exp (f (inner ℝ x.val (bulkSeparateLast (n+1) M a).2))) 1)^r := by
  rw [show bulkHamiltonian (n+1) (M+1) f v a.1 a.2 = _ from
    funext (bulkHamiltonian_last (n+1) M f v a)]
  exact gibbsReplicaMean_restore _
    ((bulkHamiltonian_continuous _ _ _ _).measurable.comp (measurable_const.prodMk measurable_id))
    (bulkHamiltonian_exp_integrable n M f v _) r F

lemma bulk_restoration_denominator_bounds (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) (z : EuclideanSpace ℝ (Fin (n+1))) :
    Real.exp (-‖f‖) ≤ tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2)
      (fun x => Real.exp (f (inner ℝ x.val z))) 1 ∧
    tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2)
      (fun x => Real.exp (f (inner ℝ x.val z))) 1 ≤ Real.exp ‖f‖ :=
  tiltMean_exp_bounds _
    ((bulkHamiltonian_continuous _ _ _ _).measurable.comp (measurable_const.prodMk measurable_id))
    (f.measurable.comp (measurable_subtype_coe.inner measurable_const))
    (bulkHamiltonian_exp_integrable n M f v a) (norm_nonneg _) (fun _ => f.norm_coe_le_norm _)

def bulkSeparateTwo (N M : ℕ) (a : BulkDisorder N (M+2)) :
    BulkDisorder N M × (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) :=
  let b := bulkSeparateLast N (M+1) a
  let c := bulkSeparateLast N M b.1
  (c.1,(c.2,b.2))

lemma bulkSeparateTwo_preserving (N M : ℕ) :
    MeasurePreserving (bulkSeparateTwo N M) (bulkDisorderLaw N (M+2))
      ((bulkDisorderLaw N M).prod
        ((stdGaussian (EuclideanSpace ℝ (Fin N))).prod (stdGaussian (EuclideanSpace ℝ (Fin N))))) := by
  exact (measurePreserving_prodAssoc _ _ _).comp
    (((bulkSeparateLast_preserving N M).prod (MeasurePreserving.id _)).comp
      (bulkSeparateLast_preserving N (M+1)))

lemma bulkHamiltonian_two (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder N (M+2)) (x : NormalizedSpin N) :
    bulkHamiltonian N (M+2) f v a.1 a.2 x =
      bulkHamiltonian N M f v (bulkSeparateTwo N M a).1.1 (bulkSeparateTwo N M a).1.2 x+
        (f (inner ℝ x.val (bulkSeparateTwo N M a).2.1)+
         f (inner ℝ x.val (bulkSeparateTwo N M a).2.2)) := by
  rw [bulkHamiltonian_last N (M+1),bulkHamiltonian_last N M]
  exact add_assoc _ _ _

lemma bulk_replica_restore_two (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) (M+2)) (r : ℕ) (F : (Fin r→NormalizedSpin (n+1))→ℝ) :
    gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) (M+2) f v a.1 a.2) r F =
      gibbsReplicaMean (unitSphereLaw (n+1))
        (bulkHamiltonian (n+1) M f v (bulkSeparateTwo (n+1) M a).1.1 (bulkSeparateTwo (n+1) M a).1.2) r
        (fun x => (∏ i, Real.exp (f (inner ℝ (x i).val (bulkSeparateTwo (n+1) M a).2.1)+
          f (inner ℝ (x i).val (bulkSeparateTwo (n+1) M a).2.2)))*F x) /
      (tiltMean (unitSphereLaw (n+1))
        (bulkHamiltonian (n+1) M f v (bulkSeparateTwo (n+1) M a).1.1 (bulkSeparateTwo (n+1) M a).1.2)
        (fun x => Real.exp (f (inner ℝ x.val (bulkSeparateTwo (n+1) M a).2.1)+
          f (inner ℝ x.val (bulkSeparateTwo (n+1) M a).2.2))) 1)^r := by
  rw [show bulkHamiltonian (n+1) (M+2) f v a.1 a.2 = _ from
    funext (bulkHamiltonian_two (n+1) M f v a)]
  exact gibbsReplicaMean_restore _
    ((bulkHamiltonian_continuous _ _ _ _).measurable.comp (measurable_const.prodMk measurable_id))
    (bulkHamiltonian_exp_integrable n M f v _) r F

lemma bulk_two_denominator_bounds (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) (z t : EuclideanSpace ℝ (Fin (n+1))) :
    Real.exp (-(2*‖f‖)) ≤ tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2)
      (fun x => Real.exp (f (inner ℝ x.val z)+f (inner ℝ x.val t))) 1 ∧
    tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2)
      (fun x => Real.exp (f (inner ℝ x.val z)+f (inner ℝ x.val t))) 1 ≤ Real.exp (2*‖f‖) := by
  apply tiltMean_exp_bounds _
    ((bulkHamiltonian_continuous _ _ _ _).measurable.comp (measurable_const.prodMk measurable_id))
    ((f.measurable.comp (measurable_subtype_coe.inner measurable_const)).add
      (f.measurable.comp (measurable_subtype_coe.inner measurable_const)))
    (bulkHamiltonian_exp_integrable n M f v a) (by positivity)
  intro x
  exact (abs_add_le _ _).trans ((add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)).trans_eq
    (two_mul ‖f‖).symm)

def bulkPermutePatterns (N M : ℕ) (e : Equiv.Perm (Fin M))
    (a : BulkDisorder N M) : BulkDisorder N M := (fun i => a.1 (e i),a.2)

lemma bulkPermutePatterns_preserving (N M : ℕ) (e : Equiv.Perm (Fin M)) :
    MeasurePreserving (bulkPermutePatterns N M e) (bulkDisorderLaw N M) (bulkDisorderLaw N M) := by
  have h := (measurePreserving_piCongrLeft
    (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1)) e.symm).prod
    (MeasurePreserving.id (stdGaussian (BulkMark N)))
  convert h using 1
  · funext a
    apply Prod.ext
    · funext i
      have he := MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _ : Fin M => Fin N→ℝ) e.symm a.1 (e i)
      change a.1 (e i) = (MeasurableEquiv.piCongrLeft (fun _ : Fin M => Fin N→ℝ) e.symm) a.1 i
      simpa only [Equiv.symm_apply_apply] using he.symm
    · rfl
  · rfl
  · rfl

lemma bulkHamiltonian_permute (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (e : Equiv.Perm (Fin M)) (a : BulkDisorder N M) :
    bulkHamiltonian N M f v (bulkPermutePatterns N M e a).1 (bulkPermutePatterns N M e a).2 =
      bulkHamiltonian N M f v a.1 a.2 := by
  funext x
  unfold bulkHamiltonian normalizedPatternEnergy bulkPermutePatterns
  congr 1
  exact Equiv.sum_comp e (fun j => f (∑ i, a.1 j i*x.val i))

def bulkReplicaMean (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (F : BulkDisorder (n+1) M → (Fin r→NormalizedSpin (n+1))→ℝ) : ℝ :=
  ∫ a, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (F a)
    ∂bulkDisorderLaw (n+1) M

lemma bulkReplicaMean_permute (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (e : Equiv.Perm (Fin M))
    (F : BulkDisorder (n+1) M → (Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) :
    bulkReplicaMean n M f v r (fun a => F (bulkPermutePatterns (n+1) M e a)) =
      bulkReplicaMean n M f v r F := by
  have hm := kernel_replicaMean_measurable (bulkSpinKernel n M)
    (H:=fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (bulkHamiltonian_continuous (n+1) M f v).measurable hF
  have h := integral_map (μ:=bulkDisorderLaw (n+1) M) (bulkPermutePatterns_preserving (n+1) M e).measurable.aemeasurable
    hm.aestronglyMeasurable
  rw [(bulkPermutePatterns_preserving (n+1) M e).map_eq] at h
  change (∫ a, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (F a) ∂bulkDisorderLaw (n+1) M) = _ at h
  unfold bulkReplicaMean
  rw [h]
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    change gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r _ =
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v (bulkPermutePatterns (n+1) M e a).1 (bulkPermutePatterns (n+1) M e a).2) r _
    rw [bulkHamiltonian_permute]

def bulkPatternFields {N M r : ℕ} (j : Fin M) (a : BulkDisorder N M)
    (x : Fin r→NormalizedSpin N) : Fin r→ℝ := fun i => ∑ t, a.1 j t*(x i).val t

lemma bulkPatternFields_measurable (N M r : ℕ) (j : Fin M) :
    Measurable (Function.uncurry (bulkPatternFields (N:=N) (r:=r) j)) := by
  have hc : Continuous (Function.uncurry (bulkPatternFields (N:=N) (r:=r) j)) := by
    unfold bulkPatternFields Function.uncurry
    fun_prop
  exact hc.measurable

lemma bulk_row_exchange (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (G : (Fin r→NormalizedSpin (n+1))→ℝ) (hG : Measurable G)
    (T : (Fin r→ℝ)→ℝ) (hT : Measurable T) (i j : Fin M) :
    bulkReplicaMean n M f v r (fun a x => G x*T (bulkPatternFields i a x)) =
      bulkReplicaMean n M f v r (fun a x => G x*T (bulkPatternFields j a x)) := by
  classical
  have hm : Measurable (Function.uncurry (fun a x => G x*T (bulkPatternFields j a x))) :=
    (hG.comp measurable_snd).mul (hT.comp (bulkPatternFields_measurable _ _ _ _))
  have h := bulkReplicaMean_permute n M f v r (Equiv.swap i j) _ hm
  have hf : (fun a x => G x*T (bulkPatternFields j (bulkPermutePatterns (n+1) M (Equiv.swap i j) a) x)) =
      (fun a x => G x*T (bulkPatternFields i a x)) := by
    funext a x
    change G x*T (fun l => ∑ t, a.1 ((Equiv.swap i j) j) t*(x l).val t) =
      G x*T (fun l => ∑ t, a.1 i t*(x l).val t)
    rw [Equiv.swap_apply_right]
  rw [hf] at h
  exact h

end SphericalPerceptronFreeEnergy
end

end OAI
