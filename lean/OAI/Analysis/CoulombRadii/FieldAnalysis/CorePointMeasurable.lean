import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PatchRawTransfer
import OAI.Analysis.CoulombRadii.ThomasFermi.TFPotentialParameter

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma potentialForm_coreSlice_point_aestronglyMeasurable {m k : ℕ}
    (u : H1Vector (m+k)) (s : Spins m)
    (W : Configuration m × Configuration k → ℝ) (hW : Measurable W) :
    AEStronglyMeasurable (fun x => potentialForm (fun v => W (x,v)) (u.coreSlice s x)) volume := by
  apply AEStronglyMeasurable.congr _
    (show (fun x => ∑ t : Spins k, ∫ v, W (x,v)*
      ‖u.value (Fin.append s t) (joinConfiguration m k (x,v))‖^2) =ᵐ[volume]
      (fun x => potentialForm (fun v => W (x,v)) (u.coreSlice s x)) from ?_)
  · apply Finset.aestronglyMeasurable_fun_sum
    intro t ht
    have hψ := ((u.value_L2 (Fin.append s t)).aestronglyMeasurable.comp_measurePreserving
      (joinConfiguration_measurePreserving m k)).norm.pow 2
    exact (hW.aestronglyMeasurable.mul hψ).integral_prod_right'
  · filter_upwards [u.coreSliceRegular_ae s] with x hx
    simp only [potentialForm,u.coreSlice_value s hx]

lemma coreScreenedField_slice_point_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) (y : Space) :
    AEStronglyMeasurable (fun x => coreScreenedField S (u.coreSlice s x).normalized y) volume := by
  have hw : Measurable (fun z : Configuration m × Configuration k => restrictedOutPotential z.2 Set.univ y) := by
    apply Finset.measurable_fun_sum
    intro i hi
    simp only [Set.mem_univ,ite_true,coulombKernel]
    exact (((continuous_position i).measurable.comp measurable_snd).sub measurable_const).norm.inv
  have H := potentialForm_coreSlice_point_aestronglyMeasurable u s _ hw
  have H' : AEStronglyMeasurable (fun x : Configuration m =>
      (mass (u.coreSlice s x))⁻¹*potentialForm (fun v => restrictedOutPotential v Set.univ y)
        (u.coreSlice s x)) volume :=
    (mass_coreSlice_integrable u s).aestronglyMeasurable.inv₀.mul H
  have H'' : AEStronglyMeasurable (fun x => coreCoulombPotential (u.coreSlice s x).normalized y) volume := by
    apply H'.congr
    filter_upwards [] with x
    symm
    rw [←potentialForm_normalized_eq,potentialForm_restrictedOutPotential _ MeasurableSet.univ]
    simp only [restrictedCorePotential,Set.mem_univ,ite_true,coreCoulombPotential]
  exact aestronglyMeasurable_const.sub H''

lemma patchTFScreenedField_slice_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) {a b t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t≤6*a) (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖) (z : Space) :
    AEStronglyMeasurable (fun x => patchTFScreenedField S (u.coreSlice s x).normalized ha hb ht y hn z) volume := by
  exact (coreScreenedField_slice_point_aestronglyMeasurable S u s z).sub
    (aestronglyMeasurable_localTFPotential measurableSet_ball _
      (coreTFField_slice_aestronglyMeasurable S u s measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht y hn)) z)

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma ae_position_ne (n : ℕ) (y : Space) : ∀ᵐ x : Configuration n,∀ i,position x i≠y := by
  rw [ae_all_iff]
  intro i
  let L : Configuration n →ₗ[ℝ] ℝ :=
    { toFun := fun x => x (i,0)
      map_add' := by intro x z; rfl
      map_smul' := by intro c x; rfl }
  have hL : LinearMap.ker L≠⊤ := by
    intro h
    have hh : EuclideanSpace.single (i,0) (1:ℝ)∈LinearMap.ker L := by rw [h]; trivial
    change (EuclideanSpace.single (i,0) (1:ℝ)) (i,0)=0 at hh
    simp at hh
  let v : Configuration n := EuclideanSpace.single (i,0) (y 0)
  have hv : v (i,0)=y 0 := by simp [v]
  have hz := Measure.addHaar_submodule (volume : Measure (Configuration n)) (LinearMap.ker L) hL
  have hnull : (volume : Measure (Configuration n)) {x | position x i=y}=0 := by
    apply measure_mono_null (t := (fun x : Configuration n => x+(-v)) ⁻¹' (LinearMap.ker L : Set (Configuration n)))
    · intro x hx
      change (x+(-v)) (i,0)=0
      simp only [PiLp.add_apply,PiLp.neg_apply,hv]
      have hs := congrArg (fun z : Space => z 0) hx
      change x (i,0)=y 0 at hs
      rw [hs,add_neg_cancel]
    · rw [measure_preimage_add_right,hz]
  rw [ae_iff]
  simpa only [not_not] using hnull

def patchFieldTransferError {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (s : Spins m) (x : Configuration m) : ℝ :=
  (coreScreenedField S (u.coreSlice s x).normalized y-nuclearPotential (unitNucleus y) x)-
    patchTFScreenedField S (u.coreSlice s x).normalized ha hb ht y hn y

lemma patchFieldTransferError_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (s : Spins m) :
    AEStronglyMeasurable (patchFieldTransferError S u ha hb ht y hn s) volume := by
  have hnuc : Measurable (nuclearPotential (n := m) (unitNucleus y)) :=
    Finset.measurable_sum _ (fun i _ => (attraction_measurable _).comp (continuous_position i).measurable)
  exact ((coreScreenedField_slice_point_aestronglyMeasurable S u s y).sub hnuc.aestronglyMeasurable).sub
    (patchTFScreenedField_slice_aestronglyMeasurable S u s ha hb ht y hn y)

def patchTransferRemainder {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (r ε : ℝ) (s : Spins m) (x : Configuration m) : ℝ :=
  ε+(5/(4*r*ε))*patchSliceTFGap S u ha hb ht y hn s x+
    nearPotential y (r+2*b) x+nearPotential y (2*b) x+
    localCount {z | t-7*b≤‖z-y‖} x/a+
    ((tfInteriorConstant thomasFermiKineticConstant/
      (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2)

lemma patchTransferRemainder_weight_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (r ε : ℝ) (s : Spins m)
    (hcs : ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    Integrable (fun x => mass (u.coreSlice s x)*patchTransferRemainder S u ha hb ht y hn r ε s x) := by
  have hgap := (patchSliceTFGap_weight_integrable S u ha hb ht y hn s hcs).const_mul (5/(4*r*ε))
  have hnear (R : ℝ) := slice_weight_integrable_const u (nearPotential y R)
    (nearPotential_outer_integrable u y R) s
  have hcount := (sliceCount_weight_integrable u (A := {z | t-7*b≤‖z-y‖})
    (isClosed_le continuous_const (by fun_prop : Continuous (fun z : Space => ‖z-y‖))).measurableSet s 1).div_const a
  simp only [pow_one] at hcount
  have hε := (mass_coreSlice_integrable u s).mul_const ε
  have hC := (mass_coreSlice_integrable u s).mul_const
    (((tfInteriorConstant thomasFermiKineticConstant/
      (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2))
  apply (((((hε.add hgap).add (hnear (r+2*b))).add (hnear (2*b))).add hcount).add hC).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.add_apply]; unfold patchTransferRemainder; ring)

lemma patchFieldTransferError_ae_bound {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0<r) (hra : r≤a) (hε : 0<ε) (s : Spins m)
    (hcs : ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    ∀ᵐ x, |patchFieldTransferError S u ha hb ht.2 y hn s x|≤
      patchTransferRemainder S u ha hb ht.2 y hn r ε s x := by
  filter_upwards [ae_position_ne m y,hcs] with x hxy hcore
  have hh := patch_raw_field_transfer S u ha hb hsmall ht y hn hr hra s x hcore hxy
  have hyoung := sqrt_young ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn s x)
    (mul_nonneg (by positivity) (patchSliceTFGap_nonneg S u ha hb ht.2 y hn s x)) hε
  have he : ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn s x)/(4*ε)=
      (5/(4*r*ε))*patchSliceTFGap S u ha hb ht.2 y hn s x := by ring
  rw [he] at hyoung
  rw [deletedLabels_patchRetained] at hh
  change |_ - _|≤_
  unfold patchTransferRemainder
  linarith

theorem patchFieldTransferError_integrable_mean {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0<r) (hra : r≤a) (hε : 0<ε)
    (hcs : ∀ s, ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    (∀ s, Integrable (fun x => mass (u.coreSlice s x)*patchFieldTransferError S u ha hb ht.2 y hn s x)) ∧
    |sliceExpectation u (patchFieldTransferError S u ha hb ht.2 y hn)|≤
      sliceExpectation u (patchTransferRemainder S u ha hb ht.2 y hn r ε) := by
  have hR := fun s => patchTransferRemainder_weight_integrable S u ha hb ht.2 y hn r ε s (hcs s)
  have hB := fun s => patchFieldTransferError_ae_bound S u ha hb hsmall ht y hn hr hra hε s (hcs s)
  have hI (s) : Integrable (fun x => mass (u.coreSlice s x)*patchFieldTransferError S u ha hb ht.2 y hn s x) := by
    apply (hR s).mono' ((mass_coreSlice_integrable u s).aestronglyMeasurable.mul
      (patchFieldTransferError_aestronglyMeasurable S u ha hb ht.2 y hn s))
    filter_upwards [hB s] with x hx
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (mass_nonneg _)]
    exact mul_le_mul_of_nonneg_left hx (mass_nonneg _)
  refine ⟨hI,?_⟩
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro s _
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_ae (hI s).abs (hR s)
  filter_upwards [hB s] with x hx
  rw [abs_mul,abs_of_nonneg (mass_nonneg _)]
  exact mul_le_mul_of_nonneg_left hx (mass_nonneg _)
end Coulomb

end

end OAI
