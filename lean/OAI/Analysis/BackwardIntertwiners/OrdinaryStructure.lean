import OAI.Analysis.BackwardIntertwiners.ErgodicTransitivity

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal


def globalTail (h : ℤ) : Submodule ℂ GlobalHilbert :=
  ⨅ j : ℤ, ⨅ _ : j < h, (coordinateL2 j).ker
lemma mem_globalTail (h : ℤ) (f : GlobalHilbert) :
    f ∈ globalTail h ↔ ∀ᵐ x ∂baseMeasure, f x ∈ coordinateTail h := by
  simp only [globalTail, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hf
    have h (j : ℤ) : ∀ᵐ x ∂baseMeasure, j < h → f x j = 0 := by
      by_cases hj : j < h
      · have hh := (Lp.eq_zero_iff_ae_eq_zero.mp (hf j hj))
        filter_upwards [coordinateL2_ae j f, hh] with x hx hzero
        intro _
        exact hx.symm.trans hzero
      · exact Filter.Eventually.of_forall fun _ => fun h => False.elim (hj h)
    exact ae_all_iff.mpr h
  · intro hf j hj
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hf, coordinateL2_ae j f] with x hx hcoord
    exact hcoord.trans (hx j hj)
lemma globalTail_closed (h : ℤ) : IsClosed (globalTail h : Set GlobalHilbert) := by
  have he : (globalTail h : Set GlobalHilbert) = ⋂ j : ℤ, ⋂ _ : j < h,
      {f : GlobalHilbert | coordinateL2 j f = 0} := by ext; simp [globalTail]
  rw [he]
  exact isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (coordinateL2 j).continuous continuous_const
lemma constantBasis_mem_globalTail {h j : ℤ} (hj : h ≤ j) : constantBasis j ∈ globalTail h := by
  rw [mem_globalTail]
  filter_upwards [constantBasis_ae j] with x hx
  rw [hx]
  exact single_mem_coordinateTail hj 1
lemma constantBasis_not_mem_globalTail {h j : ℤ} (hj : j < h) : constantBasis j ∉ globalTail h := by
  intro hm
  have hh := (mem_globalTail h _).mp hm
  have hz : ∀ᵐ x ∂baseMeasure, (1:ℂ) = 0 := by
    filter_upwards [hh, constantBasis_ae j] with x hx he
    simpa only [he, lp.single_apply_self] using hx j hj
  exact one_ne_zero hz.exists.choose_spec
lemma globalTail_nonzero (h : ℤ) : globalTail h ≠ ⊥ := by
  intro he
  have hmem := constantBasis_mem_globalTail (le_refl h)
  rw [he] at hmem
  have hm : constantBasis h = 0 := hmem
  have hn := constantBasis_norm h
  rw [hm, norm_zero] at hn
  norm_num at hn
lemma globalTail_proper (h : ℤ) : globalTail h ≠ ⊤ := by
  intro he
  apply constantBasis_not_mem_globalTail (show h-1<h by omega)
  rw [he]; trivial
lemma globalTail_forward (h : ℤ) : OperatorInvariant (globalTail h) forwardOperator := by
  intro f hf
  rw [mem_globalTail] at hf ⊢
  filter_upwards [hf, forwardOperator_ae f] with x hx he
  rw [he]
  exact forwardFiber_tail x h hx
lemma globalTail_not_backward (h : ℤ) : ¬OperatorInvariant (globalTail h) backwardOperator := by
  intro hinv
  have hm := (mem_globalTail h _).mp (hinv _ (constantBasis_mem_globalTail (le_refl h)))
  have hgood := inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae.eventually ae_goodBase
  have he := (constantBasis_ae h).comp_tendsto inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae
  have hh : ∀ᵐ x ∂baseMeasure, False := by
    filter_upwards [hm, backwardOperator_ae_inverse (constantBasis h), he, hgood] with x hx hV h₀ hg
    dsimp only [Function.comp_def] at h₀
    have hz := hx (h-1) (by omega)
    rw [hV, backwardFiber_apply, sub_add_cancel, h₀, lp.single_apply_self, mul_one] at hz
    exact (ne_of_gt (backwardCoeff_pos hg h)) (Complex.ofReal_eq_zero.mp hz)
  exact hh.exists.choose_spec


def sliceProjection (j : ℤ) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  (singleL2 j).comp (coordinateL2 j)
lemma sliceProjection_ae (j : ℤ) (f : GlobalHilbert) :
    sliceProjection j f =ᵐ[baseMeasure] fun x => lp.single 2 j (f x j) := by
  filter_upwards [singleL2_ae j (coordinateL2 j f), coordinateL2_ae j f] with x h₁ h₂
  change singleL2 j (coordinateL2 j f) x = _
  rw [h₁, h₂]
lemma sliceProjection_singleL2 (j : ℤ) (f : ScalarHilbert) :
    sliceProjection j (singleL2 j f) = singleL2 j f := by
  change singleL2 j (coordinateL2 j (singleL2 j f)) = _
  rw [coordinateL2_singleL2]
lemma sliceProjection_idempotent (j : ℤ) : sliceProjection j * sliceProjection j = sliceProjection j := by
  ext1 f
  exact sliceProjection_singleL2 j (coordinateL2 j f)
lemma sliceProjection_constantBasis (j k : ℤ) :
    sliceProjection j (constantBasis k) = if j=k then constantBasis k else 0 := by
  classical
  apply Lp.ext
  filter_upwards [sliceProjection_ae j (constantBasis k), constantBasis_ae k,
    Lp.coeFn_zero (E:=Fiber) (p:=2) (μ:=baseMeasure)] with x hx he hz
  rw [hx, he]
  by_cases hh : j=k
  · simp [hh, he]
  · simp only [ite_eq_right hh, lp.single_apply_ne _ _ _ hh, lp.single_zero, hz, Pi.zero_apply]
lemma sliceProjection_scalar_commute (j : ℤ) (g : Lp ℂ ∞ baseMeasure) :
    sliceProjection j * scalarMultiplier g = scalarMultiplier g * sliceProjection j := by
  ext1 f
  apply Lp.ext
  filter_upwards [sliceProjection_ae j (scalarMultiplier g f), scalarMultiplier_ae g f,
    scalarMultiplier_ae g (sliceProjection j f), sliceProjection_ae j f] with x h₁ h₂ h₃ h₄
  change sliceProjection j (scalarMultiplier g f) x = scalarMultiplier g (sliceProjection j f) x
  rw [h₁,h₂,h₃,h₄]
  exact lp.single_smul (E:=fun _ : ℤ => ℂ) 2 j (g x) (f x j)
lemma sliceProjection_zero_not_commute :
    sliceProjection 0 * forwardOperator ≠ forwardOperator * sliceProjection 0 := by
  intro he
  have h := congrArg (fun T : GlobalHilbert →L[ℂ] GlobalHilbert => T (constantBasis 0)) he
  simp only [mul_apply_eq_comp, forwardOperator_constantBasis_zero, map_smul,
    sliceProjection_constantBasis] at h
  norm_num at h
  have hh := congrArg norm h
  rw [norm_zero, forwardOperator_constantBasis_zero, norm_smul, constantBasis_norm, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le] at hh
  exact (Real.exp_ne_zero (-10)) hh.symm
lemma sliceProjection_zero_not_scalar :
    sliceProjection 0 ∉ Set.range (scalarMultiplier (μ:=baseMeasure)) := by
  rintro ⟨g,hg⟩
  have he0 : scalarMultiplier g (constantBasis 0) = constantBasis 0 := by
    rw [hg, sliceProjection_constantBasis]; simp
  have he1 : scalarMultiplier g (constantBasis 1) = 0 := by
    rw [hg, sliceProjection_constantBasis]; norm_num
  have h₀ := scalarMultiplier_ae g (constantBasis 0)
  have h₁ := scalarMultiplier_ae g (constantBasis 1)
  rw [he0] at h₀
  rw [he1] at h₁
  have hfalse : ∀ᵐ x ∂baseMeasure, False := by
    filter_upwards [h₀,h₁,constantBasis_ae 0, constantBasis_ae 1,
      Lp.coeFn_zero (E:=Fiber) (p:=2) (μ:=baseMeasure)] with x hv₀ hv₁ he₀ he₁ hz
    have hc₀ := congrArg (fun v : Fiber => v 0) hv₀
    have hc₁ := congrArg (fun v : Fiber => v 1) hv₁
    simp only [he₀, lp.single_apply_self, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_one] at hc₀
    simp only [hz, he₁, lp.single_apply_self, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_one, lp.coeFn_zero, Pi.zero_apply] at hc₁
    exact one_ne_zero (hc₀.trans hc₁.symm)
  exact hfalse.exists.choose_spec

lemma residue_separates {x y : Base} (h : ∀ m : ℕ, residue m x = residue m y) : x = y := by
  apply PadicInt.ext_of_toZModPow.mp
  intro m
  apply ZMod.val_injective
  exact h m

def residueClass (m t : ℕ) : Set Base := {x | residue m x = t}
lemma measurableSet_residueClass (m t : ℕ) : MeasurableSet (residueClass m t) :=
  measurableSet_eq_fun (measurable_residue m) measurable_const
lemma residueClass_nonnull {m t : ℕ} (ht : t < 2^m) : baseMeasure (residueClass m t) ≠ 0 := by
  change baseHaar {x : PadicInt 2 | twoResidue m x = t} ≠ 0
  have hcont : Continuous (twoResidue m) :=
    continuous_of_discreteTopology.comp (continuous_twoResidue m)
  have hOpen : IsOpen {x : PadicInt 2 | twoResidue m x = t} :=
    (isOpen_discrete ({t}:Set ℕ)).preimage hcont
  have hmem : twoResidue m (t : PadicInt 2) = t := by
    simp only [twoResidue, map_natCast]
    exact ZMod.val_natCast_of_lt ht
  exact (hOpen.measure_pos baseHaar ⟨(t : PadicInt 2),hmem⟩).ne'


def residueIndicator (m t : ℕ) : ScalarHilbert :=
  indicatorConstLp 2 (measurableSet_residueClass m t) (measure_ne_top baseMeasure _) (1:ℂ)
lemma residueIndicator_ae (m t : ℕ) : residueIndicator m t =ᵐ[baseMeasure]
    (residueClass m t).indicator (fun _ => (1:ℂ)) := indicatorConstLp_coeFn
lemma residueIndicator_ne_zero {m t : ℕ} (ht : t < 2^m) : residueIndicator m t ≠ 0 := by
  intro hz
  apply residueClass_nonnull ht
  rw [measure_eq_zero_iff_ae_notMem]
  have he := Lp.eq_zero_iff_ae_eq_zero.mp hz
  filter_upwards [he,residueIndicator_ae m t] with x hx hi
  intro hmem
  have h10 : (1:ℂ)=0 := by rw [← Set.indicator_of_mem hmem (fun _ => (1:ℂ)), ← hi]; exact hx
  exact one_ne_zero h10
lemma residueIndicator_orthogonal (m : ℕ) {s t : ℕ} (hst : s ≠ t) :
    inner ℂ (residueIndicator m s) (residueIndicator m t) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [residueIndicator_ae m s, residueIndicator_ae m t] with x hs ht
  rw [hs,ht]
  by_cases hxs : x ∈ residueClass m s
  · have hxt : x ∉ residueClass m t := fun hx => hst (hxs.symm.trans hx)
    simp [Set.indicator_of_notMem hxt]
  · simp [Set.indicator_of_notMem hxs]
lemma residueIndicator_independent (m : ℕ) :
    LinearIndependent ℂ (fun t : Fin (2^m) => residueIndicator m t) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro t; exact residueIndicator_ne_zero t.isLt
  · intro s t hst
    exact residueIndicator_orthogonal m (fun he => hst (Fin.ext he))
lemma scalarHilbert_infinite : ¬FiniteDimensional ℂ ScalarHilbert := by
  intro hfin
  let := hfin
  have hh := (residueIndicator_independent (Module.finrank ℂ ScalarHilbert + 1)).fintype_card_le_finrank
  simp only [Fintype.card_fin] at hh
  have hlt := Nat.lt_two_pow_self (n:=Module.finrank ℂ ScalarHilbert + 1)
  omega

lemma forwardOperator_singleL2_zero (f : ScalarHilbert) :
    forwardOperator (singleL2 0 f) = (Real.exp (-10):ℂ) • singleL2 1 f := by
  apply Lp.ext
  filter_upwards [forwardOperator_ae (singleL2 0 f), singleL2_ae 0 f, singleL2_ae 1 f,
    Lp.coeFn_smul (Real.exp (-10):ℂ) (singleL2 1 f)] with x h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₄,Pi.smul_apply,h₃,forwardFiber_single,explicitBeta_zero]
  exact lp.single_smul (E:=fun _ : ℤ => ℂ) 2 1 (Real.exp (-10):ℂ) (f x)
lemma coordinate_forward_single :
    (coordinateL2 1).comp (forwardOperator.comp (singleL2 0)) =
      (Real.exp (-10):ℂ) • (1 : ScalarHilbert →L[ℂ] ScalarHilbert) := by
  ext1 f
  change coordinateL2 1 (forwardOperator (singleL2 0 f)) = (Real.exp (-10):ℂ) • f
  rw [forwardOperator_singleL2_zero, map_smul, coordinateL2_singleL2]
lemma forwardOperator_not_compact : ¬IsCompactOperator forwardOperator := by
  intro hcomp
  have hc : IsCompactOperator ((coordinateL2 1).comp (forwardOperator.comp (singleL2 0))) :=
    (hcomp.comp_clm (singleL2 0)).clm_comp (coordinateL2 1)
  rw [coordinate_forward_single] at hc
  have he : (Real.exp (-10):ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero (-10)
  have hid : IsCompactOperator (id : ScalarHilbert → ScalarHilbert) :=
    (IsCompactOperator.smul_iff₀ he).mp hc
  exact scalarHilbert_infinite (FiniteDimensional.of_isCompactOperator_id hid)
lemma globalHilbert_infinite : ¬FiniteDimensional ℂ GlobalHilbert := by
  intro hfin
  let := hfin
  apply scalarHilbert_infinite
  apply FiniteDimensional.of_injective (singleL2 0).toLinearMap
  intro f g he
  have he' : singleL2 0 f = singleL2 0 g := he
  simpa only [coordinateL2_singleL2] using congrArg (coordinateL2 0) he'

lemma sliceProjection_selfAdjoint (j : ℤ) : IsSelfAdjoint (sliceProjection j) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (sliceProjection j f) g = inner ℂ f (sliceProjection j g)
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sliceProjection_ae j f, sliceProjection_ae j g] with x hf hg
  rw [hf,hg,lp.inner_single_left,lp.inner_single_right]
lemma sliceProjection_isStarProjection (j : ℤ) : IsStarProjection (sliceProjection j) :=
  ⟨sliceProjection_idempotent j, sliceProjection_selfAdjoint j⟩



end
end BackwardIntertwiners

end OAI
