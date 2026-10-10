import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialIntegralCoordinates

namespace OAI

namespace Release061


theorem monic_root_norm_lt_coeff_sum {K : Type*} [NormedField K]
    {p : Polynomial K} (hp : p.Monic) {z : K} (hz : p.IsRoot z) :
    ‖z‖₊ < (∑ j ∈ Finset.range p.natDegree, ‖p.coeff j‖₊) + 1 := by
  apply (hz.norm_lt_cauchyBound hp.ne_zero).trans_le
  simp only [Polynomial.cauchyBound, hp.leadingCoeff, nnnorm_one, div_one]
  exact add_le_add (Finset.sup_le fun j hj =>
    Finset.single_le_sum (f := fun j => ‖p.coeff j‖₊) (fun _ _ => zero_le) hj) le_rfl

theorem finite_fiber_of_integral_coordinates {k : Type*} [Field k]
    {n d : ℕ} {V : Set (Fin n → k)} (P : Fin d → MvPolynomial (Fin n) k)
    (Q : Fin n → Polynomial (MvPolynomial (Fin d) k))
    (hQ : ∀ i, (Q i).Monic)
    (hroot : ∀ z ∈ V, ∀ i,
      Polynomial.eval₂ (MvPolynomial.eval (fun j => MvPolynomial.eval z (P j)))
        (z i) (Q i) = 0) (y : Fin d → k) :
    {z ∈ V | (fun j => MvPolynomial.eval z (P j)) = y}.Finite := by
  let p := fun i => (Q i).map (MvPolynomial.eval y)
  have hp : ∀ i, (p i).Monic := fun i => (hQ i).map _
  apply (Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot (hp i).ne_zero).subset
  intro z hz i _
  change (p i).IsRoot (z i)
  have h := hroot z hz.1 i
  rw [hz.2] at h
  simpa only [p, Polynomial.IsRoot.def, Polynomial.eval_map] using h

theorem isCompact_preimage_of_integral_coordinates
    {n d : ℕ} {V : Set (Fin n → ℂ)} (hV : IsClosed V)
    (P : Fin d → MvPolynomial (Fin n) ℂ)
    (Q : Fin n → Polynomial (MvPolynomial (Fin d) ℂ))
    (hQ : ∀ i, (Q i).Monic)
    (hroot : ∀ z ∈ V, ∀ i,
      Polynomial.eval₂ (MvPolynomial.eval (fun j => MvPolynomial.eval z (P j)))
        (z i) (Q i) = 0) {K : Set (Fin d → ℂ)} (hK : IsCompact K) :
    IsCompact {z ∈ V | (fun j => MvPolynomial.eval z (P j)) ∈ K} := by
  classical
  let B : (Fin d → ℂ) → NNReal := fun y =>
    ∑ i : Fin n, ((∑ j ∈ Finset.range (Q i).natDegree,
      ‖MvPolynomial.eval y ((Q i).coeff j)‖₊) + 1)
  have hB : Continuous B := by
    apply continuous_finsetSum
    intro i _
    apply Continuous.add _ continuous_const
    apply continuous_finsetSum
    intro j _
    exact ((Q i).coeff j).continuous_eval.nnnorm
  obtain ⟨R, hR⟩ := hK.bddAbove_image hB.continuousOn
  have hbound : ∀ z ∈ V, (fun j => MvPolynomial.eval z (P j)) ∈ K → ‖z‖ ≤ (R : ℝ) := by
    intro z hz hzK
    apply (pi_norm_le_iff_of_nonneg R.2).mpr
    intro i
    let y := fun j => MvPolynomial.eval z (P j)
    have hp : ((Q i).map (MvPolynomial.eval y)).Monic := (hQ i).map _
    have hzroot : ((Q i).map (MvPolynomial.eval y)).IsRoot (z i) := by
      simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hroot z hz i
    have hh := monic_root_norm_lt_coeff_sum hp hzroot
    rw [(hQ i).natDegree_map] at hh
    simp only [Polynomial.coeff_map] at hh
    have hsum : ((∑ j ∈ Finset.range (Q i).natDegree,
        ‖MvPolynomial.eval y ((Q i).coeff j)‖₊) + 1) ≤ B y :=
      Finset.single_le_sum (f := fun i : Fin n =>
        (∑ j ∈ Finset.range (Q i).natDegree,
          ‖MvPolynomial.eval y ((Q i).coeff j)‖₊) + 1)
        (fun _ _ => zero_le) (Finset.mem_univ i)
    exact_mod_cast hh.le.trans (hsum.trans (hR (Set.mem_image_of_mem B hzK)))
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · exact hV.inter (hK.isClosed.preimage (continuous_pi fun i => (P i).continuous_eval))
  · exact Metric.isBounded_iff_subset_ball 0 |>.2
      ⟨(R : ℝ) + 1, fun z hz => by simpa [Metric.mem_ball, dist_zero_right] using
        (hbound z hz.1 hz.2).trans_lt (lt_add_one _)⟩

theorem IsAffineAlgebraic.exists_finite_proper_polynomial_map
    {n : ℕ} {V : Set (Affine n)} (hV : IsAffineAlgebraic V) (hne : V.Nonempty) :
    ∃ d ≤ n, ∃ P : Fin d → MvPolynomial (Fin n) ℂ,
      IsProperMap (fun z : V => fun j => MvPolynomial.eval z.val (P j)) ∧
      ∀ y : Affine d, {z : V | (fun j => MvPolynomial.eval z.val (P j)) = y}.Finite := by
  obtain ⟨d, hd, P, Q, hQ, hroot⟩ := exists_polynomial_integral_coordinates hne
  refine ⟨d, hd, P, ?_, ?_⟩
  · apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨continuous_pi fun j => (P j).continuous_eval.comp continuous_subtype_val, ?_⟩
    intro K hK
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have heq : (Subtype.val : V → Affine n) ''
        ((fun z : V => fun j => MvPolynomial.eval z.val (P j)) ⁻¹' K) =
        {z ∈ V | (fun j => MvPolynomial.eval z (P j)) ∈ K} := by
      ext z
      simp only [Set.mem_image, Set.mem_preimage, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.property, hw⟩
      · rintro ⟨hz, hKz⟩
        exact ⟨⟨z, hz⟩, hKz, rfl⟩
    rw [heq]
    exact isCompact_preimage_of_integral_coordinates hV.isClosed P Q hQ hroot hK
  · intro y
    have hf := (finite_fiber_of_integral_coordinates P Q hQ hroot y).preimage
      (f := (Subtype.val : V → Affine n)) Subtype.val_injective.injOn
    simpa only [Set.preimage_ofPred_eq, Subtype.coe_prop, true_and] using hf

theorem finite_fiber_localization
    {X Y : Type*} [TopologicalSpace X] [RegularSpace X] [T1Space X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsProperMap f)
    (q : X) (hfin : (f ⁻¹' {f q}).Finite)
    {W : Set X} (hW : IsOpen W) (hqW : q ∈ W) :
    ∃ B : Set Y, IsOpen B ∧ f q ∈ B ∧
      ∃ Ω C : Set X, IsOpen Ω ∧ q ∈ Ω ∧ Ω ⊆ W ∧ IsClosed C ∧
        Ω = C ∩ f ⁻¹' B ∧ (Ω ∩ f ⁻¹' {f q}) = {q} := by
  let H : Set X := W ∩ (f ⁻¹' {f q} \ {q})ᶜ
  have hHo : IsOpen H := hW.inter (hfin.sdiff.isClosed.isOpen_compl)
  have hqH : q ∈ H := by simp [H, hqW]
  obtain ⟨O, ⟨hqO, hOo⟩, hclO⟩ :=
    (hasBasis_opens_closure q).mem_iff.mp (hHo.mem_nhds hqH)
  have hclfiber : ∀ x ∈ closure O, f x = f q → x = q := by
    intro x hx hfx
    have h := (hclO hx).2
    by_contra hne
    exact h ⟨hfx, hne⟩
  let B := (f '' (closure O \ O))ᶜ
  have hBo : IsOpen B := (hf.isClosedMap _ (isClosed_closure.sdiff hOo)).isOpen_compl
  have hqB : f q ∈ B := by
    rintro ⟨x, hx, hfx⟩
    have h : x = q := hclfiber x hx.1 hfx
    exact hx.2 (h ▸ hqO)
  refine ⟨B, hBo, hqB, O ∩ f ⁻¹' B, closure O,
    hOo.inter (hBo.preimage hf.continuous), ⟨hqO, hqB⟩,
    fun x hx => (hclO (subset_closure hx.1)).1, isClosed_closure, ?_, ?_⟩
  · ext x
    constructor
    · exact fun hx => ⟨subset_closure hx.1, hx.2⟩
    · intro hx
      refine ⟨?_, hx.2⟩
      by_contra hnot
      exact hx.2 ⟨x, ⟨hx.1, hnot⟩, rfl⟩
  · ext x
    constructor
    · intro hx
      exact hclfiber x (subset_closure hx.1.1) hx.2
    · rintro rfl
      exact ⟨⟨hqO, hqB⟩, rfl⟩

theorem isProperMap_inter_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsProperMap f) {C : Set X} (hC : IsClosed C) (B : Set Y) :
    IsProperMap (fun x : ↥(C ∩ f ⁻¹' B) => (⟨f x.val, x.property.2⟩ : B)) := by
  let e : ↥(C ∩ f ⁻¹' B) ≃ₜ ↥((fun x : C => f x.val) ⁻¹' B) :=
    { toFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      invFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ((hf.restrict hC).restrictPreimage B).comp e.isProperMap

open Set Filter Topology

theorem analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (i : E ≃L[ℂ] F) (hi : HasFDerivAt f (i : E →L[ℂ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℂ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℂ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℂ E F).symm
      (i : E →L[ℂ] F) := by
    apply (continuousMultilinearCurryFin1 ℂ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

noncomputable def triangularDifferentialEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E × ℂ →L[ℂ] ℂ) (ha : L (0, 1) ≠ 0) : (E × ℂ) ≃L[ℂ] (E × ℂ) := by
  let A := ContinuousLinearMap.fst ℂ E ℂ
  let B := ContinuousLinearMap.snd ℂ E ℂ
  let C := L.comp ((ContinuousLinearMap.inl ℂ E ℂ).comp A)
  let inv := A.prod ((L (0, 1))⁻¹ • (B - C))
  have hL : ∀ (u : E) (v : ℂ), L (u, v) = L (u, 0) + v * L (0, 1) := by
    intro u v
    have h : (u, v) = (u, 0) + v • (0, (1 : ℂ)) := by simp
    rw [h, map_add, map_smul]
    simp
  refine ContinuousLinearEquiv.equivOfInverse (A.prod L) inv ?_ ?_
  · intro p
    ext
    · rfl
    · change (L (0, 1))⁻¹ * (L (p.1, p.2) - L (p.1, 0)) = p.2
      rw [hL p.1 p.2]
      field_simp [ha]
      ring
  · intro p
    ext
    · rfl
    · change L (p.1, (L (0, 1))⁻¹ * (p.2 - L (p.1, 0))) = p.2
      rw [hL]
      field_simp [ha]
      ring

@[simp] theorem triangularDifferentialEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E × ℂ →L[ℂ] ℂ) (ha : L (0, 1) ≠ 0) (p : E × ℂ) :
    triangularDifferentialEquiv L ha p = (p.1, L p) := rfl

theorem analytic_implicit_scalar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : E × ℂ → ℂ} {a : E} {b : ℂ}
    (hF : AnalyticAt ℂ F (a, b)) (hzero : F (a, b) = 0)
    (L : E × ℂ →L[ℂ] ℂ) (hL : HasFDerivAt F L (a, b))
    (hsimple : L (0, 1) ≠ 0) :
    ∃ g : E → ℂ, AnalyticAt ℂ g a ∧ g a = b ∧
      (∀ᶠ y in 𝓝 a, F (y, g y) = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), F p = 0 → p.2 = g p.1) := by
  let G : E × ℂ → E × ℂ := fun p => (p.1, F p)
  have hG : AnalyticAt ℂ G (a, b) :=
    ((ContinuousLinearMap.fst ℂ E ℂ).analyticAt (a, b)).prod hF
  have hdG : HasFDerivAt G (triangularDifferentialEquiv L hsimple : _ →L[ℂ] _) (a, b) :=
    hasFDerivAt_fst.prodMk hL
  obtain ⟨e, he, hmem, hia⟩ := analytic_local_inverse hG
    (triangularDifferentialEquiv L hsimple) hdG
  have hGab : G (a, b) = (a, 0) := by simp [G, hzero]
  rw [hGab] at hia
  let g : E → ℂ := fun y => (e.symm (y, 0)).2
  have hiac : AnalyticAt ℂ (fun y : E => e.symm (y, 0)) a :=
    hia.comp (f := fun y : E => (y, 0))
      ((ContinuousLinearMap.inl ℂ E ℂ).analyticAt a)
  have hg : AnalyticAt ℂ g a :=
    ((ContinuousLinearMap.snd ℂ E ℂ).analyticAt _).comp hiac
  have hsource : e.symm (a, 0) = (a, b) := by
    rw [← hGab, ← he]
    exact e.left_inv hmem
  refine ⟨g, hg, congrArg Prod.snd hsource, ?_, ?_⟩
  · have hright := e.eventually_right_inverse' hmem
    rw [he, hGab] at hright
    have ht : Tendsto (fun y : E => (y, (0 : ℂ))) (𝓝 a) (𝓝 (a, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    filter_upwards [ht.eventually hright] with y hy
    have hfst : (e.symm (y, 0)).1 = y := congrArg Prod.fst hy
    have hsnd : F (e.symm (y, 0)) = 0 := congrArg Prod.snd hy
    change F (y, (e.symm (y, 0)).2) = 0
    have hpair : (y, (e.symm (y, 0)).2) = e.symm (y, 0) :=
      Prod.ext hfst.symm rfl
    rw [hpair]
    exact hsnd
  · have hleft := e.eventually_left_inverse hmem
    rw [he] at hleft
    filter_upwards [hleft] with p hp hz
    have hGp : G p = (p.1, 0) := by simp [G, hz]
    rw [hGp] at hp
    exact (congrArg Prod.snd hp).symm

end Release061

end OAI
