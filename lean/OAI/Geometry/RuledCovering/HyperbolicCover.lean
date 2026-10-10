import OAI.Geometry.RuledCovering.LocalCover

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Sum-and-difference coordinates conjugate a hyperbolic derivative to the square lattice template. -/
def sumDifference : Coordinates ≃ₗ[ℝ] Coordinates where
  toFun x := ![x 0 + x 1, x 0 - x 1]
  invFun y := ![(y 0 + y 1) / 2, (y 0 - y 1) / 2]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp <;> ring
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

lemma hyperbolic_frame (A : Plane →L[ℝ] Plane) {lam : ℝ} (hlam : 0 < lam)
    (hplus : Module.End.HasEigenvalue A.toLinearMap lam)
    (hminus : Module.End.HasEigenvalue A.toLinearMap (-lam)) :
    ∃ M : Coordinates ≃L[ℝ] Plane, ∀ z : Coordinates,
      M.symm (A (M z)) = ![lam * z 1, lam * z 0] := by
  obtain ⟨u, hu⟩ := hplus.exists_hasEigenvector
  obtain ⟨v, hv⟩ := hminus.exists_hasEigenvector
  have hvals : Function.Injective (![lam, -lam] : Fin 2 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  have hli : LinearIndependent ℝ (![u, v] : Fin 2 → Plane) :=
    Module.End.eigenvectors_linearIndependent' A.toLinearMap ![lam, -lam] hvals ![u, v] (by
      intro i
      fin_cases i
      · exact hu
      · exact hv)
  let B : Module.Basis (Fin 2) ℝ Plane :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  let M : Coordinates ≃L[ℝ] Plane :=
    (sumDifference.trans B.equivFun.symm).toContinuousLinearEquiv
  have hM (z : Coordinates) : M z = (z 0 + z 1) • u + (z 0 - z 1) • v := by
    simp only [M]
    simp [B, sumDifference]
  have huA : A u = lam • u := hu.apply_eq_smul
  have hvA : A v = (-lam) • v := hv.apply_eq_smul
  refine ⟨M, fun z => ?_⟩
  apply M.injective
  rw [M.apply_symm_apply, hM, map_add, map_smul, map_smul,
    huA, hvA, hM]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  module
lemma HasFiniteCover.mono {shape : Cylinder → Prop} {S T : Set Space} {A B : ℝ}
    (h : HasFiniteCover shape T A) (hST : S ⊆ T) (hAB : A ≤ B) :
    HasFiniteCover shape S B := by
  obtain ⟨n, C, hC, hcov, hcost⟩ := h
  exact ⟨n, C, hC, hST.trans hcov, hcost.trans hAB⟩

lemma HasFiniteCover.empty (shape : Cylinder → Prop) {A : ℝ} (hA : 0 ≤ A) :
    HasFiniteCover shape ∅ A := by
  refine ⟨0, Fin.elim0, by intro i; exact i.elim0, by simp, ?_⟩
  simpa [familyArea] using hA

lemma HasFiniteCover.union {shape : Cylinder → Prop} {S T : Set Space} {A B : ℝ}
    (hS : HasFiniteCover shape S A) (hT : HasFiniteCover shape T B) :
    HasFiniteCover shape (S ∪ T) (A + B) := by
  obtain ⟨n, C, hC, hSC, hcostC⟩ := hS
  obtain ⟨m, D, hD, hTD, hcostD⟩ := hT
  refine ⟨n + m, Fin.addCases C D, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hC j
    · simpa using hD j
  · rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hSC hx)
      exact mem_iUnion.mpr ⟨i.castAdd m, by simpa using hi⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hTD hx)
      exact mem_iUnion.mpr ⟨j.natAdd n, by simpa using hj⟩
  · simpa [familyArea, Fin.sum_univ_add] using add_le_add hcostC hcostD

lemma physicalRuled_union (h L : ℝ) (v : Plane → Plane) (S T : Set Plane) :
    physicalRuled h (S ∪ T) v L = physicalRuled h S v L ∪ physicalRuled h T v L := by
  ext z
  simp only [physicalRuled, mem_ofPred_eq, mem_union]
  aesop

lemma physicalRuled_mono (h L : ℝ) (v : Plane → Plane) {S T : Set Plane} (hST : S ⊆ T) :
    physicalRuled h S v L ⊆ physicalRuled h T v L := by
  rintro z ⟨p, hp, r, hr, hz⟩
  exact ⟨p, hST hp, r, hr, hz⟩

lemma physicalRuled_empty (h L : ℝ) (v : Plane → Plane) : physicalRuled h ∅ v L = ∅ := by
  simp [physicalRuled]

/-- Compact pieces cut along a null frontier have exactly additive cost, even when
 the original compact set itself has a positive-area frontier. -/
lemma compact_cut_integral {K O : Set Plane} (hK : IsCompact K) (hO : IsOpen O)
    (hnull : volume (frontier O) = 0) {F : Plane → ℝ} (hF : IntegrableOn F K) :
    IsCompact (K ∩ closure O) ∧ IsCompact (K \ O) ∧
    K = (K ∩ closure O) ∪ (K \ O) ∧
    (∫ x in K, F x) = (∫ x in K ∩ closure O, F x) + (∫ x in K \ O, F x) := by
  have h₁ : IsCompact (K ∩ closure O) := hK.inter_right isClosed_closure
  have h₂ := hK.diff hO
  have hun : K = (K ∩ closure O) ∪ (K \ O) := by
    ext x
    simp only [mem_union, mem_inter_iff, Set.mem_sdiff]
    constructor
    · intro hx
      by_cases hxO : x ∈ O
      · exact Or.inl ⟨hx, subset_closure hxO⟩
      · exact Or.inr ⟨hx, hxO⟩
    · tauto
  refine ⟨h₁, h₂, hun, ?_⟩
  nth_rw 1 [hun]
  apply setIntegral_union₀
  · show volume ((K ∩ closure O) ∩ (K \ O)) = 0
    apply measure_mono_null _ hnull
    intro x hx
    rw [frontier, hO.interior_eq]
    exact ⟨hx.1.2, hx.2.2⟩
  · exact h₂.measurableSet.nullMeasurableSet
  · exact hF.mono_set inter_subset_left
  · exact hF.mono_set sdiff_subset

/-- Finite gluing over regular open patches. Only the patch frontiers must be null;
 there is deliberately no restriction on the label set's own frontier. -/
theorem glue_finite_local_covers {shape : Cylinder → Prop} (h L : ℝ) (v : Plane → Plane)
    (F : Plane → ℝ) {A : ℝ}
    {ι : Type*} (s : Finset ι) (O U : ι → Set Plane)
    (hO : ∀ i ∈ s, IsOpen (O i)) (hOU : ∀ i ∈ s, closure (O i) ⊆ U i)
    (hnull : ∀ i ∈ s, volume (frontier (O i)) = 0)
    (hlocal : ∀ i ∈ s, ∀ Q : Set Plane, IsCompact Q → Q ⊆ U i →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover shape (physicalRuled h Q v L)
        (A * (∫ p in Q, F p) + eps))
    {K : Set Plane} (hK : IsCompact K) (hF : IntegrableOn F K)
    (hcover : K ⊆ ⋃ i ∈ s, O i) {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h K v L) (A * (∫ p in K, F p) + eps) := by
  classical
  induction s using Finset.induction_on generalizing K eps with
  | empty =>
    have hKe : K = ∅ := by simpa using hcover
    rw [hKe, physicalRuled_empty]
    simpa using HasFiniteCover.empty shape heps.le
  | @insert i s hi ih =>
    have hOi := hO i (by simp)
    obtain ⟨h₁, h₂, hun, hint⟩ := compact_cut_integral hK hOi (hnull i (by simp)) hF
    have hc₁ := hlocal i (by simp) _ h₁
      (inter_subset_right.trans (hOU i (by simp))) (eps / 2) (half_pos heps)
    have hsub : K \ O i ⊆ ⋃ j ∈ s, O j := by
      intro x hx
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hcover hx.1)
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact False.elim (hx.2 hxj)
      · exact mem_iUnion₂.mpr ⟨j, hj, hxj⟩
    have hc₂ := ih (fun j hj => hO j (by simp [hj]))
      (fun j hj => hOU j (by simp [hj])) (fun j hj => hnull j (by simp [hj]))
      (fun j hj => hlocal j (by simp [hj])) h₂ (hF.mono_set sdiff_subset)
      hsub (half_pos heps)
    have hc := hc₁.union hc₂
    rw [← physicalRuled_union, ← hun] at hc
    convert hc using 1
    rw [hint]
    ring

lemma physicalWeight_pos (h : ℝ) (g : Plane) : 0 < physicalWeight h g := by
  apply one_div_pos.mpr
  apply Real.sqrt_pos.mpr
  positivity

lemma physicalWeight_continuous (h : ℝ) : Continuous (physicalWeight h) := by
  apply continuous_const.div
  · apply Real.continuous_sqrt.comp
    fun_prop
  · intro g
    exact (Real.sqrt_pos.mpr (by positivity : 0 < 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2)).ne'

lemma exists_small_inflation (L R : ℝ) {B : ℝ} (hB : 1 < B) :
    ∃ delta : ℝ, 0 < delta ∧ (1 + 2 * L * delta * R) ^ 2 < B := by
  have hc : Continuous (fun d : ℝ => (1 + 2 * L * d * R) ^ 2) := by fun_prop
  have he : ∀ᶠ d : ℝ in 𝓝 0, (1 + 2 * L * d * R) ^ 2 < B :=
    hc.continuousAt.eventually (Iio_mem_nhds (by simpa using hB))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r / 2, half_pos hr, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

/-- Every hyperbolic label has a patch whose compact subsets admit finite covers,
with one prescribed arbitrarily small area inflation. -/
theorem hyperbolic_local_patch {h L B : ℝ} (hh : 0 < h) (hL : 0 < L) (hB : 1 < B)
    {v : Plane → Plane} {U : Set Plane} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : Plane} (hp : p ∈ U) (hhyp : HyperbolicAt L v p) :
    ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧ ∀ K : Set Plane, IsCompact K → K ⊆ V →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover Cylinder.parallelogram (physicalRuled h K v L)
        (h * B * (∫ q in K, physicalWeight h (v q)) + eps) := by
  obtain ⟨lam, hlam, hsmall, hplus, hminus⟩ := hhyp
  have hlampos : 0 < lam := by nlinarith
  obtain ⟨M, hM⟩ := hyperbolic_frame (fderiv ℝ v p) hlampos hplus hminus
  let A : Coordinates →L[ℝ] Coordinates := lam • swapCLM
  let R : ℝ := 1 / (2 * (1 - L * lam))
  have hR : 0 < R := by dsimp [R]; positivity
  have hmodel : LatticeModel A L R := hyperbolic_lattice_model hL hlam hsmall
  obtain ⟨delta, hd, hDB⟩ := exists_small_inflation L R hB
  let w : Coordinates → Coordinates := fun x => M.symm (v (M x))
  let Uc : Set Coordinates := M ⁻¹' U
  have hUco : IsOpen Uc := hU.preimage M.continuous
  have hpc : M.symm p ∈ Uc := by simpa [Uc]
  have hvc : ContDiffOn ℝ 1 (fun x => v (M x)) Uc :=
    hv.comp M.contDiff.contDiffOn (fun x hx => hx)
  have hwc : ContDiffOn ℝ 1 w Uc := M.symm.contDiff.comp_contDiffOn hvc
  have hvder := (hv.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  have hwd : fderiv ℝ w (M.symm p) = A := by
    have hvd : HasFDerivAt (fun x => v (M x))
        ((fderiv ℝ v p).comp M.toContinuousLinearMap) (M.symm p) := by
      have hvdp : HasFDerivAt v (fderiv ℝ v p) (M (M.symm p)) := by
        simpa using hvder.hasFDerivAt
      exact hvdp.comp (M.symm p) M.hasFDerivAt
    have hcomp := M.symm.hasFDerivAt.comp (M.symm p) hvd
    change fderiv ℝ (M.symm ∘ (fun x => v (M x))) (M.symm p) = A
    rw [hcomp.fderiv]
    ext z i
    have hz := congrArg (fun a : Coordinates => a i) (hM z)
    fin_cases i <;> simpa [A, swapCLM, swapLinear] using hz
  obtain ⟨r, hr, hrU, hrem⟩ := c1_local_remainder hUco hwc hpc hd
  let Vc := ball (M.symm p) (r / 2)
  have hrhalf : r / 2 < r := by linarith
  have hclU : closedBall (M.symm p) (r / 2) ⊆ Uc :=
    (closedBall_subset_ball hrhalf).trans hrU
  have hclF : ContinuousOn (fun x => physicalWeight h (v (M x)))
      (closedBall (M.symm p) (r / 2)) :=
    (physicalWeight_continuous h).comp_continuousOn (hvc.continuousOn.mono hclU)
  obtain ⟨F, hF, hFnon, hFeq⟩ := continuous_nonneg_extension isClosed_closedBall hclF
    (fun x _ => (physicalWeight_pos h (v (M x))).le)
  refine ⟨M '' Vc, M.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · exact ⟨M.symm p, mem_ball_self (half_pos hr), M.apply_symm_apply p⟩
  · intro K hK hKV eps heps
    let Kc := M.symm '' K
    have hKc : IsCompact Kc := hK.image M.symm.continuous
    have hKcV : Kc ⊆ Vc := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hKV hq
      simpa using hx
    have himg : M '' Kc = K := by simp [Kc]
    have hc := framed_local_cover M hh hL.le hR.le hd.le hKc isOpen_ball hKcV v A hmodel
      (fun x hx y hy => by
        rw [← hwd]
        exact hrem x (ball_subset_ball hrhalf.le hx) y (ball_subset_ball hrhalf.le hy))
      hF hFnon (fun x hx => hFeq (ball_subset_closedBall hx)) heps
    rw [himg] at hc
    apply hc.mono Subset.rfl
    have hI : 0 ≤ ∫ q in K, physicalWeight h (v q) :=
      integral_nonneg (fun q => (physicalWeight_pos h (v q)).le)
    linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDB.le hh.le) hI]

/-- Compactness and null-frontier patches globalize the finite local producer. -/
theorem globalize_local_covers {shape : Cylinder → Prop} (h L : ℝ) (v : Plane → Plane)
    (F : Plane → ℝ) (A : ℝ) {K : Set Plane} (hK : IsCompact K) (hF : IntegrableOn F K)
    (hpatch : ∀ p ∈ K, ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧
      ∀ Q : Set Plane, IsCompact Q → Q ⊆ V → ∀ eps : ℝ, 0 < eps →
      HasFiniteCover shape (physicalRuled h Q v L) (A * (∫ q in Q, F q) + eps))
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h K v L) (A * (∫ q in K, F q) + eps) := by
  classical
  choose V hVo hpV hloc using fun p : K => hpatch p p.property
  choose r hr hrV using fun p : K => Metric.mem_nhds_iff.mp ((hVo p).mem_nhds (hpV p))
  let O : K → Set Plane := fun p => ball (p : Plane) (r p / 2)
  have hOo : ∀ p : K, IsOpen (O p) := fun _ => isOpen_ball
  have hcover : K ⊆ ⋃ p : K, O p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_ball_self (half_pos (hr ⟨p, hp⟩))⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover O hOo hcover
  apply glue_finite_local_covers h L v F s O V (fun p _ => hOo p) _ _
    (fun p _ => hloc p) hK hF hs heps
  · intro p _
    rw [show O p = ball (p : Plane) (r p / 2) from rfl,
      closure_ball (p : Plane) (half_pos (hr p)).ne']
    exact (closedBall_subset_ball (by linarith [hr p])).trans (hrV p)
  · intro p _
    apply measure_mono_null frontier_ball_subset_sphere
    exact MeasureTheory.Measure.addHaar_sphere volume (p : Plane) (r p / 2)

lemma exists_inflation_budget (C : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ B : ℝ, 1 < B ∧ B * C < C + eps := by
  have hc : Continuous (fun d : ℝ => (1+d)*C) := by fun_prop
  have he : ∀ᶠ d : ℝ in 𝓝 0, (1+d)*C < C + eps :=
    hc.continuousAt.eventually (Iio_mem_nhds (by simpa using lt_add_of_pos_right C heps))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨1+r/2, by linarith, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

/-- General physical weighted hyperbolic approximation, before isometry transport. -/
theorem physical_hyperbolic_cover {h L : ℝ} {D : Set Plane} {v : Plane → Plane}
    (hh : 0 < h) (hL : 0 < L) (hD : IsCompact D) (hv : SmoothNear 1 D v)
    (hhyp : ∀ p ∈ D, HyperbolicAt L v p) {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover Cylinder.parallelogram (physicalRuled h D v L)
      (h * (∫ p in D, physicalWeight h (v p)) + eps) := by
  obtain ⟨U, hU, hDU, hv⟩ := hv
  have hF : IntegrableOn (fun p => physicalWeight h (v p)) D :=
    ((physicalWeight_continuous h).comp_continuousOn (hv.continuousOn.mono hDU)).integrableOn_compact hD
  obtain ⟨B, hB, hbudget⟩ := exists_inflation_budget
    (h * ∫ p in D, physicalWeight h (v p)) (half_pos heps)
  have hc := globalize_local_covers h L v (fun p => physicalWeight h (v p)) (h*B) hD hF
    (fun p hp => hyperbolic_local_patch hh hL hB hU hv (hDU hp) (hhyp p hp)) (half_pos heps)
  apply hc.mono Subset.rfl
  nlinarith

end RuledApproximation

end

end OAI
