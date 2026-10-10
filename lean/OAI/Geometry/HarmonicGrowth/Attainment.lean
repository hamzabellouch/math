import Mathlib

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology

namespace HarmonicCounterexample.Transmission

/-- The robust local attainment argument, with constants independent of the
preceding pulse history. This is a genuine zero, not an approximate inverse. -/
theorem robust_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → E) (f' : E → E →L[ℝ] E)
    (A : E ≃L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hderiv : ∀ x ∈ Metric.closedBall (0 : E) r, HasFDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Metric.closedBall (0 : E) r,
      ‖ContinuousLinearMap.id ℝ E - A.symm.toContinuousLinearMap.comp (f' x)‖ ≤ 1 / 2)
    (hstart : ‖A.symm (f 0)‖ ≤ r / 2) :
    ∃ x ∈ Metric.closedBall (0 : E) r, f x = 0 := by
  let F : E → E := fun x => x - A.symm (f x)
  have hFderiv : ∀ x ∈ Metric.closedBall (0 : E) r,
      HasFDerivWithinAt F
        (ContinuousLinearMap.id ℝ E - A.symm.toContinuousLinearMap.comp (f' x))
        (Metric.closedBall (0 : E) r) x := by
    intro x hx
    exact ((hasFDerivAt_id x).sub
      (A.symm.toContinuousLinearMap.hasFDerivAt.comp x (hderiv x hx))).hasFDerivWithinAt
  have hFbound {x y : E} (hx : x ∈ Metric.closedBall (0 : E) r)
      (hy : y ∈ Metric.closedBall (0 : E) r) :
      ‖F y - F x‖ ≤ (1 / 2 : ℝ) * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hFderiv hbound
      (convex_closedBall (0 : E) r) hx hy
  have hzero : (0 : E) ∈ Metric.closedBall (0 : E) r := by simp [hr.le]
  have hmap : Set.MapsTo F (Metric.closedBall (0 : E) r)
      (Metric.closedBall (0 : E) r) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    have h := hFbound hzero (by simpa using hx)
    have h0 : ‖F 0‖ ≤ r / 2 := by simpa [F] using hstart
    have htri := norm_add_le (F x - F 0) (F 0)
    simp only [sub_add_cancel, sub_zero] at htri h
    linarith
  let Fball : Metric.closedBall (0 : E) r → Metric.closedBall (0 : E) r :=
    fun x => ⟨F x, hmap x.property⟩
  have hcon : ContractingWith (1 / 2 : NNReal) Fball := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (F x) (F y) ≤ (↑(1 / 2 : NNReal) : ℝ) * dist (x : E) (y : E)
      simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one,
        NNReal.coe_ofNat] using hFbound y.property x.property
  have : Nonempty (Metric.closedBall (0 : E) r) := ⟨⟨0, hzero⟩⟩
  have : CompleteSpace (Metric.closedBall (0 : E) r) := Metric.isClosed_closedBall.completeSpace_coe
  let x := ContractingWith.fixedPoint Fball hcon
  have hfix := congrArg Subtype.val (ContractingWith.fixedPoint_isFixedPt hcon)
  have hf : A.symm (f x) = 0 := by
    change (x : E) - A.symm (f x) = (x : E) at hfix
    exact sub_eq_self.mp hfix
  refine ⟨x, x.property, ?_⟩
  exact A.symm.injective (by simpa using hf)

end HarmonicCounterexample.Transmission

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology

namespace HarmonicCounterexample.FiniteControl
open Matrix
open scoped BigOperators Matrix.Norms.Operator
variable {β : Type*} {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nonempty (ι b)]

abbrev MatrixProduct' := ∀ b,Matrix (ι b) (ι b) ℝ

def tracefreeProduct' : Submodule ℝ (MatrixProduct' (ι:=ι)) where
  carrier := {X | ∀ b,(X b).trace=0}
  zero_mem' := by simp
  add_mem' hx hy := by intro b; rw [Pi.add_apply,Matrix.trace_add,hx,hy,add_zero]
  smul_mem' c X hx := by intro b; rw [Pi.smul_apply,Matrix.trace_smul,hx,smul_zero]

def meanTrace (X : MatrixProduct' (ι:=ι)) (b : β) : ℝ :=
  (X b).trace/(Fintype.card (ι b):ℝ)

/-- Linear local SL chart: project away scalar matrices after translating the
exact target to the identity. No abstract manifold chart is assumed. -/
def tracefreeProjection : MatrixProduct' (ι:=ι) →ₗ[ℝ] tracefreeProduct' (ι:=ι) where
  toFun X := ⟨fun b => X b-meanTrace X b • 1,by
    intro b
    have hn : (Fintype.card (ι b):ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_one,smul_eq_mul,meanTrace]
    rw [div_mul_cancel₀ _ hn,sub_self]⟩
  map_add' X Y := by
    apply Subtype.ext
    funext b
    change (X b+Y b)-meanTrace (X+Y) b • 1=
      (X b-meanTrace X b • 1)+(Y b-meanTrace Y b • 1)
    simp only [Pi.add_apply,Matrix.trace_add,meanTrace,add_div,add_smul]
    abel
  map_smul' c X := by
    apply Subtype.ext
    funext b
    change c • X b-meanTrace (c • X) b • 1=c • (X b-meanTrace X b • 1)
    simp only [Pi.smul_apply,Matrix.trace_smul,meanTrace,smul_eq_mul,
      mul_div_assoc,smul_sub,smul_smul]

/-- Projection zero is exactly scalarity, with the scalar given explicitly. -/
lemma tracefreeProjection_zero_iff (X : MatrixProduct' (ι:=ι)) :
    tracefreeProjection X=0 ↔ ∀ b,X b=meanTrace X b • 1 := by
  constructor
  · intro h b
    have he := congrFun (congrArg Subtype.val h) b
    exact sub_eq_zero.1 he
  · intro h
    apply Subtype.ext
    funext b
    change X b-meanTrace X b • 1=0
    rw [h b,sub_self]

lemma tracefreeProjection_id : tracefreeProjection (1 : MatrixProduct' (ι:=ι))=0 := by
  apply (tracefreeProjection_zero_iff _).2
  intro b
  have hn : (Fintype.card (ι b):ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp [meanTrace,hn]

lemma tracefreeProjection_subtype (X : tracefreeProduct' (ι:=ι)) :
    tracefreeProjection X=X := by
  apply Subtype.ext
  funext b
  change (X : MatrixProduct' (ι:=ι)) b-meanTrace (X : MatrixProduct' (ι:=ι)) b • 1=(X : MatrixProduct' (ι:=ι)) b
  simp only [meanTrace,X.property b,zero_div,zero_smul,sub_zero]

/-- Positivity of trace resolves the spurious negative scalar branch. This is
an OPEN condition near the prescribed positive scalar times the target. -/
lemma positive_scalar_of_projection_zero {X : MatrixProduct' (ι:=ι)}
    (hX : tracefreeProjection X=0) (htr : ∀ b,0 < (X b).trace) :
    ∀ b,∃ c : ℝ,0 < c ∧ X b=c • 1 := by
  intro b
  exact ⟨meanTrace X b,div_pos (htr b) (Nat.cast_pos.2 Fintype.card_pos),
    (tracefreeProjection_zero_iff X).1 hX b⟩

/-- Vanishing projected transmission gives the EXACT target, up to the
positive scalar permitted by source equation (exact-transmission). -/
lemma exact_scalar_target {X : MatrixProduct' (ι:=ι)} (M : (MatrixProduct' (ι:=ι))ˣ)
    (hX : tracefreeProjection (X*(↑M⁻¹ : MatrixProduct' (ι:=ι)))=0)
    (htr : ∀ b,0 < ((X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b).trace) :
    ∀ b,∃ c : ℝ,0 < c ∧ X b=c • ((M : MatrixProduct' (ι:=ι)) b) := by
  intro b
  obtain ⟨c,hc,he⟩ := positive_scalar_of_projection_zero hX htr b
  refine ⟨c,hc,?_⟩
  have h := congrArg (fun A : Matrix (ι b) (ι b) ℝ => A*((M : MatrixProduct' (ι:=ι)) b)) he
  have hi := congrFun M.inv_val b
  change ((M⁻¹ : (MatrixProduct' (ι:=ι))ˣ) : MatrixProduct' (ι:=ι)) b*
    (M : MatrixProduct' (ι:=ι)) b=1 at hi
  simpa only [Pi.mul_apply,Matrix.mul_assoc,hi,Matrix.mul_one,Matrix.smul_mul,
    Matrix.one_mul] using h

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology

namespace HarmonicCounterexample.Transmission
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The manuscript's two quarter bounds imply its half contraction, without
any implicit inverse-function robustness assertion. -/
theorem robust_zero_of_comparison (f : E → E) (f' g' : E → E →L[ℝ] E)
    (A : E ≃L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hderiv : ∀ x ∈ Metric.closedBall (0:E) r,HasFDerivAt f (f' x) x)
    (hbase : ∀ x ∈ Metric.closedBall (0:E) r,
      ‖ContinuousLinearMap.id ℝ E-A.symm.toContinuousLinearMap.comp (g' x)‖ ≤ 1/4)
    (herr : ∀ x ∈ Metric.closedBall (0:E) r,
      ‖A.symm.toContinuousLinearMap.comp (f' x-g' x)‖ ≤ 1/4)
    (hstart : ‖A.symm (f 0)‖ ≤ r/2) :
    ∃ x ∈ Metric.closedBall (0:E) r,f x=0 := by
  apply robust_zero f f' A hr hderiv _ hstart
  intro x hx
  have he : ContinuousLinearMap.id ℝ E-A.symm.toContinuousLinearMap.comp (f' x)=
      (ContinuousLinearMap.id ℝ E-A.symm.toContinuousLinearMap.comp (g' x))-
        A.symm.toContinuousLinearMap.comp (f' x-g' x) := by
    rw [ContinuousLinearMap.comp_sub]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [hbase x hx,herr x hx])

end HarmonicCounterexample.Transmission

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology

namespace HarmonicCounterexample.Transmission
open Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A single comparison ball is selected from the finite control word, before
any history or period is given. Continuity of its derivative is sufficient. -/
theorem comparison_ball (g' : E → E →L[ℝ] E) (A : E ≃L[ℝ] E)
    (hc : ContinuousAt g' 0) (h0 : g' 0=A.toContinuousLinearMap) :
    ∃ r : ℝ,0 < r ∧ ∀ x ∈ Metric.closedBall (0:E) r,
      ‖ContinuousLinearMap.id ℝ E-A.symm.toContinuousLinearMap.comp (g' x)‖ ≤ 1/4 := by
  let F : E → E →L[ℝ] E := fun x =>
    ContinuousLinearMap.id ℝ E-A.symm.toContinuousLinearMap.comp (g' x)
  have hF : ContinuousAt F 0 := continuousAt_const.sub (continuousAt_const.clm_comp hc)
  have hF0 : F 0=0 := by
    ext x
    simp [F,h0]
  have he : ∀ᶠ x in 𝓝 (0:E),‖F x‖ < (1:ℝ)/4 :=
    hF.norm.preimage_mem_nhds (Iio_mem_nhds (by rw [hF0,norm_zero]; norm_num))
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.1 he
  refine ⟨r/2,half_pos hr,fun x hx => (hsub ?_).le⟩
  rw [Metric.mem_ball]
  exact lt_of_le_of_lt hx (half_lt_self hr)

/-- Quantitative uniform local attainment: the only family-specific inputs are
C1 errors of actual maps against a fixed regular control word. The same radius
and epsilon work for all preceding histories. -/
theorem uniform_attainment_tolerance (g : E → E) (g' : E → E →L[ℝ] E)
    (A : E ≃L[ℝ] E) (hg0 : g 0=0) (hgc : ContinuousAt g' 0)
    (hg'0 : g' 0=A.toContinuousLinearMap) :
    ∃ r ε : ℝ,0 < r ∧ 0 < ε ∧
      ∀ (f : E → E) (f' : E → E →L[ℝ] E),
        (∀ x ∈ Metric.closedBall (0:E) r,HasFDerivAt f (f' x) x) →
        ‖f 0-g 0‖ ≤ ε →
        (∀ x ∈ Metric.closedBall (0:E) r,‖f' x-g' x‖ ≤ ε) →
        ∃ x ∈ Metric.closedBall (0:E) r,f x=0 := by
  obtain ⟨r,hr,hball⟩ := comparison_ball g' A hgc hg'0
  let C : ℝ := ‖A.symm.toContinuousLinearMap‖+1
  have hC : 0 < C := by dsimp [C]; positivity
  let ε : ℝ := min (1/(4*C)) (r/(2*C))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  refine ⟨r,ε,hr,hε,fun f f' hd hf hdf => ?_⟩
  apply robust_zero_of_comparison f f' g' A hr hd hball
  · intro x hx
    calc
      _ ≤ ‖A.symm.toContinuousLinearMap‖*‖f' x-g' x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C*ε := mul_le_mul (by dsimp [C]; linarith) (hdf x hx) (norm_nonneg _) hC.le
      _ ≤ 1/4 := by
        have h := mul_le_mul_of_nonneg_left (min_le_left (1/(4*C)) (r/(2*C))) hC.le
        apply h.trans_eq
        field_simp
  · rw [hg0,sub_zero] at hf
    calc
      ‖A.symm (f 0)‖ ≤ ‖A.symm.toContinuousLinearMap‖*‖f 0‖ := A.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ C*ε := mul_le_mul (by dsimp [C]; linarith) hf (norm_nonneg _) hC.le
      _ ≤ r/2 := by
        have h := mul_le_mul_of_nonneg_left (min_le_right (1/(4*C)) (r/(2*C))) hC.le
        apply h.trans_eq
        field_simp

end HarmonicCounterexample.Transmission

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology

namespace HarmonicCounterexample.Transmission
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The fixed local chart radius and C1 tolerance are selected BEFORE any
actual history-dependent map. The attained point stays in any prescribed
open neighborhood of the target, in particular the positive-trace branch. -/
theorem uniform_projected_attainment
    (Φ : E → F) (Φ' : E → E →L[ℝ] F) (L : F →L[ℝ] E) (A : E ≃L[ℝ] E)
    (hΦ : ContinuousAt Φ 0) (hΦ' : ContinuousAt Φ' 0)
    (hzero : L (Φ 0)=0) (hjet : L.comp (Φ' 0)=A.toContinuousLinearMap)
    {U : Set F} (hU : IsOpen U) (htgt : Φ 0 ∈ U) :
    ∃ r ε : ℝ,0 < r ∧ 0 < ε ∧
      ∀ (Ψ : E → F) (Ψ' : E → E →L[ℝ] F),
        (∀ x ∈ Metric.closedBall (0:E) r,HasFDerivAt Ψ (Ψ' x) x) →
        (∀ x ∈ Metric.closedBall (0:E) r,‖Ψ x-Φ x‖ ≤ ε) →
        (∀ x ∈ Metric.closedBall (0:E) r,‖Ψ' x-Φ' x‖ ≤ ε) →
        ∃ x ∈ Metric.closedBall (0:E) r,L (Ψ x)=0 ∧ Ψ x ∈ U := by
  obtain ⟨r₀,hr₀,hball⟩ := comparison_ball (fun x => L.comp (Φ' x)) A
    (continuousAt_const.clm_comp hΦ') hjet
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds htgt)
  have hnear : ∀ᶠ x in 𝓝 (0:E),‖Φ x-Φ 0‖ < δ/2 := by
    have hc : ContinuousAt (fun x => ‖Φ x-Φ 0‖) 0 :=
      (hΦ.sub continuousAt_const).norm
    exact hc.preimage_mem_nhds (Iio_mem_nhds (by simpa using half_pos hδ))
  obtain ⟨r₁,hr₁,hr₁near⟩ := Metric.mem_nhds_iff.1 hnear
  let r : ℝ := min r₀ (r₁/2)
  have hr : 0 < r := lt_min hr₀ (half_pos hr₁)
  have hr0 : r ≤ r₀ := min_le_left _ _
  have hr1 : r < r₁ := (min_le_right _ _).trans_lt (half_lt_self hr₁)
  let K : ℝ := ‖A.symm.toContinuousLinearMap‖*‖L‖+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKL : ‖A.symm.toContinuousLinearMap‖*‖L‖ ≤ K := by dsimp [K]; linarith
  let ε : ℝ := min (1/(4*K)) (min (r/(2*K)) (δ/2))
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (half_pos hδ))
  have he1 : K*ε ≤ 1/4 := by
    have he := mul_le_mul_of_nonneg_left (min_le_left (1/(4*K)) (min (r/(2*K)) (δ/2))) hK.le
    apply he.trans_eq
    field_simp
  have he2 : K*ε ≤ r/2 := by
    have he := mul_le_mul_of_nonneg_left
      ((min_le_right (1/(4*K)) (min (r/(2*K)) (δ/2))).trans (min_le_left _ _)) hK.le
    apply he.trans_eq
    field_simp
  have heδ : ε ≤ δ/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,ε,hr,hε,fun Ψ Ψ' hd hv hj => ?_⟩
  have hsub (x : E) (hx : x ∈ Metric.closedBall (0:E) r) :
      x ∈ Metric.closedBall (0:E) r₀ := le_trans hx hr0
  have hzeroBall : (0:E) ∈ Metric.closedBall (0:E) r := by simp [hr.le]
  obtain ⟨x,hx,hxzero⟩ := robust_zero_of_comparison (fun x => L (Ψ x))
    (fun x => L.comp (Ψ' x)) (fun x => L.comp (Φ' x)) A hr
    (fun x hx => L.hasFDerivAt.comp x (hd x hx))
    (fun x hx => hball x (hsub x hx)) (by
      intro x hx
      rw [← ContinuousLinearMap.comp_sub]
      calc
        _ ≤ ‖A.symm.toContinuousLinearMap‖*‖L.comp (Ψ' x-Φ' x)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖A.symm.toContinuousLinearMap‖*(‖L‖*‖Ψ' x-Φ' x‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
        _ = (‖A.symm.toContinuousLinearMap‖*‖L‖)*‖Ψ' x-Φ' x‖ := (mul_assoc _ _ _).symm
        _ ≤ K*ε := mul_le_mul hKL (hj x hx) (norm_nonneg _) hK.le
        _ ≤ 1/4 := he1) (by
      have he : L (Ψ 0)=L (Ψ 0-Φ 0) := by rw [map_sub,hzero,sub_zero]
      rw [he]
      calc
        _ ≤ ‖A.symm.toContinuousLinearMap‖*‖L (Ψ 0-Φ 0)‖ :=
          A.symm.toContinuousLinearMap.le_opNorm _
        _ ≤ ‖A.symm.toContinuousLinearMap‖*(‖L‖*‖Ψ 0-Φ 0‖) :=
          mul_le_mul_of_nonneg_left (L.le_opNorm _) (norm_nonneg _)
        _ = (‖A.symm.toContinuousLinearMap‖*‖L‖)*‖Ψ 0-Φ 0‖ := (mul_assoc _ _ _).symm
        _ ≤ K*ε := mul_le_mul hKL (hv 0 hzeroBall) (norm_nonneg _) hK.le
        _ ≤ r/2 := he2)
  refine ⟨x,hx,hxzero,hδU ?_⟩
  rw [Metric.mem_ball,dist_eq_norm]
  have hn : ‖Φ x-Φ 0‖ < δ/2 := hr₁near (lt_of_le_of_lt hx hr1)
  have he : Ψ x-Φ 0=(Ψ x-Φ x)+(Φ x-Φ 0) := by abel
  rw [he]
  have ht := norm_add_le (Ψ x-Φ x) (Φ x-Φ 0)
  linarith [hv x hx]

end HarmonicCounterexample.Transmission

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology

namespace HarmonicCounterexample.FiniteControl
open Matrix
open scoped BigOperators Matrix.Norms.Operator Topology
variable {β : Type*} [Fintype β] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nonempty (ι b)]

def translatedProjection (M : (MatrixProduct' (ι:=ι))ˣ) :
    MatrixProduct' (ι:=ι) →L[ℝ] tracefreeProduct' (ι:=ι) :=
  (tracefreeProjection (ι:=ι)).toContinuousLinearMap.comp
    ((ContinuousLinearMap.mul ℝ (MatrixProduct' (ι:=ι))).flip (↑M⁻¹))

lemma translatedProjection_apply (M : (MatrixProduct' (ι:=ι))ˣ)
    (X : MatrixProduct' (ι:=ι)) :
    translatedProjection M X=tracefreeProjection (X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) := rfl

lemma positive_trace_neighborhood (M : (MatrixProduct' (ι:=ι))ˣ) :
    IsOpen {X : MatrixProduct' (ι:=ι) | ∀ b,0 < ((X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b).trace} ∧
    (M : MatrixProduct' (ι:=ι)) ∈
      {X : MatrixProduct' (ι:=ι) | ∀ b,0 < ((X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b).trace} := by
  constructor
  · rw [show {X : MatrixProduct' (ι:=ι) | ∀ b,0 < ((X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b).trace}=
        (⋂ b,{X : MatrixProduct' (ι:=ι) | 0 < ((X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b).trace}) by ext X; simp]
    apply isOpen_iInter_of_finite
    intro b
    apply isOpen_lt continuous_const
    simp only [Matrix.trace]
    apply continuous_finsetSum
    intro i _
    apply Continuous.matrix_elem
    exact (continuous_apply b).comp (continuous_id.mul continuous_const)
  · intro b
    rw [Units.mul_inv]
    change 0 < (1 : Matrix (ι b) (ι b) ℝ).trace
    rw [Matrix.trace_one]
    exact Nat.cast_pos.2 Fintype.card_pos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance : NormedAddCommGroup (E →L[ℝ] MatrixProduct' (ι:=ι)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] MatrixProduct' (ι:=ι)) :=
  ContinuousLinearMap.toNormedSpace

/-- Quantitative actual exact positive-scalar attainment, avoiding determinant
normalization altogether. Each actual map has genuine Frechet derivatives and
uniform C1 errors; the same tolerance works for every preceding history. -/
theorem uniform_exact_scalar_attainment
    (M : (MatrixProduct' (ι:=ι))ˣ) (Φ : E → MatrixProduct' (ι:=ι))
    (Φ' : E → E →L[ℝ] MatrixProduct' (ι:=ι))
    (A : E ≃L[ℝ] tracefreeProduct' (ι:=ι))
    (hΦ : ContinuousAt Φ 0) (hΦ' : ContinuousAt Φ' 0)
    (hvalue : Φ 0=(M : MatrixProduct' (ι:=ι)))
    (hjet : (translatedProjection M).comp (Φ' 0)=A.toContinuousLinearMap) :
    ∃ r ε : ℝ,0 < r ∧ 0 < ε ∧
      ∀ (Ψ : E → MatrixProduct' (ι:=ι)) (Ψ' : E → E →L[ℝ] MatrixProduct' (ι:=ι)),
        (∀ x ∈ Metric.closedBall (0:E) r,HasFDerivAt Ψ (Ψ' x) x) →
        (∀ x ∈ Metric.closedBall (0:E) r,‖Ψ x-Φ x‖ ≤ ε) →
        (∀ x ∈ Metric.closedBall (0:E) r,‖(Ψ' x-Φ' x : E →L[ℝ] MatrixProduct' (ι:=ι))‖ ≤ ε) →
        ∃ x ∈ Metric.closedBall (0:E) r,
          ∀ b,∃ c : ℝ,0 < c ∧ Ψ x b=c • ((M : MatrixProduct' (ι:=ι)) b) := by
  let L := A.symm.toContinuousLinearMap.comp (translatedProjection M)
  have hLzero : L (Φ 0)=0 := by
    dsimp [L]
    rw [hvalue,translatedProjection_apply,Units.mul_inv,tracefreeProjection_id,map_zero]
  have hLjet : L.comp (Φ' 0)=(ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap := by
    dsimp [L]
    rw [ContinuousLinearMap.comp_assoc,hjet]
    ext x
    exact A.symm_apply_apply x
  obtain ⟨hU,htgt⟩ := positive_trace_neighborhood M
  obtain ⟨r,ε,hr,hε,hworks⟩ := HarmonicCounterexample.Transmission.uniform_projected_attainment
    Φ Φ' L (ContinuousLinearEquiv.refl ℝ E) hΦ hΦ' hLzero hLjet hU (hvalue ▸ htgt)
  refine ⟨r,ε,hr,hε,fun Ψ Ψ' hd hv hj => ?_⟩
  obtain ⟨x,hx,hxz,hxU⟩ := hworks Ψ Ψ' hd hv hj
  refine ⟨x,hx,exact_scalar_target M ?_ hxU⟩
  apply A.symm.injective
  change A.symm (translatedProjection M (Ψ x))=A.symm 0
  rw [map_zero]
  exact hxz

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology

namespace HarmonicCounterexample.FiniteControl
open Matrix
open scoped BigOperators Matrix.Norms.Operator Topology
variable {β : Type*} [Fintype β] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nonempty (ι b)]

def boundedScalarNeighborhood (M : (MatrixProduct' (ι:=ι))ˣ) : Set (MatrixProduct' (ι:=ι)) :=
  {X | ∀ b,meanTrace (X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b ∈ Set.Ioo (1/2:ℝ) (3/2)}

lemma boundedScalarNeighborhood_open (M : (MatrixProduct' (ι:=ι))ˣ) :
    IsOpen (boundedScalarNeighborhood M) ∧ (M : MatrixProduct' (ι:=ι)) ∈ boundedScalarNeighborhood M := by
  have hc (b : β) : Continuous (fun X : MatrixProduct' (ι:=ι) =>
      meanTrace (X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b) := by
    apply Continuous.div_const
    simp only [Matrix.trace]
    apply continuous_finsetSum
    intro i _
    apply Continuous.matrix_elem
    exact (continuous_apply b).comp (continuous_id.mul continuous_const)
  constructor
  · rw [show boundedScalarNeighborhood M=⋂ b,{X | meanTrace (X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b ∈ Set.Ioo (1/2:ℝ) (3/2)} by ext X;simp [boundedScalarNeighborhood]]
    exact isOpen_iInter_of_finite fun b => isOpen_Ioo.preimage (hc b)
  · intro b
    rw [Units.mul_inv]
    have hn : (Fintype.card (ι b):ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    norm_num [meanTrace,hn]

lemma bounded_scalar_target {X : MatrixProduct' (ι:=ι)} (M : (MatrixProduct' (ι:=ι))ˣ)
    (hX : translatedProjection M X=0) (hU : X ∈ boundedScalarNeighborhood M) :
    ∀ b,∃ c : ℝ,c ∈ Set.Ioo (1/2:ℝ) (3/2) ∧ X b=c • ((M : MatrixProduct' (ι:=ι)) b) := by
  intro b
  refine ⟨meanTrace (X*(↑M⁻¹ : MatrixProduct' (ι:=ι))) b,hU b,?_⟩
  change tracefreeProjection (X*(↑M⁻¹ : MatrixProduct' (ι:=ι)))=0 at hX
  have he := (tracefreeProjection_zero_iff _).1 hX b
  have h := congrArg (fun A : Matrix (ι b) (ι b) ℝ => A*((M : MatrixProduct' (ι:=ι)) b)) he
  have hi := congrFun M.inv_val b
  change (↑M⁻¹ : MatrixProduct' (ι:=ι)) b*(M : MatrixProduct' (ι:=ι)) b=1 at hi
  simpa only [Pi.mul_apply,Matrix.mul_assoc,hi,Matrix.mul_one,Matrix.smul_mul,Matrix.one_mul] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance : NormedAddCommGroup (E →L[ℝ] MatrixProduct' (ι:=ι)) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] MatrixProduct' (ι:=ι)) :=
  ContinuousLinearMap.toNormedSpace

/-- The exact target scalar stays in a fixed compact positive range. This
also supplies the uniform logarithmic scalar bound required for growth. -/
theorem uniform_exact_bounded_scalar_attainment
    (M : (MatrixProduct' (ι:=ι))ˣ) (Φ : E → MatrixProduct' (ι:=ι))
    (Φ' : E → E →L[ℝ] MatrixProduct' (ι:=ι))
    (A : E ≃L[ℝ] tracefreeProduct' (ι:=ι))
    (hΦ : ContinuousAt Φ 0) (hΦ' : ContinuousAt Φ' 0)
    (hvalue : Φ 0=(M : MatrixProduct' (ι:=ι)))
    (hjet : (translatedProjection M).comp (Φ' 0)=A.toContinuousLinearMap) :
    ∃ r ε : ℝ,0 < r ∧ 0 < ε ∧
      ∀ (Ψ : E → MatrixProduct' (ι:=ι)) (Ψ' : E → E →L[ℝ] MatrixProduct' (ι:=ι)),
        (∀ x ∈ Metric.closedBall (0:E) r,HasFDerivAt Ψ (Ψ' x) x) →
        (∀ x ∈ Metric.closedBall (0:E) r,‖Ψ x-Φ x‖ ≤ ε) →
        (∀ x ∈ Metric.closedBall (0:E) r,‖(Ψ' x-Φ' x : E →L[ℝ] MatrixProduct' (ι:=ι))‖ ≤ ε) →
        ∃ x ∈ Metric.closedBall (0:E) r,
          ∀ b,∃ c : ℝ,c ∈ Set.Ioo (1/2:ℝ) (3/2) ∧ Ψ x b=c • ((M : MatrixProduct' (ι:=ι)) b) := by
  let L := A.symm.toContinuousLinearMap.comp (translatedProjection M)
  have hLzero : L (Φ 0)=0 := by
    dsimp [L]
    rw [hvalue,translatedProjection_apply,Units.mul_inv,tracefreeProjection_id,map_zero]
  have hLjet : L.comp (Φ' 0)=(ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap := by
    dsimp [L]
    rw [ContinuousLinearMap.comp_assoc,hjet]
    ext x
    exact A.symm_apply_apply x
  obtain ⟨hU,htgt⟩ := boundedScalarNeighborhood_open M
  obtain ⟨r,ε,hr,hε,hworks⟩ := HarmonicCounterexample.Transmission.uniform_projected_attainment
    Φ Φ' L (ContinuousLinearEquiv.refl ℝ E) hΦ hΦ' hLzero hLjet hU (hvalue ▸ htgt)
  refine ⟨r,ε,hr,hε,fun Ψ Ψ' hd hv hj => ?_⟩
  obtain ⟨x,hx,hxz,hxU⟩ := hworks Ψ Ψ' hd hv hj
  refine ⟨x,hx,bounded_scalar_target M ?_ hxU⟩
  apply A.symm.injective
  change A.symm (translatedProjection M (Ψ x))=A.symm 0
  rw [map_zero]
  exact hxz

end HarmonicCounterexample.FiniteControl

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology

namespace HarmonicCounterexample.Transmission
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- Factoring the entire diagonal leg; unlike factoring only the dwell, no
large diagonal anisotropy is left inside the error term. Multiplication order
is the literal source order `D * permutation`. -/
lemma full_leg_factor (U V P B : R) (θ : ℝ) (D : Rˣ)
    (hD : (D:R)=U+θ • V) :
    (↑D⁻¹:R)*((U+V*P)*B)=
      (1+((↑D⁻¹:R)*V)*(P-θ • (1:R)))*B := by
  have he : U+V*P=(D:R)+V*(P-θ • (1:R)) := by
    rw [hD,mul_sub,mul_smul_comm,mul_one]
    abel
  rw [he,← mul_assoc,mul_add,Units.inv_mul]
  simp only [mul_assoc]

def wholePeriod (K Q B : R) : R := (1+K*Q)*B

def wholePeriodJet {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K Q B : R) (Q' B' : H →L[ℝ] R) : H →L[ℝ] R :=
  (ContinuousLinearMap.mul ℝ R (1+K*Q)).comp B'+
    ((ContinuousLinearMap.mul ℝ R).flip B).comp
      ((ContinuousLinearMap.mul ℝ R K).comp Q')

lemma wholePeriodJet_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K Q B : R) (Q' B' : H →L[ℝ] R) (v : H) :
    wholePeriodJet K Q B Q' B' v=(1+K*Q)*(B' v)+(K*(Q' v))*B := rfl

lemma wholePeriod_hasFDerivAt {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : R) {Q B : H → R} {Q' B' : H →L[ℝ] R} {x : H}
    (hQ : HasFDerivAt Q Q' x) (hB : HasFDerivAt B B' x) :
    HasFDerivAt (fun y => wholePeriod K (Q y) (B y))
      (wholePeriodJet K (Q x) (B x) Q' B') x := by
  have hd := ((hasFDerivAt_const (1:R) x).add
    ((hasFDerivAt_const K x).mul' hQ)).mul' hB
  convert hd using 1
  · rfl
  · ext v
    simp [wholePeriodJet,smul_eq_mul,add_mul]

omit [NormedAlgebra ℝ R] in
lemma wholePeriod_value_error {K Q B H : R} {K₀ ε H₀ : ℝ}
    (hK : ‖K‖ ≤ K₀) (hQ : ‖Q‖ ≤ ε) (hB : ‖B-H‖ ≤ ε) (hH : ‖H‖ ≤ H₀) :
    ‖wholePeriod K Q B-H‖ ≤ ε+K₀*ε*(H₀+ε) := by
  have hK₀ : 0 ≤ K₀ := (norm_nonneg _).trans hK
  have hε : 0 ≤ ε := (norm_nonneg _).trans hQ
  have hBn : ‖B‖ ≤ H₀+ε := by
    have hn := norm_add_le H (B-H)
    rw [add_sub_cancel] at hn
    linarith
  have he : wholePeriod K Q B-H=(B-H)+(K*Q)*B := by
    simp only [wholePeriod,add_mul,one_mul];abel
  rw [he]
  calc
    _ ≤ ‖B-H‖+‖(K*Q)*B‖ := norm_add_le _ _
    _ ≤ ε+K₀*ε*(H₀+ε) := by
      apply add_le_add hB
      exact (norm_mul_le _ _).trans
        (mul_le_mul ((norm_mul_le _ _).trans
          (mul_le_mul hK hQ (norm_nonneg _) hK₀)) hBn (norm_nonneg _) (mul_nonneg hK₀ hε))

lemma wholePeriod_jet_error {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K Q B Hval : R} {Q' B' H' : H →L[ℝ] R} {K₀ ε H₀ H₁ : ℝ}
    (hK : ‖K‖ ≤ K₀) (hQ : ‖Q‖ ≤ ε) (hB : ‖B-Hval‖ ≤ ε)
    (hH : ‖Hval‖ ≤ H₀) (hQ' : ‖Q'‖ ≤ ε) (hB' : ‖B'-H'‖ ≤ ε)
    (hH' : ‖H'‖ ≤ H₁) :
    ‖wholePeriodJet K Q B Q' B'-H'‖ ≤
      ε+K₀*ε*(H₁+ε)+K₀*ε*(H₀+ε) := by
  have hK₀ : 0 ≤ K₀ := (norm_nonneg _).trans hK
  have hε : 0 ≤ ε := (norm_nonneg _).trans hQ
  have hH₀ : 0 ≤ H₀ := (norm_nonneg _).trans hH
  have hH₁ : 0 ≤ H₁ := (norm_nonneg _).trans hH'
  have hnB : ‖B‖ ≤ H₀+ε := by
    have he := norm_add_le Hval (B-Hval)
    rw [add_sub_cancel] at he
    linarith
  have hnB' : ‖B'‖ ≤ H₁+ε := by
    have he := norm_add_le H' (B'-H')
    rw [add_sub_cancel] at he
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he : (wholePeriodJet K Q B Q' B'-H') v=
      (B'-H') v+(K*Q)*(B' v)+(K*(Q' v))*B := by
    simp only [sub_apply,wholePeriodJet_apply,add_mul,one_mul]
    abel
  rw [he]
  have hb0 : ‖(B'-H') v‖ ≤ ε*‖v‖ :=
    ((B'-H').le_opNorm v).trans (mul_le_mul_of_nonneg_right hB' (norm_nonneg _))
  have hb1 : ‖B' v‖ ≤ (H₁+ε)*‖v‖ :=
    (B'.le_opNorm v).trans (mul_le_mul_of_nonneg_right hnB' (norm_nonneg _))
  have hqv : ‖Q' v‖ ≤ ε*‖v‖ :=
    (Q'.le_opNorm v).trans (mul_le_mul_of_nonneg_right hQ' (norm_nonneg _))
  calc
    _ ≤ ‖(B'-H') v‖+‖(K*Q)*(B' v)‖+‖(K*(Q' v))*B‖ := norm_add₃_le
    _ ≤ ε*‖v‖+(K₀*ε)*((H₁+ε)*‖v‖)+(K₀*(ε*‖v‖))*(H₀+ε) := by
      apply add_le_add
      · apply add_le_add hb0
        exact (norm_mul_le _ _).trans (mul_le_mul
          ((norm_mul_le _ _).trans (mul_le_mul hK hQ (norm_nonneg _) hK₀)) hb1
          (norm_nonneg _) (mul_nonneg hK₀ hε))
      · exact (norm_mul_le _ _).trans (mul_le_mul
          ((norm_mul_le _ _).trans (mul_le_mul hK hqv (norm_nonneg _) hK₀)) hnB
          (norm_nonneg _) (by positivity))
    _ = _ := by ring

end HarmonicCounterexample.Transmission

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology

namespace HarmonicCounterexample.FiniteControl
open Matrix HarmonicCounterexample.Transmission
open scoped BigOperators Matrix.Norms.Operator Topology
variable {β : Type*} [Fintype β] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nonempty (ι b)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] MatrixProduct' (ι:=ι)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] MatrixProduct' (ι:=ι)) := ContinuousLinearMap.toNormedSpace

/-- Uniform actual WHOLE-period attainment, after factoring the entire
parameter-independent diagonal leg. The error tolerance is chosen before
K, Q and B, so it does not depend on the incoming history or diagonal
anisotropy. Q and B have genuine Frechet derivatives. -/
theorem whole_period_uniform_attainment
    (M : (MatrixProduct' (ι:=ι))ˣ) (Φ : E → MatrixProduct' (ι:=ι))
    (Φ' : E → E →L[ℝ] MatrixProduct' (ι:=ι))
    (A : E ≃L[ℝ] tracefreeProduct' (ι:=ι))
    (hΦ : Continuous Φ) (hΦ' : Continuous Φ')
    (hvalue : Φ 0=(M : MatrixProduct' (ι:=ι)))
    (hjet : (translatedProjection M).comp (Φ' 0)=A.toContinuousLinearMap)
    {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    ∃ r σ : ℝ,0 < r ∧ 0 < σ ∧
      ∀ (K : MatrixProduct' (ι:=ι)) (Q B : E → MatrixProduct' (ι:=ι))
        (Q' B' : E → E →L[ℝ] MatrixProduct' (ι:=ι)),
        ‖K‖ ≤ K₀ →
        (∀ x ∈ Metric.closedBall (0:E) r,HasFDerivAt Q (Q' x) x) →
        (∀ x ∈ Metric.closedBall (0:E) r,HasFDerivAt B (B' x) x) →
        (∀ x ∈ Metric.closedBall (0:E) r,‖Q x‖ ≤ σ) →
        (∀ x ∈ Metric.closedBall (0:E) r,‖B x-Φ x‖ ≤ σ) →
        (∀ x ∈ Metric.closedBall (0:E) r,‖Q' x‖ ≤ σ) →
        (∀ x ∈ Metric.closedBall (0:E) r,‖(B' x-Φ' x : E →L[ℝ] MatrixProduct' (ι:=ι))‖ ≤ σ) →
        ∃ x ∈ Metric.closedBall (0:E) r,
          ∀ b,∃ c : ℝ,c ∈ Set.Ioo (1/2:ℝ) (3/2) ∧
            wholePeriod K (Q x) (B x) b=c • ((M : MatrixProduct' (ι:=ι)) b) := by
  obtain ⟨r,ε,hr,hε,hworks⟩ := uniform_exact_bounded_scalar_attainment M Φ Φ' A
    hΦ.continuousAt hΦ'.continuousAt hvalue hjet
  obtain ⟨H₀,hH₀⟩ := (isCompact_closedBall (0:E) r).exists_bound_of_continuousOn hΦ.continuousOn
  obtain ⟨H₁,hH₁⟩ := (isCompact_closedBall (0:E) r).exists_bound_of_continuousOn hΦ'.continuousOn
  let V₀ := max H₀ 0
  let V₁ := max H₁ 0
  have hv₀ : 0 ≤ V₀ := le_max_right _ _
  have hv₁ : 0 ≤ V₁ := le_max_right _ _
  let N := 1+K₀*(V₁+1)+K₀*(V₀+1)
  have hN : 0 < N := by dsimp [N];positivity
  let σ := min 1 (ε/N)
  have hσ : 0 < σ := lt_min zero_lt_one (div_pos hε hN)
  have hσ₁ : σ ≤ 1 := min_le_left _ _
  have hσε : σ*N ≤ ε := (le_div_iff₀ hN).1 (min_le_right _ _)
  refine ⟨r,σ,hr,hσ,?_⟩
  intro K Q B Q' B' hK hdQ hdB hQ hB hQ' hB'
  apply hworks (fun x => wholePeriod K (Q x) (B x)) (fun x => wholePeriodJet K (Q x) (B x) (Q' x) (B' x))
  · intro x hx
    exact wholePeriod_hasFDerivAt K (hdQ x hx) (hdB x hx)
  · intro x hx
    have hb0 : ‖Φ x‖ ≤ V₀ := (hH₀ x hx).trans (le_max_left _ _)
    have hh := wholePeriod_value_error hK (hQ x hx) (hB x hx) hb0
    have hks : 0 ≤ K₀*σ := mul_nonneg hK₀ hσ.le
    have he : K₀*σ*(V₀+σ) ≤ K₀*σ*(V₀+1) :=
      mul_le_mul_of_nonneg_left (add_le_add_right hσ₁ V₀) hks
    have hextra : 0 ≤ σ*(K₀*(V₁+1)) := by positivity
    apply hh.trans
    apply le_trans _ hσε
    dsimp [N]
    nlinarith
  · intro x hx
    have hb0 : ‖Φ x‖ ≤ V₀ := (hH₀ x hx).trans (le_max_left _ _)
    have hb1 : ‖Φ' x‖ ≤ V₁ := (hH₁ x hx).trans (le_max_left _ _)
    have hh := wholePeriod_jet_error hK (hQ x hx) (hB x hx) hb0 (hQ' x hx) (hB' x hx) hb1
    have hks : 0 ≤ K₀*σ := mul_nonneg hK₀ hσ.le
    have he0 : K₀*σ*(V₀+σ) ≤ K₀*σ*(V₀+1) :=
      mul_le_mul_of_nonneg_left (add_le_add_right hσ₁ V₀) hks
    have he1 : K₀*σ*(V₁+σ) ≤ K₀*σ*(V₁+1) :=
      mul_le_mul_of_nonneg_left (add_le_add_right hσ₁ V₁) hks
    apply hh.trans
    apply le_trans _ hσε
    dsimp [N]
    nlinarith

omit [∀ (b : β), Nonempty (ι b)] in
/-- Cancellation of the factor of the ENTIRE diagonal leg gives the exact
chronological target c D M. No exponentially anisotropic conjugation occurs. -/
lemma whole_period_exact_leg {U V P B : MatrixProduct' (ι:=ι)} {θ : ℝ}
    (D M : (MatrixProduct' (ι:=ι))ˣ) (hD : (D:MatrixProduct' (ι:=ι))=U+θ • V)
    (hatt : ∀ b,∃ c : ℝ,c ∈ Set.Ioo (1/2:ℝ) (3/2) ∧
      wholePeriod ((↑D⁻¹:MatrixProduct' (ι:=ι))*V) (P-θ • 1) B b=
        c • ((M:MatrixProduct' (ι:=ι)) b)) :
    ∀ b,∃ c : ℝ,c ∈ Set.Ioo (1/2:ℝ) (3/2) ∧
      ((U+V*P)*B) b=c • (((D:MatrixProduct' (ι:=ι))*(M:MatrixProduct' (ι:=ι))) b) := by
  intro b
  obtain ⟨c,hc,he⟩ := hatt b
  refine ⟨c,hc,?_⟩
  have hf := full_leg_factor U V P B θ D hD
  change (↑D⁻¹:MatrixProduct' (ι:=ι))*((U+V*P)*B)=wholePeriod ((↑D⁻¹:MatrixProduct' (ι:=ι))*V) (P-θ • 1) B at hf
  have hh := congrArg (fun X : MatrixProduct' (ι:=ι) => ((D:MatrixProduct' (ι:=ι))*X) b) hf
  rw [← mul_assoc,Units.mul_inv,one_mul] at hh
  rw [hh]
  change (D:MatrixProduct' (ι:=ι)) b*wholePeriod ((↑D⁻¹:MatrixProduct' (ι:=ι))*V) (P-θ • 1) B b=_
  rw [he,Matrix.mul_smul]
  rfl

end HarmonicCounterexample.FiniteControl

end

end OAI
