import OAI.Geometry.HarmonicGrowth.InsertedWord

namespace OAI

noncomputable section


namespace HarmonicCounterexample.PulseTaylor
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform value and derivative bounds on the fixed positive stretch interval.
These are bounds for the actual nonlinear Berger formula. -/
theorem angular_uniform_bounds (r : ℝ) (b D : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Icc (1/2:ℝ) (3/2),
      ‖angular r b D q-b‖ ≤ C*|q-1| ∧ ‖angularD r b D q‖ ≤ C := by
  obtain ⟨C,hC,hest⟩ := angular_remainder r b D
  refine ⟨C+‖r • b+D‖,add_nonneg hC (norm_nonneg _),?_⟩
  intro q hq
  have hq₁ : |q-1| ≤ 1 := (abs_le.2 ⟨by linarith [hq.1],by linarith [hq.2]⟩)
  have hq₂ : (q-1)^2 ≤ |q-1| := by
    nlinarith [sq_abs (q-1),mul_le_mul_of_nonneg_left hq₁ (abs_nonneg (q-1))]
  obtain ⟨hv,hd⟩ := hest q hq
  constructor
  · calc
      ‖angular r b D q-b‖ ≤ ‖angular r b D q-b-(q-1) • (r • b+D)‖+
          ‖(q-1) • (r • b+D)‖ := norm_le_norm_sub_add _ _
      _ ≤ C*(q-1)^2+|q-1| *‖r • b+D‖ := by
        simpa only [norm_smul,Real.norm_eq_abs] using add_le_add hv (le_refl ‖(q-1) • (r • b+D)‖)
      _ ≤ (C+‖r • b+D‖)*|q-1| := by nlinarith [mul_le_mul_of_nonneg_left hq₂ hC]
  · calc
      ‖angularD r b D q‖ ≤ ‖angularD r b D q-(r • b+D)‖+‖r • b+D‖ := norm_le_norm_sub_add _ _
      _ ≤ C*|q-1|+‖r • b+D‖ := add_le_add hd le_rfl
      _ ≤ C+‖r • b+D‖ := by nlinarith [mul_le_mul_of_nonneg_left hq₁ hC]

end HarmonicCounterexample.PulseTaylor

end

noncomputable section


namespace HarmonicCounterexample.FiniteControl.SmoothWord
open Set
open scoped BigOperators
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}

/-- The finite C1 amplitude family has one bound on its compact parameter set;
no incoming metric or regular-solution history occurs in this choice. -/
lemma compact_amplitude_jet_bound {K : Set H} (hK : IsCompact K)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K) :
    ∃ U : ℝ,0 ≤ U ∧ ∀ x ∈ K,∀ j,|amps j x| ≤ U ∧ ‖amps' j x‖ ≤ U := by
  classical
  choose C hC using fun j => hK.exists_bound_of_continuousOn (hc j)
  choose D hD using fun j => hK.exists_bound_of_continuousOn (hd j)
  let U := ∑ j : Fin n,max (max (C j) (D j)) 0
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨U,hU,?_⟩
  intro x hx j
  have hj : max (max (C j) (D j)) 0 ≤ U :=
    Finset.single_le_sum (f := fun j : Fin n => max (max (C j) (D j)) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
  have hac : |amps j x| ≤ C j := by simpa only [Real.norm_eq_abs] using hC j x hx
  exact ⟨hac.trans
      ((le_max_left _ _).trans ((le_max_left _ _).trans hj)),
    (hD j x hx).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hj))⟩

/-- Quantitative compact-ball-ready C1 bounds for the nonlinear word on ALL
of the time axis. The constants precede amplitudes, parameter jets, and duration. -/
theorem nonlinearBergerWord_uniform_C1_bound (r : ℝ) (b : E) (D : Fin n → E) :
    ∃ C₀ C : ℝ,0 ≤ C₀ ∧ 0 ≤ C ∧
      ∀ (amps : Fin n → ℝ) (jets : Fin n → H →L[ℝ] ℝ) (U T : ℝ),
        0 ≤ U → (∀ j,|amps j| ≤ U) → (∀ j,‖jets j‖ ≤ U) →
        0 < T → 2*C₀*U ≤ T → ∀ t,
        ‖nonlinearBergerWord r b D amps T t-b‖ ≤ C*U/T ∧
        ‖∑ j : Fin n,((T⁻¹*duration n*bump j (duration n*t)) • jets j).smulRight
          (PulseTaylor.angularD r b (D j) (packetStretch amps T t j))‖ ≤ C*U/T := by
  classical
  obtain ⟨C₀,hC₀,hpos⟩ := packetStretch_uniform_positive n
  choose B hB hb using fun j : Fin n => packet_functions_bounded j
  choose K hK hk using fun j : Fin n => PulseTaylor.angular_uniform_bounds r b (D j)
  let C := ∑ j : Fin n,duration n*B j*K j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (duration_pos n).le (hB j)) (hK j))
  refine ⟨C₀,C,hC₀,hC,?_⟩
  intro amps jets U T hU ha hj hT hlong t
  have hq (j : Fin n) := hpos amps U T hU ha hT hlong t j
  have hsmall (j : Fin n) : |packetStretch amps T t j-1| ≤ duration n*B j*U/T := by
    calc
      _ = duration n*|bump j (duration n*t)| *|amps j|/T := by
        simp only [packetStretch,add_sub_cancel_left,abs_mul,abs_inv,
          abs_of_pos hT,abs_of_pos (duration_pos n)]
        ring
      _ ≤ duration n*B j*U/T := by
        apply div_le_div_of_nonneg_right _ hT.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hb j _).1 (duration_pos n).le)
          (ha j) (abs_nonneg _) (mul_nonneg (duration_pos n).le (hB j))
  have hend : (∑ j : Fin n,(duration n*B j*K j)*U/T)=C*U/T := by
    rw [← Finset.sum_div,← Finset.sum_mul]
  constructor
  · have he : nonlinearBergerWord r b D amps T t-b =
        ∑ j : Fin n,(PulseTaylor.angular r b (D j) (packetStretch amps T t j)-b) := by
      simp only [nonlinearBergerWord,nonlinearPacket,add_sub_cancel_left]
    rw [he]
    calc
      _ ≤ ∑ j : Fin n,‖PulseTaylor.angular r b (D j) (packetStretch amps T t j)-b‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n,(duration n*B j*K j)*U/T := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ K j*|packetStretch amps T t j-1| := (hk j _ (hq j)).1
          _ ≤ K j*(duration n*B j*U/T) := mul_le_mul_of_nonneg_left (hsmall j) (hK j)
          _ = (duration n*B j*K j)*U/T := by ring
      _ = C*U/T := hend
  · calc
      _ ≤ ∑ j : Fin n,‖((T⁻¹*duration n*bump j (duration n*t)) • jets j).smulRight
          (PulseTaylor.angularD r b (D j) (packetStretch amps T t j))‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n,(duration n*B j*K j)*U/T := by
        apply Finset.sum_le_sum
        intro j _
        rw [ContinuousLinearMap.norm_smulRight_apply,norm_smul,Real.norm_eq_abs,
          abs_mul,abs_mul,abs_inv,abs_of_pos hT,abs_of_pos (duration_pos n)]
        have hw : T⁻¹*duration n*|bump j (duration n*t)| *‖jets j‖ ≤
            T⁻¹*duration n*B j*U :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hb j _).1 (mul_nonneg (inv_nonneg.2 hT.le) (duration_pos n).le))
            (hj j) (norm_nonneg _) (mul_nonneg (mul_nonneg (inv_nonneg.2 hT.le) (duration_pos n).le) (hB j))
        calc
          _ ≤ (T⁻¹*duration n*B j*U)*K j :=
            mul_le_mul hw (hk j _ (hq j)).2 (norm_nonneg _) (mul_nonneg
              (mul_nonneg (mul_nonneg (inv_nonneg.2 hT.le) (duration_pos n).le) (hB j)) hU)
          _ = (duration n*B j*K j)*U/T := by ring
      _ = C*U/T := hend

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section


namespace HarmonicCounterexample.FiniteControl.SmoothWord
open Set
open scoped BigOperators
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}

/-- One parameter-ball bound for the actual inserted coefficient and its actual
Frechet derivative. Both constants are fixed before ALL histories and time shifts. -/
theorem insertWord_compact_C1_bound {K : Set H} (hK : IsCompact K)
    (r : ℝ) (b : E) (D : Fin n → E)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (ha : ∀ x ∈ K,∀ j,HasFDerivAt (amps j) (amps' j x) x)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K) :
    ∃ T₀ C : ℝ,1 ≤ T₀ ∧ 0 ≤ C ∧ ∀ T ≥ T₀,∀ x ∈ K,
      (∀ j t,packetStretch (fun i => amps i x) T t j ∈ Icc (1/2:ℝ) (3/2)) ∧
      ∀ (history : ℝ → E) (α : ℝ → ℝ) (M a : ℝ),0 ≤ M →
        (∀ t,|α t| ≤ M) → ∀ t,
        ‖insertWord history α r b D (fun i => amps i x) a T t-history t‖ ≤ M*C/T ∧
        ‖fderiv ℝ (fun y => insertWord history α r b D (fun i => amps i y) a T t) x‖ ≤ M*C/T := by
  obtain ⟨U,hU,hbound⟩ := compact_amplitude_jet_bound hK amps amps' hc hd
  obtain ⟨C₀,C,hC₀,hC,hest⟩ := nonlinearBergerWord_uniform_C1_bound (H := H) r b D
  obtain ⟨P,hP,hpos⟩ := packetStretch_uniform_positive n
  let T₀ := max 1 (max (2*C₀*U) (2*P*U))
  refine ⟨T₀,C*U,le_max_left _ _,mul_nonneg hC hU,?_⟩
  intro T hT x hx
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hT)
  have hl₀ : 2*C₀*U ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hl₁ : 2*P*U ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have has (j : Fin n) := (hbound x hx j).1
  have hjs (j : Fin n) := (hbound x hx j).2
  have hq (j : Fin n) (t : ℝ) := hpos (fun i => amps i x) U T hU has hTpos hl₁ t j
  refine ⟨hq,?_⟩
  intro history α M a hM hα t
  have he := hest (fun i => amps i x) (fun i => amps' i x) U T hU has hjs hTpos hl₀ ((t-a)/T)
  have hne (j : Fin n) : packetStretch (fun i => amps i x) T ((t-a)/T) j ≠ 0 := by
    have := (hq j ((t-a)/T)).1
    linarith
  constructor
  · change ‖history t+α t • (nonlinearBergerWord r b D (fun i => amps i x) T ((t-a)/T)-b)-history t‖ ≤ _
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ M*(C*U/T) := mul_le_mul (hα t) he.1 (norm_nonneg _) hM
      _ = M*(C*U)/T := by ring
  · rw [(insertWord_hasFDerivAt history α r b D amps (fun i => amps' i x)
      (ha x hx) a T t hne).fderiv,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ M*(C*U/T) := mul_le_mul (hα t) he.2 (norm_nonneg _) hM
      _ = M*(C*U)/T := by ring

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open scoped ContDiff
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- Fixed continuous linear injection from angular coefficients to the
lower-left phase block. It does not depend on histories or parameters. -/
def phaseCoefficientInjection : (E →L[ℝ] E) →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E :=
  (ContinuousLinearMap.compL ℝ (OperatorPhase E) (E →L[ℝ] E) (OperatorPhase E)
      (ContinuousLinearMap.inr ℝ (E →L[ℝ] E) (E →L[ℝ] E))).comp
    (((ContinuousLinearMap.compL ℝ (OperatorPhase E) (E →L[ℝ] E) (E →L[ℝ] E)).flip
      (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E))).comp
        (ContinuousLinearMap.mul ℝ (E →L[ℝ] E)))

lemma phaseCoefficientInjection_apply (A : E →L[ℝ] E) (w : OperatorPhase E) :
    phaseCoefficientInjection A w=(0,A*w.1) := by
  rfl

lemma block_actual_fderiv_coeff {A : H → ℝ → E →L[ℝ] E} {x : H}
    (b : ℝ → ℝ) (t : ℝ) (hA : DifferentiableAt ℝ (fun q => A q t) x) :
    HasFDerivAt (fun q => block (leftAction (A q)) b t)
      (phaseCoefficientInjection.comp (fderiv ℝ (fun q => A q t) x)) x := by
  obtain ⟨K,hK,he⟩ := operator_block_parameter_jet_exists b t hA.hasFDerivAt
  have hEq : K=phaseCoefficientInjection.comp (fderiv ℝ (fun q => A q t) x) := by
    apply ContinuousLinearMap.ext
    intro h
    apply ContinuousLinearMap.ext
    intro w
    exact he h w
  rwa [hEq] at hK

lemma block_actual_fderiv_smooth {A : H → ℝ → E →L[ℝ] E} {x : H}
    (b : ℝ → ℝ) (hA : ∀ t,DifferentiableAt ℝ (fun q => A q t) x)
    (hs : ContDiff ℝ ∞ (fun t => fderiv ℝ (fun q => A q t) x)) :
    ContDiff ℝ ∞ (fun t => fderiv ℝ (fun q => block (leftAction (A q)) b t) x) := by
  have he : (fun t => fderiv ℝ (fun q => block (leftAction (A q)) b t) x)=
      (fun t => phaseCoefficientInjection.comp (fderiv ℝ (fun q => A q t) x)) := by
    funext t
    exact (block_actual_fderiv_coeff b t (hA t)).fderiv
  rw [he]
  exact (contDiff_const.clm_comp hs)

lemma operator_phase_jet_norm_le (A' : H →L[ℝ] E →L[ℝ] E)
    (K : H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (hK : ∀ h w,K h w=(0,A' h*w.1)) : ‖K‖ ≤ ‖A'‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro h
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro w
  rw [hK h w,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
  exact (norm_mul_le _ _).trans (mul_le_mul (A'.le_opNorm h) (norm_fst_le w)
    (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

lemma block_actual_fderiv_norm {A : H → ℝ → E →L[ℝ] E} {x : H}
    (b : ℝ → ℝ) (t : ℝ) (hA : DifferentiableAt ℝ (fun q => A q t) x) :
    ‖fderiv ℝ (fun q => block (leftAction (A q)) b t) x‖ ≤
      ‖fderiv ℝ (fun q => A q t) x‖ := by
  rw [(block_actual_fderiv_coeff b t hA).fderiv]
  exact operator_phase_jet_norm_le _ _ (fun h w => rfl)

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ} [NeZero n]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- All global coefficient/phase regularity and bounds for a new pulse over
a fixed compact parameter ball, produced by the actual Berger formula.
The duration threshold precedes the incoming history and its time origin. -/
theorem actual_insertWord_compact_producer {K : Set H} (hK : IsCompact K)
    (r B : ℝ) (D : Fin n → E →L[ℝ] E)
    (hD : ∀ j v,inner ℝ v (D j v) ≤ 0)
    (hBD : ∀ j v,-(B*‖v‖^2) ≤ inner ℝ v (D j v))
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (ha : ∀ x ∈ K,∀ j,HasFDerivAt (amps j) (amps' j x) x)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K) :
    ∃ T₀ C : ℝ,1 ≤ T₀ ∧ 0 ≤ C ∧ ∀ T ≥ T₀,
    ∀ (history : ℝ → E →L[ℝ] E) (α b : ℝ → ℝ) (M MH a : ℝ),
      ContDiff ℝ ∞ history → ContDiff ℝ ∞ α → 0 ≤ M → 0 ≤ MH →
      (∀ t,|α t| ≤ M) → (∀ t,‖history t‖ ≤ MH) →
      (∀ t v,0 ≤ inner ℝ v (history t v)) →
      (∀ t ∈ Icc a (a+T),0 ≤ α t) →
      (∀ t ∈ Icc a (a+T),history t=α t • (B • (1:E →L[ℝ] E))) →
      let A := fun x => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T
      let A' := fun x t => fderiv ℝ (fun y => A y t) x
      let P' := fun x t => fderiv ℝ (fun y => block (leftAction (A y)) b t) x
      ∀ x ∈ K,
      ContDiff ℝ ∞ (A x) ∧ ContDiff ℝ ∞ (A' x) ∧ ContDiff ℝ ∞ (P' x) ∧
      (∀ t,HasFDerivAt (fun y => A y t) (A' x t) x) ∧
      (∀ t,HasFDerivAt (fun y => block (leftAction (A y)) b t) (P' x t) x) ∧
      (∀ t u w,P' x t u w=(0,A' x t u*w.1)) ∧
      (∀ t v,0 ≤ inner ℝ v (A x t v)) ∧
      (∀ t,‖A x t‖ ≤ MH+M*C) ∧
      (∀ t,‖A' x t‖ ≤ M*C/T) ∧ (∀ t,‖P' x t‖ ≤ M*C/T) := by
  obtain ⟨T₀,C,hT₀,hC,hbound⟩ := insertWord_compact_C1_bound hK r (B • (1:E →L[ℝ] E)) D amps amps' ha hc hd
  obtain ⟨d,hsel⟩ := exists_packet_selector n
  refine ⟨T₀,C,hT₀,hC,?_⟩
  intro T hT history α b M MH a hhistory hα hM hMH hnα hnHistory hhistPos hαpos hround
  dsimp only
  intro x hx
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (hT₀.trans hT)
  obtain ⟨hq,he⟩ := hbound T hT x hx
  have hne (j : Fin n) (t : ℝ) : packetStretch (fun i => amps i x) T t j ≠ 0 := by
    have := (hq j t).1
    linarith
  let A := fun x => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T
  let A' := fun x t => fderiv ℝ (fun y => A y t) x
  let P' := fun x t => fderiv ℝ (fun y => block (leftAction (A y)) b t) x
  have hdiff (t : ℝ) : DifferentiableAt ℝ (fun y => A y t) x :=
    (insertWord_hasFDerivAt history α r (B • (1:E →L[ℝ] E)) D amps (fun j => amps' j x)
      (ha x hx) a T t (fun j => hne j _)).differentiableAt
  have hjet : ContDiff ℝ ∞ (A' x) :=
    insertWord_actual_jet_smooth history α hα r (B • (1:E →L[ℝ] E)) D amps (fun j => amps' j x)
      (ha x hx) a T hne
  have hphase (t : ℝ) := block_actual_fderiv_coeff b t (hdiff t)
  have hPeq (t : ℝ) : P' x t=phaseCoefficientInjection.comp (A' x t) := hphase t |>.fderiv
  refine ⟨insertWord_smooth history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T hhistory hα hne,
    hjet,block_actual_fderiv_smooth b hdiff hjet,fun t => (hdiff t).hasFDerivAt,?_,?_,?_,?_,?_,?_⟩
  · intro t
    exact (hphase t).differentiableAt.hasFDerivAt
  · intro t u w
    change P' x t u w = (0,A' x t u*w.1)
    rw [hPeq t]
    rfl
  · exact insertWord_nonneg history α r B D (fun j => amps j x) a T hTpos hhistPos hαpos hround
      (fun t v => nonlinearBergerWord_nonneg r B D (fun j => amps j x) T t (d (duration n*t))
        (fun j hj => (hsel _ j hj).1) (le_trans (by norm_num) (hq _ t).1) hD hBD v)
  · intro t
    calc
      ‖A x t‖ ≤ ‖A x t-history t‖+‖history t‖ := norm_le_norm_sub_add _ _
      _ ≤ M*C/T+MH := add_le_add (he history α M a hM hnα t).1 (hnHistory t)
      _ ≤ MH+M*C := by
        have hi : M*C/T ≤ M*C := (div_le_self (mul_nonneg hM hC) (hT₀.trans hT))
        linarith
  · intro t
    exact (he history α M a hM hnα t).2
  · intro t
    exact (block_actual_fderiv_norm b t (hdiff t)).trans (he history α M a hM hnα t).2

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter
open scoped Topology

namespace HarmonicCounterexample.LinearODE
open Set Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {E H ι : Type*} {n : ℕ} [NeZero n] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

open HarmonicCounterexample.FiniteControl.SmoothWord

/-- Model-specific value and variational-slope estimates for an EXPLICIT smooth
finite word, with all shape identities and bounds discharged. The selector and
constants are chosen before every history, amplitude vector and duration. -/
theorem selected_finite_berger_word_estimates (basis : OrthonormalBasis ι ℝ E)
    (r B β p₀ θ γ : ℝ) (D : Fin n → E →L[ℝ] E) {M U : ℝ}
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hc : p₀+2*θ ≠ 0) (hroot : β*B-p₀*θ-θ^2=0) :
    ∃ Z C : ℝ,∃ d : ℝ → Fin n,0 ≤ Z ∧ 1 ≤ C ∧
      (∀ u j,j ≠ d u → bump j (duration n*u)=0 ∧ deriv (bump j) (duration n*u)=0) ∧
      (∀ t,(∀ᶠ s in 𝓝 t,d s=d t) ∨
        (∀ᶠ s in 𝓝 t,∀ v : Fin n → ℝ,unitPacketScalar v s=0)) ∧ ∀ (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
      (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
      (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E) (x h : H)
      (α p : ℝ → ℝ) (amps rays : Fin n → ℝ) (Mp MB MA Mb l B₀ a T δ ε : ℝ),
      (∀ j,|amps j| ≤ U) → (∀ j,|rays j| ≤ U) →
      Continuous (A x) → Continuous b → Continuous (B' x) →
      Continuous (fun t => A' x t h) →
      (∀ t v w,B' x t v w=(0,A' x t v*w.1)) →
      0 ≤ MB → 0 ≤ MA → 0 ≤ Mb →
      (∀ t,‖block (leftAction (A x)) b t‖ ≤ MB) → (∀ t,‖B' x t‖ ≤ MB) →
      (∀ t,‖A x t‖ ≤ MA) → (∀ t,|b t| ≤ Mb) →
      (∀ t v,0 ≤ inner ℝ v (A x t v)) → 0 < l →
      (∀ t ≤ 0,∀ v,A x t v=(l*(l+B₀)) • v) → (∀ t ≤ 0,b t=B₀) →
      Continuous α → Continuous p → 0 ≤ Mp →
      (∀ t,|α t| ≤ M) → (∀ t,|p t| ≤ Mp) → (∀ t,0 ≤ t → 0 ≤ α t*B) →
      0 ≤ a → 1 ≤ T → 0 ≤ δ → 0 ≤ ε →
      (∀ t ∈ Icc 0 T,|α t-β| ≤ δ) → (∀ t ∈ Icc 0 T,|p t-p₀| ≤ δ) →
      (∀ t ∈ Icc 0 T,γ ≤ p t) →
      2*Z ≤ T →
      ((|B|+|θ|)/γ)*δ+T⁻¹*(∑ j : Fin n,|β/(p₀+2*θ)| *Z*‖r • (B • (1:E →L[ℝ] E))+D j‖) ≤ θ/2 →
      (∀ t ∈ Icc a (a+T),b t=p (t-a)) →
      (∀ t ∈ Icc a (a+T),A x t=
        α (t-a) • PulseTaylor.angular r (B • (1:E →L[ℝ] E)) (D (d (T⁻¹*(t-a)))) (1+T⁻¹*unitPacketScalar amps (T⁻¹*(t-a)))) →
      (∀ t ∈ Icc a (a+T),A' x t h=
        (T⁻¹*unitPacketScalar rays (T⁻¹*(t-a))) • (α (t-a) •
          PulseTaylor.angularD r (B • (1:E →L[ℝ] E)) (D (d (T⁻¹*(t-a)))) (1+T⁻¹*unitPacketScalar amps (T⁻¹*(t-a))))) →
      ‖orthogonalMatrix basis (slope (A x) b l a)-θ • (1:Matrix ι ι ℝ)‖ ≤ ε →
      orthogonalMatrix basis (slopeJet A b B' l x a h)=0 →
      let Q := fun t => orthogonalMatrix basis
        (scalarBaseline (fun s => α s*B) p θ (t-a) • (1:E →L[ℝ] E)+T⁻¹ • unitPacketCoefficient amps (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) (T⁻¹*(t-a)))
      let Qh := fun t => orthogonalMatrix basis
        (T⁻¹ • unitPacketCoefficient rays (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) (T⁻¹*(t-a)))
      (∀ t ∈ Icc a (a+T),‖orthogonalMatrix basis (slope (A x) b l t)-Q t‖ ≤
        (C+C/γ)*(δ+T⁻¹+ε)) ∧
      (∫ t in a..a+T,‖orthogonalMatrix basis (slope (A x) b l t)-Q t‖) ≤
        2*C*(δ+T⁻¹+ε)/γ ∧
      (∀ t ∈ Icc a (a+T),‖orthogonalMatrix basis (slopeJet A b B' l x t h)-Qh t‖ ≤
        (C+2*C*(C+C/γ))*(δ+T⁻¹+ε)/(γ*T)) ∧
      (∫ t in a..a+T,‖orthogonalMatrix basis (slopeJet A b B' l x t h)-Qh t‖) ≤
        C*(δ+T⁻¹+ε)/γ+4*C^2*(δ+T⁻¹+ε)/γ^2 := by
  obtain ⟨K,hK,hbound⟩ := unitPacketScalar_uniform_bound n
  let Z := K*U
  have hZ : 0 ≤ Z := mul_nonneg hK hU
  obtain ⟨d₀,hd₀,hgap⟩ := exists_round_gap_selector n
  let d : ℝ → Fin n := fun u => d₀ (duration n*u)
  let X : Fin n → E →L[ℝ] E := fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)
  obtain ⟨C,hC,hest⟩ := actual_switched_berger_estimates (H := H) basis r B β p₀ θ γ D hM hZ hθ hγ hc hroot
  refine ⟨Z,C,d,hZ,hC,?_,?_,?_⟩
  · intro u j hj
    exact hd₀ (duration n*u) j hj
  · intro t
    have ht : Tendsto (fun s : ℝ => duration n*s) (𝓝 t) (𝓝 (duration n*t)) :=
      (continuous_const.mul continuous_id).continuousAt
    rcases hgap (duration n*t) with h|h
    · exact Or.inl (ht.eventually h)
    · right
      filter_upwards [ht.eventually h] with s hs
      intro v
      simp only [unitPacketScalar,packetScalar,hs,mul_zero,Finset.sum_const_zero]
  intro A b B' A' x h α p amps rays Mp MB MA Mb l B₀ a T δ ε hamper hray
    hA hb hB' hA' hblock hMB hMA hMb hbblock hbB' hbA hbb hpos hl hcore hcoreb
    hα hp hMp hbα hbp hαpos ha hT hδ hε hαclose hpclose hγp hZT hcoerc hpb hcoeff hjet hinit hjetinit
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hshape (u : ℝ) := unitBergerPacket_selected amps D r B β p₀ θ d₀ hd₀ u
  have hrayshape (u : ℝ) := unitBergerPacket_selected rays D r B β p₀ θ d₀ hd₀ u
  have hamps (u : ℝ) := hbound amps U hU hamper u
  have hrays (u : ℝ) := hbound rays U hU hray u
  have hq (t : ℝ) (_ht : t ∈ Icc 0 T) :
      1+T⁻¹*unitPacketScalar amps (T⁻¹*t) ∈ Icc (1/2:ℝ) (3/2) := by
    have hz := (hamps (T⁻¹*t)).1
    have hhalf : |T⁻¹*unitPacketScalar amps (T⁻¹*t)| ≤ (1/2:ℝ) := by
      rw [abs_mul,abs_of_pos (inv_pos.2 hTpos)]
      apply (mul_le_mul_of_nonneg_left hz (inv_nonneg.2 hTpos.le)).trans
      rw [inv_mul_eq_div]
      exact (div_le_iff₀ hTpos).2 (by linarith)
    exact ⟨by linarith [(abs_le.1 hhalf).1],by linarith [(abs_le.1 hhalf).2]⟩
  exact hest A b B' A' x h α p (unitPacketScalar amps) (unitPacketScalarD amps)
    (unitPacketScalar rays) (unitPacketScalarD rays) d
    (unitPacketCoefficient amps X) (unitPacketCoefficientD amps X)
    (unitPacketCoefficient rays X) (unitPacketCoefficientD rays X) Mp MB MA Mb l B₀ a T δ ε
    hA hb hB' hA' hblock hMB hMA hMb hbblock hbB' hbA hbb hpos hl hcore hcoreb
    hα hp hMp hbα hbp hαpos ha hT hδ hε hαclose hpclose hγp
    (unitPacketCoefficient_deriv amps X) (unitPacketCoefficient_deriv rays X)
    (unitPacketCoefficientD_smooth amps X).continuous (unitPacketCoefficientD_smooth rays X).continuous
    (unitPacketCoefficient_zero amps X) (unitPacketCoefficient_zero rays X)
    (fun u => ⟨(hshape u).1,(hshape u).2,(hrayshape u).1,(hrayshape u).2⟩)
    (fun t _ => ⟨(hamps _).1,(hamps _).2,(hrays _).1,(hrays _).2⟩)
    hq hcoerc hpb hcoeff hjet hinit hjetinit

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {E H ι : Type*} {n : ℕ} [NeZero n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

/-- The actual smooth insertion satisfies all four physical value/ray error
bounds, uniformly on a fixed compact parameter ball. Constants and duration
thresholds precede incoming histories. All incoming jets are proved zero by
causality, and all coefficient identities are obtained by differentiation. -/
theorem compact_inserted_physical_estimates (basis : OrthonormalBasis ι ℝ E)
    {K : Set H} (hK : IsCompact K)
    (r B β p₀ θ γ M : ℝ) (D : Fin n → E →L[ℝ] E)
    (hD : ∀ j v,inner ℝ v (D j v) ≤ 0)
    (hBD : ∀ j v,-(B*‖v‖^2) ≤ inner ℝ v (D j v))
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hden : p₀+2*θ ≠ 0) (hroot : β*B-p₀*θ-θ^2=0)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (ha : ∀ x ∈ K,∀ j,HasFDerivAt (amps j) (amps' j x) x)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K) :
    ∃ T₀ Z C : ℝ,1 ≤ T₀ ∧ 0 ≤ Z ∧ 1 ≤ C ∧ ∀ T ≥ T₀,
      ∀ (history : ℝ → E →L[ℝ] E) (α b : ℝ → ℝ) (MH Mb l B₀ a δ ε : ℝ),
      ContDiff ℝ ∞ history → ContDiff ℝ ∞ α → Continuous b → 0 ≤ MH → 0 ≤ Mb →
      (∀ t,|α t| ≤ M) → (∀ t,0 ≤ α t) → (∀ t,|b t| ≤ Mb) →
      (∀ t,‖history t‖ ≤ MH) → (∀ t v,0 ≤ inner ℝ v (history t v)) →
      (∀ t ∈ Icc a (a+T),history t=α t • (B • (1:E →L[ℝ] E))) →
      0 < l → (∀ t ≤ 0,∀ v,history t v=(l*(l+B₀)) • v) → (∀ t ≤ 0,b t=B₀) →
      0 ≤ a → 0 ≤ δ → 0 ≤ ε →
      (∀ t ∈ Icc a (a+T),|α t-β| ≤ δ) → (∀ t ∈ Icc a (a+T),|b t-p₀| ≤ δ) →
      (∀ t ∈ Icc a (a+T),γ ≤ b t) →
      ((|B|+|θ|)/γ)*δ+T⁻¹*(∑ j : Fin n,|β/(p₀+2*θ)| *Z*‖r • (B • (1:E →L[ℝ] E))+D j‖) ≤ θ/2 →
      ‖orthogonalMatrix basis (slope history b l a)-θ • (1:Matrix ι ι ℝ)‖ ≤ ε →
      let A := fun x => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T
      let P' := fun x t => fderiv ℝ (fun y => block (leftAction (A y)) b t) x
      let X := fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)
      ∀ x ∈ K,∀ h : H,‖h‖ ≤ 1 →
      let Q := fun t => orthogonalMatrix basis
        (scalarBaseline (fun s => α (a+s)*B) (fun s => b (a+s)) θ (t-a) • (1:E →L[ℝ] E)+
          T⁻¹ • unitPacketCoefficient (fun j => amps j x) X (T⁻¹*(t-a)))
      let Qh := fun t => orthogonalMatrix basis
        (T⁻¹ • unitPacketCoefficient (fun j => amps' j x h) X (T⁻¹*(t-a)))
      (∀ t ∈ Icc a (a+T),‖orthogonalMatrix basis (slope (A x) b l t)-Q t‖ ≤
        (C+C/γ)*(δ+T⁻¹+ε)) ∧
      (∫ t in a..a+T,‖orthogonalMatrix basis (slope (A x) b l t)-Q t‖) ≤
        2*C*(δ+T⁻¹+ε)/γ ∧
      (∀ t ∈ Icc a (a+T),‖orthogonalMatrix basis (slopeJet A b P' l x t h)-Qh t‖ ≤
        (C+2*C*(C+C/γ))*(δ+T⁻¹+ε)/(γ*T)) ∧
      (∫ t in a..a+T,‖orthogonalMatrix basis (slopeJet A b P' l x t h)-Qh t‖) ≤
        C*(δ+T⁻¹+ε)/γ+4*C^2*(δ+T⁻¹+ε)/γ^2 := by
  obtain ⟨U,hU,hamp⟩ := compact_amplitude_jet_bound hK amps amps' hc hd
  obtain ⟨Z,C,d,hZ,hC,hsel,hgap,hest⟩ := selected_finite_berger_word_estimates (H := H)
    basis r B β p₀ θ γ D hM hU hθ hγ hden hroot
  obtain ⟨T₁,J,hT₁,hJ,hproduce⟩ := actual_insertWord_compact_producer hK r B D hD hBD amps amps' ha hc hd
  obtain ⟨P,hP,hpositive⟩ := packetStretch_uniform_positive n
  let T₀ := max T₁ (max (2*Z) (2*P*U))
  have hT₀ : 1 ≤ T₀ := hT₁.trans (le_max_left _ _)
  refine ⟨T₀,Z,C,hT₀,hZ,hC,?_⟩
  intro T hT history α b MH Mb l B₀ a δ ε hhistory hα hb hMH hMb hnα hαpos hnb
    hnHistory hhPos hround hl hcenter hbcenter ha₀ hδ hε hαclose hbclose hγb hsmall heps
  dsimp only
  intro x hx h hh
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (hT₀.trans hT)
  have hTJ : T₁ ≤ T := (le_max_left _ _).trans hT
  have hTZ : 2*Z ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTP : 2*P*U ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hq (j : Fin n) (t : ℝ) : packetStretch (fun i => amps i x) T t j ≠ 0 := by
    have hh := (hpositive (fun i => amps i x) U T hU (fun i => (hamp x hx i).1) hTpos hTP t j).1
    linarith
  let A := fun x => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T
  let A' := fun x t => fderiv ℝ (fun y => A y t) x
  let P' := fun x t => fderiv ℝ (fun y => block (leftAction (A y)) b t) x
  have hprod := hproduce T hTJ history α b M MH a hhistory hα hM hMH hnα hnHistory
    hhPos (fun t _ => hαpos t) hround x hx
  dsimp only at hprod
  obtain ⟨hs,hsA',hsP',hdA,hdP,hPeq,hpos,hnA,hnA',hnP'⟩ := hprod
  let MA := MH+M*J
  let MB := 1+MA+Mb+M*J
  have hMA : 0 ≤ MA := add_nonneg hMH (mul_nonneg hM hJ)
  have hMB : 0 ≤ MB := by dsimp [MB]; positivity
  have hnP (t : ℝ) : ‖P' x t‖ ≤ MB := by
    calc
      _ ≤ M*J/T := hnP' t
      _ ≤ M*J := div_le_self (mul_nonneg hM hJ) (hT₀.trans hT)
      _ ≤ MB := by dsimp [MB]; linarith
  have hnBlock (t : ℝ) : ‖block (leftAction (A x)) b t‖ ≤ MB := by
    apply (block_bound hMA hMb (fun t => (leftAction_norm_le (A x) t).trans (hnA t)) hnb t).trans
    dsimp [MB]
    linarith [mul_nonneg hM hJ]
  have hray (j : Fin n) : |amps' j x h| ≤ U := by
    calc
      _ ≤ ‖amps' j x‖*‖h‖ := (amps' j x).le_opNorm h
      _ ≤ U*1 := mul_le_mul (hamp x hx j).2 hh (norm_nonneg _) hU
      _ = U := mul_one _
  have htshift (t : ℝ) (ht : t ∈ Icc 0 T) : a+t ∈ Icc a (a+T) :=
    ⟨by linarith [ht.1],by linarith [ht.2]⟩
  apply hest A b P' A' x h (fun s => α (a+s)) (fun s => b (a+s))
    (fun j => amps j x) (fun j => amps' j x h) Mb MB MA Mb l B₀ a T δ ε
    (fun j => (hamp x hx j).1) hray hs.continuous hb hsP'.continuous
    ((hsA'.continuous).clm_apply continuous_const) hPeq hMB hMA hMb hnBlock hnP hnA hnb hpos hl
  · intro t ht v
    change insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T t v=_
    rw [insertWord_before _ _ _ _ _ _ _ _ _ hTpos (ht.trans ha₀)]
    exact hcenter t ht v
  · exact hbcenter
  · exact hα.continuous.comp (continuous_const.add continuous_id)
  · exact hb.comp (continuous_const.add continuous_id)
  · exact hMb
  · intro t
    exact hnα _
  · intro t
    exact hnb _
  · intro t ht
    exact mul_nonneg (hαpos _) hB
  · exact ha₀
  · exact hT₀.trans hT
  · exact hδ
  · exact hε
  · intro t ht
    exact hαclose _ (htshift t ht)
  · intro t ht
    exact hbclose _ (htshift t ht)
  · intro t ht
    exact hγb _ (htshift t ht)
  · exact hTZ
  · exact hsmall
  · intro t ht
    congr 1; ring
  · intro t ht
    change insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T t=_
    rw [insertWord_on_round _ _ _ _ _ _ _ _ _ (hround t ht)]
    have he := nonlinearBergerWord_selected r (B • (1:E →L[ℝ] E)) D (fun j => amps j x)
      T ((t-a)/T) (d ((t-a)/T)) (fun j hj => (hsel _ j hj).1)
    rw [he]
    congr 2 <;> ring_nf
  · intro t ht
    change fderiv ℝ (fun y => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j y) a T t) x h=_
    rw [insertWord_fderiv_ray_selected history α r (B • (1:E →L[ℝ] E)) D amps
      (fun j => amps' j x) (ha x hx) a T t (fun j => hq j _) (d ((t-a)/T))
      (fun j hj => (hsel _ j hj).1) h]
    congr 2 <;> ring_nf
  · simpa only [A,insertWord_incoming_slope history α r (B • (1:E →L[ℝ] E)) D
      (fun j => amps j x) a T hTpos ha₀ b l] using heps
  · have hz := insertWord_incoming_slopeJet history α r (B • (1:E →L[ℝ] E)) D
      (fun y j => amps j y) a T hTpos ha₀ b l x
    change orthogonalMatrix basis ((slopeJet A b P' l x a) h)=0
    change slopeJet A b P' l x a=0 at hz
    rw [hz]
    simp

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.FiniteControl.SmoothWord
open Set MeasureTheory
open scoped ContDiff BigOperators
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}
local instance : NormedAddCommGroup (H →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

/-- The actual Frechet derivative of the ideal packet, retained as a continuous
linear map rather than only its finitely many rays. -/
def unitPacketJet (a' : Fin n → H →L[ℝ] ℝ) (X : Fin n → E) (t : ℝ) : H →L[ℝ] E :=
  duration n • (∑ j,(a' j).smulRight (bump j (duration n*t) • X j))

lemma unitPacketJet_smooth (a' : Fin n → H →L[ℝ] ℝ) (X : Fin n → E) :
    ContDiff ℝ ∞ (unitPacketJet a' X) := by
  unfold unitPacketJet
  apply (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => duration n)).smul
  apply ContDiff.sum
  intro j _
  have he : (fun t => (a' j).smulRight (bump j (duration n*t) • X j))=
      (fun t => bump j (duration n*t) • (a' j).smulRight (X j)) := by
    ext t z
    simp only [ContinuousLinearMap.smulRight_apply,smul_apply]
    exact smul_comm _ _ _
  rw [he]
  exact ((bump_smooth j).comp (contDiff_const.mul contDiff_id)).smul contDiff_const

/-- A single value-and-operator-jet bound on a compact parameter set, chosen
before any physical history, duration or radial coefficients. -/
theorem compact_ideal_packet_bound {K : Set H} (hK : IsCompact K)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K)
    (X : Fin n → E) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ x ∈ K,
      (∀ t,‖unitPacketCoefficient (fun j => amps j x) X t‖ ≤ C) ∧
      (∀ t,‖unitPacketJet (fun j => amps' j x) X t‖ ≤ C) ∧
      (∫ t in (0:ℝ)..1,‖unitPacketCoefficient (fun j => amps j x) X t‖)+
        (∫ t in (0:ℝ)..1,‖unitPacketJet (fun j => amps' j x) X t‖) ≤ 2*C := by
  classical
  obtain ⟨U,hU,hbound⟩ := compact_amplitude_jet_bound hK amps amps' hc hd
  choose B hB hb using fun j : Fin n => packet_functions_bounded j
  let C := duration n * ∑ j : Fin n,U*B j*‖X j‖
  have hC : 0 ≤ C := mul_nonneg (duration_pos n).le (Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg hU (hB j)) (norm_nonneg _)))
  refine ⟨C,hC,?_⟩
  intro x hx
  have hv (t : ℝ) : ‖unitPacketCoefficient (fun j => amps j x) X t‖ ≤ C := by
    rw [unitPacketCoefficient,norm_smul,Real.norm_eq_abs,abs_of_pos (duration_pos n)]
    apply mul_le_mul_of_nonneg_left _ (duration_pos n).le
    calc
      ‖packetCoefficient (fun j => amps j x) X (duration n*t)‖ ≤
          ∑ j : Fin n,‖(amps j x*bump j (duration n*t)) • X j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n,U*B j*‖X j‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul,Real.norm_eq_abs,abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hbound x hx j).1 (hb j _).1 (abs_nonneg _) hU) (norm_nonneg _)
  have hj (t : ℝ) : ‖unitPacketJet (fun j => amps' j x) X t‖ ≤ C := by
    rw [unitPacketJet,norm_smul,Real.norm_eq_abs,abs_of_pos (duration_pos n)]
    apply mul_le_mul_of_nonneg_left _ (duration_pos n).le
    calc
      _ ≤ ∑ j : Fin n,‖(amps' j x).smulRight (bump j (duration n*t) • X j)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n,U*B j*‖X j‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [ContinuousLinearMap.norm_smulRight_apply,norm_smul,Real.norm_eq_abs,← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hbound x hx j).2 (hb j _).1 (abs_nonneg _) hU) (norm_nonneg _)
  refine ⟨hv,hj,?_⟩
  have hvI := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    ((unitPacketCoefficient_smooth (fun j => amps j x) X).continuous.norm.intervalIntegrable 0 1)
    (intervalIntegrable_const (c := C)) (fun t _ => hv t)
  have hjI := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    ((unitPacketJet_smooth (fun j => amps' j x) X).continuous.norm.intervalIntegrable 0 1)
    (intervalIntegrable_const (c := C)) (fun t _ => hj t)
  simp only [intervalIntegral.integral_const,sub_zero,one_smul] at hvI hjI
  linarith

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set

/-- Positive-time scalar baseline with a continuous global extension. This
avoids making a false global nonsingularity claim at negative time. -/
lemma clipped_scalarBaseline_continuous {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {θ : ℝ} (hθ : 0 ≤ θ) (a : ℝ) :
    Continuous (fun t => scalarBaseline A p θ (max 0 (t-a))) := by
  have hc : ContinuousOn (scalarBaseline A p θ) (Ici 0) := by
    intro t ht
    exact (actual_scalar_baseline_deriv hA hp hMA hMp hAn hpn hAp hθ ht).continuousAt.continuousWithinAt
  exact hc.comp_continuous (continuous_const.max (continuous_id.sub continuous_const))
    (fun t => show 0 ≤ max 0 (t-a) from le_max_left _ _)

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {E H ι κ : Type*} {n : ℕ} [NeZero n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [Fintype ι] [DecidableEq ι] [Fintype κ]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

/-- From the actual nonlinear coefficient producer and physical estimates to
an actual normalized second-order transmission C1 estimate. Every error
constant and duration threshold is chosen before the incoming history. -/
theorem compact_inserted_endpoint_C1 (basis : OrthonormalBasis ι ℝ E)
    (hbasis : OrthonormalBasis κ ℝ H) {K : Set H} (hK : IsCompact K)
    (r B β p₀ θ γ M : ℝ) (D : Fin n → E →L[ℝ] E)
    (hD : ∀ j v,inner ℝ v (D j v) ≤ 0)
    (hBD : ∀ j v,-(B*‖v‖^2) ≤ inner ℝ v (D j v))
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hden : p₀+2*θ ≠ 0) (hroot : β*B-p₀*θ-θ^2=0)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (ha : ∀ x ∈ K,∀ j,HasFDerivAt (amps j) (amps' j x) x)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K) :
    ∃ T₀ Z C J : ℝ,1 ≤ T₀ ∧ 0 ≤ Z ∧ 1 ≤ C ∧ 0 ≤ J ∧ ∀ T ≥ T₀,
      ∀ (history : ℝ → E →L[ℝ] E) (α b : ℝ → ℝ) (MH Mb l B₀ a δ ε : ℝ)
        (S : Set H), IsOpen S → IsPreconnected S → S ⊆ K →
      ContDiff ℝ ∞ history → ContDiff ℝ ∞ α → Continuous b → 0 ≤ MH → 0 ≤ Mb →
      (∀ t,|α t| ≤ M) → (∀ t,0 ≤ α t) → (∀ t,|b t| ≤ Mb) →
      (∀ t,‖history t‖ ≤ MH) → (∀ t v,0 ≤ inner ℝ v (history t v)) →
      (∀ t ∈ Icc a (a+T),history t=α t • (B • (1:E →L[ℝ] E))) →
      0 < l → (∀ t ≤ 0,∀ v,history t v=(l*(l+B₀)) • v) → (∀ t ≤ 0,b t=B₀) →
      0 ≤ a → 0 ≤ δ → 0 ≤ ε →
      (∀ t ∈ Icc a (a+T),|α t-β| ≤ δ) → (∀ t ∈ Icc a (a+T),|b t-p₀| ≤ δ) →
      (∀ t ∈ Icc a (a+T),γ ≤ b t) →
      ((|B|+|θ|)/γ)*δ+T⁻¹*(∑ j : Fin n,|β/(p₀+2*θ)| *Z*‖r • (B • (1:E →L[ℝ] E))+D j‖) ≤ θ/2 →
      ‖orthogonalMatrix basis (slope history b l a)-θ • (1:Matrix ι ι ℝ)‖ ≤ ε →
      let A := fun x => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T
      let v := fun t => scalarBaseline (fun s => α (a+s)*B) (fun s => b (a+s)) θ (max 0 (t-a))
      let W := fun x => flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E)
        (unitPacketCoefficient (fun j => amps j x) (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) t)) 1 1
      let Y := fun x => Real.exp (-(∫ t in a..a+T,v t)) •
        (operatorValue (A x) b l (a+T)*Ring.inverse (operatorValue (A x) b l a))
      let η := (3*C/γ+4*C^2/γ^2)*(δ+T⁻¹+ε)
      ∀ x ∈ S,max ‖Y x-W x‖ ‖fderiv ℝ Y x-fderiv ℝ W x‖ ≤ Real.exp (2*J+J*η)*(J*η) := by
  let X := fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)
  obtain ⟨MI,hMI,hideal⟩ := compact_ideal_packet_bound hK amps amps' hc hd X
  obtain ⟨J,hCJ,hJ,hendpoint⟩ := actual_physical_endpoint_C1 basis hbasis (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hMI)
  obtain ⟨T₁,Z,C,hT₁,hZ,hC,hphysical⟩ := compact_inserted_physical_estimates basis hK
    r B β p₀ θ γ M D hD hBD hM hB hθ hγ hden hroot amps amps' ha hc hd
  obtain ⟨T₂,JC,hT₂,hJC,hproduce⟩ := actual_insertWord_compact_producer hK r B D hD hBD amps amps' ha hc hd
  refine ⟨max T₁ T₂,Z,C,J,hT₁.trans (le_max_left _ _),hZ,hC,hJ,?_⟩
  intro T hT history α b MH Mb l B₀ a δ ε S hS hSc hSK hhistory hα hb hMH hMb hnα hαpos hnb
    hnHistory hhPos hround hl hcenter hbcenter ha₀ hδ hε hαclose hbclose hγb hsmall heps
  dsimp only
  intro x hx
  have hT₁T : T₁ ≤ T := (le_max_left _ _).trans hT
  have hT₂T : T₂ ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (hT₁.trans hT₁T)
  let A := fun x => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T
  let A' := fun x t => fderiv ℝ (fun y => A y t) x
  let P' := fun x t => fderiv ℝ (fun y => block (leftAction (A y)) b t) x
  let v := fun t => scalarBaseline (fun s => α (a+s)*B) (fun s => b (a+s)) θ (max 0 (t-a))
  let I := fun x t => unitPacketCoefficient (fun j => amps j x) X t
  let I' := fun x t => unitPacketJet (fun j => amps' j x) X t
  have prod (q : H) (hq : q ∈ S) := hproduce T hT₂T history α b M MH a hhistory hα hM hMH hnα hnHistory
    hhPos (fun t _ => hαpos t) hround q (hSK hq)
  dsimp only at prod
  let MA := MH+M*JC
  let MB := 1+MA+Mb+M*JC
  have hMA : 0 ≤ MA := add_nonneg hMH (mul_nonneg hM hJC)
  have hMB : 0 ≤ MB := by dsimp [MB]; positivity
  have hnA (q : H) (hq : q ∈ S) (t : ℝ) : ‖A q t‖ ≤ MA := (prod q hq).2.2.2.2.2.2.2.1 t
  have hnP (q : H) (hq : q ∈ S) (t : ℝ) : ‖P' q t‖ ≤ MB := by
    calc
      _ ≤ M*JC/T := (prod q hq).2.2.2.2.2.2.2.2.2 t
      _ ≤ M*JC := div_le_self (mul_nonneg hM hJC) (hT₂.trans hT₂T)
      _ ≤ MB := by dsimp [MB]; linarith
  have hnBlock (q : H) (hq : q ∈ S) (t : ℝ) : ‖block (leftAction (A q)) b t‖ ≤ MB := by
    apply (block_bound hMA hMb (fun t => (leftAction_norm_le (A q) t).trans (hnA q hq t)) hnb t).trans
    dsimp [MB]
    linarith [mul_nonneg hM hJC]
  have hαshift : Continuous (fun s => α (a+s)*B) :=
    (hα.continuous.comp (continuous_const.add continuous_id)).mul_const B
  have hbshift : Continuous (fun s => b (a+s)) := hb.comp (continuous_const.add continuous_id)
  have hnαshift (t : ℝ) : |α (a+t)*B| ≤ M*B := by
    rw [abs_mul,abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_right (hnα _) hB
  have hv : Continuous v := clipped_scalarBaseline_continuous hαshift hbshift (mul_nonneg hM hB) hMb
    hnαshift (fun t => hnb _) (fun t _ => mul_nonneg (hαpos _) hB) hθ a
  let η := (3*C/γ+4*C^2/γ^2)*(δ+T⁻¹+ε)
  have hC0 : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans hC
  have hd0 : 0 ≤ δ+T⁻¹+ε := by positivity
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hvbound : 2*C*(δ+T⁻¹+ε)/γ ≤ η := by
    calc
      _ ≤ 2*C*(δ+T⁻¹+ε)/γ+(C/γ*(δ+T⁻¹+ε)+4*C^2/γ^2*(δ+T⁻¹+ε)) := by
        apply le_add_of_nonneg_right
        positivity
      _ = η := by dsimp [η]; ring
  have hjbound : C*(δ+T⁻¹+ε)/γ+4*C^2*(δ+T⁻¹+ε)/γ^2 ≤ η := by
    calc
      _ ≤ (C*(δ+T⁻¹+ε)/γ+4*C^2*(δ+T⁻¹+ε)/γ^2)+2*C/γ*(δ+T⁻¹+ε) := by
        apply le_add_of_nonneg_right
        positivity
      _ = η := by dsimp [η]; ring
  have hest (h : H) (hh : ‖h‖ ≤ 1) := hphysical T hT₁T history α b MH Mb l B₀ a δ ε
    hhistory hα hb hMH hMb hnα hαpos hnb hnHistory hhPos hround hl hcenter hbcenter ha₀
    hδ hε hαclose hbclose hγb hsmall heps x (hSK hx) h hh
  dsimp only at hest
  apply hendpoint A b v P' A' I I' S x MB MA Mb MI l a T η hS hSc hx
    (fun q hq => (prod q hq).1.continuous) hb hv
    (fun q hq => (prod q hq).2.2.1.continuous)
    (fun q hq => (prod q hq).2.2.2.2.2.1)
    (fun q hq => (prod q hq).2.2.2.2.1) hMB hMA hMb hMI hnBlock hnP hnA hnb
    (fun q hq => (prod q hq).2.2.2.2.2.2.1) hl ha₀ hTpos hη
  · intro q hq
    exact (unitPacketCoefficient_smooth (fun j => amps j q) X).continuous.continuousOn
  · intro q hq
    exact (unitPacketJet_smooth (fun j => amps' j q) X).continuous.continuousOn
  · intro q hq u hu
    exact unitPacketCoefficient_hasFDerivAt amps X (fun j => amps' j q) (ha q (hSK hq)) u
  · intro q hq u hu
    exact (hideal q (hSK hq)).1 u
  · intro q hq u hu
    exact (hideal q (hSK hq)).2.1 u
  · exact (hideal x (hSK hx)).2.2
  · calc
      _ = ∫ t in a..a+T,‖orthogonalMatrix basis (slope (A x) b l t)-
          orthogonalMatrix basis (scalarBaseline (fun s => α (a+s)*B) (fun s => b (a+s)) θ (t-a) • (1:E →L[ℝ] E)+T⁻¹ • I x (T⁻¹*(t-a)))‖ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith : a ≤ a+T)] at ht
        dsimp only [v]
        rw [max_eq_right (by linarith [ht.1] : 0 ≤ t-a)]
      _ ≤ 2*C*(δ+T⁻¹+ε)/γ := (hest 0 (by simp)).2.1
      _ ≤ η := hvbound
  · intro i
    change (∫ t in a..a+T,‖orthogonalMatrix basis (slopeJet A b P' l x t (hbasis i))-
      orthogonalMatrix basis (T⁻¹ • unitPacketJet (fun j => amps' j x) X (T⁻¹*(t-a)) (hbasis i))‖) ≤ η
    simp only [unitPacketJet,unitPacketCoefficient_jet_apply]
    exact ((hest (hbasis i) (by simp)).2.2.2).trans hjbound

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ} [NeZero n]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- Actual parameter differentiability of every center-regular value and slope
for compactly supported smooth insertions. Bounds are local in parameter,
not artificially global in the unbounded control space. -/
theorem actual_insertWord_differentiable {K : Set H} (hK : IsCompact K)
    (r B : ℝ) (D : Fin n → E →L[ℝ] E)
    (hD : ∀ j v,inner ℝ v (D j v) ≤ 0)
    (hBD : ∀ j v,-(B*‖v‖^2) ≤ inner ℝ v (D j v))
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (ha : ∀ x ∈ K,∀ j,HasFDerivAt (amps j) (amps' j x) x)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K) :
    ∃ T₀ C : ℝ,1 ≤ T₀ ∧ 0 ≤ C ∧ ∀ T ≥ T₀,
    ∀ (history : ℝ → E →L[ℝ] E) (α b : ℝ → ℝ) (M MH Mb a l B₀ : ℝ)
      (S : Set H), IsOpen S → IsPreconnected S → S ⊆ K →
      ContDiff ℝ ∞ history → ContDiff ℝ ∞ α → Continuous b → 0 ≤ M → 0 ≤ MH → 0 ≤ Mb →
      (∀ t,|α t| ≤ M) → (∀ t,‖history t‖ ≤ MH) → (∀ t,|b t| ≤ Mb) →
      (∀ t v,0 ≤ inner ℝ v (history t v)) →
      (∀ t ∈ Icc a (a+T),0 ≤ α t) →
      (∀ t ∈ Icc a (a+T),history t=α t • (B • (1:E →L[ℝ] E))) →
      0 ≤ a → 0 < l → (∀ t ≤ 0,∀ v,history t v=(l*(l+B₀)) • v) → (∀ t ≤ 0,b t=B₀) →
      let A := fun x => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T
      let P' := fun x t => fderiv ℝ (fun y => block (leftAction (A y)) b t) x
      ∀ x ∈ S,∀ t : ℝ,
      HasFDerivAt (fun y => operatorValue (A y) b l t) (valueJet A b P' l x t) x ∧
      HasFDerivAt (fun y => slope (A y) b l t) (slopeJet A b P' l x t) x ∧
      IsUnit (operatorValue (A x) b l t) := by
  obtain ⟨T₀,C,hT₀,hC,hproduce⟩ := actual_insertWord_compact_producer hK r B D hD hBD amps amps' ha hc hd
  refine ⟨T₀,C,hT₀,hC,?_⟩
  intro T hT history α b M MH Mb a l B₀ S hS hSc hSK hhistory hα hb hM hMH hMb hnα hnHistory hnb
    hhPos hαpos hround ha₀ hl hcenter hbcenter
  dsimp only
  let A := fun x => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T
  let P' := fun x t => fderiv ℝ (fun y => block (leftAction (A y)) b t) x
  have prod (q : H) (hq : q ∈ S) := hproduce T hT history α b M MH a hhistory hα hM hMH hnα hnHistory
    hhPos hαpos hround q (hSK hq)
  dsimp only at prod
  let MA := MH+M*C
  let MB := 1+MA+Mb+M*C
  have hMA : 0 ≤ MA := add_nonneg hMH (mul_nonneg hM hC)
  have hMB : 0 ≤ MB := by dsimp [MB]; positivity
  have hnA (q : H) (hq : q ∈ S) (t : ℝ) : ‖A q t‖ ≤ MA := (prod q hq).2.2.2.2.2.2.2.1 t
  have hnP (q : H) (hq : q ∈ S) (t : ℝ) : ‖P' q t‖ ≤ MB := by
    calc
      _ ≤ M*C/T := (prod q hq).2.2.2.2.2.2.2.2.2 t
      _ ≤ M*C := div_le_self (mul_nonneg hM hC) (hT₀.trans hT)
      _ ≤ MB := by dsimp [MB]; linarith
  have hnBlock (q : H) (hq : q ∈ S) (t : ℝ) : ‖block (leftAction (A q)) b t‖ ≤ MB := by
    apply (block_bound hMA hMb (fun t => (leftAction_norm_le (A q) t).trans (hnA q hq t)) hnb t).trans
    dsimp [MB]
    linarith [mul_nonneg hM hC]
  have hTA : 0 < T := lt_of_lt_of_le zero_lt_one (hT₀.trans hT)
  intro x hx t
  have hunit : IsUnit (operatorValue (A x) b l t) := by
    apply actual_value_unit_all_time (prod x hx).1.continuous hb hMA hMb (hnA x hx) hnb
      (prod x hx).2.2.2.2.2.2.1 hl ?_ hbcenter
    intro s hs v
    rw [insertWord_before _ _ _ _ _ _ _ _ _ hTA (hs.trans ha₀)]
    exact hcenter s hs v
  have hf := flow_hasFDerivAt_parameter_on (fun q => block (leftAction (A q)) b) P'
    hS hSc (fun q hq => block_continuous (leftAction_continuous (prod q hq).1.continuous) hb)
    (fun q hq => (prod q hq).2.2.1.continuous) (fun q hq => (prod q hq).2.2.2.2.1)
    hMB hnBlock hnP ((1:E →L[ℝ] E),l • (1:E →L[ℝ] E)) hx t
  refine ⟨(ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E)).hasFDerivAt.comp x hf,?_,hunit⟩
  exact slope_hasFDerivAt_jet_on A b P' hS hSc (fun q hq => (prod q hq).1.continuous) hb
    (fun q hq => (prod q hq).2.2.1.continuous) (fun q hq => (prod q hq).2.2.2.2.1)
    hMB hnBlock hnP l hx t hunit

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {E H ι : Type*} {n : ℕ} [NeZero n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (H →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

theorem compact_inserted_outgoing_C1 (basis : OrthonormalBasis ι ℝ E)
    {K : Set H} (hK : IsCompact K)
    (r B β p₀ θ γ M : ℝ) (D : Fin n → E →L[ℝ] E)
    (hD : ∀ j v,inner ℝ v (D j v) ≤ 0)
    (hBD : ∀ j v,-(B*‖v‖^2) ≤ inner ℝ v (D j v))
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hden : p₀+2*θ ≠ 0) (hroot : β*B-p₀*θ-θ^2=0)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (ha : ∀ x ∈ K,∀ j,HasFDerivAt (amps j) (amps' j x) x)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K) :
    ∃ T₀ Z C : ℝ,1 ≤ T₀ ∧ 0 ≤ Z ∧ 1 ≤ C ∧ ∀ T ≥ T₀,
      ∀ (history : ℝ → E →L[ℝ] E) (α b : ℝ → ℝ) (MH Mb l B₀ a δ ε : ℝ)
        (S : Set H), IsOpen S → IsPreconnected S → S ⊆ K →
      ContDiff ℝ ∞ history → ContDiff ℝ ∞ α → Continuous b → 0 ≤ MH → 0 ≤ Mb →
      (∀ t,|α t| ≤ M) → (∀ t,0 ≤ α t) → (∀ t,|b t| ≤ Mb) →
      (∀ t,‖history t‖ ≤ MH) → (∀ t v,0 ≤ inner ℝ v (history t v)) →
      (∀ t ∈ Icc a (a+T),history t=α t • (B • (1:E →L[ℝ] E))) →
      0 < l → (∀ t ≤ 0,∀ v,history t v=(l*(l+B₀)) • v) → (∀ t ≤ 0,b t=B₀) →
      0 ≤ a → 0 ≤ δ → 0 ≤ ε →
      (∀ t ∈ Icc a (a+T),|α t-β| ≤ δ) → (∀ t ∈ Icc a (a+T),|b t-p₀| ≤ δ) →
      (∀ t ∈ Icc a (a+T),γ ≤ b t) →
      ((|B|+|θ|)/γ)*δ+T⁻¹*(∑ j : Fin n,|β/(p₀+2*θ)| *Z*‖r • (B • (1:E →L[ℝ] E))+D j‖) ≤ θ/2 →
      ‖orthogonalMatrix basis (slope history b l a)-θ • (1:Matrix ι ι ℝ)‖ ≤ ε →
      let A := fun x => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T
      let Q := fun x => orthogonalMatrix basis (slope (A x) b l (a+T))-θ • (1:Matrix ι ι ℝ)
      ∀ x ∈ S,DifferentiableAt ℝ Q x ∧ max ‖Q x‖ ‖fderiv ℝ Q x‖ ≤ C*(δ+T⁻¹+ε) := by
  obtain ⟨T₁,Z,C,hT₁,hZ,hC,hphysical⟩ := compact_inserted_physical_estimates basis hK
    r B β p₀ θ γ M D hD hBD hM hB hθ hγ hden hroot amps amps' ha hc hd
  obtain ⟨T₂,JC,hT₂,hJC,hproduce⟩ := actual_insertWord_differentiable hK r B D hD hBD amps amps' ha hc hd
  let V := C+C/γ
  let R := (C+2*C*(C+C/γ))/γ
  let L := ((|B|+|θ|)/γ)*‖(1:Matrix ι ι ℝ)‖
  have hC0 : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans hC
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨max T₁ T₂,Z,1+V+R+L,hT₁.trans (le_max_left _ _),hZ,by linarith,?_⟩
  intro T hT history α b MH Mb l B₀ a δ ε S hS hSc hSK hhistory hα hb hMH hMb hnα hαpos hnb
    hnHistory hhPos hround hl hcenter hbcenter ha₀ hδ hε hαclose hbclose hγb hsmall heps
  dsimp only
  intro x hx
  have hT₁T : T₁ ≤ T := (le_max_left _ _).trans hT
  have hT₂T : T₂ ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (hT₁.trans hT₁T)
  have hTne : T ≠ 0 := ne_of_gt hTpos
  let A := fun x => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T
  let P' := fun x t => fderiv ℝ (fun y => block (leftAction (A y)) b t) x
  let Q := fun x => orthogonalMatrix basis (slope (A x) b l (a+T))-θ • (1:Matrix ι ι ℝ)
  let d := δ+T⁻¹+ε
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hslope := (hproduce T hT₂T history α b M MH Mb a l B₀ S hS hSc hSK hhistory hα hb hM hMH hMb
    hnα hnHistory hnb hhPos (fun t _ => hαpos t) hround ha₀ hl hcenter hbcenter x hx (a+T)).2.1
  have hQ : HasFDerivAt Q ((orthogonalMatrix basis).comp (slopeJet A b P' l x (a+T))) x :=
    ((orthogonalMatrix basis).hasFDerivAt.comp x hslope).sub_const _
  have hest (h : H) (hh : ‖h‖ ≤ 1) := hphysical T hT₁T history α b MH Mb l B₀ a δ ε
    hhistory hα hb hMH hMb hnα hαpos hnb hnHistory hhPos hround hl hcenter hbcenter ha₀
    hδ hε hαclose hbclose hγb hsmall heps x (hSK hx) h hh
  dsimp only at hest
  have hend : a+T ∈ Icc a (a+T) := ⟨by linarith,le_rfl⟩
  have harg : T⁻¹*(a+T-a)=1 := by rw [add_sub_cancel_left,inv_mul_cancel₀ hTne]
  let v := scalarBaseline (fun s => α (a+s)*B) (fun s => b (a+s)) θ T
  have hbase : |v-θ| ≤ ((|B|+|θ|)/γ)*δ := by
    apply berger_scalar_baseline_close (hα.continuous.comp (continuous_const.add continuous_id))
      (hb.comp (continuous_const.add continuous_id)) hM hMb hθ hγ hδ
      (fun t => hnα _) (fun t => hnb _) (fun t _ => mul_nonneg (hαpos _) hB) hroot
      (fun t ht => hαclose (a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩)
      (fun t ht => hbclose (a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩)
      (fun t ht => hγb (a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩) T ⟨hTpos.le,le_rfl⟩
  have hval : ‖Q x‖ ≤ (V+L)*d := by
    have he := (hest 0 (by simp)).1 (a+T) hend
    simp only [add_sub_cancel_left,inv_mul_cancel₀ hTne,unitPacketCoefficient_end,smul_zero,add_zero] at he
    have he' : ‖orthogonalMatrix basis (slope (A x) b l (a+T))-v • (1:Matrix ι ι ℝ)‖ ≤ V*d := by
      simpa only [map_smul,orthogonalMatrix_one] using he
    have hb' : ‖v • (1:Matrix ι ι ℝ)-θ • (1:Matrix ι ι ℝ)‖ ≤ L*δ := by
      rw [← sub_smul,norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hbase (norm_nonneg _)).trans_eq (by dsimp [L];ring)
    calc
      _ ≤ ‖orthogonalMatrix basis (slope (A x) b l (a+T))-v • (1:Matrix ι ι ℝ)‖+
        ‖v • (1:Matrix ι ι ℝ)-θ • (1:Matrix ι ι ℝ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ V*d+L*δ := add_le_add he' hb'
      _ ≤ (V+L)*d := by
        have : δ ≤ d := by dsimp [d]; linarith [inv_nonneg.mpr hTpos.le]
        nlinarith [mul_le_mul_of_nonneg_left this hL]
  have hjet : ‖fderiv ℝ Q x‖ ≤ R*d := by
    rw [hQ.fderiv]
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg hR hd0)
    intro h hh
    have he := (hest h hh.le).2.2.1 (a+T) hend
    simp only [add_sub_cancel_left,inv_mul_cancel₀ hTne,unitPacketCoefficient_end,smul_zero,map_zero,sub_zero] at he
    change ‖orthogonalMatrix basis (slopeJet A b P' l x (a+T) h)‖ ≤ _
    apply he.trans
    calc
      (C+2*C*(C+C/γ))*(δ+T⁻¹+ε)/(γ*T) = R*d/T := by dsimp [R,d]; ring
      _ ≤ R*d := div_le_self (mul_nonneg hR hd0) (hT₁.trans hT₁T)
  refine ⟨hQ.differentiableAt,max_le ?_ ?_⟩
  · exact hval.trans (mul_le_mul_of_nonneg_right (by linarith : V+L ≤ 1+V+R+L) hd0)
  · exact hjet.trans (mul_le_mul_of_nonneg_right (by linarith : R ≤ 1+V+R+L) hd0)

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff
variable {H A : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {n : ℕ}
lemma leftWord_differentiableAt (X : ℕ → H → A) {x : H}
    (hX : ∀ j,DifferentiableAt ℝ (X j) x) (m : ℕ) :
    DifferentiableAt ℝ (fun y => leftWord (fun j => X j y) m) x := by
  induction m with
  | zero => exact differentiableAt_const _
  | succ m ih =>
    exact (((contDiff_iff_contDiffAt.2 (fun z => (NormedSpace.exp_analytic (𝕂:=ℝ) z).contDiffAt) : ContDiff ℝ ∞ (NormedSpace.exp : A → A)) : ContDiff ℝ ∞ (NormedSpace.exp : A → A)).differentiable (by simp)).differentiableAt.comp x (hX m) |>.mul ih

lemma actual_packet_differentiableAt (amps : Fin n → H → ℝ) (X : Fin n → A)
    {x : H} (ha : ∀ j,DifferentiableAt ℝ (amps j) x) :
    DifferentiableAt ℝ (fun y => LinearODE.flow (fun t => ContinuousLinearMap.mul ℝ A
      (unitPacketCoefficient (fun j => amps j y) X t)) 1 1) x := by
  simp_rw [actual_packet_endpoint]
  apply leftWord_differentiableAt
  intro j
  by_cases hj : j < n
  · simpa only [extendWord,dite_eq_left hj,Pi.smul_apply,Pi.smul_apply',smul_eq_mul] using (ha ⟨j,hj⟩).smul_const (X ⟨j,hj⟩)
  · simpa only [extendWord,dite_eq_right hj] using (differentiableAt_const (0:A) : DifferentiableAt ℝ (fun _ : H => (0:A)) x)

lemma leftWord_contDiff (X : ℕ → H → A) (hX : ∀ j,ContDiff ℝ ∞ (X j)) (m : ℕ) :
    ContDiff ℝ ∞ (fun y => leftWord (fun j => X j y) m) := by
  induction m with
  | zero => exact contDiff_const
  | succ m ih => exact ((contDiff_iff_contDiffAt.2 (fun z => (NormedSpace.exp_analytic (𝕂:=ℝ) z).contDiffAt) : ContDiff ℝ ∞ (NormedSpace.exp : A → A)).comp (hX m)).mul ih

lemma actual_packet_contDiff (amps : Fin n → H → ℝ) (X : Fin n → A)
    (ha : ∀ j,ContDiff ℝ ∞ (amps j)) :
    ContDiff ℝ ∞ (fun y => LinearODE.flow (fun t => ContinuousLinearMap.mul ℝ A
      (unitPacketCoefficient (fun j => amps j y) X t)) 1 1) := by
  simp_rw [actual_packet_endpoint]
  apply leftWord_contDiff
  intro j
  by_cases hj : j < n
  · simpa only [extendWord,dite_eq_left hj,Pi.smul_apply,Pi.smul_apply',smul_eq_mul] using (ha ⟨j,hj⟩).smul_const (X ⟨j,hj⟩)
  · simpa only [extendWord,dite_eq_right hj] using (contDiff_const : ContDiff ℝ ∞ (fun _ : H => (0:A)))
end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
lemma normalized_transmission_differentiableAt (A : H → ℝ → E →L[ℝ] E)
    (b : ℝ → ℝ) (l a t c : ℝ) {x : H}
    {Da Dt : H →L[ℝ] E →L[ℝ] E}
    (ha : HasFDerivAt (fun y => operatorValue (A y) b l a) Da x)
    (ht : HasFDerivAt (fun y => operatorValue (A y) b l t) Dt x)
    (hu : IsUnit (operatorValue (A x) b l a)) :
    DifferentiableAt ℝ (fun y => c • (operatorValue (A y) b l t*
      Ring.inverse (operatorValue (A y) b l a))) x :=
  (ht.mul' (clm_inverse_fderiv hu ha)).differentiableAt.const_smul c
end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {E H ι κ : Type*} {n : ℕ} [NeZero n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [Fintype ι] [DecidableEq ι] [Fintype κ]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (H →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

lemma small_radius_bounds {G L F θ d : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hF : 0 ≤ F) (hθ : 0 < θ) (hd : 0 ≤ d)
    (h : d ≤ min (1/(1+G)) (θ/(2*(1+L+F)))) :
    G*d ≤ 1 ∧ (L+F)*d ≤ θ/2 := by
  constructor
  · have hi := (le_div_iff₀ (show 0 < 1+G by linarith)).1 (h.trans (min_le_left _ _))
    nlinarith
  · have hratio : (L+F)/(2*(1+L+F)) ≤ 1/2 :=
      (div_le_iff₀ (show 0 < 2*(1+L+F) by positivity)).2 (by linarith)
    calc
      (L+F)*d ≤ (L+F)*(θ/(2*(1+L+F))) :=
        mul_le_mul_of_nonneg_left (h.trans (min_le_right _ _)) (add_nonneg hL hF)
      _ = ((L+F)/(2*(1+L+F)))*θ := by ring
      _ ≤ (1/2)*θ := mul_le_mul_of_nonneg_right hratio hθ.le
      _ = θ/2 := by ring

lemma source_small_of_total {n : ℕ} (f : Fin n → ℝ) (hf : ∀ j,0 ≤ f j)
    {Z L δ u d θ F : ℝ} (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hfF : (∑ j,f j*Z) ≤ F)
    (hδ : δ ≤ d) (hu : u ≤ d) (hd : 0 ≤ d) (hS : (L+F)*d ≤ θ/2) :
    L*δ+u*(∑ j,f j*Z) ≤ θ/2 := by
  have hz : 0 ≤ ∑ j,f j*Z := Finset.sum_nonneg (fun j _ => mul_nonneg (hf j) hZ)
  calc
    _ ≤ L*d+d*F := add_le_add (mul_le_mul_of_nonneg_left hδ hL) (mul_le_mul hu hfF hz hd)
    _ = (L+F)*d := by ring
    _ ≤ θ/2 := hS

lemma exponential_error_linear {J G d : ℝ} (hJ : 0 ≤ J) (hG : 0 ≤ G)
    (hd : 0 ≤ d) (hGd : G*d ≤ 1) :
    Real.exp (2*J+J*(G*d))*(J*(G*d)) ≤ (Real.exp (3*J)*J*G)*d := by
  calc
    _ ≤ Real.exp (3*J)*(J*(G*d)) := by
      apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hGd hJ]
    _ = _ := by ring

theorem compact_inserted_linear_C1 (basis : OrthonormalBasis ι ℝ E)
    (hbasis : OrthonormalBasis κ ℝ H) {K : Set H} (hK : IsCompact K)
    (r B β p₀ θ γ M : ℝ) (D : Fin n → E →L[ℝ] E)
    (hD : ∀ j v,inner ℝ v (D j v) ≤ 0)
    (hBD : ∀ j v,-(B*‖v‖^2) ≤ inner ℝ v (D j v))
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hθ : 0 < θ) (hγ : 0 < γ)
    (hden : p₀+2*θ ≠ 0) (hroot : β*B-p₀*θ-θ^2=0)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (ha : ∀ x ∈ K,∀ j,HasFDerivAt (amps j) (amps' j x) x)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K) :
    ∃ T₀ ρ C : ℝ,1 ≤ T₀ ∧ 0 < ρ ∧ 1 ≤ C ∧ ∀ T ≥ T₀,
      ∀ (history : ℝ → E →L[ℝ] E) (α b : ℝ → ℝ) (MH Mb l B₀ a δ ε : ℝ)
        (S : Set H), IsOpen S → IsPreconnected S → S ⊆ K →
      ContDiff ℝ ∞ history → ContDiff ℝ ∞ α → Continuous b → 0 ≤ MH → 0 ≤ Mb →
      (∀ t,|α t| ≤ M) → (∀ t,0 ≤ α t) → (∀ t,|b t| ≤ Mb) →
      (∀ t,‖history t‖ ≤ MH) → (∀ t v,0 ≤ inner ℝ v (history t v)) →
      (∀ t ∈ Icc a (a+T),history t=α t • (B • (1:E →L[ℝ] E))) →
      0 < l → (∀ t ≤ 0,∀ v,history t v=(l*(l+B₀)) • v) → (∀ t ≤ 0,b t=B₀) →
      0 ≤ a → 0 ≤ δ → 0 ≤ ε →
      (∀ t ∈ Icc a (a+T),|α t-β| ≤ δ) → (∀ t ∈ Icc a (a+T),|b t-p₀| ≤ δ) →
      (∀ t ∈ Icc a (a+T),γ ≤ b t) →
      δ+T⁻¹+ε ≤ ρ →
      ‖orthogonalMatrix basis (slope history b l a)-θ • (1:Matrix ι ι ℝ)‖ ≤ ε →
      let A := fun x => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T
      let v := fun t => scalarBaseline (fun s => α (a+s)*B) (fun s => b (a+s)) θ (max 0 (t-a))
      let W := fun x => flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E)
        (unitPacketCoefficient (fun j => amps j x) (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) t)) 1 1
      let Y := fun x => Real.exp (-(∫ t in a..a+T,v t)) •
        (operatorValue (A x) b l (a+T)*Ring.inverse (operatorValue (A x) b l a))
      let Q := fun x => orthogonalMatrix basis (slope (A x) b l (a+T))-θ • (1:Matrix ι ι ℝ)
      ∀ x ∈ S,DifferentiableAt ℝ Y x ∧ DifferentiableAt ℝ Q x ∧
        max (max ‖Y x-W x‖ ‖fderiv ℝ Y x-fderiv ℝ W x‖)
          (max ‖Q x‖ ‖fderiv ℝ Q x‖) ≤ C*(δ+T⁻¹+ε) := by
  obtain ⟨T₁,Z₁,C₁,J,hT₁,hZ₁,hC₁,hJ,hend⟩ := compact_inserted_endpoint_C1 basis hbasis hK
    r B β p₀ θ γ M D hD hBD hM hB hθ.le hγ hden hroot amps amps' ha hc hd
  obtain ⟨T₂,Z₂,C₂,hT₂,hZ₂,hC₂,hout⟩ := compact_inserted_outgoing_C1 basis hK
    r B β p₀ θ γ M D hD hBD hM hB hθ.le hγ hden hroot amps amps' ha hc hd
  obtain ⟨T₃,JC,hT₃,hJC,hdiff⟩ := actual_insertWord_differentiable hK r B D hD hBD amps amps' ha hc hd
  let G := 3*C₁/γ+4*C₁^2/γ^2
  let L := (|B|+|θ|)/γ
  let F := ∑ j : Fin n,|β/(p₀+2*θ)| *(Z₁+Z₂)*‖r • (B • (1:E →L[ℝ] E))+D j‖
  have hC₁0 : 0 ≤ C₁ := (by norm_num : (0:ℝ) ≤ 1).trans hC₁
  have hC₂0 : 0 ≤ C₂ := (by norm_num : (0:ℝ) ≤ 1).trans hC₂
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let ρ := min (1/(1+G)) (θ/(2*(1+L+F)))
  let CE := Real.exp (3*J)*J*G
  have hCE : 0 ≤ CE := by dsimp [CE]; positivity
  refine ⟨max T₁ (max T₂ T₃),ρ,1+CE+C₂,hT₁.trans (le_max_left _ _),by dsimp [ρ]; positivity,by linarith,?_⟩
  intro T hT history α b MH Mb l B₀ a δ ε S hS hSc hSK hhistory hα hb hMH hMb hnα hαpos hnb
    hnHistory hhPos hround hl hcenter hbcenter ha₀ hδ hε hαclose hbclose hγb hsmall heps
  dsimp only
  intro x hx
  have hT₁T : T₁ ≤ T := (le_max_left _ _).trans hT
  have hT₂T : T₂ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hT₃T : T₃ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (hT₁.trans hT₁T)
  have hTi : 0 ≤ T⁻¹ := inv_nonneg.mpr hTpos.le
  let d := δ+T⁻¹+ε
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hδd : δ ≤ d := by dsimp [d]; linarith
  have hTid : T⁻¹ ≤ d := by dsimp [d]; linarith
  obtain ⟨hGd,hSd⟩ := small_radius_bounds hG hL hF hθ hd0 hsmall
  have hs (Z : ℝ) (hZ : 0 ≤ Z) (hZZ : Z ≤ Z₁+Z₂) :
      L*δ+T⁻¹*(∑ j : Fin n,|β/(p₀+2*θ)| *Z*‖r • (B • (1:E →L[ℝ] E))+D j‖) ≤ θ/2 := by
    have hzF : (∑ j : Fin n,|β/(p₀+2*θ)| *Z*‖r • (B • (1:E →L[ℝ] E))+D j‖) ≤ F := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZZ (abs_nonneg _)) (norm_nonneg _)
    have hh := source_small_of_total (fun j : Fin n => |β/(p₀+2*θ)| *‖r • (B • (1:E →L[ℝ] E))+D j‖)
      (fun j => mul_nonneg (abs_nonneg _) (norm_nonneg _)) hZ hL
      (by simpa only [mul_right_comm] using hzF) hδd hTid hd0 hSd
    simpa only [mul_right_comm] using hh
  have he := hend T hT₁T history α b MH Mb l B₀ a δ ε S hS hSc hSK hhistory hα hb hMH hMb
    hnα hαpos hnb hnHistory hhPos hround hl hcenter hbcenter ha₀ hδ hε hαclose hbclose hγb
    (hs Z₁ hZ₁ (by linarith)) heps x hx
  have ho := hout T hT₂T history α b MH Mb l B₀ a δ ε S hS hSc hSK hhistory hα hb hMH hMb
    hnα hαpos hnb hnHistory hhPos hround hl hcenter hbcenter ha₀ hδ hε hαclose hbclose hγb
    (hs Z₂ hZ₂ (by linarith)) heps x hx
  have hf := hdiff T hT₃T history α b M MH Mb a l B₀ S hS hSc hSK hhistory hα hb hM hMH hMb
    hnα hnHistory hnb hhPos (fun t _ => hαpos t) hround ha₀ hl hcenter hbcenter x hx
  dsimp only at he ho hf
  refine ⟨normalized_transmission_differentiableAt _ _ _ _ _ _ (hf a).1 (hf (a+T)).1 (hf a).2.2,ho.1,max_le ?_ ?_⟩
  · apply he.trans
    exact (exponential_error_linear hJ hG hd0 hGd).trans
      (mul_le_mul_of_nonneg_right (by linarith : CE ≤ 1+CE+C₂) hd0)
  · exact ho.2.trans (mul_le_mul_of_nonneg_right (by linarith : C₂ ≤ 1+CE+C₂) hd0)

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set
open scoped ContDiff BigOperators Matrix.Norms.Frobenius
variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
local instance : NormedAddCommGroup (H →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (H →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

lemma linear_C1_error (L : E →L[ℝ] F) {f g : H → E} {x : H} {η : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (he : max ‖f x-g x‖ ‖fderiv ℝ f x-fderiv ℝ g x‖ ≤ η) :
    max ‖L (f x)-L (g x)‖
      ‖fderiv ℝ (fun y => L (f y)) x-fderiv ℝ (fun y => L (g y)) x‖ ≤ ‖L‖*η := by
  apply max_le
  · rw [← map_sub]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans he) (norm_nonneg _))
  · change ‖fderiv ℝ (L ∘ f) x-fderiv ℝ (L ∘ g) x‖ ≤ ‖L‖*η
    rw [(L.hasFDerivAt.comp x hf.hasFDerivAt).fderiv,
      (L.hasFDerivAt.comp x hg.hasFDerivAt).fderiv,← ContinuousLinearMap.comp_sub]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans he) (norm_nonneg _))

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open HarmonicCounterexample.FiniteControl.SmoothWord
open scoped Matrix.Norms.Frobenius
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

def orthogonalMatrixAlgHom (b : OrthonormalBasis ι ℝ E) :
    (E →L[ℝ] E) →ₐ[ℝ] Matrix ι ι ℝ where
  toFun := orthogonalMatrix b
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := orthogonalMatrix_one b
  map_mul' := orthogonalMatrix_mul b
  commutes' c := by simp only [Algebra.algebraMap_eq_smul_one,map_smul,orthogonalMatrix_one]

lemma orthogonalMatrix_exp (b : OrthonormalBasis ι ℝ E) (X : E →L[ℝ] E) :
    orthogonalMatrix b (NormedSpace.exp X)=NormedSpace.exp (orthogonalMatrix b X) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact NormedSpace.map_exp (orthogonalMatrixAlgHom b) (orthogonalMatrix b).continuous X

lemma orthogonalMatrix_leftWord (b : OrthonormalBasis ι ℝ E) (X : ℕ → E →L[ℝ] E) (n : ℕ) :
    orthogonalMatrix b (leftWord X n)=leftWord (fun j => orthogonalMatrix b (X j)) n := by
  induction n with
  | zero => exact orthogonalMatrix_one b
  | succ n ih =>
    rw [leftWord,orthogonalMatrix_mul,orthogonalMatrix_exp,ih]
    rfl

/-- Orthonormal coordinates of the genuine chronological ideal packet. -/
lemma orthogonalMatrix_packet (b : OrthonormalBasis ι ℝ E) {n : ℕ}
    (a : Fin n → ℝ) (X : Fin n → E →L[ℝ] E) :
    orthogonalMatrix b (flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E)
      (unitPacketCoefficient a X t)) 1 1)=
      flow (fun t => ContinuousLinearMap.mul ℝ (Matrix ι ι ℝ)
        (unitPacketCoefficient a (fun j => orthogonalMatrix b (X j)) t)) 1 1 := by
  rw [actual_packet_endpoint,actual_packet_endpoint,orthogonalMatrix_leftWord]
  congr 1
  funext j
  by_cases hj : j < n
  · simp only [extendWord,dite_eq_left hj,map_smul]
  · simp only [extendWord,dite_eq_right hj,map_zero]

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {E H ι κ : Type*} {n : ℕ} [NeZero n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [Fintype ι] [DecidableEq ι] [Fintype κ]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (H →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

theorem compact_inserted_matrix_C1 (basis : OrthonormalBasis ι ℝ E)
    (hbasis : OrthonormalBasis κ ℝ H) {K : Set H} (hK : IsCompact K)
    (r B β p₀ θ γ M : ℝ) (D : Fin n → E →L[ℝ] E)
    (hD : ∀ j v,inner ℝ v (D j v) ≤ 0)
    (hBD : ∀ j v,-(B*‖v‖^2) ≤ inner ℝ v (D j v))
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hθ : 0 < θ) (hγ : 0 < γ)
    (hden : p₀+2*θ ≠ 0) (hroot : β*B-p₀*θ-θ^2=0)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (ha : ∀ x ∈ K,∀ j,HasFDerivAt (amps j) (amps' j x) x)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K) :
    ∃ T₀ ρ C : ℝ,1 ≤ T₀ ∧ 0 < ρ ∧ 1 ≤ C ∧ ∀ T ≥ T₀,
      ∀ (history : ℝ → E →L[ℝ] E) (α b : ℝ → ℝ) (MH Mb l B₀ a δ ε : ℝ)
        (S : Set H), IsOpen S → IsPreconnected S → S ⊆ K →
      ContDiff ℝ ∞ history → ContDiff ℝ ∞ α → Continuous b → 0 ≤ MH → 0 ≤ Mb →
      (∀ t,|α t| ≤ M) → (∀ t,0 ≤ α t) → (∀ t,|b t| ≤ Mb) →
      (∀ t,‖history t‖ ≤ MH) → (∀ t v,0 ≤ inner ℝ v (history t v)) →
      (∀ t ∈ Icc a (a+T),history t=α t • (B • (1:E →L[ℝ] E))) →
      0 < l → (∀ t ≤ 0,∀ v,history t v=(l*(l+B₀)) • v) → (∀ t ≤ 0,b t=B₀) →
      0 ≤ a → 0 ≤ δ → 0 ≤ ε →
      (∀ t ∈ Icc a (a+T),|α t-β| ≤ δ) → (∀ t ∈ Icc a (a+T),|b t-p₀| ≤ δ) →
      (∀ t ∈ Icc a (a+T),γ ≤ b t) →
      δ+T⁻¹+ε ≤ ρ →
      ‖orthogonalMatrix basis (slope history b l a)-θ • (1:Matrix ι ι ℝ)‖ ≤ ε →
      let A := fun x => insertWord history α r (B • (1:E →L[ℝ] E)) D (fun j => amps j x) a T
      let v := fun t => scalarBaseline (fun s => α (a+s)*B) (fun s => b (a+s)) θ (max 0 (t-a))
      let W := fun x => orthogonalMatrix basis (flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E)
        (unitPacketCoefficient (fun j => amps j x) (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) t)) 1 1)
      let Y := fun x => orthogonalMatrix basis (Real.exp (-(∫ t in a..a+T,v t)) •
        (operatorValue (A x) b l (a+T)*Ring.inverse (operatorValue (A x) b l a)))
      let Q := fun x => orthogonalMatrix basis (slope (A x) b l (a+T))-θ • (1:Matrix ι ι ℝ)
      ∀ x ∈ S,DifferentiableAt ℝ Y x ∧ DifferentiableAt ℝ Q x ∧
        max (max ‖Y x-W x‖ ‖fderiv ℝ Y x-fderiv ℝ W x‖)
          (max ‖Q x‖ ‖fderiv ℝ Q x‖) ≤ C*(δ+T⁻¹+ε) := by
  obtain ⟨T₀,ρ,C,hT₀,hρ,hC,hworks⟩ := compact_inserted_linear_C1 basis hbasis hK
    r B β p₀ θ γ M D hD hBD hM hB hθ hγ hden hroot amps amps' ha hc hd
  let L := orthogonalMatrix basis
  have hL : 1 ≤ max 1 ‖L‖ := le_max_left _ _
  refine ⟨T₀,ρ,max 1 ‖L‖*C,hT₀,hρ,(by nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ C by linarith)]),?_⟩
  intro T hT history α b MH Mb l B₀ a δ ε S hS hSc hSK hhistory hα hb hMH hMb hnα hαpos hnb
    hnHistory hhPos hround hl hcenter hbcenter ha₀ hδ hε hαclose hbclose hγb hsmall heps
  dsimp only
  intro x hx
  obtain ⟨hY,hQ,he⟩ := hworks T hT history α b MH Mb l B₀ a δ ε S hS hSc hSK hhistory hα hb hMH hMb
    hnα hαpos hnb hnHistory hhPos hround hl hcenter hbcenter ha₀ hδ hε hαclose hbclose hγb
    hsmall heps x hx
  have hW := actual_packet_differentiableAt amps
    (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) (fun j => (ha x (hSK hx) j).differentiableAt)
  have hd0 : 0 ≤ δ+T⁻¹+ε := by
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (hT₀.trans hT)
    positivity
  refine ⟨L.differentiableAt.comp x hY,hQ,max_le ?_ ?_⟩
  · exact (linear_C1_error L hY hW ((le_max_left _ _).trans he)).trans
      (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) ‖L‖) (mul_nonneg (by linarith : 0 ≤ C) hd0))
  · apply ((le_max_right _ _).trans he).trans
    have hc0 : 0 ≤ C*(δ+T⁻¹+ε) := mul_nonneg (by linarith) hd0
    rw [mul_assoc]
    exact le_mul_of_one_le_left hc0 hL

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open scoped BigOperators
variable {β H : Type*} [Fintype β] [NormedAddCommGroup H] [NormedSpace ℝ H]
  {F : β → Type*} [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)]
local instance : NormedAddCommGroup (H →L[ℝ] ((i : β) → F i)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] ((i : β) → F i)) := ContinuousLinearMap.toNormedSpace

lemma pi_linear_difference_bound (f g : (i : β) → H →L[ℝ] F i) {η : ℝ}
    (hη : 0 ≤ η) (he : ∀ i,‖f i-g i‖ ≤ η) :
    ‖ContinuousLinearMap.pi f-ContinuousLinearMap.pi g‖ ≤ η := by
  apply ContinuousLinearMap.opNorm_le_bound _ hη
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hη (norm_nonneg v))).2
  intro i
  change ‖(f i-g i) v‖ ≤ η*‖v‖
  exact ((f i-g i).le_opNorm v).trans (mul_le_mul_of_nonneg_right (he i) (norm_nonneg v))

/-- Simultaneous finite-factor Frechet C1 control in the actual product norm. -/
theorem finite_C1_error {f g : (i : β) → H → F i} {x : H} {η : ℝ}
    (hη : 0 ≤ η) (hf : ∀ i,DifferentiableAt ℝ (f i) x)
    (hg : ∀ i,DifferentiableAt ℝ (g i) x)
    (he : ∀ i,max ‖f i x-g i x‖ ‖fderiv ℝ (f i) x-fderiv ℝ (g i) x‖ ≤ η) :
    DifferentiableAt ℝ (fun y i => f i y) x ∧
      max ‖(fun i => f i x)-(fun i => g i x)‖
        ‖fderiv ℝ (fun y i => f i y) x-fderiv ℝ (fun y i => g i y) x‖ ≤ η := by
  have hdf := hasFDerivAt_pi.2 (fun i => (hf i).hasFDerivAt)
  have hdg := hasFDerivAt_pi.2 (fun i => (hg i).hasFDerivAt)
  refine ⟨hdf.differentiableAt,max_le ?_ ?_⟩
  · exact (pi_norm_le_iff_of_nonneg hη).2 (fun i => (le_max_left _ _).trans (he i))
  · rw [hdf.fderiv,hdg.fderiv]
    exact pi_linear_difference_bound _ _ hη (fun i => (le_max_right _ _).trans (he i))

lemma finite_C1_norm {f : (i : β) → H → F i} {x : H} {η : ℝ}
    (hη : 0 ≤ η) (hf : ∀ i,DifferentiableAt ℝ (f i) x)
    (he : ∀ i,max ‖f i x‖ ‖fderiv ℝ (f i) x‖ ≤ η) :
    DifferentiableAt ℝ (fun y i => f i y) x ∧
      max ‖(fun i => f i x)‖ ‖fderiv ℝ (fun y i => f i y) x‖ ≤ η := by
  have hdf := hasFDerivAt_pi.2 (fun i => (hf i).hasFDerivAt)
  refine ⟨hdf.differentiableAt,max_le ?_ ?_⟩
  · exact (pi_norm_le_iff_of_nonneg hη).2 (fun i => (le_max_left _ _).trans (he i))
  · rw [hdf.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ hη
    intro v
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hη (norm_nonneg v))).2
    intro i
    exact ((fderiv ℝ (f i) x).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (he i)) (norm_nonneg v))

end HarmonicCounterexample.LinearODE

end

end OAI
