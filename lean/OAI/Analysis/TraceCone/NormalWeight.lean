import OAI.Analysis.TraceCone.WeakClosure

namespace OAI

/-!
# The tracial weight on the GNS weak closure

Finite-root actions recover the Hilbert norm. Strong-star density then extends
the trace identity from the represented algebra to its weak closure.
-/

noncomputable section

open Filter Topology
open scoped NNReal ENNReal

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

/-- The positive contractive action of a finite trace square root. -/
def finiteRootAction (e : τ.FiniteTraceContraction) : τ.TraceGNS →L[ℂ] τ.TraceGNS :=
  τ.traceGNSRep (CFC.sqrt e.1.1)

lemma finiteRootAction_norm_le (e : τ.FiniteTraceContraction) : ‖τ.finiteRootAction e‖ ≤ 1 := by
  calc
    ‖τ.finiteRootAction e‖ ≤ ‖CFC.sqrt e.1.1‖ := NonUnitalStarAlgHom.norm_apply_le _ _
    _ = Real.sqrt ‖e.1.1‖ := CFC.norm_sqrt e.1.1 e.1.2
    _ ≤ 1 := (Real.sqrt_le_one).mpr e.2.2.le

lemma finiteRootAction_apply_norm_le (e : τ.FiniteTraceContraction) (ξ : τ.TraceGNS) :
    ‖τ.finiteRootAction e ξ‖ ≤ ‖ξ‖ := by
  exact ((τ.finiteRootAction e).le_opNorm ξ).trans (mul_le_of_le_one_left (norm_nonneg _) (τ.finiteRootAction_norm_le e))

lemma finiteRootAction_on_lambda (e : τ.FiniteTraceContraction) (x : τ.finiteSquareAlgebra) :
    ‖τ.finiteRootAction e (τ.traceGNSLambda x)‖ ^ 2 =
      τ.traceVectorForm e.1 e.2.1 (τ.traceGNSRep (x.1 * star x.1)) := by
  change ‖τ.traceGNSRep (CFC.sqrt e.1.1) (τ.traceGNSLambda x)‖ ^ 2 = _
  rw [τ.traceGNSRep_covariance,τ.traceGNSLambda_norm_sq]
  have he : x.1*star x.1 = star (star x.1)*star x.1 := by rw [star_star]
  conv_rhs => rw [he,τ.traceVectorForm_rep_starMul]
  congr 2
  apply Subtype.ext
  change star (CFC.sqrt e.1.1 * x.1) * (CFC.sqrt e.1.1 * x.1) =
    star (star (star x.1)) * e.1.1 * star (star x.1)
  simp only [star_mul,star_star,(CFC.sqrt_nonneg e.1.1).isSelfAdjoint.star_eq,
    mul_assoc,← mul_assoc (CFC.sqrt e.1.1) (CFC.sqrt e.1.1),CFC.sqrt_mul_sqrt_self e.1.1 e.1.2]

lemma finiteRootAction_iSup_lambda (x : τ.finiteSquareAlgebra) :
    (⨆ e : τ.FiniteTraceContraction, ENNReal.ofReal (‖τ.finiteRootAction e (τ.traceGNSLambda x)‖ ^ 2)) =
      ENNReal.ofReal (‖τ.traceGNSLambda x‖ ^ 2) := by
  simp_rw [τ.finiteRootAction_on_lambda]
  change τ.traceNormalWeight (τ.traceGNSPositive (Positive.mulStar x.1)) = _
  have hf : τ (Positive.mulStar x.1) < ∞ := by rw [← τ.tracial]; exact x.2
  rw [τ.traceNormalWeight_rep_eq_of_finite _ hf,τ.traceGNSLambda_norm_sq,ENNReal.ofReal_toReal (τ.traceSquare_ne_top x),τ.tracial]

/-- The finite-root actions detect the Hilbert norm by density and the finite trace identity. -/
lemma finiteRootAction_detects_norm (ξ : τ.TraceGNS) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ e : τ.FiniteTraceContraction, ‖τ.finiteRootAction e ξ‖ ≤ r) : ‖ξ‖ ≤ r := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x,hx⟩ := τ.traceGNSLambda_dense.exists_dist_lt ξ (half_pos hε)
  have hx' : ‖τ.traceGNSLambda x-ξ‖ < ε/2 := by simpa only [dist_eq_norm,norm_sub_rev] using hx
  have hbound : ∀ e : τ.FiniteTraceContraction,
      ‖τ.finiteRootAction e (τ.traceGNSLambda x)‖ ≤ r+ε/2 := by
    intro e
    calc
      ‖τ.finiteRootAction e (τ.traceGNSLambda x)‖ ≤
          ‖τ.finiteRootAction e ξ‖ + ‖τ.finiteRootAction e (τ.traceGNSLambda x-ξ)‖ := by
            rw [map_sub]
            exact norm_le_norm_add_norm_sub' _ _
      _ ≤ r + ε/2 := add_le_add (h e) ((τ.finiteRootAction_apply_norm_le e _).trans hx'.le)
  have hn : ENNReal.ofReal (‖τ.traceGNSLambda x‖ ^ 2) ≤ ENNReal.ofReal ((r+ε/2)^2) := by
    rw [← τ.finiteRootAction_iSup_lambda]
    exact iSup_le (fun e => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hbound e) 2))
  have hn' : ‖τ.traceGNSLambda x‖ ^ 2 ≤ (r+ε/2)^2 := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hn
  have hnorm : ‖τ.traceGNSLambda x‖ ≤ r+ε/2 := by nlinarith [norm_nonneg (τ.traceGNSLambda x)]
  have ht := norm_le_norm_add_norm_sub' ξ (τ.traceGNSLambda x)
  rw [norm_sub_rev] at ht
  linarith

lemma finiteRootAction_iSup_norm (ξ : τ.TraceGNS) :
    (⨆ e : τ.FiniteTraceContraction, ENNReal.ofReal (‖τ.finiteRootAction e ξ‖ ^ 2)) =
      ENNReal.ofReal (‖ξ‖ ^ 2) := by
  let c : ℝ≥0∞ := ⨆ e : τ.FiniteTraceContraction, ENNReal.ofReal (‖τ.finiteRootAction e ξ‖ ^ 2)
  have hle : c ≤ ENNReal.ofReal (‖ξ‖ ^ 2) :=
    iSup_le (fun e => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (τ.finiteRootAction_apply_norm_le e ξ) 2))
  have hc : c ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  apply le_antisymm hle
  have hbound (e : τ.FiniteTraceContraction) : ‖τ.finiteRootAction e ξ‖ ≤ Real.sqrt c.toReal := by
    have hi : ENNReal.ofReal (‖τ.finiteRootAction e ξ‖ ^ 2) ≤ c :=
      le_iSup (fun e : τ.FiniteTraceContraction => ENNReal.ofReal (‖τ.finiteRootAction e ξ‖ ^ 2)) e
    have hi' : ‖τ.finiteRootAction e ξ‖ ^ 2 ≤ c.toReal := by
      have hh := ENNReal.toReal_mono hc hi
      simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hh
    exact (Real.le_sqrt (norm_nonneg _) ENNReal.toReal_nonneg).mpr hi'
  have hn := τ.finiteRootAction_detects_norm ξ (Real.sqrt c.toReal) (Real.sqrt_nonneg _) hbound
  have hn' : ‖ξ‖ ^ 2 ≤ c.toReal := by
    calc
      ‖ξ‖ ^ 2 ≤ (Real.sqrt c.toReal)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = c.toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  calc
    ENNReal.ofReal (‖ξ‖ ^ 2) ≤ ENNReal.ofReal c.toReal := ENNReal.ofReal_le_ofReal hn'
    _ = c := ENNReal.ofReal_toReal hc

end ExtendedTrace
end TraceConeClassification

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : ExtendedTrace A)

lemma finiteRootAction_double_rep (e f : τ.FiniteTraceContraction) (x : A) :
    ‖τ.finiteRootAction f (τ.traceGNSRep x (τ.traceVector e.1 e.2.1))‖ ^ 2 =
      ‖τ.finiteRootAction e (star (τ.traceGNSRep x) (τ.traceVector f.1 f.2.1))‖ ^ 2 := by
  rw [← map_star]
  change ‖τ.traceGNSRep (CFC.sqrt f.1.1) (τ.traceGNSRep x (τ.traceGNSLambda (τ.finiteTraceSqrt e.1 e.2.1)))‖ ^ 2 =
    ‖τ.traceGNSRep (CFC.sqrt e.1.1) (τ.traceGNSRep (star x) (τ.traceGNSLambda (τ.finiteTraceSqrt f.1 f.2.1)))‖ ^ 2
  simp_rw [τ.traceGNSRep_covariance,τ.traceGNSLambda_norm_sq]
  rw [τ.tracial]
  congr 2
  apply Subtype.ext
  change (CFC.sqrt f.1.1 * (x * CFC.sqrt e.1.1))*star (CFC.sqrt f.1.1 * (x * CFC.sqrt e.1.1)) =
    star (CFC.sqrt e.1.1 * (star x * CFC.sqrt f.1.1))*(CFC.sqrt e.1.1 * (star x * CFC.sqrt f.1.1))
  simp only [star_mul,star_star,(CFC.sqrt_nonneg e.1.1).isSelfAdjoint.star_eq,
    (CFC.sqrt_nonneg f.1.1).isSelfAdjoint.star_eq,mul_assoc]

lemma finiteRootAction_double (e f : τ.FiniteTraceContraction) (T : τ.traceWeakClosure) :
    ‖τ.finiteRootAction f (T.1 (τ.traceVector e.1 e.2.1))‖ ^ 2 =
      ‖τ.finiteRootAction e (star T.1 (τ.traceVector f.1 f.2.1))‖ ^ 2 := by
  let ξ : Fin 2 → τ.TraceGNS := ![τ.traceVector e.1 e.2.1,τ.traceVector f.1 f.2.1]
  have happ (n : ℕ) : ∃ x : A, ∀ i,
      ‖τ.traceGNSRep x (ξ i)-T.1 (ξ i)‖ < 1/(n+1:ℝ) ∧
      ‖star (τ.traceGNSRep x) (ξ i)-star T.1 (ξ i)‖ < 1/(n+1:ℝ) := by
    obtain ⟨R,hR,he⟩ := weakClosure_strong_star_density
      (NonUnitalStarAlgHom.range τ.traceGNSRep) T.1 T.2 2 ξ (1/(n+1:ℝ)) (by positivity)
    obtain ⟨x,rfl⟩ := hR
    exact ⟨x,he⟩
  choose x hx using happ
  have ht : Tendsto (fun n => τ.traceGNSRep (x n) (ξ 0)) atTop (𝓝 (T.1 (ξ 0))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hx n 0).1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hts : Tendsto (fun n => star (τ.traceGNSRep (x n)) (ξ 1)) atTop (𝓝 (star T.1 (ξ 1))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hx n 1).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have h₁ := (((τ.finiteRootAction f).continuous.tendsto (T.1 (ξ 0))).comp ht).norm.pow 2
  have h₂ := (((τ.finiteRootAction e).continuous.tendsto (star T.1 (ξ 1))).comp hts).norm.pow 2
  exact tendsto_nhds_unique h₁ (h₂.congr (fun n => (τ.finiteRootAction_double_rep e f (x n)).symm))

lemma traceNormalWeight_tracial (T : τ.traceWeakClosure) :
    τ.traceNormalWeight (Positive.starMul T) = τ.traceNormalWeight (Positive.mulStar T) := by
  change (⨆ e : τ.FiniteTraceContraction, ENNReal.ofReal (τ.traceVectorForm e.1 e.2.1 (star T.1*T.1))) =
    ⨆ e : τ.FiniteTraceContraction, ENNReal.ofReal (τ.traceVectorForm e.1 e.2.1 (T.1*star T.1))
  have he : T.1*star T.1 = star (star T.1)*star T.1 := by rw [star_star]
  rw [he]
  simp_rw [τ.traceVectorForm_starMul]
  calc
    (⨆ e : τ.FiniteTraceContraction, ENNReal.ofReal (‖T.1 (τ.traceVector e.1 e.2.1)‖ ^ 2)) =
        ⨆ e : τ.FiniteTraceContraction, ⨆ f : τ.FiniteTraceContraction,
          ENNReal.ofReal (‖τ.finiteRootAction f (T.1 (τ.traceVector e.1 e.2.1))‖ ^ 2) := by
      congr 1
      funext e
      exact (τ.finiteRootAction_iSup_norm _).symm
    _ = ⨆ f : τ.FiniteTraceContraction, ⨆ e : τ.FiniteTraceContraction,
          ENNReal.ofReal (‖τ.finiteRootAction f (T.1 (τ.traceVector e.1 e.2.1))‖ ^ 2) := iSup_comm
    _ = ⨆ f : τ.FiniteTraceContraction, ENNReal.ofReal (‖star T.1 (τ.traceVector f.1 f.2.1)‖ ^ 2) := by
      congr 1
      funext f
      simp_rw [τ.finiteRootAction_double _ f T]
      exact τ.finiteRootAction_iSup_norm _

/-- The tracial weight on the GNS weak operator closure. -/
def normalTraceCandidate : ExtendedTrace τ.traceWeakClosure where
  toFun := τ.traceNormalWeight
  map_zero := τ.traceNormalWeight_zero
  map_add := τ.traceNormalWeight_add
  map_scale r _ := τ.traceNormalWeight_scale r
  tracial := τ.traceNormalWeight_tracial
  lowerSemicontinuous := τ.traceNormalWeight_lowerSemicontinuous

end ExtendedTrace
end TraceConeClassification

end

end OAI
