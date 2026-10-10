import OAI.Analysis.FactorGeneration.PatchingBounds
import OAI.Analysis.FactorGeneration.RepresentedCorners
import OAI.Analysis.FactorGeneration.ResidualEstimates

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Construct local patches in the actual f=1 residual. Both residual trace
terms are retained. Admissibility of the full extended word family is not asserted. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
theorem unitResidual_scalar_two_moment_bound (v : PartialUnitary M)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4)
    (x : M.toStarSubalgebra) (A B : ℝ) (hAB : 0 ≤ A+B)
    (hA : ‖τ.trace x‖ ≤ A*(τ.trace v.support.val).re)
    (hB : ‖τ.trace (star v.val*x*v.val)‖ ≤ B*(τ.trace v.support.val).re) :
    ‖cornerScalar τ (unitResidual v) x‖ ≤ (A+B)/3 := by
  have htrace : τ.trace ((unitResidual v).val*x*(unitResidual v).val)=
      τ.trace x-τ.trace (star v.val*x*v.val) := by
    simpa only [residualCorner,unitResidual,identityProjection,one_mul] using
      residualCorner_compression_trace τ (identityProjection M) v (one_mul _) x
  rw [cornerScalar,htrace,norm_div,projection_trace_real τ (unitResidual v),
    Complex.norm_real,Real.norm_of_nonneg (unitResidual_positive τ v hsmall).le]
  rw [div_le_iff₀ (unitResidual_positive τ v hsmall)]
  have hn := norm_sub_le (τ.trace x) (τ.trace (star v.val*x*v.val))
  rw [unitResidual_trace,Complex.sub_re,Complex.one_re]
  nlinarith [mul_le_mul_of_nonneg_left hsmall hAB]

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_unitResidual_local_compression
    (v : PartialUnitary M) (hvN : v.val.val ∈ N)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra) (A B : ι → ℝ)
    (hAB : ∀ i ∈ F,0 ≤ A i+B i)
    (hA : ∀ i ∈ F,‖τ.trace (x i)‖ ≤ A i*(τ.trace v.support.val).re)
    (hB : ∀ i ∈ F,‖τ.trace (star v.val*x i*v.val)‖ ≤ B i*(τ.trace v.support.val).re)
    (η : ℝ) (hη : 0 < η) :
    ∃ q : AlgebraProjection M,q ≤ unitResidual v ∧ q.val ≠ 0 ∧ q.val.val ∈ N ∧
      ∀ i ∈ F,τ.norm₂ (q.val*x i*q.val) < (η+(A i+B i)/3)*τ.norm₂ q.val ∧
        norm₁ τ (q.val*x i*q.val) < (η+(A i+B i)/3)*(τ.trace q.val).re := by
  have hp : (unitResidual v).val ≠ 0 := by
    intro h
    have hh := unitResidual_positive τ v hsmall
    rw [h,show τ.trace 0=0 from inner_zero_right _,Complex.zero_re] at hh
    exact (lt_irrefl _ hh)
  have hpN : (unitResidual v).val.val ∈ N := by
    have hvp : v.support.val.val ∈ N := by
      rw [← v.unitary.initial]
      exact N.mul_mem (N.toStarSubalgebra.star_mem' hvN) hvN
    exact N.sub_mem N.one_mem hvp
  obtain ⟨q,hqp,hq,hqN,hlocal⟩ := exists_irreducible_corner_local_piece τ hNM hfactor hdiff hirr hsep
    (unitResidual v) hp hpN F x η hη
  refine ⟨q,hqp,hq,hqN,fun i hi => ?_⟩
  have hs := unitResidual_scalar_two_moment_bound τ v hsmall (x i) (A i) (B i)
    (hAB i hi) (hA i hi) (hB i hi)
  have hn : τ.norm₂ (q.val*x i*q.val) < (η+(A i+B i)/3)*τ.norm₂ q.val := by
    have ht := τ.norm₂_add_le (q.val*x i*q.val-cornerScalar τ (unitResidual v) (x i) • q.val)
      (cornerScalar τ (unitResidual v) (x i) • q.val)
    rw [sub_add_cancel,τ.norm₂_smul] at ht
    have hmul := mul_le_mul_of_nonneg_right hs (show 0 ≤ τ.norm₂ q.val from norm_nonneg _)
    have hh := (hlocal i hi).1
    nlinarith only [ht,hmul,hh]
  exact ⟨hn,compression_norm₁_lt_of_norm₂ τ q hq (x i) _ hn⟩

/-- Choose the patch unitary after q, so the same q controls all two-letter
terms and the signed one-letter traces are as small as prescribed. -/
theorem exists_unitResidual_controlled_patch
    (v : PartialUnitary M) (hvN : v.val.val ∈ N)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra) (A B : ι → ℝ)
    (hAB : ∀ i ∈ F,0 ≤ A i+B i)
    (hA : ∀ i ∈ F,‖τ.trace (x i)‖ ≤ A i*(τ.trace v.support.val).re)
    (hB : ∀ i ∈ F,‖τ.trace (star v.val*x i*v.val)‖ ≤ B i*(τ.trace v.support.val).re)
    (L R : Finset M.toStarSubalgebra) (η κ : ℝ) (hη : 0 < η) (hκ : 0 < κ) :
    ∃ (q : AlgebraProjection M) (w : CornerUnitary q),
      q ≤ unitResidual v ∧ q.val ≠ 0 ∧ q.val.val ∈ N ∧ w.val.val ∈ N ∧
      (∀ a ∈ L,∀ b ∈ R,∀ s : Bool,‖τ.trace (a*signedLetter w.val s*b)‖ < κ*(τ.trace q.val).re) ∧
      (∀ i ∈ F,∀ u z : CornerUnitary q,∀ a b : M.toStarSubalgebra,‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
        ‖τ.trace (a*u.val*x i*z.val*b)‖ < (η+(A i+B i)/3)*(τ.trace q.val).re) := by
  obtain ⟨q,hqp,hq,hqN,hlocal⟩ := exists_unitResidual_local_compression τ hNM hfactor hdiff hirr hsep
    v hvN hsmall F x A B hAB hA hB η hη
  let qN := projectionInSubalgebra q hqN
  have hqN0 : qN.val ≠ 0 := by
    intro hz
    exact hq (Subtype.ext (congrArg (fun a : N.toStarSubalgebra => a.val) hz))
  obtain ⟨w,hw⟩ := exists_cornerUnitary_small_signed_traces τ hNM hdiff qN hqN0 L R
    (κ*(τ.trace q.val).re) (mul_pos hκ (projection_trace_pos τ q.val q.property hq))
  let wM : CornerUnitary q := {
    val := coordinateInclusion hNM w.val
    initial := by
      rw [← map_star,← map_mul,w.initial]
      rfl
    final := by
      rw [← map_star,← map_mul,w.final]
      rfl }
  refine ⟨q,wM,hqp,hq,hqN,w.val.property,hw,fun i hi u z a b ha hb => ?_⟩
  have hh := (hlocal i hi).1
  calc _ ≤ τ.norm₂ (q.val*x i*q.val)*τ.norm₂ q.val := two_patch_trace_le τ q u z a (x i) b ha hb
       _ < ((η+(A i+B i)/3)*τ.norm₂ q.val)*τ.norm₂ q.val :=
         mul_lt_mul_of_pos_right hh (corner_norm₂_pos τ q hq)
       _ = _ := by rw [projection_trace_sq τ q.val q.property]; ring

end

/-! A single actual residual patch controls every finite internal word of the
source family. All scalar moment premises are proved from admissibility. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_admissible_family_patch
    (F : Finset M.toStarSubalgebra) (hcenter : ∀ x ∈ F,τ.trace x=0)
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (v : PartialUnitary M)
    (hv : PatchingAdmissibleIn (P := N) τ (identityProjection M) F n (patchingTolerance δ) v)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ (q : AlgebraProjection M) (w : CornerUnitary q),
      q ≤ unitResidual v ∧ q.val ≠ 0 ∧ q.val.val ∈ N ∧ w.val.val ∈ N ∧
      (∀ a ∈ outerWordFamily v.val F n,∀ b ∈ outerWordFamily v.val F n,∀ s : Bool,
        ‖τ.trace (a*signedLetter w.val s*b)‖ < κ*(τ.trace q.val).re) ∧
      (∀ x ∈ F,∀ xs : List (Bool × M.toStarSubalgebra),
        xs.length+2 ≤ n → (∀ a ∈ xs,a.2 ∈ F) →
        ∀ u z : CornerUnitary q,∀ a b : M.toStarSubalgebra,‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
        ‖τ.trace (a*u.val*(x*patchingWord v.val xs)*z.val*b)‖ <
          (2*patchingTolerance δ (xs.length+2)/3)*(τ.trace q.val).re) := by
  let X := middleWordFamily F n
  let mid := fun i : M.toStarSubalgebra × List (Bool × M.toStarSubalgebra) =>
    i.1*patchingWord v.val i.2
  let A := fun i : M.toStarSubalgebra × List (Bool × M.toStarSubalgebra) =>
    middleMomentError (patchingTolerance δ) i.2.length
  let B := fun i : M.toStarSubalgebra × List (Bool × M.toStarSubalgebra) =>
    patchingTolerance δ (i.2.length+2)
  have hm := middleWordFamily_moments τ v (identityProjection M) F n
    (patchingTolerance δ) hv.1 hcenter
  obtain ⟨q,w,hqp,hq,hqN,hwN,hfirst,hsecond⟩ := exists_unitResidual_controlled_patch τ hNM
    hfactor hdiff hirr hsep v hv.2 hsmall X mid A B
    (fun i _ => add_nonneg
      (middleMomentError_nonneg _ (fun k => (patchingTolerance_pos δ hδ k).le) _)
      (patchingTolerance_pos δ hδ _).le)
    (fun i hi => (hm i hi).1) (fun i hi => (hm i hi).2)
    (outerWordFamily v.val F n) (outerWordFamily v.val F n)
    (δ/3) κ (by positivity) hκ
  refine ⟨q,w,hqp,hq,hqN,hwN,hfirst,?_⟩
  intro x hx xs hlen hxs u z a b ha hb
  have hi : (x,xs) ∈ X := (mem_middleWordFamily F n x xs).mpr ⟨hx,hlen,hxs⟩
  have hh := hsecond (x,xs) hi u z a b ha hb
  exact hh.trans_le (mul_le_mul_of_nonneg_right (patchingTolerance_middle_budget δ hδ xs.length)
    (projection_trace_pos τ q.val q.property hq).le)

end

/-! Trace estimates for each actual binary-mask term, using the constructed
finite families. No moment estimate or middle-family extraction is assumed. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def signedCornerUnitary {q : AlgebraProjection M} (w : CornerUnitary q) (s : Bool) :
    CornerUnitary q := if s then w.adjoint else w

@[simp] theorem signedCornerUnitary_val {q : AlgebraProjection M} (w : CornerUnitary q) (s : Bool) :
    (signedCornerUnitary w s).val=signedLetter w.val s := by cases s <;> rfl

theorem maskedWord_one_decomposition
    (xs : List (Bool × M.toStarSubalgebra)) (bs : List Bool)
    (hlen : bs.length=xs.length) (hcount : bs.count true=1) :
    ∃ pre a post,xs=pre++a::post ∧
      bs=List.replicate pre.length false++true::List.replicate post.length false := by
  obtain ⟨i,cs,hbs⟩ := exists_first_true bs (by omega)
  have hc : cs.count true=0 := by simpa [hbs,List.count_replicate] using hcount
  have hcs := (count_true_zero_iff cs).mp hc
  have hl : i+1+cs.length=xs.length := by
    rw [hbs] at hlen
    simp only [List.length_append,List.length_replicate,List.length_cons] at hlen
    omega
  obtain ⟨pre,a,post,hxs,hp⟩ := exists_list_split xs i (by omega)
  have ht : cs.length=post.length := by rw [hxs,List.length_append,List.length_cons,hp] at hl; omega
  refine ⟨pre,a,post,hxs,?_⟩
  simpa only [hp,ht] using (hbs.trans (congrArg (fun ds => List.replicate i false++true::ds) hcs))

theorem maskedWord_one_trace_lt (v : PartialUnitary M) {q : AlgebraProjection M}
    (w : CornerUnitary q) (F : Finset M.toStarSubalgebra) (n : ℕ) (κ : ℝ)
    (hfirst : ∀ a ∈ outerWordFamily v.val F n,∀ b ∈ outerWordFamily v.val F n,∀ s : Bool,
      ‖τ.trace (a*signedLetter w.val s*b)‖ < κ*(τ.trace q.val).re)
    (x₀ : M.toStarSubalgebra) (hx₀ : x₀ ∈ (F : Set M.toStarSubalgebra) ∪ {1})
    (xs : List (Bool × M.toStarSubalgebra)) (hn : xs.length ≤ n)
    (hc : patchingCoefficients (F : Set M.toStarSubalgebra) xs)
    (bs : List Bool) (hlen : bs.length=xs.length) (hcount : bs.count true=1) :
    ‖τ.trace (x₀*maskedWord v.val w.val xs bs)‖ < κ*(τ.trace q.val).re := by
  obtain ⟨pre,a,post,hxs,hbs⟩ := maskedWord_one_decomposition xs bs hlen hcount
  have hall := patchingCoefficients_mem (F : Set M.toStarSubalgebra) xs hc
  have hpre : ∀ c ∈ pre,c.2 ∈ (F : Set M.toStarSubalgebra) ∪ {1} := by
    intro c hc; apply hall c; simp [hxs,hc]
  have hpost : ∀ c ∈ post,c.2 ∈ (F : Set M.toStarSubalgebra) ∪ {1} := by
    intro c hc; apply hall c; simp [hxs,hc]
  have ha : a.2 ∈ (F : Set M.toStarSubalgebra) ∪ {1} := hall a (by simp [hxs])
  have hsize : pre.length+1+post.length ≤ n := by simpa [hxs,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hn
  have hL := mem_outerWordFamily v.val F n x₀ pre hx₀ (by omega) hpre
  have hR := mem_outerWordFamily v.val F n a.2 post ha (by omega) hpost
  have hh := hfirst _ hL _ hR a.1
  rw [hxs,hbs,maskedWord_one]
  simpa only [mul_assoc] using hh

theorem maskedWord_two_trace_lt (v : PartialUnitary M) {q : AlgebraProjection M}
    (w : CornerUnitary q) (F : Finset M.toStarSubalgebra) (n : ℕ) (δ : ℝ)
    (hF : ∀ x ∈ F,‖x‖ ≤ 1)
    (hsecond : ∀ x ∈ F,∀ ys : List (Bool × M.toStarSubalgebra),
      ys.length+2 ≤ n → (∀ a ∈ ys,a.2 ∈ F) →
      ∀ u z : CornerUnitary q,∀ a b : M.toStarSubalgebra,‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖τ.trace (a*u.val*(x*patchingWord v.val ys)*z.val*b)‖ <
        (2*patchingTolerance δ (ys.length+2)/3)*(τ.trace q.val).re)
    (x₀ : M.toStarSubalgebra) (h₀ : ‖x₀‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (hn : xs.length ≤ n)
    (hc : patchingCoefficients (F : Set M.toStarSubalgebra) xs)
    (bs : List Bool) (hlen : bs.length=xs.length) (hcount : 2 ≤ bs.count true) :
    ∃ r,r+2 ≤ xs.length ∧
      (bs ≠ exceptionalMask xs.length → r+2 ≤ xs.length-1) ∧
      ‖τ.trace (x₀*maskedWord v.val w.val xs bs)‖ <
        (2*patchingTolerance δ (r+2)/3)*(τ.trace q.val).re := by
  obtain ⟨pre,a,mid,b,post,cs,hxs,hbs,ha,hm,ht,hsize⟩ :=
    maskedWord_two_decomposition (F : Set M.toStarSubalgebra) xs hc bs hlen hcount
  have hall := patchingCoefficients_norm (F : Set M.toStarSubalgebra) hF xs hc
  have hpre : ∀ c ∈ pre,‖c.2‖ ≤ 1 := by intro c hc; apply hall c; simp [hxs,hc]
  have hpost : ∀ c ∈ post,‖c.2‖ ≤ 1 := by intro c hc; apply hall c; simp [hxs,hc]
  have hb : ‖b.2‖ ≤ 1 := hall b (by simp [hxs])
  have hp := patchingWord_norm_le_one v.val v.unitary.norm_le_one pre hpre
  have ht' := maskedWord_norm_le_one v.val w.val v.unitary.norm_le_one w.norm_le_one post cs hpost
  have hL : ‖x₀*patchingWord v.val pre‖ ≤ 1 := (norm_mul_le _ _).trans
    ((mul_le_mul h₀ hp (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))
  have hR : ‖b.2*maskedWord v.val w.val post cs‖ ≤ 1 := (norm_mul_le _ _).trans
    ((mul_le_mul hb ht' (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))
  refine ⟨mid.length,hsize,?_,?_⟩
  · intro he
    by_contra h
    have heq : mid.length+2=xs.length := by omega
    have heq' : mid.length+2=
        (List.replicate pre.length false++true::(List.replicate mid.length false++true::cs)).length := by
      rw [← hbs,hlen,heq]
    have hh := first_two_eq_exceptional pre.length mid.length cs heq'
    rw [← hbs,hlen] at hh
    exact he hh
  · have hh := hsecond a.2 ha mid (by omega) hm
      (signedCornerUnitary w a.1) (signedCornerUnitary w b.1)
      (x₀*patchingWord v.val pre) (b.2*maskedWord v.val w.val post cs) hL hR
    rw [hxs,hbs,maskedWord_first_two]
    simpa only [signedCornerUnitary_val,mul_assoc] using hh

end

/-! Strict support growth for the actual f=1 admissible set. The single patch
is chosen from the finite coefficient families before any word is tested. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem unitResidual_orthogonal (v : PartialUnitary M) (q : AlgebraProjection M)
    (hq : q ≤ unitResidual v) : v.support.val*q.val=0 := by
  change (1-v.support.val)*q.val=q.val at hq
  have hh : q.val-v.support.val*q.val=q.val := by simpa only [sub_mul,one_mul] using hq
  exact sub_eq_self.mp hh

def unitResidualPatch (v : PartialUnitary M) (q : AlgebraProjection M) (w : CornerUnitary q)
    (hq : q ≤ unitResidual v) : PartialUnitary M :=
  ⟨⟨v.support.val+q.val,v.support.property.add q.property (unitResidual_orthogonal v q hq)⟩,
    v.unitary.patch w (unitResidual_orthogonal v q hq)⟩

theorem unitResidualPatch_extends (v : PartialUnitary M) (q : AlgebraProjection M)
    (w : CornerUnitary q) (hq : q ≤ unitResidual v) : v ≤ unitResidualPatch v q w hq := by
  have hh := v.unitary.patch_extends w (unitResidual_orthogonal v q hq)
  change (v.unitary.patch w (unitResidual_orthogonal v q hq)).val*v.support.val=v.val
  simpa only [v.unitary.initial] using hh

theorem unitResidualPatch_trace (v : PartialUnitary M) (q : AlgebraProjection M)
    (w : CornerUnitary q) (hq : q ≤ unitResidual v) :
    (τ.trace (unitResidualPatch v q w hq).support.val).re =
      (τ.trace v.support.val).re+(τ.trace q.val).re := by
  change (τ.trace (v.support.val+q.val)).re=_
  rw [cornerTrace_add,Complex.add_re]

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

/-- The full extension satisfies every original admissibility inequality and
has strictly greater support trace. No patch growth premise is assumed. -/
theorem exists_strict_admissible_unit_patch
    (F : Finset M.toStarSubalgebra) (hF : ∀ x ∈ F,‖x‖ ≤ 1)
    (hcenter : ∀ x ∈ F,τ.trace x=0) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (v : PartialUnitary M)
    (hv : PatchingAdmissibleIn (P := N) τ (identityProjection M) F n (patchingTolerance δ) v)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4) :
    ∃ u : PartialUnitary M,
      PatchingAdmissibleIn (P := N) τ (identityProjection M) F n (patchingTolerance δ) u ∧
      v ≤ u ∧ (τ.trace v.support.val).re < (τ.trace u.support.val).re := by
  classical
  obtain ⟨q,w,hqp,hq,hqN,hwN,hfirst,hsecond⟩ := exists_admissible_family_patch τ hNM
    hfactor hdiff hirr hsep F hcenter n δ hδ v hv hsmall (δ/3) (by positivity)
  let u := unitResidualPatch v q w hqp
  have htq := projection_trace_pos τ q.val q.property hq
  have htv : 0 ≤ (τ.trace v.support.val).re := by
    rw [← v.unitary.trace_norm_sq τ]; positivity
  have hg : (τ.trace u.support.val).re=(τ.trace v.support.val).re+(τ.trace q.val).re :=
    unitResidualPatch_trace τ v q w hqp
  refine ⟨u,⟨⟨?_,?_⟩,?_⟩,unitResidualPatch_extends v q w hqp,by rw [hg]; linarith⟩
  · exact one_mul _
  · intro x₀ hx₀ xs hpos hn hc
    have h₀ : ‖x₀‖ ≤ 1 := by
      rcases hx₀ with h | h
      · exact hF x₀ h
      · rw [Set.mem_singleton_iff.mp h]; exact (IsStarProjection.one _).norm_le
    let k := xs.length
    let A := patchingTolerance δ k*(τ.trace v.support.val).re
    let B := (2*patchingTolerance δ k/3)*(τ.trace q.val).re
    let C := (2*patchingTolerance δ (k-1)/3)*(τ.trace q.val).re
    have hεk := patchingTolerance_pos δ hδ k
    have hεprev := patchingTolerance_pos δ hδ (k-1)
    have hA : 0 ≤ A := mul_nonneg (patchingTolerance_pos δ hδ k).le htv
    have hB : 0 ≤ B := mul_nonneg (by positivity) htq.le
    have hC : 0 ≤ C := mul_nonneg (by positivity) htq.le
    have hκ : (δ/3)*(τ.trace q.val).re ≤ C := by
      have hd : δ ≤ patchingTolerance δ (k-1) := patchingTolerance_mono δ hδ (Nat.zero_le _)
      apply mul_le_mul_of_nonneg_right _ htq.le
      linarith
    have hterm : ∀ bs ∈ binaryMasks k,
        ‖τ.trace (x₀*maskedWord v.val w.val xs bs)‖ ≤
          C+(if bs=List.replicate k false then A else 0)+(if bs=exceptionalMask k then B else 0) := by
      intro bs hbs
      have hlen : bs.length=xs.length := (mem_binaryMasks k bs).mp hbs
      have hAi : 0 ≤ (if bs=List.replicate k false then A else 0) := by split_ifs <;> positivity
      have hBi : 0 ≤ (if bs=exceptionalMask k then B else 0) := by split_ifs <;> positivity
      by_cases hz : bs.count true=0
      · have he : bs=List.replicate k false := by
          simpa only [hlen] using (count_true_zero_iff bs).mp hz
        have hh : ‖τ.trace (x₀*maskedWord v.val w.val xs bs)‖ ≤ A := by
          rw [he,maskedWord_no_patch]
          exact hv.1.2 x₀ hx₀ xs hpos hn hc
        rw [ite_eq_left he]
        linarith
      · by_cases ho : bs.count true=1
        · have hh := (maskedWord_one_trace_lt τ v w F n (δ/3) hfirst x₀ hx₀ xs hn hc bs hlen ho).le.trans hκ
          linarith
        · obtain ⟨r,hr,hex,hbound⟩ := maskedWord_two_trace_lt τ v w F n δ hF hsecond x₀ h₀ xs hn hc bs hlen (by omega)
          by_cases he : bs=exceptionalMask k
          · have hmono := patchingTolerance_mono δ hδ hr
            have hb : (2*patchingTolerance δ (r+2)/3)*(τ.trace q.val).re ≤ B := by
              apply mul_le_mul_of_nonneg_right _ htq.le
              linarith
            have hh := hbound.le.trans hb
            rw [ite_eq_left he]
            linarith
          · have hmono := patchingTolerance_mono δ hδ (hex he)
            have hb : (2*patchingTolerance δ (r+2)/3)*(τ.trace q.val).re ≤ C := by
              apply mul_le_mul_of_nonneg_right _ htq.le
              linarith
            have hh := hbound.le.trans hb
            linarith
    have hsum := sum_three_budgets (binaryMasks k) (binaryMasks_nodup k)
      (fun bs => ‖τ.trace (x₀*maskedWord v.val w.val xs bs)‖)
      (List.replicate k false) (exceptionalMask k) C A B hA hB hterm
    have hbudget : ((binaryMasks k).length : ℝ)*C+B=patchingTolerance δ k*(τ.trace q.val).re := by
      rw [binaryMasks_length,Nat.cast_pow,Nat.cast_ofNat]
      have hh := congrArg (fun z : ℝ => z*(τ.trace q.val).re) (patchingTolerance_mask_budget δ k hpos)
      dsimp [C,B]
      nlinarith only [hh]
    have hh := (patching_trace_sum_le τ v.val w.val x₀ xs).trans hsum
    change ‖τ.trace (x₀*patchingWord (v.val+w.val) xs)‖ ≤ _
    rw [hg]
    dsimp [A] at hh
    nlinarith only [hh,hbudget]
  · exact N.add_mem hv.2 hwN

/-- The maximal-element contradiction now gives support trace strictly greater
than one quarter in the f=1 scalar-commutant setting. -/
theorem exists_large_admissible_partialUnitary
    (F : Finset M.toStarSubalgebra) (hF : ∀ x ∈ F,‖x‖ ≤ 1)
    (hcenter : ∀ x ∈ F,τ.trace x=0) (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v : PartialUnitary M,
      PatchingAdmissibleIn (P := N) τ (identityProjection M) F n (patchingTolerance δ) v ∧
      1/4 < (τ.trace v.support.val).re := by
  obtain ⟨v,hv,hmax⟩ := exists_maximal_patchingAdmissibleIn τ hNM (identityProjection M) F hF n (patchingTolerance δ)
  refine ⟨v,hv,?_⟩
  by_contra h
  obtain ⟨u,hu,hvu,hgrow⟩ := exists_strict_admissible_unit_patch τ hNM hfactor hdiff hirr hsep
    F hF hcenter n δ hδ v hv (by linarith)
  have hh := PartialUnitary.support_trace_mono τ (hmax u hu hvu)
  linarith

end Generator.Tracial

end

end OAI
