import OAI.Analysis.KadisonKastler.StateScalingTransport
import OAI.Analysis.KadisonKastler.ProductCentralizerDiffuse
import OAI.Analysis.KadisonKastler.FiniteTraceMatrix

namespace OAI

/-! # Extending a modular partial isometry to a coisometry

In a diffuse factorial centralizer, a nonzero scaling partial isometry of
ratio at most one can be cut and moved into a finite orthogonal partition
of the identity. This is the finite construction needed for absorption.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem exists_state_scaling_coisometry
    (hunit : ‖Ω‖=1) (hsep : Function.Injective (algebraVectorMap M Ω))
    (hf : ScalarCenter (stateCentralizerVonNeumann (M := M) Ω))
    (hdiff : ∀ p : Algebra (stateCentralizerVonNeumann (M := M) Ω),
      IsStarProjection p → p ≠ 0 → ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p*q=q ∧ q*p=q)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (v : PartialIsometry M)
    (hv : StateScales M Ω r v.val.val) (hv0 : v.val ≠ 0) :
    ∃ w : Algebra M, w*star w=1 ∧ StateScales M Ω r w.val := by
  classical
  let N := stateCentralizerVonNeumann (M := M) Ω
  let τ := stateCentralizerTrace Ω hunit hsep
  let Q := scalingTarget v hv hr.ne'
  have hQ0 : Q.val ≠ 0 := by
    intro hz
    apply hv0
    have hz' : v.val*star v.val=0 := by
      apply Subtype.ext
      exact congrArg (fun a : Algebra N => a.val) hz
    exact (CStarRing.mul_star_self_eq_zero_iff v.val).mp hz'
  have hQpos := projection_trace_pos τ Q.val Q.property hQ0
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hQpos
  let n := k+1
  have hn : 0 < n := Nat.succ_pos k
  have htpos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hn)
  have htQ : (n : ℝ)⁻¹ ≤ (τ.trace Q.val).re := by
    simpa only [n,Nat.cast_add,Nat.cast_one,one_div] using hk.le
  obtain ⟨q,hq,hQq,_,hqt⟩ := exists_exact_trace_subprojection τ hdiff
    Q.val Q.property (n : ℝ)⁻¹ htpos.le htQ
  let qP : AlgebraProjection N := ⟨q,hq⟩
  let qM := includeCentralizerProjection qP
  have hqM : qM ≤ v.target := by
    change v.target.val*(stateCentralizerInclusion Ω q)=stateCentralizerInclusion Ω q
    apply Subtype.ext
    exact congrArg (fun a : Algebra N => a.val) hQq
  let y := cutPartialIsometryTarget v qM hqM
  have hy : StateScales M Ω r y.val.val :=
    cutPartialIsometryTarget_scales v hv qM hqM q.property.2
  have hyT : scalingTarget y hy hr.ne'=qP := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun p : AlgebraProjection M => p.val.val)
      (cutPartialIsometryTarget_target v qM hqM)
  have hytrace : τ.trace (scalingSupport y hy hr.ne').val =
      ((r*(n : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [scalingSupport_trace y hy hr.ne' hunit hsep,hyT]
    change (r : ℂ)*τ.trace q = _
    rw [hqt,Complex.ofReal_mul]
  have hf' : ∀ c : Algebra N, (∀ a : Algebra N, a*c=c*a) →
      ∃ z : ℂ, c=z • (1 : Algebra N) := by
    intro c hc
    obtain ⟨z,hz⟩ := hf c.val c.property
      (fun a ha => congrArg Subtype.val (hc ⟨a,ha⟩))
    exact ⟨z,Subtype.ext hz⟩
  obtain ⟨E,hEt⟩ := exists_uniform_trace_matrix τ hf' hdiff n hn
  let e : Fin n → AlgebraProjection N := fun i => ⟨E.entry i i,E.diagonal_projection i⟩
  have hcuts (i : Fin n) : ∃ d : AlgebraProjection N,
      d ≤ e i ∧ τ.trace d.val=((r*(n : ℝ)⁻¹ : ℝ) : ℂ) := by
    obtain ⟨d,hd,hed,_,hdt⟩ := exists_exact_trace_subprojection τ hdiff
      (E.entry i i) (E.diagonal_projection i) (r*(n : ℝ)⁻¹)
      (mul_nonneg hr.le htpos.le) (by
        rw [hEt,Complex.ofReal_re]
        exact mul_le_of_le_one_left htpos.le hr1)
    exact ⟨⟨d,hd⟩,hed,hdt⟩
  choose d hd hdt using hcuts
  have hpieces (i : Fin n) : ∃ z : PartialIsometry M,
      z.support=includeCentralizerProjection (d i) ∧
      z.target=includeCentralizerProjection (e i) ∧ StateScales M Ω r z.val.val := by
    apply exists_state_scaling_transport hunit hsep hf hr.ne' y hy (d i) (e i)
    · rw [hdt,hytrace]
    · rw [hyT]
      exact (hEt i).trans hqt.symm
  choose z hzs hzt hzscale using hpieces
  have hzorth (i j : Fin n) (hij : i ≠ j) :
      (z i).support.val*(z j).support.val=0 := by
    rw [hzs,hzs]
    have he : (e i).val*(e j).val=0 := by
      change E.entry i i*E.entry j j=0
      simpa only [hij,↓reduceIte] using E.mul_entry i i j j
    have hh := projection_orthogonal_of_le he (hd i) (hd j)
    change stateCentralizerInclusion Ω (d i).val *
      stateCentralizerInclusion Ω (d j).val=0
    rw [← map_mul,hh,map_zero]
  have htotal : ∑ i, (z i).target.val=1 := by
    simp_rw [hzt]
    change (∑ i, stateCentralizerInclusion Ω (E.entry i i))=1
    rw [← map_sum,E.total,map_one]
  refine ⟨∑ i, (z i).val,partialIsometry_sum_coisometry z hzorth htotal,?_⟩
  change StateScales M Ω r (M.toStarSubalgebra.subtype (∑ i, (z i).val))
  rw [map_sum]
  exact StateScales.sum Finset.univ (fun i => (z i).val.val) (fun i _ => hzscale i)

end

end KadisonKastler

end OAI
