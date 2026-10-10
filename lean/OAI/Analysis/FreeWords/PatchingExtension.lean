import Mathlib
import OAI.Analysis.FreeWords.LocalPatch
import OAI.Analysis.FreeWords.PatchingBudget
import OAI.Analysis.FreeWords.PatchingMaximal
import OAI.Analysis.FreeWords.PatchingTermBound

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKMatrixQuantization

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

theorem patching_extension
    (hF : IsFactor M) (hD : IsDiffuse M)
    {X : Set (ConcreteAlgebra M)} {K : Set ℤ} {N : ℕ}
    (hXfin : X.Finite) (hKfin : K.Finite)
    (hXnorm : ∀ x∈X, ‖x‖≤1) (hXcenter : ∀ x∈X, τ.map x=0)
    (hKzero : ∀ k∈K, k≠0) (hK1 : 1∈K) (hKm1 : -1∈K)
    {δ C η : ℝ} (hδ : 0<δ) (hC : 0≤C) (hη : 0<η)
    (hdom : (2:ℝ)^N*(2/η+1)≤C)
    (v : PartialUnitary (ConcreteAlgebra M))
    (ht : (τ.map v.support).re<1-η)
    (hv : ∀ a, PatchingWord.Admissible X K N a →
      ‖τ.map (a.value v.power)‖≤patchingBudget δ C (τ.map v.support).re) :
    ∃ v' : PartialUnitary (ConcreteAlgebra M), v<v' ∧
      PatchingBounds τ {a | PatchingWord.Admissible X K N a} (patchingBudget δ C) (1-η) v' := by
  classical
  let t := (τ.map v.support).re
  let b := patchingBudget δ C t
  have ht0 : 0≤t := by dsimp only [t]; rw [← traceNorm_projection_sq τ v.projection]; exact sq_nonneg _
  have hb : 0≤b := patchingBudget_nonneg hδ.le hC ht0
  let a := min (δ/2) ((δ/2)^2)
  have ha : 0<a := lt_min (by positivity) (sq_pos_of_pos (by positivity))
  have hasmall : Real.sqrt a+a≤δ := by
    have h1 : a≤δ/2 := min_le_left _ _
    have h2 : Real.sqrt a≤δ/2 := (Real.sqrt_le_iff).mpr ⟨by positivity,min_le_right _ _⟩
    linarith
  let W : Set (PatchingWord (ConcreteAlgebra M)) := {w | PatchingWord.Admissible X K N w}
  let : Fintype W := (PatchingWord.admissible_finite hXfin hKfin N).fintype
  let ε := min a (1-η-t)
  have hε : 0<ε := lt_min ha (sub_pos.mpr ht)
  let p := 1-v.support
  have hp : IsStarProjection p := v.projection.one_sub
  have hp0 : p≠0 := by
    intro he
    have he1 : v.support=1 := (sub_eq_zero.mp he).symm
    have hc : t=1 := by dsimp only [t]; rw [he1,τ.normalized]; rfl
    linarith
  obtain ⟨w,hw0,hwp,hwt,hcomp,hweak⟩ := local_patch M τ hF hD p hp hp0
    (fun i:PatchingTerms W => i.split.gap v.power)
    (fun i:PatchingTerms W => i.split.coefficient v.power i.1.val.right)
    (fun i:PatchingTerms W => i.split.exponent)
    (fun i => i.exponent_ne_zero hKzero (fun _ h => h)) ε hε
  have hq0 : 0<(τ.map w.support).re := trace_projection_pos τ w.projection hw0
  have horth : v.support*w.support=0 := by
    have hright : w.support*v.support=0 := by
      change w.support*(1-v.support)=w.support at hwp
      rw [mul_sub,mul_one] at hwp
      exact sub_eq_self.mp hwp
    have hh := congrArg star hright
    simpa only [star_mul,v.projection.isSelfAdjoint.star_eq,
      w.projection.isSelfAdjoint.star_eq,star_zero] using hh
  let v' := v.sum w horth
  have hts : (τ.map v'.support).re=t+(τ.map w.support).re := by
    change (τ.map (v.support+w.support)).re=_
    rw [map_add,Complex.add_re]
  have hlt : v<v' := by
    apply lt_of_le_of_ne (v.le_sum w horth)
    intro he
    have heS := congrArg PartialUnitary.support he
    change v.support=v.support+w.support at heS
    exact hw0 (add_eq_left.mp heS.symm)
  refine ⟨v',hlt,?_,?_⟩
  · rw [hts]
    have he := hwt.trans_le (min_le_right a (1-η-t))
    linarith
  · intro A hA
    have hterms : ∀ c∈Colored.changes A.raw,
        ‖τ.map (Colored.value v.power w.power c*A.right)‖≤
          (2*b/η+δ)*(τ.map w.support).re := by
      intro c hc
      let i : PatchingTerms W := ⟨⟨A,hA⟩,⟨c,hc⟩⟩
      let scalar := (τ.map p)⁻¹*τ.map (p*i.split.gap v.power*p)
      have hgap := i.gap_bounds τ hXcenter hK1 hKm1 (fun _ h => h) v hb hv
      have hscalar : ‖scalar‖≤2*b/η :=
        corner_scalar_bound τ v.support (i.split.gap v.power) v.projection hη ht.le hgap.1 hgap.2
      have hcompress : (traceNorm τ (w.support*i.split.gap v.power*w.support-scalar • w.support))^2
          ≤a*(τ.map w.support).re := by
        have hi := (Finset.single_le_sum (fun j _ => sq_nonneg (traceNorm τ
          (w.support*j.split.gap v.power*w.support-
            ((τ.map p)⁻¹*τ.map (p*j.split.gap v.power*p)) • w.support))) (Finset.mem_univ i)).trans hcomp.le
        exact hi.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hq0.le)
      have hweak' : ‖τ.map (w.power i.split.exponent*i.split.coefficient v.power i.1.val.right)‖≤
          a*(τ.map w.support).re := (hweak i).le.trans
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hq0.le)
      have hnorm := norm_raw_coefficients hXnorm hA
      have hi := patching_term_bound τ v w i ha.le (by positivity) scalar hscalar hnorm.1 hnorm.2 hcompress hweak'
      exact hi.trans (mul_le_mul_of_nonneg_right (by linarith) hq0.le)
    have hB0 : 0≤(2*b/η+δ)*(τ.map w.support).re := by positivity
    have hbound := expanded_trace_bound τ A v.power w.power hB0 hterms
    have hpown : (2:ℝ)^A.length≤2^N := pow_le_pow_right₀ (by norm_num) hA.2.2.2.2
    have hbig : ‖τ.map (A.value v'.power)‖≤b+2^N*(2*b/η+δ)*(τ.map w.support).re := by
      calc
        _ ≤ ‖τ.map (A.value v.power)‖+2^A.length*((2*b/η+δ)*(τ.map w.support).re) := hbound
        _ ≤ b+2^N*((2*b/η+δ)*(τ.map w.support).re) :=
          add_le_add (hv A hA) (mul_le_mul_of_nonneg_right hpown hB0)
        _ = _ := by ring
    rw [hts]
    exact hbig.trans (patchingBudget_increment hδ.le (by positivity) hη hC hdom ht0 hq0.le)

end

end KKLocalPatching
end

end OAI
