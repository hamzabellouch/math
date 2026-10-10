import OAI.Analysis.ModularRecovery.RealGraph

namespace OAI

/-! The commutant core and reverse operators. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace RealSpectralCalculus
lemma halfGraph_smul (D : RealSpectralCalculus H) {x y : H}
    (hxy : (x,y) ∈ D.halfGraph) (c : ℂ) : (c • x,c • y) ∈ D.halfGraph := by
  rw [D.halfGraph_iff_resolvent] at hxy ⊢
  rw [← smul_add, map_smul, hxy]
end RealSpectralCalculus

namespace StandardModularData

lemma fixed_adjoint_core_approx (S : StandardModularData H) {z : H}
    (hz : (S.J z,z) ∈ S.D.halfGraph) :
    z ∈ closure {v : H | ∃ b : H →L[ℂ] H,
      b ∈ S.M.commutant ∧ IsSelfAdjoint b ∧ b S.xi = v} := by
  apply real_commutation S.M S.xi z S.cyclic
  intro a ha
  have hi := S.D.halfGraph_symmetric hz (S.core_halfGraph a ha)
  rw [antiunitary_inner] at hi
  change inner ℂ z (a S.xi) = (starRingEnd ℂ) (inner ℂ z ((star a) S.xi)) at hi
  rw [inner_conj_symm] at hi
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hi.symm

lemma commutant_tomita_graph (S : StandardModularData H) :
    closure {p : H × H | ∃ b : H →L[ℂ] H,
      b ∈ S.M.commutant ∧ p = (b S.xi, (star b) S.xi)} =
      {p | (S.J p.1,p.2) ∈ S.D.halfGraph} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro p ⟨b,hb,rfl⟩
      exact S.commutant_halfGraph b hb
    · exact S.D.halfGraph_isClosed.preimage (S.J.continuous.comp continuous_fst |>.prodMk continuous_snd)
  · rintro ⟨x,y⟩ hxy
    change (S.J x,y) ∈ S.D.halfGraph at hxy
    have hyx : (S.J y,x) ∈ S.D.halfGraph := by
      have hh := S.halfGraph_flip hxy
      change (S.J y,S.J (S.J x)) ∈ S.D.halfGraph at hh
      rwa [S.conjugation x] at hh
    let z₁ := (1/2:ℂ) • (x+y)
    let z₂ := (-Complex.I/2:ℂ) • (x-y)
    have h₁ : (S.J z₁,z₁) ∈ S.D.halfGraph := by
      have he : S.J z₁ = (1/2:ℂ) • (S.J x+S.J y) := by
        simp [z₁, map_smulₛₗ, map_ofNat]
      rw [he]
      convert S.D.halfGraph_smul (S.D.halfGraph_add hxy hyx) (1/2:ℂ) using 1
      exact congrArg (fun v : H => ((1/2:ℂ) • (S.J x+S.J y),v))
        (by dsimp [z₁]; rw [add_comm])
    have h₂ : (S.J z₂,z₂) ∈ S.D.halfGraph := by
      have he : S.J z₂ = (Complex.I/2) • (S.J x-S.J y) := by
        simp [z₂, map_smulₛₗ, map_ofNat]
      rw [he]
      convert S.D.halfGraph_smul (S.D.halfGraph_sub hxy hyx) (Complex.I/2) using 1
      congr 1
      dsimp [z₂]; module
    obtain ⟨f,hf,hft⟩ := mem_closure_iff_seq_limit.mp (S.fixed_adjoint_core_approx h₁)
    obtain ⟨g,hg,hgt⟩ := mem_closure_iff_seq_limit.mp (S.fixed_adjoint_core_approx h₂)
    choose b hb hbs hbxi using hf
    choose c hc hcs hcxi using hg
    have hx : z₁ + Complex.I • z₂ = x := by
      dsimp [z₁,z₂]
      rw [smul_smul]
      have hi : Complex.I * (-Complex.I/2) = (1/2:ℂ) := by
        rw [← mul_div_assoc, mul_neg, Complex.I_mul_I]
        norm_num
      rw [hi]
      module
    have hy : z₁ - Complex.I • z₂ = y := by
      dsimp [z₁,z₂]
      rw [smul_smul]
      have hi : Complex.I * (-Complex.I/2) = (1/2:ℂ) := by
        rw [← mul_div_assoc, mul_neg, Complex.I_mul_I]
        norm_num
      rw [hi]
      module
    have ht : Tendsto (fun n => ((b n + Complex.I • c n) S.xi,
        (star (b n + Complex.I • c n)) S.xi)) atTop (𝓝 (x,y)) := by
      convert (hft.add (hgt.const_smul Complex.I)).prodMk_nhds
        (hft.sub (hgt.const_smul Complex.I)) using 1
      · ext n <;> simp [star_add, star_smul, (hbs n).star_eq, (hcs n).star_eq,
          hbxi n, hcxi n, sub_eq_add_neg]
      · rw [hx,hy]
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun n =>
      ⟨b n + Complex.I • c n,
        add_mem (hb n) (S.M.commutant.toStarSubalgebra.smul_mem (hc n) _), rfl⟩))

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spectralReflection : (BoundedContinuousFunction ℝ ℂ) →⋆ₐ[ℂ]
    (BoundedContinuousFunction ℝ ℂ) where
  toFun f := f.compContinuous ⟨Neg.neg,continuous_neg⟩
  map_zero' := by ext; rfl
  map_one' := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl
  commutes' _ := by ext; rfl
  map_star' _ := by ext; rfl

@[simp] lemma spectralReflection_apply (f : BoundedContinuousFunction ℝ ℂ) (u : ℝ) :
    spectralReflection f u = f (-u) := rfl

@[simp] lemma spectralReflection_involutive (f : BoundedContinuousFunction ℝ ℂ) :
    spectralReflection (spectralReflection f) = f := by ext; simp

lemma spectralReflection_halfResolvent : spectralReflection halfResolvent = 1-halfResolvent := by
  ext u
  change (((Real.exp (-u/2)+1)⁻¹ : ℝ) : ℂ) = 1-(((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ)
  have he : -u/2 = -(u/2) := by ring
  rw [he, Real.exp_neg]
  have hpos := Real.exp_pos (u/2)
  have heq : ((Real.exp (u/2))⁻¹+1)⁻¹ = 1-(Real.exp (u/2)+1)⁻¹ := by
    field_simp
    ring
  exact_mod_cast heq

namespace RealSpectralCalculus

def reverse (D : RealSpectralCalculus H) : RealSpectralCalculus H where
  calculus := D.calculus.comp spectralReflection
  nondegenerate := D.nondegenerate.mono (by
    rintro h ⟨f,hf,k,rfl⟩
    exact ⟨spectralReflection f,hf.comp_homeomorph (Homeomorph.neg ℝ),k,
      by simp only [StarAlgHom.comp_apply, spectralReflection_involutive]⟩)

lemma reverse_halfGraph (D : RealSpectralCalculus H) (x y : H) :
    (x,y) ∈ D.reverse.halfGraph ↔ (y,x) ∈ D.halfGraph := by
  rw [D.reverse.halfGraph_iff_resolvent, D.halfGraph_iff_resolvent]
  change D.calculus (spectralReflection halfResolvent) (x+y) = x ↔ _
  rw [spectralReflection_halfResolvent, map_sub, map_one]
  simp only [sub_apply, one_apply_eq_self]
  rw [add_comm x y]
  constructor
  · intro he
    have hz : y+x - D.calculus halfResolvent (y+x) - x = 0 := by rw [he,sub_self]
    have he' : y-D.calculus halfResolvent (y+x) = 0 := by convert hz using 1; abel
    exact (sub_eq_zero.mp he').symm
  · intro he
    rw [he]
    abel

lemma reverse_unitary (D : RealSpectralCalculus H) (t : ℝ) :
    D.reverse.unitary t = D.unitary (-t) := by
  change D.calculus (spectralReflection (spectralCharacter t)) = D.calculus (spectralCharacter (-t))
  congr 1
  ext u
  simp [spectralReflection_apply, spectralCharacter, mul_neg, neg_mul]

end RealSpectralCalculus

namespace StandardModularData

lemma commutant_separating (S : StandardModularData H) (b : H →L[ℂ] H)
    (hb : b ∈ S.M.commutant) (hbxi : b S.xi = 0) : b = 0 := by
  apply ContinuousLinearMap.ext
  intro h
  change b h = 0
  refine S.cyclic.induction ?_ (isClosed_eq b.continuous continuous_const) h
  rintro v ⟨a,ha,rfl⟩
  have he := congrArg (fun A : H →L[ℂ] H => A S.xi)
    (VonNeumannAlgebra.mem_commutant_iff.mp hb a ha)
  simpa only [mul_apply_eq_comp, hbxi, map_zero] using he.symm

def commutantData (S : StandardModularData H) : StandardModularData H where
  M := S.M.commutant
  xi := S.xi
  norm_xi := S.norm_xi
  cyclic := commutant_cyclic S.M S.xi S.separating
  separating := S.commutant_separating
  D := S.D.reverse
  J := S.J
  conjugation := S.conjugation
  tomita_graph := by
    rw [S.commutant_tomita_graph]
    ext p
    change (S.J p.1,p.2) ∈ S.D.halfGraph ↔ ∃ q,
      (p.1,q) ∈ S.D.reverse.halfGraph ∧ p.2 = S.J q
    constructor
    · intro hp
      refine ⟨S.J p.2,?_,(S.conjugation p.2).symm⟩
      rw [S.D.reverse_halfGraph]
      have hh := S.halfGraph_flip hp
      change (S.J p.2,S.J (S.J p.1)) ∈ S.D.halfGraph at hh
      rwa [S.conjugation p.1] at hh
    · rintro ⟨q,hq,he⟩
      rw [S.D.reverse_halfGraph] at hq
      have hh := S.halfGraph_flip hq
      change (S.J p.1,S.J q) ∈ S.D.halfGraph at hh
      rwa [← he] at hh

end StandardModularData
end BoundedRecovery

end
end

end OAI
