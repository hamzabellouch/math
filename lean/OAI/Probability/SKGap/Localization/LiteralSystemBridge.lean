import Mathlib
import OAI.Probability.SKGap.Localization.LiteralInitialSystem

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

def LiteralEquations (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n) : Prop :=
  Equations j (siteMean (fun v i=>phi (z v i) (r i) (a v)) x) (n:ℝ)⁻¹
    (siteMean (initialP f z a r e) x) (phiDiagonal (z x) r (a x))
    (toEuclideanCLM (𝕜:=ℝ) J) (WithLp.toLp 2 (initialU f z a r e x))
    (WithLp.toLp 2 (m x)) (WithLp.toLp 2 (fun i=>Real.tanh (r i)))
    (WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)))
    (WithLp.toLp 2 (w x)) (WithLp.toLp 2 (y x)) (c x)

lemma phiDiagonal_apply (z r : Fin n→ℝ) (a : ℝ) (v : Euclid n) (i : Fin n) :
    phiDiagonal z r a v i=phi (z i) (r i) a*v i := by
  change (toEuclideanCLM (𝕜:=ℝ) (diagonal (fun k=>phi (z k) (r k) a)) (WithLp.toLp 2 v.ofLp)) i=_
  simp only [toEuclideanCLM_toLp,WithLp.ofLp_toLp,mulVec_diagonal]

lemma literal_first_equation (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n) :
    ((WithLp.toLp 2 (w x) : Euclid n)=phiDiagonal (z x) r (a x)
      (WithLp.toLp 2 (initialU f z a r e x)+WithLp.toLp 2 (y x)-
        (j*c x) • WithLp.toLp 2 (fun i=>Real.tanh (r i)))) ↔
      w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x := by
  have he : (phiDiagonal (z x) r (a x)
      (WithLp.toLp 2 (initialU f z a r e x)+WithLp.toLp 2 (y x)-
        (j*c x) • WithLp.toLp 2 (fun i=>Real.tanh (r i)))).ofLp=
      (literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x := by
    ext i
    rw [literalInitial_source _ _ _ _ _ _ _ _ _ _ _ hd]
    change phiDiagonal _ _ _ _ i=_
    rw [phiDiagonal_apply]
    change phi (z x i) (r i) (a x)*
      (f.eval (z x i) (r i) (a x)/phi (z x i) (r i) (a x)*e i+y x i-j*c x*Real.tanh (r i))=_
    field_simp [(phi_pos (z x i) (r i) (a x)).ne']
    ring
  constructor
  · intro h; exact (congrArg WithLp.ofLp h).trans he
  · intro h; exact WithLp.ofLp_injective 2 (h.trans he.symm)

lemma literalEquations_recipe (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (hd : d≠0) (x : Spin n) :
    LiteralEquations J j f z m w y a c r e x ↔
      w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x ∧
      y x=(literalInitial J j d f z m a c r e).fieldOf 1 (fun _=>w) (fun _=>y) x ∧
      c x=siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x := by
  have hc (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x) :
      c x=(n:ℝ)⁻¹*inner ℝ (WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)) : Euclid n)
          (WithLp.toLp 2 (w x))+siteMean (initialP f z a r e) x ↔
        c x=siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x := by
    rw [initial_scalar_equation]
    change c x=(∑i,(logSlope (z x i) (r i) (a x)*w x i+initialP f z a r e x i))/(n:ℝ) ↔ _
    rw [siteMean,literalInitial_partial_source _ _ _ _ _ _ _ _ _ _ _ _ hd x hw]
  have hy (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x)
      (hc : c x=siteMean ((literalInitial J j d f z m a c r e).implicitPartial y) x) :
      (WithLp.toLp 2 (y x) : Euclid n)=toEuclideanCLM (𝕜:=ℝ) J (WithLp.toLp 2 (w x))-
        (j*siteMean (fun v i=>phi (z v i) (r i) (a v)) x) • WithLp.toLp 2 (w x)-
        (j*c x) • WithLp.toLp 2 (m x) ↔
      y x=(literalInitial J j d f z m a c r e).fieldOf 1 (fun _=>w) (fun _=>y) x := by
    rw [literalInitial_field _ _ _ _ _ _ _ _ _ _ _ _ x hw hc]
    constructor
    · intro h; exact congrArg WithLp.ofLp h
    · intro h; exact WithLp.ofLp_injective 2 h
  constructor
  · intro h
    have hw:=(literal_first_equation J j d f z m w y a c r e hd x).mp h.1
    have hs:=(hc hw).mp h.2.2
    exact ⟨hw,(hy hw hs).mp h.2.1,hs⟩
  · rintro ⟨hw,hy',hc'⟩
    exact ⟨(literal_first_equation J j d f z m w y a c r e hd x).mpr hw,
      (hy hw hc').mpr hy',(hc hw).mpr hc'⟩
end SKGapCutoff.Recipe

end
end

end OAI
