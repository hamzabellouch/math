import OAI.Algebra.AffineCancellation.PositiveObstruction
import OAI.Algebra.AffineCancellation.DegenerationGrading

namespace OAI

noncomputable section

namespace ComplexCancellation.Torsor
open LaurentPolynomial
open MvPolynomial (X aeval aeval_X eval₂Hom_C eval₂Hom_X)
variable {P : Type*} [CommRing P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P)
structure Frame where
  a₀ : P
  d₀ : P
  b₀ : P
  c₀ : P
  ab : a₀*b₀=ρ Degeneration.x
  dc : d₀*c₀=ρ Degeneration.y
  db : d₀*b₀=ρ Degeneration.z
  det : a₀*c₀-d₀*b₀=1
variable (Q : Frame ρ)
abbrev L := LaurentPolynomial P
def cc : P →ₐ[ℂ] L (P := P) := IsScalarTower.toAlgHom ℂ P (L (P := P))
def base : Degeneration.G →ₐ[ℂ] L (P := P) := (cc (P := P)).comp ρ
omit [Algebra ℂ P] in
lemma mono_pair (r s : P) : C r*T (1:ℤ)*(C s*T (-1))=C (r*s) := by
  calc C r*T (1:ℤ)*(C s*T (-1)) = C (r*s)*(T (1:ℤ)*T (-1)) := by rw [map_mul]; ring
    _ = _ := by rw [← T_add]; norm_num

def frameEval : Determinant.Poly →ₐ[ℂ] L (P := P) :=
  aeval ![C Q.a₀*T 1,C Q.d₀*T 1,C Q.b₀*T (-1),C Q.c₀*T (-1),C (ρ Degeneration.u)]
lemma frameEval_relation : frameEval ρ Q Determinant.relation=0 := by
  simp only [frameEval,Determinant.relation,map_sub,map_mul,map_one,aeval_X,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [mono_pair,mul_comm (C Q.b₀*T (-1)),mono_pair,← map_sub,Q.det,map_one,sub_self]
def frameMap : Determinant.T →ₐ[ℂ] L (P := P) :=
  Ideal.Quotient.liftₐ _ (frameEval ρ Q) (by
    intro r hr
    obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
    rw [map_mul,frameEval_relation,zero_mul])
@[simp] lemma frameMap_π (r : Determinant.Poly) : frameMap ρ Q (Determinant.π r)=frameEval ρ Q r :=
  Ideal.Quotient.lift_mk _ _ _
@[simp] lemma frameMap_a : frameMap ρ Q Determinant.a=C Q.a₀*T 1 := by simp [Determinant.a,frameEval]
@[simp] lemma frameMap_d : frameMap ρ Q Determinant.d=C Q.d₀*T 1 := by simp [Determinant.d,frameEval]
@[simp] lemma frameMap_b : frameMap ρ Q Determinant.b=C Q.b₀*T (-1) := by simp [Determinant.b,frameEval,Matrix.cons_val]
@[simp] lemma frameMap_c : frameMap ρ Q Determinant.c=C Q.c₀*T (-1) := by simp [Determinant.c,frameEval,Matrix.cons_val]
@[simp] lemma frameMap_u : frameMap ρ Q Determinant.u=C (ρ Degeneration.u) := by simp [Determinant.u,frameEval,Matrix.cons_val]
lemma frameMap_inclusion : (frameMap ρ Q).comp Bundle.inclusion = (base ρ).comp Degeneration.coefficientMap := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change frameMap ρ Q (Bundle.inclusion Quadric.x)=base ρ (Degeneration.coefficientMap Quadric.x)
    rw [Bundle.inclusion_x,map_mul,frameMap_a,frameMap_b,mono_pair,Q.ab,Degeneration.coefficientMap_x]
    rfl
  · change frameMap ρ Q (Bundle.inclusion Quadric.y)=base ρ (Degeneration.coefficientMap Quadric.y)
    rw [Bundle.inclusion_y,map_mul,frameMap_d,frameMap_c,mono_pair,Q.dc,Degeneration.coefficientMap_y]
    rfl
  · change frameMap ρ Q (Bundle.inclusion Quadric.z)=base ρ (Degeneration.coefficientMap Quadric.z)
    rw [Bundle.inclusion_z,map_mul,frameMap_d,frameMap_b,mono_pair,Q.db,Degeneration.coefficientMap_z]
    rfl
  · change frameMap ρ Q (Bundle.inclusion Quadric.u)=base ρ (Degeneration.coefficientMap Quadric.u)
    rw [Bundle.inclusion_u,frameMap_u,Degeneration.coefficientMap_u]
    rfl
lemma frame_f : base ρ Degeneration.p^2*base ρ Degeneration.F =
    frameMap ρ Q Bundle.C₁*frameMap ρ Q Determinant.v := by
  have h := DFunLike.congr_fun (frameMap_inclusion ρ Q) Quadric.f
  simpa only [AlgHom.comp_apply,Bundle.inclusion_f,map_mul,Degeneration.coefficientMap_f,map_pow] using h.symm
lemma frame_g : base ρ Degeneration.p^2*base ρ Degeneration.J =
    frameMap ρ Q (Determinant.b^2)*frameMap ρ Q Determinant.v := by
  have h := DFunLike.congr_fun (frameMap_inclusion ρ Q) Quadric.g
  simpa only [AlgHom.comp_apply,Bundle.inclusion_g,map_mul,Degeneration.coefficientMap_g,map_pow] using h.symm

def vb : L (P := P) := frameMap ρ Q Bundle.α*base ρ Degeneration.F+frameMap ρ Q Bundle.β*base ρ Degeneration.J
lemma vb_equation : base ρ Degeneration.p^2*vb ρ Q=frameMap ρ Q Determinant.v := by
  have h := congrArg (frameMap ρ Q) Bundle.certificate
  simp only [map_add,map_mul,map_one] at h
  calc _ = frameMap ρ Q Bundle.α*(base ρ Degeneration.p^2*base ρ Degeneration.F)+
      frameMap ρ Q Bundle.β*(base ρ Degeneration.p^2*base ρ Degeneration.J) := by dsimp [vb]; ring
    _ = _ := by rw [frame_f,frame_g]; linear_combination frameMap ρ Q Determinant.v*h

def forwardEval : AffineModification.P Determinant.T →ₐ[ℂ] L (P := P) where
  __ := MvPolynomial.eval₂Hom (frameMap ρ Q).toRingHom ![base ρ Degeneration.p,vb ρ Q]
  commutes' r := by
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C (algebraMap ℂ Determinant.T r))=_
    rw [eval₂Hom_C]
    exact (frameMap ρ Q).commutes r
@[simp] lemma forwardEval_C (r : Determinant.T) : forwardEval ρ Q (MvPolynomial.C r)=frameMap ρ Q r := eval₂Hom_C _ _ _
@[simp] lemma forwardEval_X (i : Fin 2) : forwardEval ρ Q (X i)=![base ρ Degeneration.p,vb ρ Q] i := by
  change MvPolynomial.eval₂ _ _ (X i)=_
  exact MvPolynomial.eval₂_X _ _ _
lemma forwardEval_rel : forwardEval ρ Q (AffineModification.rel Determinant.T Determinant.v)=0 := by
  simp only [AffineModification.rel,map_sub,map_mul,map_pow,forwardEval_C,forwardEval_X,
    Matrix.cons_val_zero,Matrix.cons_val_one,vb_equation,sub_self]
def forward : Bundle.B →ₐ[ℂ] L (P := P) :=
  Ideal.Quotient.liftₐ _ (forwardEval ρ Q) (by
    intro r hr
    obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
    rw [map_mul,forwardEval_rel,zero_mul])
@[simp] lemma forward_π (r : AffineModification.P Determinant.T) :
    forward ρ Q (AffineModification.π Determinant.T Determinant.v r)=forwardEval ρ Q r :=
  Ideal.Quotient.lift_mk _ _ _
@[simp] lemma forward_j (r : Determinant.T) : forward ρ Q (Bundle.j r)=frameMap ρ Q r :=
by
  change forward ρ Q (AffineModification.π Determinant.T Determinant.v (MvPolynomial.C r))=_
  rw [forward_π,forwardEval_C]
@[simp] lemma forward_τ : forward ρ Q Bundle.τ=base ρ Degeneration.p := by
  simp [Bundle.τ,AffineModification.τ]
@[simp] lemma forward_V : forward ρ Q Bundle.V=vb ρ Q := by
  simp [Bundle.V,AffineModification.V]
lemma base_p_ne_zero (hρ : Function.Injective ρ) : base ρ Degeneration.p ≠ 0 := by
  have hp : Degeneration.p ≠ 0 := Degeneration.p_regular.ne_zero
  change C (ρ Degeneration.p) ≠ 0
  intro hz
  have hn : ρ Degeneration.p ≠ 0 := by simpa only [map_zero] using hρ.ne hp
  apply hn
  have he := congrArg (fun z : L (P := P) => z.coeff 0) hz
  simpa [LaurentPolynomial.C_apply] using he
variable [IsDomain P]
lemma forward_pullback (hρ : Function.Injective ρ) : (forward ρ Q).comp Bundle.pullback=base ρ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change forward ρ Q (Bundle.pullback (Degeneration.π (X i)))=base ρ (Degeneration.π (X i))
  rw [Bundle.pullback_π]
  simp only [Bundle.eval,MvPolynomial.aeval_X,Bundle.values]
  fin_cases i
  · change forward ρ Q Bundle.τ=base ρ Degeneration.p
    exact forward_τ ρ Q
  · change forward ρ Q (Bundle.j (Bundle.inclusion Quadric.s))=base ρ Degeneration.s
    rw [forward_j]
    simpa only [AlgHom.comp_apply,Degeneration.coefficientMap_s] using DFunLike.congr_fun (frameMap_inclusion ρ Q) Quadric.s
  · change forward ρ Q (Bundle.j Determinant.u)=base ρ Degeneration.u
    rw [forward_j,frameMap_u]
    rfl
  · change forward ρ Q (Bundle.j Bundle.C₁*Bundle.V)=base ρ Degeneration.F
    rw [map_mul,forward_j,forward_V]
    apply mul_left_cancel₀ (pow_ne_zero 2 (base_p_ne_zero ρ hρ))
    calc _ = frameMap ρ Q Bundle.C₁*(base ρ Degeneration.p^2*vb ρ Q) := by ring
      _ = _ := by rw [vb_equation,← frame_f]
  · change forward ρ Q (Bundle.j (Determinant.b^2)*Bundle.V)=base ρ Degeneration.J
    rw [map_mul,forward_j,forward_V]
    apply mul_left_cancel₀ (pow_ne_zero 2 (base_p_ne_zero ρ hρ))
    calc _ = frameMap ρ Q (Determinant.b^2)*(base ρ Degeneration.p^2*vb ρ Q) := by ring
      _ = _ := by rw [vb_equation,← frame_g]
end ComplexCancellation.Torsor

end

end OAI
