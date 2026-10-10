import OAI.Algebra.AffineCancellation.TorsorFrame

namespace OAI

noncomputable section

namespace ComplexCancellation.Torsor
open LaurentPolynomial
variable {P : Type*} [CommRing P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ)
abbrev KB := FractionRing Bundle.B
def ib : Bundle.B →ₐ[ℂ] KB := IsScalarTower.toAlgHom ℂ Bundle.B KB
def bc : Determinant.T →ₐ[ℂ] KB := ib.comp Bundle.j
variable (f : P →ₐ[ℂ] KB) (hf : f.comp ρ=ib.comp Bundle.pullback)
include hf
lemma compatibility (r : Quadric.R) : f (ρ (Degeneration.coefficientMap r))=bc (Bundle.inclusion r) := by
  rw [← AlgHom.comp_apply,hf]
  change ib (Bundle.pullback (Degeneration.coefficientMap r))=_
  change ib ((Bundle.pullback.comp Degeneration.coefficientMap) r)=_
  rw [Bundle.pullback_coefficientMap]
  rfl
lemma back_ab : f Q.a₀*f Q.b₀=bc Determinant.a*bc Determinant.b := by
  rw [← map_mul,Q.ab]
  simpa only [Degeneration.coefficientMap_x,Bundle.inclusion_x,map_mul] using compatibility ρ f hf Quadric.x
lemma back_dc : f Q.d₀*f Q.c₀=bc Determinant.d*bc Determinant.c := by
  rw [← map_mul,Q.dc]
  simpa only [Degeneration.coefficientMap_y,Bundle.inclusion_y,map_mul] using compatibility ρ f hf Quadric.y
lemma back_db : f Q.d₀*f Q.b₀=bc Determinant.d*bc Determinant.b := by
  rw [← map_mul,Q.db]
  simpa only [Degeneration.coefficientMap_z,Bundle.inclusion_z,map_mul] using compatibility ρ f hf Quadric.z
omit hf in
lemma bc_det : bc Determinant.a*bc Determinant.c-bc Determinant.b*bc Determinant.d=1 := by
  simpa only [map_mul,map_sub,map_one] using congrArg bc Determinant.determinant
lemma back_ac : f Q.a₀*f Q.c₀=bc Determinant.a*bc Determinant.c := by
  have he := congrArg f Q.det
  simp only [map_mul,map_sub,map_one] at he
  rw [back_db ρ Q f hf] at he
  linear_combination he-bc_det

def w : KB := f Q.c₀*bc Determinant.a-f Q.b₀*bc Determinant.d
def wi : KB := f Q.a₀*bc Determinant.c-f Q.d₀*bc Determinant.b
lemma back_a : f Q.a₀*w ρ Q f=bc Determinant.a := by
  dsimp [w]
  calc _ = (f Q.a₀*f Q.c₀)*bc Determinant.a-(f Q.a₀*f Q.b₀)*bc Determinant.d := by ring
    _ = _ := by rw [back_ac ρ Q f hf,back_ab ρ Q f hf]; linear_combination bc Determinant.a*bc_det
lemma back_d : f Q.d₀*w ρ Q f=bc Determinant.d := by
  dsimp [w]
  calc _ = (f Q.d₀*f Q.c₀)*bc Determinant.a-(f Q.d₀*f Q.b₀)*bc Determinant.d := by ring
    _ = _ := by rw [back_dc ρ Q f hf,back_db ρ Q f hf]; linear_combination bc Determinant.d*bc_det
lemma back_b : f Q.b₀*wi ρ Q f=bc Determinant.b := by
  dsimp [wi]
  calc _ = (f Q.a₀*f Q.b₀)*bc Determinant.c-(f Q.d₀*f Q.b₀)*bc Determinant.b := by ring
    _ = _ := by rw [back_ab ρ Q f hf,back_db ρ Q f hf]; linear_combination bc Determinant.b*bc_det
lemma back_c : f Q.c₀*wi ρ Q f=bc Determinant.c := by
  dsimp [wi]
  calc _ = (f Q.a₀*f Q.c₀)*bc Determinant.c-(f Q.d₀*f Q.c₀)*bc Determinant.b := by ring
    _ = _ := by rw [back_ac ρ Q f hf,back_dc ρ Q f hf]; linear_combination bc Determinant.c*bc_det
lemma w_wi : w ρ Q f*wi ρ Q f=1 := by
  calc _ = bc Determinant.a*(f Q.c₀*wi ρ Q f)-bc Determinant.d*(f Q.b₀*wi ρ Q f) := by dsimp [w]; ring
    _ = _ := by rw [back_c ρ Q f hf,back_b ρ Q f hf]; linear_combination bc_det
def W : KBˣ := ⟨w ρ Q f,wi ρ Q f,w_wi ρ Q f hf,by rw [mul_comm]; exact w_wi ρ Q f hf⟩
def backward : L (P := P) →ₐ[ℂ] KB where
  __ := LaurentPolynomial.eval₂ f.toRingHom (W ρ Q f hf)
  commutes' r := by
    change LaurentPolynomial.eval₂ f.toRingHom (W ρ Q f hf) (C (algebraMap ℂ P r))=_
    rw [LaurentPolynomial.eval₂_C]
    exact f.commutes r
@[simp] lemma backward_C (r : P) : backward ρ Q f hf (C r)=f r := LaurentPolynomial.eval₂_C _ _ _
@[simp] lemma backward_T_one : backward ρ Q f hf (T 1)=w ρ Q f := by
  change LaurentPolynomial.eval₂ f.toRingHom (W ρ Q f hf) (T 1)=_
  rw [LaurentPolynomial.eval₂_T]
  simp only [zpow_one,W,Units.val_mk]
@[simp] lemma backward_T_neg_one : backward ρ Q f hf (T (-1))=wi ρ Q f := by
  change LaurentPolynomial.eval₂ f.toRingHom (W ρ Q f hf) (T (-1))=_
  rw [LaurentPolynomial.eval₂_T]
  simp only [zpow_neg_one]
  rfl
lemma backward_frameMap : (backward ρ Q f hf).comp (frameMap ρ Q)=bc := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change backward ρ Q f hf (frameMap ρ Q Determinant.a)=bc Determinant.a
    rw [frameMap_a,map_mul,backward_C,backward_T_one,back_a ρ Q f hf]
  · change backward ρ Q f hf (frameMap ρ Q Determinant.d)=bc Determinant.d
    rw [frameMap_d,map_mul,backward_C,backward_T_one,back_d ρ Q f hf]
  · change backward ρ Q f hf (frameMap ρ Q Determinant.b)=bc Determinant.b
    rw [frameMap_b,map_mul,backward_C,backward_T_neg_one,back_b ρ Q f hf]
  · change backward ρ Q f hf (frameMap ρ Q Determinant.c)=bc Determinant.c
    rw [frameMap_c,map_mul,backward_C,backward_T_neg_one,back_c ρ Q f hf]
  · change backward ρ Q f hf (frameMap ρ Q Determinant.u)=bc Determinant.u
    rw [frameMap_u,backward_C]
    simpa only [Degeneration.coefficientMap_u,Bundle.inclusion_u] using compatibility ρ f hf Quadric.u
lemma backward_forward_j (r : Determinant.T) : backward ρ Q f hf (forward ρ Q (Bundle.j r))=ib (Bundle.j r) := by
  rw [forward_j]
  exact DFunLike.congr_fun (backward_frameMap ρ Q f hf) r
lemma backward_forward_τ : backward ρ Q f hf (forward ρ Q Bundle.τ)=ib Bundle.τ := by
  rw [forward_τ]
  change backward ρ Q f hf (C (ρ Degeneration.p))=_
  rw [backward_C,← AlgHom.comp_apply,hf]
  change ib (Bundle.pullback (Degeneration.π (MvPolynomial.X 0)))=_
  rw [Bundle.pullback_π]
  congr 1
  exact MvPolynomial.aeval_X _ 0
lemma backward_forward_V : backward ρ Q f hf (forward ρ Q Bundle.V)=ib Bundle.V := by
  have hp : ib Bundle.τ ≠ 0 := by
    have hi : Function.Injective ib := IsFractionRing.injective Bundle.B KB
    simpa only [map_zero] using hi.ne Bundle.τ_ne_zero
  apply mul_left_cancel₀ (pow_ne_zero 2 hp)
  have he := congrArg (fun z => backward ρ Q f hf (forward ρ Q z)) Bundle.equation
  rw [map_mul,map_pow,map_mul,map_pow,backward_forward_τ,backward_forward_j] at he
  rw [he,← Bundle.equation,map_mul,map_pow]
lemma backward_forward : (backward ρ Q f hf).comp (forward ρ Q)=ib := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext'
  · ext r
    exact backward_forward_j ρ Q f hf r
  · intro i
    fin_cases i
    · exact backward_forward_τ ρ Q f hf
    · exact backward_forward_V ρ Q f hf
lemma forward_injective : Function.Injective (forward ρ Q) := by
  apply Function.Injective.of_comp (f := backward ρ Q f hf)
  rw [← AlgHom.coe_comp,backward_forward]
  exact IsFractionRing.injective Bundle.B KB
end ComplexCancellation.Torsor

end

end OAI
