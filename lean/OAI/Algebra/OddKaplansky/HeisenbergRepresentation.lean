import OAI.Algebra.OddKaplansky.Heisenberg

namespace OAI

universe portUniverse1

section
namespace OddKaplansky.Heisenberg
noncomputable section
open scoped Classical BigOperators Matrix
variable (M q : ℕ) [NeZero M] {K : Type portUniverse1} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
lemma character_dot (s y : Z M q) : Fourier.character M hζ s y = Fourier.cyclicCharacter M hζ (dot M q y s) := by
  rw [dot_symm]; rfl

def ρGroup : GroupData M q →* Matrix (Z M q) (Z M q) K where
  toFun g := Matrix.of fun u s => if u=s*g.x then (Fourier.cyclicCharacter M hζ g.k : K)*(Fourier.character M hζ s g.y : K) else 0
  map_one' := by ext u s; simp [Matrix.of_apply, Matrix.one_apply]
  map_mul' g h := by
    ext u s
    rw [Matrix.mul_apply,Finset.sum_eq_single (s*h.x)]
    · simp only [Matrix.of_apply,mul_x,mul_y,mul_k,map_mul,Units.val_mul]
      by_cases he : u=s*h.x*g.x
      · rw [show s*(g.x*h.x)=s*h.x*g.x by ac_rfl,ite_eq_left he,ite_eq_left he,ite_true]
        rw [Fourier.character_mul,MonoidHom.mul_apply,Units.val_mul]
        simp only [character_dot]
        ring
      · simp only [show s*(g.x*h.x)=s*h.x*g.x by ac_rfl,ite_eq_right he,zero_mul]
    · intro b _ hb
      simp only [Matrix.of_apply,ite_eq_right hb,mul_zero]
    · simp

def ρ : MonoidAlgebra K (GroupData M q) →ₐ[K] Matrix (Z M q) (Z M q) K := MonoidAlgebra.lift K _ _ (ρGroup M q hζ)
lemma ρ_single (g : GroupData M q) (c : K) (u s : Z M q) :
    ρ M q hζ (MonoidAlgebra.single g c) u s =
      if u=s*g.x then c*(Fourier.cyclicCharacter M hζ g.k : K)*(Fourier.character M hζ s g.y : K) else 0 := by
  rw [ρ,MonoidAlgebra.lift_single]
  change c*(if u=s*g.x then _ else 0)=_
  split_ifs <;> simp [mul_assoc]
def f : MonoidAlgebra K (GroupData M q) := CharacterIdempotents.pushed (central M q) (Fourier.cyclicCharacter M hζ)
lemma f_idempotent (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) : f M q hζ*f M q hζ=f M q hζ := CharacterIdempotents.pushed_idempotent _ _ hc
lemma f_ne_zero (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) : f M q hζ ≠ 0 := CharacterIdempotents.pushed_ne_zero _ (central_injective M q) _ hc
lemma f_central (a : MonoidAlgebra K (GroupData M q)) : Commute (f M q hζ) a := CharacterIdempotents.pushed_central _ _ (central_commute M q) a
lemma ρ_f (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) : ρ M q hζ (f M q hζ)=1 := by
  ext u s
  rw [f,CharacterIdempotents.pushed_eq_sum,map_smul,map_sum]
  simp only [Matrix.smul_apply,Matrix.sum_apply,ρ_single,central,MonoidHom.coe_mk,OneHom.coe_mk,mul_one,map_one,Units.val_one,mul_one,Matrix.one_apply]
  by_cases he : u=s
  · subst u
    simp only [ite_true,inv_mul_cancel₀ (Units.ne_zero _),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,smul_eq_mul]
    exact inv_mul_cancel₀ hc
  · simp [he]
def p (v : Z M q) : MonoidAlgebra K (GroupData M q) := CharacterIdempotents.pushed (Y M q) (Fourier.character M hζ v)
def D (v : Z M q) : MonoidAlgebra K (GroupData M q) := f M q hζ * p M q hζ v
lemma ρ_p (hc : (Fintype.card (Z M q) : K) ≠ 0) (v : Z M q) :
    ρ M q hζ (p M q hζ v) = Matrix.single v v 1 := by
  ext u s
  rw [p,CharacterIdempotents.pushed_eq_sum,map_smul,map_sum]
  simp only [Matrix.smul_apply,Matrix.sum_apply,ρ_single,Y,MonoidHom.coe_mk,OneHom.coe_mk,mul_one,map_one,Units.val_one]
  by_cases he : u=s
  · subst u
    simp only [ite_true,smul_eq_mul]
    have hs : ∑ a : Z M q, (Fourier.character M hζ v a : K)⁻¹ * (Fourier.character M hζ s a : K) = if s=v then (Fintype.card (Z M q) : K) else 0 := by
      by_cases hsv : s=v
      · subst s; simp
      · rw [ite_eq_right hsv]
        have hh := CharacterIdempotents.sum_character_eq_zero ((Fourier.character M hζ s)*(Fourier.character M hζ v)⁻¹) (by
          intro h
          apply hsv
          apply Fourier.character_injective M hζ
          apply MonoidHom.ext
          intro a
          exact mul_inv_eq_one.mp (congrArg (fun f : Z M q →* Kˣ => f a) h))
        simpa [mul_comm] using hh
    rw [hs]
    by_cases hsv : s=v
    · subst s
      simpa only [Matrix.single_apply,ite_true,and_self] using inv_mul_cancel₀ hc
    · simp [hsv,Ne.symm hsv,Matrix.single]
  · simp [he,Matrix.single]; aesop
lemma ρ_D (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) (hz : (Fintype.card (Z M q) : K) ≠ 0) (v : Z M q) :
    ρ M q hζ (D M q hζ v)=Matrix.single v v 1 := by rw [D,map_mul,ρ_f M q hζ hc,one_mul,ρ_p M q hζ hz]
def xElt (u : Z M q) : MonoidAlgebra K (GroupData M q) := MonoidAlgebra.single (X M q u) 1
def Ω (u v : Z M q) : MonoidAlgebra K (GroupData M q) := xElt M q (u*v⁻¹) * D M q hζ v
lemma ρ_Ω (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) (hz : (Fintype.card (Z M q) : K) ≠ 0) (u v : Z M q) :
    ρ M q hζ (Ω M q hζ u v)=Matrix.single u v 1 := by
  rw [Ω,map_mul,ρ_D M q hζ hc hz]
  ext a b
  simp only [Matrix.mul_apply,xElt,ρ_single,X,MonoidHom.coe_mk,OneHom.coe_mk,map_one,Units.val_one,mul_one,Matrix.single]
  by_cases hb : b=v
  · subst b
    simp only [Matrix.of_apply,ite_and,mul_ite,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    simp [eq_comm]
  · simp [Ne.symm hb,Matrix.of_apply]
end
end OddKaplansky.Heisenberg

end

end OAI
