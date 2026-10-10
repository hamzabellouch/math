import OAI.NumberTheory.Ostmann.Characters.MixedIndicator
import OAI.NumberTheory.Ostmann.Construction.NormalizedCRTPoisson

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Characters

def characterAmplitude {p:ℕ} [Fact p.Prime]
    (χ:MulChar (ZMod p) ℂ) (a v:ZMod p) : ℂ :=
  (gaussSum χ ZMod.stdAddChar/(Real.sqrt p:ℂ))*
    ZMod.stdAddChar (-(a*v))*χ⁻¹ (-v)

theorem unitaryDFT_translated_character {p:ℕ} [Fact p.Prime]
    (χ:MulChar (ZMod p) ℂ) (hχ:χ≠1) (a v:ZMod p) :
    Supply.unitaryDFT (fun x=>χ (x-a)) v=characterAmplitude χ a v := by
  have hd : ZMod.dft (fun x=>χ (x-a)) v =
      ZMod.stdAddChar (-(a*v))*(χ⁻¹ (-v)*gaussSum χ ZMod.stdAddChar) := by
    rw [ZMod.dft_apply]
    simp only [smul_eq_mul]
    calc
      _ = ∑y:ZMod p,ZMod.stdAddChar (-((y+a)*v))*χ y := by
        simpa only [Equiv.coe_addRight,add_sub_cancel_right] using
          Equiv.sum_comp (Equiv.addRight a) (fun x:ZMod p=>ZMod.stdAddChar (-(x*v))*χ (x-a)) |>.symm
      _ = _ := by
        rw [← gauss_transform χ hχ ZMod.stdAddChar (-v),Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        rw [show -((y+a)*v)=-(a*v)+(-v)*y by ring,AddChar.map_add_eq_mul]
        ring
  unfold Supply.unitaryDFT characterAmplitude
  rw [hd]
  ring

theorem characterAmplitude_zero {p:ℕ} [Fact p.Prime]
    (χ:MulChar (ZMod p) ℂ) (a:ZMod p) : characterAmplitude χ a 0=0 := by
  simp [characterAmplitude,MulChar.map_zero]

theorem norm_characterAmplitude {p:ℕ} [Fact p.Prime]
    (χ:MulChar (ZMod p) ℂ) (hχ:χ≠1) (a v:ZMod p) (hv:v≠0) :
    ‖characterAmplitude χ a v‖=1 := by
  have hp : (0:ℝ)<p := by exact_mod_cast Fact.out (p:=p.Prime) |>.pos
  simp only [characterAmplitude,norm_mul,norm_div,
    norm_gaussSum χ hχ _ (ZMod.isPrimitive_stdAddChar p),ZMod.card,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    (ZMod.stdAddChar : AddChar (ZMod p) ℂ).norm_apply,norm_character_of_ne_zero χ⁻¹ (neg_ne_zero.mpr hv),mul_one]
  exact div_self (Real.sqrt_pos.mpr hp).ne'

theorem character_normalized_poisson {ι:Type*} [Fintype ι] [DecidableEq ι]
    (p:ι→ℕ) [∀i,Fact (p i).Prime] [NeZero (∏i,p i)]
    (hcop:Pairwise (fun i j=>(p i).Coprime (p j)))
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (hχ:∀i,χ i≠1)
    (a:∀i,ZMod (p i)) (ψ:SchwartzMap ℝ ℂ) {X:ℝ} (hX:0<X) :
    (∑' n:ℤ,(∏i,χ i ((n:ZMod (p i))-a i))*ψ ((n:ℝ)/X))/(Real.sqrt X:ℂ) =
      (Real.sqrt (X/(∏i,p i:ℕ)):ℂ)*
        (∑' s:ℤ,(∏i,characterAmplitude (χ i) (a i) (Construction.crtFrequency p s i))*
          𝓕 ψ (-(s:ℝ)*X/(∏i,p i:ℕ))) := by
  rw [Construction.crt_normalized_poisson p hcop (fun i x=>χ i (x-a i)) ψ hX]
  simp_rw [unitaryDFT_translated_character _ (hχ _)]

end Ostmann.Characters

end

end OAI
