import OAI.NumberTheory.DirichletL.Moments.PlainGlobalBound
import OAI.NumberTheory.DirichletL.Hecke.DyadicScale

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.CenteredMomentPlainGlobalActual
open HeckeFamily HeckeDyadic CenteredMomentPlainGlobalBound

 theorem global_polynomial_bound (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀W:SchwartzMap ℝ ℂ,Function.support (W:ℝ→ℂ)⊆Icc a b→
    ∀χ:Character,χ.residue≠1→∀D freq:ℝ,1≤D→
      ‖polynomial χ false W D 0 freq‖≤
        C*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          (χ.modulus.absNorm:ℝ)*(3+|freq|)^2:=by
  obtain ⟨S,Cm,hCm,hm⟩:=profile_strip_decay a b ha (1/2) 2 6
  obtain ⟨Cg,hCg,hg⟩:=original_upper_strip (3/10) (by norm_num)
  let E:=HeckeReciprocalBound.bound 2
  have hE:0≤E:=tsum_nonneg (fun _=>norm_nonneg _)
  let C:ℝ:=Cm*(Cg*(Real.pi+3)+E*Real.pi)/(2*Real.pi)
  have hC:0<C:=div_pos (mul_pos hCm (add_pos_of_pos_of_nonneg
    (mul_pos hCg (by positivity)) (mul_nonneg hE Real.pi_pos.le))) (by positivity)
  refine ⟨S,C,hC,?_⟩
  intro W hWs χ hχ D freq hD
  let Q:ℝ:=χ.modulus.absNorm
  let V:ℝ:=3+|freq|
  let B:ℝ:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB:0≤B:=apply_nonneg _ _
  have hQ:1≤Q:=by
    dsimp [Q]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  have hV:1≤V:=by dsimp [V]; linarith [abs_nonneg freq]
  have hQ0:0≤Q:=zero_le_one.trans hQ
  have hrad:((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)≤Q:=radical_norm_le_modulus χ
  have hrad0:0≤((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ):=Nat.cast_nonneg _
  have hcost:Q^(3/5:ℝ)*((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)^((1/10+(3/10)):ℝ)≤Q:=by
    calc
      _≤Q^(3/5:ℝ)*Q^((1/10+(3/10)):ℝ):=mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hrad0 hrad (by norm_num)) (Real.rpow_nonneg hQ0 _)
      _=Q:=by rw [←Real.rpow_add (zero_lt_one.trans_le hQ)]; norm_num
  have hgrowth (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(t:ℝ):
      ‖series χ false ((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)‖≤(Cg*Q*V^2)*(1+|t|)^2:=by
    have hs:-(1/10:ℝ)≤(((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)).re:=by simp [HeckeDyadic.shift]; linarith [hx.1]
    have hh:=hg χ hχ _ hs
    have him:(((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)).im=t-freq:=by simp [HeckeDyadic.shift,sub_eq_add_neg]
    rw [him] at hh
    have ht:3+|t-freq|≤V*(1+|t|):=by
      dsimp [V]
      have hab:=abs_sub t freq
      nlinarith [abs_nonneg t,abs_nonneg freq,mul_nonneg (abs_nonneg t) (abs_nonneg freq)]
    apply hh.trans
    change Cg*Q^(3/5:ℝ)*((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)^((1/10+(3/10)):ℝ)*
      (3+|t-freq|)^2≤_
    have hc:=mul_le_mul (mul_le_mul_of_nonneg_left hcost hCg.le)
      (pow_le_pow_left₀ (by positivity) ht 2) (by positivity) (mul_nonneg hCg.le hQ0)
    convert hc using 1 <;> ring
  have hb:=finite_strip_bound χ hχ W a b ha hWs (W.smooth ⊤) D freq (Cm*B) (Cg*Q*V^2)
    hD (mul_nonneg hCm.le hB) (by positivity) (hm W hWs) hgrowth
  have hQV:1≤Q*V^2:=one_le_mul_of_one_le_of_one_le hQ (one_le_pow₀ hV)
  have he:E≤E*(Q*V^2):=le_mul_of_one_le_right hE hQV
  apply hb.trans
  dsimp only [C]
  change _≤Cm*(Cg*(Real.pi+3)+E*Real.pi)/(2*Real.pi)*B*Q*V^2
  have hCe: Cm*B*E*Real.pi≤Cm*B*(E*(Q*V^2))*Real.pi:=by gcongr
  dsimp only [E] at hCe ⊢
  calc
    _≤(1/(2*Real.pi))*
      (Cm*B*(Cg*Q*V^2)*Real.pi+3*(Cm*B)*(Cg*Q*V^2)+
       Cm*B*(HeckeReciprocalBound.bound 2*(Q*V^2))*Real.pi):=
      mul_le_mul_of_nonneg_left (add_le_add_right hCe _) (by positivity)
    _=_:=by ring

end SevenEighths.CenteredMomentPlainGlobalActual

end

end OAI
