import OAI.NumberTheory.DirichletL.Moments.PlainGlobalEnergy

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentPlainPositiveScale
open HeckeFamily HeckeDyadic CenteredMomentPlainGlobalActual CenteredMomentPlainGlobalEnergy
open CenteredMomentHeckeTwist CenteredMomentDetectorDictionary

 theorem small_polynomial (χ:Character)(W:SchwartzMap ℝ ℂ)(a b:ℝ)(ha:0<a)
    (hWs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)(D freq:ℝ)(hD:0<D)(hD1:D≤1):
    ‖polynomial χ false W D 0 freq‖≤
      (128*max 0 b)*(SchwartzMap.seminorm ℝ 0 0 W):=by
  let B:=SchwartzMap.seminorm ℝ 0 0 W
  have hB:0≤B:=apply_nonneg _ _
  have hWs':Function.support (W:ℝ→ℂ)⊆Set.Icc a (max 0 b):=by
    intro x hx
    exact ⟨(hWs hx).1,(hWs hx).2.trans (le_max_right _ _)⟩
  have hs:=twistedIdealSum_absolute χ W a (max 0 b) B ha (le_max_left _ _) hB hWs' (W.smooth ⊤)
    (fun x=>SchwartzMap.norm_le_seminorm ℝ W x) freq D hD
  rw [←plain_height_norm χ W a b ha hWs (W.smooth ⊤) freq D hD,norm_mul,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
  have hsq:(Real.sqrt D)^2=D:=Real.sq_sqrt hD.le
  have hroot:0<Real.sqrt D:=Real.sqrt_pos.mpr hD
  have hle:Real.sqrt D≤1:=by exact (Real.sqrt_le_one).mpr hD1
  have he:(Real.sqrt D)⁻¹*((128*max 0 b*B)*D)=(128*max 0 b*B)*Real.sqrt D:=by
    calc
      _=(128*max 0 b*B)*((Real.sqrt D)⁻¹*(Real.sqrt D*Real.sqrt D)):=by rw [←pow_two,hsq];ring
      _=_:=by rw [inv_mul_cancel_left₀ hroot.ne']
  rw [he]
  exact mul_le_of_le_one_right (by positivity) hle

 theorem global_positive_scale (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀W:SchwartzMap ℝ ℂ,Function.support (W:ℝ→ℂ)⊆Set.Icc a b→
    ∀χ:Character,χ.residue≠1→∀D freq:ℝ,0<D→
      ‖polynomial χ false W D 0 freq‖≤
        C*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          (χ.modulus.absNorm:ℝ)*(3+|freq|)^2:=by
  obtain ⟨S,C,hC,hg⟩:=global_polynomial_bound a b ha
  let S':Finset (ℕ×ℕ):=insert (0,0) S
  let C':ℝ:=C+128*max 0 b
  have hC':0<C':=add_pos_of_pos_of_nonneg hC (by positivity)
  refine ⟨S',C',hC',?_⟩
  intro W hWs χ hχ D freq hD
  have hB:0≤S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=apply_nonneg _ _
  have hsup:S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) W
  have hzero:SchwartzMap.seminorm ℝ 0 0 W≤S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=
    Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) (s:=S') (i:=(0,0)) (x:=W) (Finset.mem_insert_self (0,0) S)
  have hQ:1≤(χ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  have hV:1≤(3+|freq|)^2:=one_le_pow₀ (by linarith [abs_nonneg freq])
  by_cases hD1:1≤D
  · apply (hg W hWs χ hχ D freq hD1).trans
    gcongr
    dsimp [C']; linarith [le_max_left (0:ℝ) b]
  · have hh:=small_polynomial χ W a b ha hWs D freq hD (le_of_lt (lt_of_not_ge hD1))
    apply hh.trans
    calc
      _≤C'*(S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W):=by
        apply mul_le_mul _ hzero (apply_nonneg _ _) hC'.le
        dsimp [C'];linarith
      _≤(C'*(S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W))*
          ((χ.modulus.absNorm:ℝ)*(3+|freq|)^2):=
        le_mul_of_one_le_right (mul_nonneg hC'.le hB) (one_le_mul_of_one_le_of_one_le hQ hV)
      _=_:=by ring

end SevenEighths.CenteredMomentPlainPositiveScale

end

end OAI
