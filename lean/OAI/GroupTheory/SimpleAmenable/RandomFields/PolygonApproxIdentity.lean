import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.SignalGoodRows

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonApproxIdentity
open Classical

theorem polygon_signal_approx_identity {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K L : ℝ)
    (hL : 0<L) (hKL : K+2 ≤ L)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    (hχ₁ : ∀x,‖x‖ ≤ K+2 → χ x=1)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0) :
    ∃R Q Cv Ca : ℝ,0 ≤ R ∧ 0 ≤ Q ∧ 0 ≤ Cv ∧ 0 ≤ Ca ∧
      ∀(N r η κ : ℝ) (hN : 1 ≤ N),Q ≤ N → 1 ≤ r → r ≤ N →
        0<η → η ≤ 1 → 0<κ → 36 ≤ r*η → 1 ≤ 2*κ/(r/N) → R ≤ κ/(r/N) →
        let J := flagBoxFinset (a:=a) (m:=m) (v:=v) hD
          (mul_pos (lt_of_lt_of_le zero_lt_one hN) hL)
        let h := flagSignalDifference (v:=v) hD g (fun x => q+ψ x) N
        let e := fun z => (∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w)-h z
        let δ := 38880/((D:ℝ)*Real.sqrt (r*η))
        (∀z,z∉J → e z=0) ∧
        ∑z∈J,(e z)^2 ≤ flagVolumeConstant m D L*(Cv*η*(1+δ)+Ca*δ)^2+
          flagExceptionalConstant a m D L*(κ+r/N)*(flagRowSumConstant D*Ca)^2 := by
  obtain ⟨R,Q₁,Cv,Ca,hR,hQ₁,hCv,hCa,hamp,hgood⟩ :=
    flagSignal_good_row_constants (v:=v) hD g ψ χ hψ hsψ q K hcompact hχ₁
  obtain ⟨Q₂,hQ₂,hsupp⟩ := flagSignal_box_support (v:=v) hD g ψ q hL (by linarith) hcompact
  refine ⟨R,max Q₁ Q₂,Cv,Ca,hR,(hQ₁.trans (le_max_left _ _)),hCv,hCa,
    fun N r η κ hN hQN hr hrN hη hη₁ hκ hscale hline hRf => ?_⟩
  have hN' : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hr' : 0<r := lt_of_lt_of_le zero_lt_one hr
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have hρ : 0<(D:ℝ)^4/5 := by positivity
  let J := flagBoxFinset (a:=a) (m:=m) (v:=v) hD (mul_pos hN' hL)
  let h := flagSignalDifference (v:=v) hD g (fun x => q+ψ x) N
  let e := fun z => (∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w)-h z
  let δ := 38880/((D:ℝ)*Real.sqrt (r*η))
  change (∀z,z∉J → e z=0) ∧ _
  have hprod (z w : FlagSite a m D v) (hw : w∉J) :
      flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w=0 := by
    rw [flagAveragingMatrix_box_support hD χ hL hN' hχc _ _ _ _ z w (Or.inr hw),zero_mul]
  refine ⟨?_,?_⟩
  · intro z hz
    have hh := hsupp N hN' ((le_max_right _ _).trans hQN) z hz
    dsimp [e,h]
    rw [hh,sub_zero]
    apply Finset.sum_eq_zero
    intro w hw
    rw [flagAveragingMatrix_box_support hD χ hL hN' hχc _ _ _ _ z w (Or.inl hz),zero_mul]
  · apply flag_good_bad_energy hD hL hκ (div_pos hr' hN') ((div_le_one hN').mpr hrN) hN
        (by rwa [div_mul_cancel₀ _ hN'.ne'])
        (show 0 ≤ Cv*η*(1+δ)+Ca*δ by dsimp [δ]; positivity)
        (show 0 ≤ flagRowSumConstant D*Ca by dsimp [flagRowSumConstant]; positivity) J
        (fun z hz => by simpa only [mul_comm N L] using (mem_flagBoxFinset _ _ _).mp hz) e
    · intro z hz hzg
      have hh := hgood N r η κ hN' ((le_max_left _ _).trans hQN) hr' hη hη₁ hκ
        hscale hline hRf z J hzg (hprod z)
      convert hh using 1
      dsimp [e,h,δ]
      ring
    · intro z hz
      have hh := flagAveragingMatrix_crude_error hD χ hχ h hρ hN' hr' hη hκ
        (show 1 ≤ r*η by linarith) (div_nonneg hCa hN'.le) (hamp N hN') z J
      convert hh using 1
      dsimp [e,flagRowSumConstant]
      ring

end PolygonApproxIdentity

section FiniteResolvent
open Classical Matrix

noncomputable def finiteL2Norm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ‖WithLp.toLp 2 x‖

theorem finiteL2Norm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ finiteL2Norm x := norm_nonneg _

theorem finiteL2Norm_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    finiteL2Norm x^2=∑i,x i^2 := by
  simp [finiteL2Norm,PiLp.norm_sq_eq_of_L2,Real.norm_eq_abs,sq_abs]

theorem finiteL2Norm_add {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    finiteL2Norm (x+y) ≤ finiteL2Norm x+finiteL2Norm y := by
  simpa only [finiteL2Norm,WithLp.toLp_add] using norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

theorem finiteL2Norm_sub {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    finiteL2Norm (x-y) ≤ finiteL2Norm x+finiteL2Norm y := by
  simpa only [finiteL2Norm,WithLp.toLp_sub] using norm_sub_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

theorem finiteL2Norm_smul {ι : Type*} [Fintype ι] (c : ℝ) (x : ι → ℝ) :
    finiteL2Norm (c • x)=|c| * finiteL2Norm x := by
  simp only [finiteL2Norm,WithLp.toLp_smul,norm_smul,Real.norm_eq_abs]

theorem finiteL2Norm_one_add_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (x : ι → ℝ) :
    finiteL2Norm x ≤ finiteL2Norm ((1+B)*ᵥx) := by
  let y := (1+B)*ᵥx
  let S := ∑i,x i^2
  let T := ∑i,y i^2
  let P := ∑i,x i*y i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hp : 0 ≤ ∑i,x i*(B*ᵥx) i := by
    simpa only [dotProduct,star_trivial] using hB.dotProduct_mulVec_nonneg x
  have he : P=S+(∑i,x i*(B*ᵥx) i) := by
    simp only [P,S,y,Matrix.add_mulVec,Matrix.one_mulVec,Pi.add_apply,mul_add,Finset.sum_add_distrib,pow_two]
  have hSP : S ≤ P := by linarith
  have hP : 0 ≤ P := hS.trans hSP
  have hcs : P^2 ≤ S*T := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hST : S ≤ T := by
    by_cases h : S=0
    · simpa only [h] using hT
    · have hS' : 0<S := lt_of_le_of_ne hS (Ne.symm h)
      have hsq := pow_le_pow_left₀ hS hSP 2
      nlinarith
  apply (sq_le_sq₀ (finiteL2Norm_nonneg _) (finiteL2Norm_nonneg _)).mp
  simpa only [finiteL2Norm_sq] using hST

theorem one_add_psd_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) : IsUnit (1+B).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.PosDef.one.add_posSemidef hB).isUnit

theorem finiteL2Norm_inverse_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (x : ι → ℝ) :
    finiteL2Norm ((1+B)⁻¹*ᵥx) ≤ finiteL2Norm x := by
  have hh := finiteL2Norm_one_add_le B hB ((1+B)⁻¹*ᵥx)
  rwa [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (one_add_psd_isUnit_det B hB),Matrix.one_mulVec] at hh

theorem finiteL2Norm_inverse_signal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (W : ℝ) (hW : 0 ≤ W) (h : ι → ℝ) :
    finiteL2Norm ((1+B)⁻¹*ᵥh) ≤
      (finiteL2Norm h+finiteL2Norm (B*ᵥh-W • h))/(1+W) := by
  let C := (1+B)⁻¹
  let e := B*ᵥh-W • h
  have hid : C*ᵥ((1+B)*ᵥh)=h := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (one_add_psd_isUnit_det B hB),Matrix.one_mulVec]
  have he : (1+B)*ᵥh=(1+W) • h+e := by
    ext i
    simp only [Matrix.add_mulVec,Matrix.one_mulVec,Pi.add_apply,Pi.smul_apply,smul_eq_mul,e,Pi.sub_apply]
    ring
  rw [he,Matrix.mulVec_add,Matrix.mulVec_smul] at hid
  have he' : (1+W) • (C*ᵥh)=h-C*ᵥe := by
    exact eq_sub_iff_add_eq.mpr hid
  have hb := finiteL2Norm_sub h (C*ᵥe)
  rw [← he',finiteL2Norm_smul,abs_of_pos (show 0<1+W by linarith)] at hb
  have hc := finiteL2Norm_inverse_contraction B hB e
  apply (le_div_iff₀ (show 0<1+W by linarith)).mpr
  change finiteL2Norm (C*ᵥh)*(1+W) ≤ finiteL2Norm h+finiteL2Norm e
  nlinarith

end FiniteResolvent

end SimpleAmenable
end
end

end OAI
