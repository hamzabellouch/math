import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicCutoff

namespace OAI

noncomputable section

open scoped Classical ContDiff
open Set
namespace SevenEighths.HeckeDetectorDyadicActual
open HeckeFamily HeckeDyadic HeckeDetectorDyadicProfiles HeckeDetectorProfiles

lemma inverse_profile_smooth (Dstar D : ℝ) :
    ContDiff ℝ ∞ (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D) := by
  unfold HeckeDetectorDyadicBridge.inverseProfile
  have hv : ContDiff ℝ ∞ (fun x : ℝ => cutoff (D*x/Dstar)) := (cutoff.smooth ⊤).comp (by fun_prop)
  exact hv.mul positiveAnnular_smooth

lemma inverse_profile_support (Dstar D : ℝ) :
    Function.support (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D)⊆Icc (1/4) (9/4) := by
  intro x hx
  exact positiveAnnular_support ((mul_ne_zero_iff.mp hx).2)

theorem simultaneous_upper (R dmax τ ε e κ η : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
        (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
        51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, ∀ Dstar r m σ freq : ℝ,
        (χ j).modulus.absNorm≤Z^d → 0<Dstar →
        0≤r → r≤R → 0≤m → m≤R → (Z^d)^r≤4*Dstar →
        51/100≤σ → σ≤1 → |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
        (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
        ‖polynomial (χ j) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
          ((Z^d)^r) σ freq‖^2≤C*(Z^d)^((2*a-1)*r+ε) ∧
        ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) σ freq‖^2≤
          C*(Z^d)^((2*a-1)*min m (1-m)+ε) := by
  obtain ⟨Cp,hCp,hplain,hinverse⟩ := actual_profile_bounds
  obtain ⟨n,C,hC,hbound⟩ := source_dyadic_bounds R dmax τ ε e κ η
    hR hdmax hτ hε he he' hκ hκ' hη hbudget Cp (fun k => (hCp k).le)
  refine ⟨C,hC,?_⟩
  intro Z d hZ hd hdmax' hT ι _ χ hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσ hσ' hfreq hheight
  have hU : 1≤Z^d := Real.one_le_rpow hZ hd
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (by linarith) _
  have hstrip : Icc (1-a-6*e-σ) (2-σ)⊆Icc (-2 : ℝ) 2 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hInv := hbound Z d hZ hd hdmax' hT χ hχ a i ha ha' hmax j true
    (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
    (1/4) (9/4) (by norm_num) (inverse_profile_support Dstar ((Z^d)^r))
    (inverse_profile_smooth Dstar ((Z^d)^r)) r σ freq hQ hr hrR hfreq hheight
    (fun x hx t => hinverse 2 Dstar ((Z^d)^r) hDs hD.le hratio x (hstrip hx) t)
    (fun x hx t => hinverse (n+2) Dstar ((Z^d)^r) hDs hD.le hratio x (hstrip hx) t)
  have hPlain := hbound Z d hZ hd hdmax' hT χ hχ a i ha ha' hmax j false
    positiveAnnular (1/4) (9/4) (by norm_num) positiveAnnular_support positiveAnnular_smooth
    m σ freq hQ hm hmR hfreq hheight
    (fun x hx t => hplain 2 x (hstrip hx) t)
    (fun x hx t => hplain (n+2) x (hstrip hx) t)
  exact ⟨hInv.1,hPlain.2⟩

end SevenEighths.HeckeDetectorDyadicActual

end

end OAI
