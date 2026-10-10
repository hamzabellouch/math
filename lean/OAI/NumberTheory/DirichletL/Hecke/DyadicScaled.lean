import OAI.NumberTheory.DirichletL.Hecke.DyadicLossBudget

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem scaled_direct_bound (e κ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R η σ freq V C₂ Cn : ℝ) (n : ℕ),
      (χ j).modulus.absNorm≤U → 0≤r → r≤R → 0≤η → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^4≤U^η → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (a+6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) inverse W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2+6*e)*r+2*κ+η)+C*Cn*U^(2*R+2+η)/(1+V)^n := by
  obtain ⟨Cb,hCb,hbound⟩ := buffered_polynomial_bound e κ he he' hκ
  let E := HeckeReciprocalBound.bound 2
  have hE : 0≤E := tsum_nonneg (fun _ => norm_nonneg _)
  let C := 1+2*Cb*Real.pi+8*Cb+E*Real.pi
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j inverse W A B hA hWs hW
    U r R η σ freq V C₂ Cn n hQ hr hrR hη hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤H := by dsimp [H]; positivity
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤U^r := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j inverse W A B hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only at hb
  have hcentral := positive_central_cost (χ j) U H a e κ η r hQ hH hκ.le hκ' hheight
  have hexternal := direct_external_cost (χ j) U H κ η r R hQ hH hκ.le hκ' hr hrR hheight
  have hpow : (U^r)^(3/2 : ℝ)≤U^(2*R+2+η) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |2-a-6*e|≤2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hc : C₂*(U^r)^(a+6*e-1/2)*(Cb*(presentationComplexity (χ j) H)^κ)*Real.pi≤
      (2*Cb*Real.pi)*C₂*U^((a-1/2+6*e)*r+2*κ+η) := by
    calc
      _ = (C₂*Cb*Real.pi)*((U^r)^(a+6*e-1/2)*(presentationComplexity (χ j) H)^κ) := by ring
      _ ≤ (C₂*Cb*Real.pi)*(2*U^((a-1/2+6*e)*r+2*κ+η)) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
      _ = _ := by ring
  have hj : 2*(Cn*(U^r)^(3/2 : ℝ)*(Cb*(presentationComplexity (χ j) H)^κ)/(1+V)^n)*|2-a-6*e|≤
      (8*Cb)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ = 2*Cn*Cb*((U^r)^(3/2 : ℝ)*(presentationComplexity (χ j) H)^κ)/(1+V)^n*|2-a-6*e| := by ring
      _ ≤ 2*Cn*Cb*(2*U^(2*R+2+η))/(1+V)^n*2 := by gcongr
      _ = _ := by ring
  have ht : (Cn*(U^r)^(3/2 : ℝ)*E)/(1+V)^n*Real.pi≤
      (E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ ≤ (Cn*U^(2*R+2+η)*E)/(1+V)^n*Real.pi := by gcongr
      _ = _ := by ring
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hcomp : 0≤(presentationComplexity (χ j) H)^κ := Real.rpow_nonneg (by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity) _
  apply (hb.trans (mul_le_of_le_one_left (by positivity) hfac)).trans
  change _ ≤ _ at hc hj ht
  have hcC : 2*Cb*Real.pi≤C := by dsimp [C]; nlinarith [mul_nonneg hE Real.pi_pos.le]
  have heC : 8*Cb+E*Real.pi≤C := by dsimp [C]; nlinarith [Real.pi_pos]
  calc
    _ ≤ (2*Cb*Real.pi)*C₂*U^((a-1/2+6*e)*r+2*κ+η)+
        (8*Cb)*Cn*U^(2*R+2+η)/(1+V)^n+(E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
      exact add_le_add (add_le_add hc hj) ht
    _ = (2*Cb*Real.pi)*C₂*U^((a-1/2+6*e)*r+2*κ+η)+
        (8*Cb+E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by ring
    _ ≤ _ := by gcongr

end SevenEighths.HeckeDyadic

end

end OAI
