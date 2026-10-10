import OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicScale

namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeDeletionBounds

theorem scaled_direct_bound (e κ η : ℝ) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R σ freq V C₂ Cn : ℝ) (n : ℕ),
      2≤U → (χ j).modulus.absNorm≤U → 0≤r → r≤R → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^2≤U^η → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+8*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (a+8*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2+8*e)*r+κ)+C*Cn*U^(2*R+κ)/(1+V)^n := by
  obtain ⟨B,hB,hbound⟩ := polynomial_bound_in_bin e he he'
  let Cb := (B*(2+η)+localBound (1/2))/κ
  have hCb : 0<Cb := div_pos
    (add_pos_of_nonneg_of_pos (mul_nonneg hB (by linarith))
      (localBound_pos (by norm_num : (0 : ℝ)<1/2))) hκ
  let E := eulerBound 2
  have hE : 0≤E := tsum_nonneg (fun I => mul_nonneg (IdealMangoldt.value_nonneg _) (Real.rpow_nonneg (norm_pos I).le _))
  let C := 1+Cb*Real.pi+4*Cb+E*Real.pi
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B' hA hWs hW
    U r R σ freq V C₂ Cn n hU2 hQ hr hrR hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤H := by dsimp [H]; positivity
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤U^r := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j W A B' hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hC₂ hCn hfreq hm₂ hmn
  have hcost : binCost B (χ j) H ≤ Cb*U^κ :=
    binCost_le_power (χ j) B U H η κ hB hU2 hQ hη hκ (by rw [abs_of_nonneg hH]; exact hheight)
  have hcentral : (U^r)^(a+8*e-1/2)*binCost B (χ j) H ≤
      Cb*U^((a-1/2+8*e)*r+κ) := by
    calc
      _ ≤ (U^r)^(a+8*e-1/2)*(Cb*U^κ) :=
        mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (Real.rpow_nonneg hUp.le _) _)
      _ = _ := by rw [←Real.rpow_mul hUp.le, mul_left_comm, ←Real.rpow_add hUp]; congr 2; ring
  have hexternal : (U^r)^(3/2 : ℝ)*binCost B (χ j) H ≤ Cb*U^(2*R+κ) := by
    calc
      _ ≤ (U^r)^(3/2 : ℝ)*(Cb*U^κ) :=
        mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (Real.rpow_nonneg hUp.le _) _)
      _ = Cb*U^(r*(3/2)+κ) := by rw [←Real.rpow_mul hUp.le, mul_left_comm, ←Real.rpow_add hUp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)) hCb.le
  have hpow : (U^r)^(3/2 : ℝ)≤U^(2*R+κ) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |2-a-8*e|≤2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hc : C₂*(U^r)^(a+8*e-1/2)*binCost B (χ j) H*Real.pi≤
      (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ) := by
    calc
      _ = (C₂*Real.pi)*((U^r)^(a+8*e-1/2)*binCost B (χ j) H) := by ring
      _ ≤ (C₂*Real.pi)*(Cb*U^((a-1/2+8*e)*r+κ)) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
      _ = _ := by ring
  have hj : 2*(Cn*(U^r)^(3/2 : ℝ)*binCost B (χ j) H/(1+V)^n)*|2-a-8*e|≤
      (4*Cb)*Cn*U^(2*R+κ)/(1+V)^n := by
    calc
      _ = 2*Cn*((U^r)^(3/2 : ℝ)*binCost B (χ j) H)/(1+V)^n*|2-a-8*e| := by ring
      _ ≤ 2*Cn*(Cb*U^(2*R+κ))/(1+V)^n*2 := by gcongr
      _ = _ := by ring
  have ht : (Cn*(U^r)^(3/2 : ℝ)*E)/(1+V)^n*Real.pi≤
      (E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by
    calc
      _ ≤ (Cn*U^(2*R+κ)*E)/(1+V)^n*Real.pi := by gcongr
      _ = _ := by ring
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hcomp : 0≤binCost B (χ j) H := binCost_nonneg hB _ _
  apply (hb.trans (mul_le_of_le_one_left (by positivity) hfac)).trans
  change _ ≤ _ at hc hj ht
  have hcC : Cb*Real.pi≤C := by dsimp [C]; nlinarith only [hCb, mul_nonneg hE Real.pi_pos.le]
  have heC : 4*Cb+E*Real.pi≤C := by dsimp [C]; nlinarith only [mul_nonneg hCb.le Real.pi_pos.le]
  calc
    _ ≤ (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ)+
        (4*Cb)*Cn*U^(2*R+κ)/(1+V)^n+(E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by
      exact add_le_add (add_le_add hc hj) ht
    _ = (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ)+
        (4*Cb+E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by ring
    _ ≤ _ := by gcongr

end SevenEighths.HeckePrimeDyadic

end

end OAI
