import OAI.NumberTheory.DirichletL.Hecke.DetectorNormalized
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicActual

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorSaturation
open HeckeDetectorFrequency

lemma logarithmic_cost_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ U : ℝ in atTop, (C*(Real.logb 2 U)^2)^2≤U^ε := by
  have ht := (logb_square_div_rpow_tendsto (ε/2) (by linarith)).pow 2
  have ht' := ht.const_mul (C^2)
  have hbound : ∀ᶠ U : ℝ in atTop,
      C^2*((Real.logb 2 U)^2/U^(ε/2))^2≤1 := by
    have hh : Tendsto (fun U : ℝ => C^2*((Real.logb 2 U)^2/U^(ε/2))^2)
        atTop (𝓝 0) := by simpa using ht'
    exact (tendsto_order.mp hh).2 1 (by norm_num) |>.mono (fun _ h => h.le)
  filter_upwards [hbound,eventually_gt_atTop (0 : ℝ)] with U hb hU
  have he : (U^(ε/2))^2=U^ε := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hU.le]
    congr 1
    norm_num
  rw [div_pow, he] at hb
  have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hU ε)).mp
    (show C^2*((Real.logb 2 U)^2)^2/U^ε≤1 by simpa only [mul_div_assoc] using hb)
  simpa only [one_mul,mul_one,mul_pow] using hh

lemma normalized_product_lower (U r m σ a ε K A B : ℝ)
    (hU : 1<U) (hr : 0≤r) (hm : 0≤m) (hσ : a≤σ)
    (_hK : 0≤K) (_hA : 0≤A) (_hB : 0≤B)
    (hcost : K^2≤U^ε)
    (hprod : 1≤K*(U^r)^(1/2-σ)*(U^m)^(1/2-σ)*(A*B)) :
    U^((2*a-1)*(r+m)-ε)≤A^2*B^2 := by
  have hUp : 0<U := by linarith
  have hcentral : (U^r)^(1/2-σ)*(U^m)^(1/2-σ)=U^((1/2-σ)*(r+m)) := by
    rw [← Real.rpow_mul hUp.le,← Real.rpow_mul hUp.le,← Real.rpow_add hUp]
    congr 1
    ring
  have hp : 1≤K*U^((1/2-σ)*(r+m))*(A*B) := by
    calc
      1 ≤ K*(U^r)^(1/2-σ)*(U^m)^(1/2-σ)*(A*B) := hprod
      _ = _ := by rw [←hcentral]; ring
  have hsq : 1≤(K*U^((1/2-σ)*(r+m))*(A*B))^2 := by nlinarith
  have he : (U^((1/2-σ)*(r+m)))^2=U^((1-2*σ)*(r+m)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
    congr 1
    ring
  rw [mul_pow,mul_pow,he,mul_pow] at hsq
  let q := (2*a-1)*(r+m)-ε
  let L := K^2*U^((1-2*σ)*(r+m))
  have hLq : L*U^q≤1 := by
    calc
      _ ≤ U^ε*U^((1-2*σ)*(r+m))*U^q := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
        exact mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hUp.le _)
      _ = U^(ε+(1-2*σ)*(r+m)+q) := by rw [←Real.rpow_add hUp,←Real.rpow_add hUp]
      _ ≤ U^0 := Real.rpow_le_rpow_of_exponent_le hU.le (by
        dsimp [q]
        nlinarith [mul_nonneg (sub_nonneg.mpr hσ) (add_nonneg hr hm)])
      _ = 1 := Real.rpow_zero _
  calc
    U^q = U^q*1 := by ring
    _ ≤ U^q*(L*(A^2*B^2)) := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hUp.le _)
    _ = (L*U^q)*(A^2*B^2) := by ring
    _ ≤ 1*(A^2*B^2) := mul_le_mul_of_nonneg_right hLq (by positivity)
    _ = _ := by ring

open HeckeFamily HeckeDyadic HeckeDetectorDyadicActual HeckeDetectorDyadicProfiles HeckeDetectorProfiles

theorem actual_saturation (R dmax τ ε e κ η Clower : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε/2) (hClower : 0≤Clower) :
    ∃ U₀ : ℝ, ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
      U₀≤Z^d → 1<Z^d →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
        (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
        51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, ∀ Dstar r m σ freq : ℝ,
        (χ j).modulus.absNorm≤Z^d → 0<Dstar →
        0≤r → r≤R → 0≤m → m≤R → (Z^d)^r≤4*Dstar →
        a≤σ → σ≤1 → |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
        (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
        let M := polynomial (χ j) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
          ((Z^d)^r) σ freq
        let S := polynomial (χ j) false positiveAnnular ((Z^d)^m) σ freq
        1≤Clower*(Real.logb 2 (Z^d))^2*((Z^d)^r)^(1/2-σ)*((Z^d)^m)^(1/2-σ)*(‖M‖*‖S‖) →
        m≤1/2+75*ε ∧ (Z^d)^((2*a-1)*r-2*ε)≤‖M‖^2 ∧
          (Z^d)^((2*a-1)*m-2*ε)≤‖S‖^2 := by
  obtain ⟨Cu,hCu,hupper⟩ := simultaneous_upper R dmax τ (ε/2) e κ η
    hR hdmax hτ (by linarith) he he' hκ hκ' hη hbudget
  have hev := (logarithmic_cost_eventually Clower ε hε).and
    (constant_absorbed_eventually Cu (ε/2) (by linarith))
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨U₀,?_⟩
  intro Z d hZ hd hd' hT hlarge hU ι _ χ hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσ hσ' hfreq hheight M S hprod
  have hσlo : 51/100≤σ := ha.trans hσ
  obtain ⟨hcost,hconst⟩ := hU₀ (Z^d) hlarge
  obtain ⟨hMu,hSu⟩ := hupper Z d hZ hd hd' hT χ hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσlo hσ' hfreq hheight
  have hp := normalized_product_lower (Z^d) r m σ a ε
    (Clower*(Real.logb 2 (Z^d))^2) ‖M‖ ‖S‖ hU hr hm hσ
    (mul_nonneg hClower (sq_nonneg _)) (norm_nonneg _) (norm_nonneg _) hcost hprod
  have hbound (x : ℝ) : Cu*(Z^d)^(x+ε/2)≤(Z^d)^(x+ε) := by
    calc
      _ ≤ (Z^d)^(ε/2)*(Z^d)^(x+ε/2) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (by linarith) _)
      _ = _ := by rw [←Real.rpow_add (by linarith : 0<Z^d)]; congr 1; ring
  exact Detector.simultaneous_saturation hU (by linarith) hε.le (sq_nonneg _) (sq_nonneg _)
    hp (hMu.trans (hbound _)) (hSu.trans (hbound _))

end SevenEighths.HeckeDetectorSaturation

end

end OAI
