import OAI.NumberTheory.DirichletL.Hecke.DyadicScaledReflection

namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem source_dyadic_bounds (R dmax τ ε e κ η : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0≤profileBound k) :
    ∃ n : ℕ, ∃ C : ℝ, 0<C ∧
    ∀ (Z d : ℝ), 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ r σ freq : ℝ, (χ j).modulus.absNorm≤Z^d → 0≤r → r≤R →
      |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
      (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^2*‖mellin W ((x : ℂ)+t*I)‖≤profileBound 2) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤profileBound (n+2)) →
      ‖polynomial (χ j) inverse W ((Z^d)^r) σ freq‖^2≤C*(Z^d)^((2*a-1)*r+ε) ∧
      ‖polynomial (χ j) false W ((Z^d)^r) σ freq‖^2≤C*(Z^d)^((2*a-1)*min r (1-r)+ε) := by
  obtain ⟨Cd,hCd,hdirect⟩ := scaled_direct_bound e κ he he' hκ hκ'
  obtain ⟨Cr,hCr,hreflect⟩ := scaled_reflected_bound e κ he he' hκ hκ'
  obtain ⟨n,htail⟩ := uniform_external_tail_order τ dmax (2*R+2+η) (R+1)
    hτ hdmax (by positivity) (by positivity)
  let K := Cd+Cr
  have hK : 0<K := add_pos hCd hCr
  let M := K*profileBound 2
  let E := K*profileBound (n+2)*(2 : ℝ)^n
  let C := (M+E)^2+1
  have hM : 0≤M := mul_nonneg hK.le (hprofile 2)
  have hE : 0≤E := mul_nonneg (mul_nonneg hK.le (hprofile (n+2))) (by positivity)
  refine ⟨n,C,by dsimp [C]; positivity,?_⟩
  intro Z d hZ hd hd' hT ι _ χ hχ a i ha ha' hmax j inverse W A B hA hWs hW
    r σ freq hQ hr hrR hfreq hheight hm₂ hmn
  let U := Z^d
  have hU : 1≤U := Real.one_le_rpow hZ hd
  have hV : 0≤Z^τ/2 := by positivity
  have hleft : a+6*e-σ ∈ Icc (1-a-6*e-σ) (2-σ) := ⟨by linarith,by linarith⟩
  have hleft' : 1-a-6*e-σ ∈ Icc (1-a-6*e-σ) (2-σ) := ⟨le_rfl,by linarith⟩
  have hsub : Icc (a+6*e-σ) (2-σ)⊆Icc (1-a-6*e-σ) (2-σ) := by
    intro x hx
    exact ⟨hleft.1.trans hx.1,hx.2⟩
  have hD (inv : Bool) := hdirect χ hχ (Z^τ) a i hT ha ha' hmax j inv W A B hA hWs hW
    U r R η σ freq (Z^τ/2) (profileBound 2) (profileBound (n+2)) n hQ hr hrR hη hV
    hfreq hheight (hprofile 2) (hprofile (n+2))
    (hm₂ _ hleft) (fun x hx => hmn x (hsub hx))
  have hP := hreflect χ hχ (Z^τ) a i hT ha ha' hmax j W A B hA hWs hW
    U r R η σ freq (Z^τ/2) (profileBound 2) (profileBound (n+2)) n hQ hr hrR hη hV
    hfreq hheight (hprofile 2) (hprofile (n+2)) (hm₂ _ hleft') hmn
  have hCdK : Cd≤K := le_add_of_nonneg_right hCr.le
  have hCrK : Cr≤K := le_add_of_nonneg_left hCd.le
  have hnormD (inv : Bool) :
      ‖polynomial (χ j) inv W (U^r) σ freq‖≤
        M*U^((a-1/2)*r+(6*e*r+2*κ+η))+
          K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n := by
    apply (hD inv).trans
    dsimp only [M]
    have hexp : (a-1/2+6*e)*r+2*κ+η=(a-1/2)*r+(6*e*r+2*κ+η) := by ring
    rw [hexp]
    gcongr <;> exact hprofile _
  have hnormP : ‖polynomial (χ j) false W (U^r) σ freq‖≤
      M*U^((a-1/2)*(1-r)+(6*e*(2-r)+4*κ+η))+
        K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n := by
    apply hP.trans
    dsimp only [M]
    have hexp : (a-1/2)*(1-r)+6*e*(2-r)+4*κ+η=
        (a-1/2)*(1-r)+(6*e*(2-r)+4*κ+η) := by ring
    rw [hexp]
    gcongr <;> exact hprofile _
  have hfinish (z : ℂ) (p b : ℝ) (hp : -(R+1)≤p) (hb : 2*b≤ε)
      (hz : ‖z‖≤M*U^(p+b)+K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n) :
      ‖z‖^2≤C*U^(2*p+ε) := by
    have ht := htail Z d p hZ hd hd' hp
    have herror : K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n≤E*U^p := by
      calc
        _ = (K*profileBound (n+2))*(U^(2*R+2+η)/(1+Z^τ/2)^n) := by ring
        _ ≤ (K*profileBound (n+2))*((2 : ℝ)^n*U^p) :=
          mul_le_mul_of_nonneg_left ht (mul_nonneg hK.le (hprofile _))
        _ = _ := by dsimp [E]; ring
    have hn := hz.trans (add_le_add (le_refl _) herror)
    have hs := squared_bound_of_central_and_error z U M E p b ε hU hM hE hε.le hb hn
    apply hs.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    dsimp [C]
    linarith
  have hpos : 0≤(a-1/2)*r := mul_nonneg (by linarith) hr
  have href : -(R+1)≤(a-1/2)*(1-r) := by
    have hp : (a-1/2)*r≤(1/2)*R := mul_le_mul (by linarith) hrR hr (by norm_num)
    nlinarith
  have hbud := central_squared_exponents R a e κ η ε r r hR he.le hκ.le hη hrR hr hbudget
  have hbD : 2*(6*e*r+2*κ+η)≤ε := by nlinarith [hbud.1]
  have hbP : 2*(6*e*(2-r)+4*κ+η)≤ε := by nlinarith [hbud.2]
  have hfinalD (inv : Bool) :
      ‖polynomial (χ j) inv W (U^r) σ freq‖^2≤C*U^((2*a-1)*r+ε) := by
    convert hfinish _ ((a-1/2)*r) (6*e*r+2*κ+η) (by linarith) hbD (hnormD inv) using 1 ;
      congr 2 ; ring
  have hfinalP : ‖polynomial (χ j) false W (U^r) σ freq‖^2≤C*U^((2*a-1)*(1-r)+ε) := by
    convert hfinish _ ((a-1/2)*(1-r)) (6*e*(2-r)+4*κ+η) href hbP hnormP using 1 ;
      congr 2 ; ring
  exact ⟨hfinalD inverse,min_plain_bound _ C U (2*a-1) r ε (hfinalD false) hfinalP⟩

end SevenEighths.HeckeDyadic

end

end OAI
