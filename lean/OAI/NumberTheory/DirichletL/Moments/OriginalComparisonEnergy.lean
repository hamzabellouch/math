import OAI.NumberTheory.DirichletL.Moments.NaturalRetainedEnergy
import OAI.NumberTheory.DirichletL.Moments.OriginalReflectionEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentOriginalComparisonEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentNaturalRetainedEnergy CenteredMomentOriginalReflectionEnergy
open CenteredMomentSectorLocalization

theorem actual_original_comparison (a b epsilon Cscale xi saving L : ℝ)
    (ha : 0<a) (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃n ne : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(χ : ι→Character)(P : ι→ℂ)(t omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      (∀i,(χ i).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i) false Wlong (Z^along) 0 (2*Real.pi*t i)*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*(1+T)^(2*ne)*Z^(-2*saving)*
          (∑i,‖polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2) := by
  obtain ⟨n,hn⟩ := actual_natural_retained_energy a b epsilon Cscale xi ha hepsilon hscale hxi B J hB
  obtain ⟨ne,hne⟩ := actual_original_energy_to_retained a b (xi/2) saving L Cscale epsilon
    ha (by positivity) hscale hepsilon
  refine ⟨n,ne,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hr⟩ := hn Wlong hs hW
  obtain ⟨D,hD,ho⟩ := hne Wlong hs hW
  refine ⟨2*C,D,by positivity,hD,?_⟩
  filter_upwards [hr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ χ P t omega Wshort c d M along bshort E T Rcap hχ hd hshort hshortsmooth
    hML hmod hE hT ht hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  obtain ⟨ψ,hψ,horiginal⟩ := ho χ hχ
  let Q (i : ι) := polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i
  have hsource (i : ι) : ((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*Z^along := by
    have hh := (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hML) hscale.le)
    rw [Real.rpow_add hz] at hh
    simpa only [mul_assoc] using hh
  have he := horiginal (fun _=>Z^along) t Q T Z Rcap hT hZ.1.le hRcap
    (fun _=>Real.rpow_pos_of_pos hz _) ht hcap hsource
  have hcut : (xi/2)/2=xi/4 := by ring
  rw [hcut] at he
  have hretained := hZ.2 χ ψ P t omega Wshort c d M along bshort E T Rcap
    hd hshort hshortsmooth (fun i=>(hψ i).2.2) hmod hE hT ht hRcap hcap henergy
  dsimp only [Q] at he
  simp only [←mul_assoc] at he
  have hh := he.trans (add_le_add (mul_le_mul_of_nonneg_left hretained (by norm_num : (0:ℝ)≤2)) le_rfl)
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentOriginalComparisonEnergy

end

end OAI
