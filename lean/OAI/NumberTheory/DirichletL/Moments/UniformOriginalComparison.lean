import OAI.NumberTheory.DirichletL.Moments.UniformNaturalRetained
import OAI.NumberTheory.DirichletL.Moments.UniformOriginalEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentUniformOriginalComparison
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentUniformNaturalRetained CenteredMomentUniformOriginalEnergy
open CenteredMomentSectorLocalization

theorem actual_original_comparison (epsilon Cscale xi saving L : ℝ)
     (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort E S Rcap : ℝ),
      (∀i,(χ i).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0<S → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤S) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i) false (G i) (Z^along) 0 0*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*S^2*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*S^2*Z^(-2*saving)*
          (∑i,‖polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2) := by
  obtain ⟨H,C,hC,hr⟩ := actual_natural_retained_energy epsilon Cscale xi hepsilon hscale hxi B J hB
  obtain ⟨H',D,hD,ho⟩ := actual_original_energy_to_retained (xi/2) saving L Cscale epsilon
    (by positivity) hscale hepsilon
  refine ⟨H∪H',2*C,D,by positivity,hD,?_⟩
  filter_upwards [hr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ G χ P omega Wshort c d M along bshort E S Rcap hχ hd hshort hshortsmooth
    hML hmod hE hS hGS hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  have hG1 (i:ι):H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤S :=
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left : H⊆H∪H')) (G i)).trans (hGS i)
  have hG2 (i:ι):H'.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤S :=
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right : H'⊆H∪H')) (G i)).trans (hGS i)
  obtain ⟨ψ,hψ,horiginal⟩ := ho χ hχ
  let Q (i : ι) := polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i
  have hsource (i : ι) : ((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*Z^along := by
    have hh := (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hML) hscale.le)
    rw [Real.rpow_add hz] at hh
    simpa only [mul_assoc] using hh
  have he := horiginal G (fun _=>Z^along) Q S Z Rcap hS hZ.1.le hRcap
    (fun _=>Real.rpow_pos_of_pos hz _) hG2 hcap hsource
  have hcut : (xi/2)/2=xi/4 := by ring
  rw [hcut] at he
  have hretained := hZ.2 G χ ψ P omega Wshort c d M along bshort S E Rcap
    hd hshort hshortsmooth (fun i=>(hψ i).2.2) hmod hS hE hG1 hRcap hcap henergy
  dsimp only [Q] at he
  simp only [←mul_assoc] at he
  have hh := he.trans (add_le_add (mul_le_mul_of_nonneg_left hretained (by norm_num : (0:ℝ)≤2)) le_rfl)
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentUniformOriginalComparison

end

end OAI
