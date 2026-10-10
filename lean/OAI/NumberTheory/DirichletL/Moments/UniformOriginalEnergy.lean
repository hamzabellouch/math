import OAI.NumberTheory.DirichletL.Moments.UniformReflectionApproximation
import OAI.NumberTheory.DirichletL.Moments.OriginalReflectionEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformOriginalEnergy
open HeckeFamily CenteredMomentUniformReflectionApproximation CenteredMomentNaturalPrimitive
open CenteredMomentOriginalReflectionEnergy

theorem actual_original_energy_to_retained (xi saving L Cscale ε : ℝ)
     (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀χ : ι→Character,
        (∀i,(χ i).residue≠1) →
        ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
        ∀(W : ι→𝓢(ℝ,ℂ))(X : ι→ℝ)(P : ι→ℂ)(D Z Rcap : ℝ),0<D → 1≤Z → 1≤Rcap →
          (∀i,0<X i) → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W i)≤D) → (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
          (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*X i) →
          (∑i,‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i‖^2)≤
            2*(∑i,‖retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2))*P i‖^2)+
            C*Rcap^(2*ε)*D^2*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨H,C,hC,hb⟩ := actual_original_approximation xi saving L Cscale ε hxi hscale hε
  refine ⟨H,2*C^2,by positivity,?_⟩
  intro ι _ χ hχ
  choose ψ G hp hnψ hG hcap happrox using fun i=>hb (χ i) (hχ i)
  refine ⟨ψ,fun i=>⟨hp i,hnψ i,hcap i⟩,?_⟩
  intro W X P D Z Rcap hD hZ hR hX hWD hmod hsource
  let B := C*D*Rcap^ε*Z^(-saving)
  have hB : 0≤B := by dsimp [B];positivity
  have herr (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0-
        G i*retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2))‖≤B := by
    apply (happrox i (W i) (X i) Z (hX i) hZ (hsource i)).trans
    dsimp [B]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hWD i) hC.le)
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hmod i) hε.le)
      (by positivity) (by positivity)
  have hpoint (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i‖^2≤
      2*‖retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2))*P i‖^2+B^2*(2*‖P i‖^2) := by
    have hh := norm_sq_comparison
      (HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i)
      ((G i*retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2)))*P i)
    have he : ‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i-
        (G i*retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2)))*P i‖≤B*‖P i‖ := by
      rw [←sub_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right (herr i) (norm_nonneg _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
    simp only [norm_mul,hG,one_mul] at hh
    simp only [mul_pow] at hs
    simp only [norm_mul]
    nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset ι))=>hpoint i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hBeq : B^2*2=(2*C^2)*Rcap^(2*ε)*D^2*Z^(-2*saving) := by
    have hr0 : 0≤Rcap := by linarith
    have hz0 : 0≤Z := by linarith
    have hr : (Rcap^ε)^2=Rcap^(2*ε) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hr0];congr 1;ring
    have hz : (Z^(-saving))^2=Z^(-2*saving) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hz0];congr 1;ring
    dsimp [B]
    rw [mul_pow,mul_pow,mul_pow,hr,hz]
    ring
  convert hh using 1
  rw [←mul_assoc,hBeq]

end SevenEighths.CenteredMomentUniformOriginalEnergy

end

end OAI
