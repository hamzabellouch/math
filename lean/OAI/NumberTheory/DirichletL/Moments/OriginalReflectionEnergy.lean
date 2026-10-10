import OAI.NumberTheory.DirichletL.Moments.OriginalReflectionApproximation

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentOriginalReflectionEnergy
open HeckeFamily CenteredMomentOriginalReflectionApproximation CenteredMomentNaturalPrimitive

lemma norm_sq_comparison (a b : ℂ) : ‖a‖^2≤2*‖b‖^2+2*‖a-b‖^2 := by
  have he : a=b+(a-b) := by ring
  have hh : ‖a‖≤‖b‖+‖a-b‖ := by nth_rw 1 [he];exact norm_add_le _ _
  nlinarith [norm_nonneg a,norm_nonneg b,norm_nonneg (a-b),sq_nonneg (‖b‖-‖a-b‖)]

theorem actual_original_energy_to_retained (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀χ : ι→Character,
        (∀i,(χ i).residue≠1) →
        ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
        ∀(X t : ι→ℝ)(P : ι→ℂ)(T Z Rcap : ℝ),0≤T → 1≤Z → 1≤Rcap →
          (∀i,0<X i) → (∀i,‖t i‖≤T) → (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
          (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*X i) →
          (∑i,‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i‖^2)≤
            2*(∑i,‖retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i)*P i‖^2)+
            C*Rcap^(2*ε)*(1+T)^(2*n)*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨n,hn⟩ := actual_original_retained_approximation a b xi saving L Cscale ε ha hxi hscale hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨2*C^2,by positivity,?_⟩
  intro ι _ χ hχ
  choose ψ G hp hnψ hG hcap happrox using fun i=>hb (χ i) (hχ i)
  refine ⟨ψ,fun i=>⟨hp i,hnψ i,hcap i⟩,?_⟩
  intro X t P T Z Rcap hT hZ hR hX ht hmod hsource
  let B := C*Rcap^ε*(1+T)^n*Z^(-saving)
  have hB : 0≤B := by dsimp [B];positivity
  have herr (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)-
        G i*retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i)‖≤B := by
    apply (happrox i (X i) (t i) Z (hX i) hZ (hsource i)).trans
    dsimp [B]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hmod i) hε.le) hC.le)
      (pow_le_pow_left₀ (by positivity) (by simpa only [Real.norm_eq_abs,add_comm] using add_le_add_left (ht i) 1) n) (by positivity) (by positivity)
  have hpoint (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i‖^2≤
      2*‖retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i)*P i‖^2+B^2*(2*‖P i‖^2) := by
    have hh := norm_sq_comparison
      (HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i)
      ((G i*retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i))*P i)
    have he : ‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i-
        (G i*retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i))*P i‖≤B*‖P i‖ := by
      rw [←sub_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right (herr i) (norm_nonneg _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
    simp only [norm_mul,hG,one_mul] at hh
    simp only [mul_pow] at hs
    simp only [norm_mul]
    nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset ι))=>hpoint i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hBeq : B^2*2=(2*C^2)*Rcap^(2*ε)*(1+T)^(2*n)*Z^(-2*saving) := by
    have hr0 : 0≤Rcap := by linarith
    have hz0 : 0≤Z := by linarith
    have hr : (Rcap^ε)^2=Rcap^(2*ε) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hr0];congr 1;ring
    have hz : (Z^(-saving))^2=Z^(-2*saving) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hz0];congr 1;ring
    dsimp [B]
    rw [mul_pow,mul_pow,mul_pow,hr,hz,←pow_mul]
    rw [Nat.mul_comm n 2]
    ring
  convert hh using 1
  rw [←mul_assoc,hBeq]

end SevenEighths.CenteredMomentOriginalReflectionEnergy

end

end OAI
