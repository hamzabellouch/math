import OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalMeasure

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialRetainedSupport
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT CompletedGauss
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialKernelBridge SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,goodLambda∉Ideal.span {p i})

theorem live_cutoffs (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m:ℝ)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    W₁ (coordinates p x 0*coordinates p x 2*coordinates p x 4/Z^D)≠0 ∧
    W₂ (coordinates p x 0*coordinates p x 2*coordinates p x 5/Z^D)≠0 := by
  rw [physicalTerm_extracted p hp hcop hg hpr Ψ j σ W₁ W₂ Φ Z D m x hx ρ] at hne
  have hk:= (mul_ne_zero_iff.mp hne).2
  unfold physicalKernel at hk
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hk).1).1).2,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hk).1).2⟩

theorem live_whole_columns (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m b:ℝ)(hZ:0<Z)(hs₁:Function.support W₁⊆Set.Iic b)
    (hs₂:Function.support W₂⊆Set.Iic b)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    coordinates p x 0*coordinates p x 2*coordinates p x 4≤b*Z^D ∧
    coordinates p x 0*coordinates p x 2*coordinates p x 5≤b*Z^D := by
  obtain ⟨h₁,h₂⟩:=live_cutoffs p hp hcop hg hpr Ψ j σ W₁ W₂ Φ Z D m x hx ρ hne
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ D)).mp (hs₁ h₁),
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ D)).mp (hs₂ h₂)⟩

include hp in
omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
theorem ideal_coordinates_one (x:Point ι):
    1≤coordinates p x 0 ∧ 1≤coordinates p x 1 ∧ 1≤coordinates p x 2 ∧
    1≤coordinates p x 4 ∧ 1≤coordinates p x 5 := by
  have hi (S:Finset ι):(1:ℝ)≤((sourceIdeal p S).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp S))
  exact ⟨hi _,hi _,hi _,hi _,hi _⟩

theorem live_ideal_caps (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m b:ℝ)(hZ:0<Z)(hs₁:Function.support W₁⊆Set.Iic b)
    (hs₂:Function.support W₂⊆Set.Iic b)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    coordinates p x 0≤b*Z^D ∧ coordinates p x 1≤b*Z^D ∧
    coordinates p x 2≤b*Z^D ∧ coordinates p x 4≤b*Z^D ∧
    coordinates p x 5≤b*Z^D := by
  obtain ⟨h₁,h₂⟩:=live_whole_columns p hp hcop hg hpr Ψ j σ W₁ W₂ Φ
    Z D m b hZ hs₁ hs₂ x hx ρ hne
  obtain ⟨hC,hd,hs,hn₁,hn₂⟩:=ideal_coordinates_one p hp x
  have hpair:1≤coordinates p x 0*coordinates p x 2:=by nlinarith
  have hcp:coordinates p x 0≤coordinates p x 0*coordinates p x 2:=
    le_mul_of_one_le_right (by linarith) hs
  have hsp:coordinates p x 2≤coordinates p x 0*coordinates p x 2:=
    le_mul_of_one_le_left (by linarith) hC
  have hbig:coordinates p x 0*coordinates p x 2≤b*Z^D:=
    (le_mul_of_one_le_right (by positivity) hn₁).trans h₁
  have hdiv:coordinates p x 1≤coordinates p x 0:=by
    change ((sourceIdeal p x.divisor).absNorm:ℝ)≤(sourceIdeal p x.common).absNorm
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _)))
      (map_dvd Ideal.absNorm (sourceIdeal_dvd p _ _ hx.divisor_subset))
  exact ⟨hcp.trans hbig,hdiv.trans (hcp.trans hbig),hsp.trans hbig,
    (le_mul_of_one_le_left (by linarith) hpair).trans h₁,
    (le_mul_of_one_le_left (by linarith) hpair).trans h₂⟩

end SevenEighths.InverseInitialRetainedSupport

end

end OAI
