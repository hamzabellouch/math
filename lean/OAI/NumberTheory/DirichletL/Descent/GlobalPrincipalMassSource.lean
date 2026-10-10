import OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassWeighted

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma active_norm_of_square {ι : Type*} [DecidableEq ι] (p : ι→O)
    (A : Finset ι) (Z R eta : ℝ) (hZ : 0<Z)
    (hA : primeProductNorm p A≤Z^(R+eta)) :
    ‖eisEmbedding (∏i∈A,p i)‖≤Z^((R+eta)/2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg hZ.le _)).mp
  have hh : (Z^((R+eta)/2))^2=Z^(R+eta) := by
    rw [←Real.rpow_mul_natCast hZ.le]
    congr 1
    norm_num
  rw [hh]
  exact hA

theorem original_weighted_source (Jmax : ℕ) (delta : ℝ) (hdelta : 0<delta) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(Z ell R Bfirst t eta a loss : ℝ),
    1≤Z → 0≤ell+eta → 0≤a →
    7*eta/2+delta*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)≤loss →
    (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(R+eta)) →
    (∀x∈S,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta)) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤Z^(t+eta)) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^a)≤
      C*Z^(ell+R/2+Bfirst+t+loss) := by
  obtain ⟨C,hC,hraw⟩ := original_weighted_mass Jmax delta hdelta
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z ell R Bfirst t eta a loss hZ hell ha hloss hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hh := hraw p hp hinj Jo hJo S (Z^(ell+eta)) (Z^((R+eta)/2))
    (Z^(Bfirst+eta)) (Z^(t+eta)) a (Real.one_le_rpow hZ hell)
    (Real.rpow_nonneg hZp.le _) (Real.rpow_pos_of_pos hZp _)
    (Real.rpow_pos_of_pos hZp _) ha hS hb₁ hb₂
    (fun x hx=>active_norm_of_square p _ Z R eta hZp (hactive x hx))
    hcommon hquot extra negative hextra
  apply hh.trans
  calc
    _ = C*( (Z^(ell+eta))^(1+delta)*Z^((R+eta)/2)*Z^(Bfirst+eta)*Z^(t+eta)*
      ((Z^(ell+eta))^2*Z^(Bfirst+eta)*Z^(t+eta))^(delta+a)) := by ring
    _ = C*Z^(ell+R/2+Bfirst+t+7*eta/2+delta*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)) := by
      rw [weighted_mass_power Z ell R Bfirst t eta delta a hZp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hC.le

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI
