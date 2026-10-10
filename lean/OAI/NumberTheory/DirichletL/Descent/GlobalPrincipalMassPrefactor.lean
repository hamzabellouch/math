import OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassSource
import OAI.NumberTheory.DirichletL.Descent.PhysicalExponents

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def physicalPrincipalFactor (Z M r ell V delta A B R j t eta tau eps window : ℝ) : ℝ :=
  (Z^(firstKappa M r ell V delta A B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
    Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)*
    (Z^(r-A-B-t)*Real.exp window)^(1+eps)

lemma principal_nominal_identity (M r ell V delta A B R j t : ℝ) :
    firstKappa M r ell V delta A B R+firstPhysicalHeight M r ell V delta B j+
      (r-A-B-t)+(ell+R/2+B+t)=r+3*ell+V-B-j := by
  unfold firstKappa firstPhysicalHeight
  ring

lemma physical_principal_exact (Z M r ell V delta A B R j t eta tau eps window loss : ℝ)
    (hZ : 0<Z) :
    physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      Z^(ell+R/2+B+t+loss)=
    Real.exp (window*(1+eps))*
      Z^(r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss) := by
  have he : Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^((9/2:ℝ)*eta) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  have hw : (Real.exp window)^(1+eps)=Real.exp (window*(1+eps)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  unfold physicalPrincipalFactor
  rw [he,Real.mul_rpow (Real.rpow_nonneg hZ.le _) (Real.exp_pos _).le,
    ←Real.rpow_mul hZ.le,hw]
  have hx : r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss=
    firstKappa M r ell V delta A B R+(9/2:ℝ)*eta+
    (firstPhysicalHeight M r ell V delta B j+12*eta+tau)+
    (r-A-B-t)*(1+eps)+(ell+R/2+B+t+loss) := by
    unfold firstKappa firstPhysicalHeight
    ring
  rw [hx]
  simp only [Real.rpow_add hZ]
  ring

theorem original_physical_weighted_source (Jmax : ℕ) (dsmall : ℝ) (hdsmall : 0<dsmall) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))
    (Z M r ell V delta A B R j t eta tau eps window pi : ℝ),
    1≤Z → 0≤ell+eta → 0≤eps → 0≤B → 0≤j →
    eps*(r-A-B-t)+7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*eps*(2*ell+B+t+4*eta)≤pi+eta/2 →
    (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(R+eta)) →
    (∀x∈S,primeProductNorm p x.firstCommon≤Z^(B+eta)) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤Z^(t+eta)) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^(2*eps))≤
      C*Real.exp (window*(1+eps))*Z^(r+3*ell+V+17*eta+tau+pi) := by
  obtain ⟨C,hC,hsource⟩ := original_weighted_source Jmax dsmall hdsmall
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z M r ell V delta A B R j t eta tau eps window pi hZ hell heps hB hj hcost hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  let loss := 7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*eps*(2*ell+B+t+4*eta)
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hh := hsource p hp hinj Jo hJo S Z ell R B t eta (2*eps) loss hZ hell
    (by positivity) (le_refl _) hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hP : 0≤physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window := by
    unfold physicalPrincipalFactor
    positivity
  calc
    _ ≤ physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      (C*Z^(ell+R/2+B+t+loss)) := mul_le_mul_of_nonneg_left hh hP
    _ = C*(physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      Z^(ell+R/2+B+t+loss)) := by ring
    _ = C*(Real.exp (window*(1+eps))*
      Z^(r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss)) := by
      rw [physical_principal_exact Z M r ell V delta A B R j t eta tau eps window loss hZp]
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ _) (by positivity)
      dsimp [loss]
      linarith

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI
