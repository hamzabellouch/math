import OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassCount

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def principalSupport {ι : Type*} [DecidableEq ι] {Jo : ℕ}
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool) (x : Source ι Jo) : Finset ι :=
  (extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪x.quotientSupport

lemma principalSupport_norm {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool) (x : Source ι Jo)
    (hx : SourceValid p x) (hextra : extra x.cube⊆x.cube.support)
    (B V T : ℝ) (hB : 0≤B) (hV : 0≤V)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (hC : primeProductNorm p x.firstCommon≤V) (ht : primeProductNorm p x.quotientSupport≤T) :
    primeProductNorm p (principalSupport extra negative x)≤B^2*V*T := by
  have hh := first_whole_extracted_norm p hp x.cube hx.admissible x.firstCommon (extra x.cube)
    hextra negative B hB hb₁ hb₂
  unfold principalSupport
  apply (primeProductNorm_union_le_mul p hp _ _).trans
  exact mul_le_mul (hh.trans (mul_le_mul_of_nonneg_left hC (sq_nonneg _))) ht
    (primeProductNorm_pos p hp _).le (mul_nonneg (sq_nonneg _) hV)

theorem original_weighted_mass (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(B H V T a : ℝ),
    1≤B → 0≤H → 0<V → 0<T → 0≤a → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤H) →
    (∀x∈S,primeProductNorm p x.firstCommon≤V) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤T) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^a)≤
      C*B^(1+eps)*H*V*T*(B^2*V*T)^(eps+a) := by
  obtain ⟨C,hC,hcount⟩ := original_source_card Jmax eps heps
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S B H V T a hB hH hV hT ha hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hcard := hcount p hp hinj Jo hJo S B H V T hB hH hV hT hS hb₁ hb₂ hactive hcommon hquot
  have hBp : 0<B := zero_lt_one.trans_le hB
  calc
    _ ≤ ∑_x∈S,(B^2*V*T)^a := Finset.sum_le_sum (fun x hx=>
      Real.rpow_le_rpow (primeProductNorm_pos p hp _).le
        (principalSupport_norm p hp extra negative x (hS x hx) (hextra x hx) B V T hBp.le hV.le
          (hb₁ x hx) (hb₂ x hx) (hcommon x hx) (hquot x hx)) ha)
    _ = (S.card:ℝ)*(B^2*V*T)^a := by simp
    _ ≤ (C*B^(1+eps)*H*V*T*(B^2*V*T)^eps)*(B^2*V*T)^a :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [mul_assoc,←Real.rpow_add (by positivity : 0<B^2*V*T)]

lemma weighted_mass_power (Z ell R Bfirst t eta eps a : ℝ) (hZ : 0<Z) :
    (Z^(ell+eta))^(1+eps)*Z^((R+eta)/2)*Z^(Bfirst+eta)*Z^(t+eta)*
      ((Z^(ell+eta))^2*Z^(Bfirst+eta)*Z^(t+eta))^(eps+a)=
    Z^(ell+R/2+Bfirst+t+7*eta/2+eps*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul_natCast hZ.le]
  repeat rw [←Real.rpow_add hZ]
  rw [←Real.rpow_mul hZ.le,←Real.rpow_add hZ]
  congr 1
  norm_num
  ring

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI
